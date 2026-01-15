// TodoMultiCollaboration.dfy - Concrete refinement with proofs
//
// This module refines TodoMultiCollaborationSpec, providing:
// - Lemma bodies (proofs) for abstract lemmas declared in the spec
// - Helper lemmas used in the proofs
// - TodoAppCore (compiled client API)
//
// The spec file (TodoMultiCollaborationSpec.dfy) contains the abstract
// types, functions, and lemma signatures. This file provides the proofs.

// === Inlined from TodoMultiCollaborationSpec.dfy ===
// === Inlined from ../kernels/MultiCollaboration.dfy ===
abstract module {:compile false} Domain {

  // --------------------------
  // Core types
  // --------------------------
  type Model(==)
  type Action(==)
  type Err

  datatype Result<T, E> =
    | Ok(value: T)
    | Err(error: E)

  // --------------------------
  // Distinguished error
  // --------------------------
  // Used by the kernel when *no candidate succeeds*.
  // This is NOT a semantic error like MissingCard, etc.
  function RejectErr(): Err

  // --------------------------
  // Semantics
  // --------------------------

  // Global invariant
  ghost predicate Inv(m: Model)

  // Initial model
  function Init(): Model

  // Apply a concrete action; may reject with a domain error
  function TryStep(m: Model, a: Action): Result<Model, Err>

  // Domain obligation: initial model satisfies invariant
  lemma InitSatisfiesInv()
    ensures Inv(Init())

  // Domain obligation: successful steps preserve invariant
  lemma StepPreservesInv(m: Model, a: Action, m2: Model)
    requires Inv(m)
    requires TryStep(m, a) == Ok(m2)
    ensures  Inv(m2)

  // --------------------------
  // Collaboration hooks
  // --------------------------

  // Intent-aware rebasing (total)
  function Rebase(remote: Action, local: Action): Action

  function RebaseThroughSuffix(suffix: seq<Action>, a: Action): Action
    decreases |suffix|
  {
    if |suffix| == 0 then a
    else
      RebaseThroughSuffix(suffix[..|suffix|-1],
                          Rebase(suffix[|suffix|-1], a))
  }

  // Finite set of admissible candidates the server will try
  function Candidates(m: Model, a: Action): seq<Action>

  // Meaning-preservation relation (ghost)
  ghost predicate Explains(orig: Action, cand: Action)

  // --------------------------
  // Small reject surface obligation
  // --------------------------
  // If some admissible interpretation exists, it must appear in Candidates.
  lemma CandidatesComplete(m: Model, orig: Action, aGood: Action, m2: Model)
    requires Inv(m)
    requires Explains(orig, aGood)
    requires TryStep(m, aGood) == Ok(m2)
    ensures  aGood in Candidates(m, orig)
}

abstract module {:compile false} MultiCollaboration {
  import D : Domain

  datatype RejectReason =
    | DomainInvalid

  datatype Reply =
    | Accepted(newVersion: nat, newPresent: D.Model, applied: D.Action, noChange: bool)
    | Rejected(reason: RejectReason, rebased: D.Action)

  datatype RequestOutcome =
    | AuditAccepted(applied: D.Action, noChange: bool)
    | AuditRejected(reason: RejectReason, rebased: D.Action)

  datatype RequestRecord = Req(
    baseVersion: nat,
    orig: D.Action,
    rebased: D.Action,
    chosen: D.Action,
    outcome: RequestOutcome
  )

  datatype ServerState = ServerState(
    present: D.Model,
    appliedLog: seq<D.Action>,
    auditLog: seq<RequestRecord>
  )

  function Version(s: ServerState): nat { |s.appliedLog| }

  // Initialize server with domain's initial model
  function InitServer(): ServerState {
    ServerState(D.Init(), [], [])
  }

  lemma InitServerSatisfiesInv()
    ensures D.Inv(InitServer().present)
  {
  }

  // Choose first candidate that succeeds. If none succeed, reject.
  function ChooseCandidate(m: D.Model, cs: seq<D.Action>): D.Result<(D.Model, D.Action), D.Err>
    decreases |cs|
    ensures ChooseCandidate(m, cs).Ok? ==>
            D.TryStep(m, ChooseCandidate(m, cs).value.1) == D.Ok(ChooseCandidate(m, cs).value.0)
  {
    if |cs| == 0 then D.Err(D.RejectErr()) // NOTE: never exposed; kernel maps this to Reject
    else
      match D.TryStep(m, cs[0])
        case Ok(m2) => D.Ok((m2, cs[0]))
        case Err(_) => ChooseCandidate(m, cs[1..])
  }

  function Dispatch(s: ServerState, baseVersion: nat, orig: D.Action): (ServerState, Reply)
    requires baseVersion <= Version(s)
    requires D.Inv(s.present)
    ensures  D.Inv(Dispatch(s, baseVersion, orig).0.present)
    ensures  Version(Dispatch(s, baseVersion, orig).0) == Version(s) ||
             Version(Dispatch(s, baseVersion, orig).0) == Version(s) + 1
  {
    var suffix := s.appliedLog[baseVersion..];
    var rebased := D.RebaseThroughSuffix(suffix, orig);

    var cs := D.Candidates(s.present, rebased);

    // Try candidates in order.
    match ChooseCandidate(s.present, cs)
      case Ok(pair) =>
        var m2 := pair.0;
        var chosen := pair.1;

        D.StepPreservesInv(s.present, chosen, m2);

        var noChange := (m2 == s.present);
        var newApplied := s.appliedLog + [chosen];
        var rec := Req(baseVersion, orig, rebased, chosen, AuditAccepted(chosen, noChange));
        var newAudit := s.auditLog + [rec];

        (ServerState(m2, newApplied, newAudit),
         Accepted(|newApplied|, m2, chosen, noChange))

      case Err(_) =>
        // Rejected: no candidate succeeded.
        var rec := Req(baseVersion, orig, rebased, rebased, AuditRejected(DomainInvalid, rebased));
        var newAudit := s.auditLog + [rec];

        (ServerState(s.present, s.appliedLog, newAudit),
         Rejected(DomainInvalid, rebased))
  }

  // ===========================================================================
  // Client-side state management
  // ===========================================================================

  datatype ClientState = ClientState(
    baseVersion: nat,           // last synced server version
    present: D.Model,           // current local model (optimistic)
    pending: seq<D.Action>      // actions waiting to be flushed
  )

  // Initialize client from version and model
  function InitClient(version: nat, model: D.Model): ClientState
  {
    ClientState(version, model, [])
  }

  // Create client state synced to server
  function InitClientFromServer(server: ServerState): ClientState
  {
    ClientState(Version(server), server.present, [])
  }

  // Sync: reset client to server state (discard pending)
  function Sync(server: ServerState): ClientState
  {
    ClientState(Version(server), server.present, [])
  }

  // Local dispatch (optimistic update)
  // Policy: apply optimistically if TryStep succeeds, always enqueue
  function ClientLocalDispatch(client: ClientState, action: D.Action): ClientState
  {
    var result := D.TryStep(client.present, action);
    match result
      case Ok(newModel) =>
        // Optimistic success: update local model and enqueue
        ClientState(client.baseVersion, newModel, client.pending + [action])
      case Err(_) =>
        // Optimistic failure: still enqueue (server might accept with fallback)
        ClientState(client.baseVersion, client.present, client.pending + [action])
  }

  // Re-apply pending actions to a model (used after realtime update)
  function ReapplyPending(model: D.Model, pending: seq<D.Action>): D.Model
    decreases |pending|
  {
    if |pending| == 0 then model
    else
      var result := D.TryStep(model, pending[0]);
      var newModel := match result
        case Ok(m) => m
        case Err(_) => model;
      ReapplyPending(newModel, pending[1..])
  }

  // Handle realtime update from server - preserves pending actions
  function HandleRealtimeUpdate(client: ClientState, serverVersion: nat, serverModel: D.Model): ClientState
  {
    if serverVersion > client.baseVersion then
      // Accept update, re-apply pending to get correct optimistic view
      var newPresent := ReapplyPending(serverModel, client.pending);
      ClientState(serverVersion, newPresent, client.pending)
    else
      // Stale update, ignore
      client
  }

  // ===========================================================================
  // Client reply handling
  // ===========================================================================

  // Handle accepted reply from server - removes the dispatched action and preserves the rest
  // Used when a dispatch succeeds and we need to update the client state while keeping
  // any actions that were added to pending while the dispatch was in progress
  function ClientAcceptReply(client: ClientState, newVersion: nat, newPresent: D.Model): ClientState
  {
    if |client.pending| == 0 then
      // No pending actions (shouldn't happen in normal flow, but handle gracefully)
      ClientState(newVersion, newPresent, [])
    else
      // Remove the first pending action (the one that was just dispatched)
      // and re-apply the remaining pending actions on top of the new server state
      var rest := client.pending[1..];
      var reappliedPresent := ReapplyPending(newPresent, rest);
      ClientState(newVersion, reappliedPresent, rest)
  }

  // Handle rejected reply from server - drops the rejected action but preserves the rest
  // Used when a dispatch is rejected by the domain and we need to sync to server state
  // while keeping any other pending actions
  function ClientRejectReply(client: ClientState, freshVersion: nat, freshModel: D.Model): ClientState
  {
    if |client.pending| == 0 then
      // No pending actions (shouldn't happen in normal flow, but handle gracefully)
      ClientState(freshVersion, freshModel, [])
    else
      // Drop the first pending action (the rejected one)
      // and re-apply the remaining pending actions on top of the fresh server state
      var rest := client.pending[1..];
      var reappliedPresent := ReapplyPending(freshModel, rest);
      ClientState(freshVersion, reappliedPresent, rest)
  }

  // ===========================================================================
  // Client state accessors
  // ===========================================================================

  function PendingCount(client: ClientState): nat
  {
    |client.pending|
  }

  function ClientModel(client: ClientState): D.Model
  {
    client.present
  }

  function ClientVersion(client: ClientState): nat
  {
    client.baseVersion
  }

  // ===========================================================================
  // Kernel theorems
  // ===========================================================================

  lemma DispatchPreservesInv(s: ServerState, baseVersion: nat, orig: D.Action)
    requires baseVersion <= Version(s)
    requires D.Inv(s.present)
    ensures  D.Inv(Dispatch(s, baseVersion, orig).0.present)
  {
  }

  // Minimal-reject property (relative to CandidatesComplete):
  // If there exists an explainable action that succeeds, Dispatch must not reject.
  // Contrapositive: if Dispatch rejects, no explainable action can succeed.
  lemma DispatchRejectIsMinimal(s: ServerState, baseVersion: nat, orig: D.Action, aGood: D.Action, m2: D.Model)
    requires baseVersion <= Version(s)
    requires D.Inv(s.present)
    requires D.Explains(D.RebaseThroughSuffix(s.appliedLog[baseVersion..], orig), aGood)
    requires D.TryStep(s.present, aGood) == D.Ok(m2)
    // If an explainable action succeeds, Dispatch cannot reject
    ensures  !Dispatch(s, baseVersion, orig).1.Rejected?
  {
  }

  // Helper: if aGood is in candidates and succeeds, ChooseCandidate returns Ok
  lemma ChooseCandidateFindsGood(m: D.Model, cs: seq<D.Action>, aGood: D.Action, m2: D.Model)
    requires aGood in cs
    requires D.TryStep(m, aGood) == D.Ok(m2)
    ensures  ChooseCandidate(m, cs).Ok?
    decreases |cs|
  {
  }
}

// === End ../kernels/MultiCollaboration.dfy ===

// =============================================================================
// TodoDomain: A collaborative Todo app with projects, lists, tasks, and tags
// =============================================================================
//
// Design decisions:
// - Tasks stay in place when completed (marked done, not moved)
// - Tasks can be assigned to multiple users (set<UserId>)
// - Tasks have optional due dates with timezone-aware validation
// - Tasks can be starred (surfaces to top as priority)
// - No subtasks for now (flat task list)
// - All lists are user-created and equivalent (no special "Inbox")
// - Tasks within lists are ordered and can be reordered
// - Projects start Personal or Collaborative; Personal can become Collaborative
// - Member roles: owner (exactly one) and members
// - Tags are project-scoped
// - Soft delete: deleted tasks stay in DB for restore capability
// - ListId is internal (nat), ListName is user-visible (string)
//
// Conflict resolution (Rebase):
// - DeleteTask conflicts: honor delete, both users notified (app layer)
// - RemoveMember + assignment: remove member, reject assignment
// - MoveList conflicts: remote wins, local warned (app layer)
//
// View layer:
// - Smart lists: Priority (starred, not completed, not deleted), Logbook (completed, not deleted)
// - Multi-project aggregation for "All Projects" view
// - All filtering/counting logic compiled to JS (not ghost)
//
// =============================================================================

abstract module {:compile false} TodoDomainSpec refines Domain {

  // ===========================================================================
  // Core Types
  // ===========================================================================

  type TaskId = nat
  type ListId = nat           // Internal ID, not user-visible
  type TagId = nat
  type UserId = string        // Supabase user IDs are UUIDs as strings

  datatype Option<T> = None | Some(value: T)

  // ---------------------------------------------------------------------------
  // Date with validation
  // ---------------------------------------------------------------------------
  // Note: Timezone handling happens at the app layer (JS Date conversion).
  // The Dafny spec stores dates in user's local timezone as provided by client.

  datatype Date = Date(year: nat, month: nat, day: nat)

  // Days in each month (non-leap year)
  function DaysInMonth(month: nat, year: nat): nat
  {
    if month == 1 then 31
    else if month == 2 then (if IsLeapYear(year) then 29 else 28)
    else if month == 3 then 31
    else if month == 4 then 30
    else if month == 5 then 31
    else if month == 6 then 30
    else if month == 7 then 31
    else if month == 8 then 31
    else if month == 9 then 30
    else if month == 10 then 31
    else if month == 11 then 30
    else if month == 12 then 31
    else 0  // Invalid month
  }

  predicate IsLeapYear(year: nat) {
    (year % 4 == 0 && year % 100 != 0) || (year % 400 == 0)
  }

  predicate ValidDate(d: Date) {
    d.year >= 1970 &&                           // Reasonable minimum
    d.month >= 1 && d.month <= 12 &&            // Valid month
    d.day >= 1 && d.day <= DaysInMonth(d.month, d.year)  // Valid day for month
  }

  // ---------------------------------------------------------------------------
  // Task data
  // ---------------------------------------------------------------------------

  datatype Task = Task(
    title: string,
    notes: string,
    completed: bool,
    starred: bool,             // Starred tasks surface as priority
    dueDate: Option<Date>,     // Optional due date
    assignees: set<UserId>,    // Who is this task assigned to? (multiple)
    tags: set<TagId>,          // Tags attached to this task
    deleted: bool,             // Soft delete flag
    deletedBy: Option<UserId>, // Who deleted it (for restore notification)
    deletedFromList: Option<ListId>  // Which list it was in (for restore)
  )

  // Tag data (just a name for now)
  datatype Tag = Tag(name: string)

  // Project collaboration mode
  datatype ProjectMode = Personal | Collaborative

  // The Model represents a single project's state
  // (Each Supabase project row contains one Model)
  datatype Model = Model(
    mode: ProjectMode,                    // Personal or Collaborative
    owner: UserId,                        // Project owner (exactly one)
    members: set<UserId>,                 // Users who can access (includes owner)
    lists: seq<ListId>,                   // Ordered list IDs (internal)
    listNames: map<ListId, string>,       // ListId -> user-visible name
    tasks: map<ListId, seq<TaskId>>,      // List -> ordered task IDs
    taskData: map<TaskId, Task>,          // TaskId -> Task
    tags: map<TagId, Tag>,                // TagId -> Tag
    nextListId: nat,                      // List ID allocator
    nextTaskId: nat,                      // Task ID allocator
    nextTagId: nat                        // Tag ID allocator
  )

  // ===========================================================================
  // Errors
  // ===========================================================================

  datatype Err =
    | MissingList
    | MissingTask
    | MissingTag
    | MissingUser
    | DuplicateList
    | DuplicateTask        // Task with same title already exists in list
    | DuplicateTag         // Tag with same name already exists in project
    | BadAnchor
    | NotAMember           // User not in project members
    | PersonalProject      // Tried to add member to personal project
    | AlreadyCollaborative // Tried to make collaborative when already is
    | CannotRemoveOwner    // Tried to remove the owner
    | TaskDeleted          // Tried to operate on deleted task
    | InvalidDate          // Due date failed validation
    | Rejected             // Kernel rejection (no candidate succeeded)

  function RejectErr(): Err { Rejected }

  // Convert error to human-readable string (compiled, for JS interop)
  function ErrToString(err: Err): string
  {
    match err
    case MissingList => "List not found"
    case MissingTask => "Task not found"
    case MissingTag => "Tag not found"
    case MissingUser => "User not found"
    case DuplicateList => "List with this name already exists"
    case DuplicateTask => "Task with this title already exists in list"
    case DuplicateTag => "Tag with this name already exists"
    case BadAnchor => "Invalid anchor position"
    case NotAMember => "User is not a project member"
    case PersonalProject => "Cannot add members to personal project"
    case AlreadyCollaborative => "Project is already collaborative"
    case CannotRemoveOwner => "Cannot remove the project owner"
    case TaskDeleted => "Task has been deleted"
    case InvalidDate => "Invalid date"
    case Rejected => "Action rejected"
  }

  // ===========================================================================
  // Anchor-based placement
  // ===========================================================================

  datatype Place =
    | AtEnd
    | Before(anchor: TaskId)
    | After(anchor: TaskId)

  datatype ListPlace =
    | ListAtEnd
    | ListBefore(anchor: ListId)
    | ListAfter(anchor: ListId)

  // ===========================================================================
  // Actions
  // ===========================================================================

  datatype Action =
    // No-op (useful for rebasing)
    | NoOp

    // List CRUD
    | AddList(name: string)                              // Creates list with name
    | RenameList(listId: ListId, newName: string)        // Rename existing list
    | DeleteList(listId: ListId)
    | MoveList(listId: ListId, listPlace: ListPlace)

    // Task CRUD
    | AddTask(listId: ListId, title: string)
    | EditTask(taskId: TaskId, title: string, notes: string)
    | DeleteTask(taskId: TaskId, userId: UserId)         // Soft delete, track who
    | RestoreTask(taskId: TaskId)                        // Undo soft delete
    | MoveTask(taskId: TaskId, toList: ListId, taskPlace: Place)

    // Task status
    | CompleteTask(taskId: TaskId)
    | UncompleteTask(taskId: TaskId)
    | StarTask(taskId: TaskId)
    | UnstarTask(taskId: TaskId)

    // Task due date
    | SetDueDate(taskId: TaskId, dueDate: Option<Date>)

    // Task assignment (multiple assignees)
    | AssignTask(taskId: TaskId, userId: UserId)      // Add assignee
    | UnassignTask(taskId: TaskId, userId: UserId)    // Remove assignee

    // Tags on tasks
    | AddTagToTask(taskId: TaskId, tagId: TagId)
    | RemoveTagFromTask(taskId: TaskId, tagId: TagId)

    // Tag CRUD (project-level)
    | CreateTag(name: string)
    | RenameTag(tagId: TagId, newName: string)
    | DeleteTag(tagId: TagId)

    // Project mode
    | MakeCollaborative    // Convert Personal -> Collaborative

    // Membership (collaborative projects only)
    | AddMember(userId: UserId)
    | RemoveMember(userId: UserId)

  // ===========================================================================
  // Invariant
  // ===========================================================================

  ghost predicate Inv(m: Model)
  {
    // A: Lists are unique
    NoDupSeq(m.lists)

    // B: listNames and tasks maps defined exactly on lists
    && (forall l :: l in m.listNames <==> SeqContains(m.lists, l))
    && (forall l :: l in m.tasks <==> SeqContains(m.lists, l))

    // C: Every taskId in any list exists in taskData
    && (forall l, id :: l in m.tasks && SeqContains(m.tasks[l], id) ==> id in m.taskData)

    // D: Every non-deleted task appears in exactly one list
    && (forall id :: id in m.taskData && !m.taskData[id].deleted ==> CountInLists(m, id) == 1)

    // D': Deleted tasks are not in any list (required for RestoreTask correctness)
    && (forall id :: id in m.taskData && m.taskData[id].deleted ==> CountInLists(m, id) == 0)

    // E: No duplicate task IDs within any single list
    && (forall l :: l in m.tasks ==> NoDupSeq(m.tasks[l]))

    // F: All tags referenced by tasks exist
    && (forall id :: id in m.taskData ==> m.taskData[id].tags <= m.tags.Keys)

    // G: Allocators fresh
    && (forall id :: SeqContains(m.lists, id) ==> id < m.nextListId)
    && (forall id :: id in m.taskData ==> id < m.nextTaskId)
    && (forall id :: id in m.tags ==> id < m.nextTagId)

    // H: Assignees must be members
    && (forall id :: id in m.taskData ==> m.taskData[id].assignees <= m.members)

    // I: Owner is always a member
    && m.owner in m.members

    // J: Personal projects have exactly one member (the owner)
    && (m.mode.Personal? ==> m.members == {m.owner})

    // K: Collaborative projects have at least one member
    && (m.mode.Collaborative? ==> |m.members| >= 1)

    // L: Due dates are valid if present
    && (forall id :: id in m.taskData && m.taskData[id].dueDate.Some?
          ==> ValidDate(m.taskData[id].dueDate.value))

    // M: List names are unique within the project (case-insensitive)
    && (forall l1, l2 :: l1 in m.listNames && l2 in m.listNames && l1 != l2
          ==> !EqIgnoreCase(m.listNames[l1], m.listNames[l2]))

    // N: Task titles are unique within each list (case-insensitive)
    && (forall l, t1, t2 :: l in m.tasks
          && SeqContains(m.tasks[l], t1) && t1 in m.taskData && !m.taskData[t1].deleted
          && SeqContains(m.tasks[l], t2) && t2 in m.taskData && !m.taskData[t2].deleted
          && t1 != t2
          ==> !EqIgnoreCase(m.taskData[t1].title, m.taskData[t2].title))

    // O: Tag names are unique within the project (case-insensitive)
    && (forall t1, t2 :: t1 in m.tags && t2 in m.tags && t1 != t2
          ==> !EqIgnoreCase(m.tags[t1].name, m.tags[t2].name))
  }

  // ===========================================================================
  // Initial Model
  // ===========================================================================

  // Placeholder for initial owner (will be replaced by app layer)
  const InitialOwner: UserId := ""

  function Init(): Model {
    Model(
      Personal,
      InitialOwner,         // owner
      {InitialOwner},       // members (owner only for Personal)
      [],                   // lists
      map[],                // listNames
      map[],                // tasks
      map[],                // taskData
      map[],                // tags
      0,                    // nextListId
      0,                    // nextTaskId
      0                     // nextTagId
    )
  }

  // ===========================================================================
  // Helper Functions
  // ===========================================================================

  predicate NoDupSeq<T(==)>(s: seq<T>)
  {
    forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j]
  }

  function SeqContains<T(==)>(s: seq<T>, x: T): bool {
    exists i :: 0 <= i < |s| && s[i] == x
  }

  function RemoveFirst<T(==)>(s: seq<T>, x: T): seq<T>
  {
    if |s| == 0 then []
    else if s[0] == x then s[1..]
    else [s[0]] + RemoveFirst(s[1..], x)
  }

  function InsertAt<T>(s: seq<T>, i: nat, x: T): seq<T>
    requires i <= |s|
  {
    s[..i] + [x] + s[i..]
  }

  function IndexOf<T(==)>(s: seq<T>, x: T): int
  {
    if |s| == 0 then -1
    else if s[0] == x then 0
    else
      var j := IndexOf(s[1..], x);
      if j < 0 then -1 else j + 1
  }

  function ClampPos(pos: int, n: int): nat
    requires n >= 0
  {
    if pos <= 0 then 0
    else if pos >= n then n as nat
    else pos as nat
  }

  function Get<K,V>(mp: map<K,V>, k: K, d: V): V {
    if k in mp then mp[k] else d
  }

  function TaskList(m: Model, l: ListId): seq<TaskId> {
    Get(m.tasks, l, [])
  }

  // Find which list contains a task (returns None if not found)
  function FindListForTask(m: Model, taskId: TaskId): Option<ListId>
  {
    FindListForTaskHelper(m.lists, m.tasks, taskId)
  }

  function FindListForTaskHelper(lists: seq<ListId>, tasks: map<ListId, seq<TaskId>>, taskId: TaskId): Option<ListId>
  {
    if |lists| == 0 then None
    else
      var l := lists[0];
      var lane := if l in tasks then tasks[l] else [];
      if SeqContains(lane, taskId) then Some(l)
      else FindListForTaskHelper(lists[1..], tasks, taskId)
  }

  // Count occurrences of taskId across all lists
  function CountInLists(m: Model, id: TaskId): nat
  {
    CountInListsHelper(m.lists, m.tasks, id)
  }

  function CountInListsHelper(lists: seq<ListId>, tasks: map<ListId, seq<TaskId>>, id: TaskId): nat
  {
    if |lists| == 0 then 0
    else
      var l := lists[0];
      var lane := if l in tasks then tasks[l] else [];
      var here := if SeqContains(lane, id) then 1 else 0;
      here + CountInListsHelper(lists[1..], tasks, id)
  }

  // Position from anchor for tasks
  function PosFromPlace(lane: seq<TaskId>, p: Place): int
  {
    match p
      case AtEnd => |lane|
      case Before(a) =>
        var i := IndexOf(lane, a);
        if i < 0 then -1 else i
      case After(a) =>
        var i := IndexOf(lane, a);
        if i < 0 then -1 else i + 1
  }

  // Position from anchor for lists
  function PosFromListPlace(lists: seq<ListId>, p: ListPlace): int
  {
    match p
      case ListAtEnd => |lists|
      case ListBefore(a) =>
        var i := IndexOf(lists, a);
        if i < 0 then -1 else i
      case ListAfter(a) =>
        var i := IndexOf(lists, a);
        if i < 0 then -1 else i + 1
  }

  // Remove a tag from all tasks
  function RemoveTagFromAllTasks(taskData: map<TaskId, Task>, tagId: TagId): map<TaskId, Task>
  {
    map id | id in taskData ::
      var t := taskData[id];
      Task(t.title, t.notes, t.completed, t.starred, t.dueDate, t.assignees,
           t.tags - {tagId}, t.deleted, t.deletedBy, t.deletedFromList)
  }

  // Remove assignee from all tasks (when member is removed)
  function ClearAssigneeFromAllTasks(taskData: map<TaskId, Task>, userId: UserId): map<TaskId, Task>
  {
    map id | id in taskData ::
      var t := taskData[id];
      Task(t.title, t.notes, t.completed, t.starred, t.dueDate,
           t.assignees - {userId}, t.tags, t.deleted, t.deletedBy, t.deletedFromList)
  }

  // ---------------------------------------------------------------------------
  // Case-insensitive string comparison
  // ---------------------------------------------------------------------------

  // Convert a single character to lowercase
  function ToLowerChar(c: char): char
  {
    if 'A' <= c <= 'Z' then (c as int - 'A' as int + 'a' as int) as char
    else c
  }

  // Convert a string to lowercase
  function ToLower(s: string): string
  {
    if |s| == 0 then ""
    else [ToLowerChar(s[0])] + ToLower(s[1..])
  }

  // Case-insensitive string equality
  predicate EqIgnoreCase(a: string, b: string)
  {
    ToLower(a) == ToLower(b)
  }

  // Check if a list name exists (optionally excluding one list, for rename)
  // Uses case-insensitive comparison
  predicate ListNameExists(m: Model, name: string, excludeList: Option<ListId>)
  {
    exists l :: l in m.listNames &&
      (excludeList.None? || l != excludeList.value) &&
      EqIgnoreCase(m.listNames[l], name)
  }

  // Check if a task title exists in a specific list (optionally excluding one task, for edit)
  // Uses case-insensitive comparison
  predicate TaskTitleExistsInList(m: Model, listId: ListId, title: string, excludeTask: Option<TaskId>)
  {
    listId in m.tasks &&
    exists taskId :: taskId in m.taskData &&
      SeqContains(m.tasks[listId], taskId) &&
      !m.taskData[taskId].deleted &&
      (excludeTask.None? || taskId != excludeTask.value) &&
      EqIgnoreCase(m.taskData[taskId].title, title)
  }

  // Check if a tag name exists (optionally excluding one tag, for rename)
  // Uses case-insensitive comparison
  predicate TagNameExists(m: Model, name: string, excludeTag: Option<TagId>)
  {
    exists t :: t in m.tags &&
      (excludeTag.None? || t != excludeTag.value) &&
      EqIgnoreCase(m.tags[t].name, name)
  }

  // ===========================================================================
  // TryStep: Apply an action to the model
  // ===========================================================================

  function TryStep(m: Model, a: Action): Result<Model, Err>
  {
    match a

      case NoOp => Ok(m)

      // -----------------------------------------------------------------------
      // List operations
      // -----------------------------------------------------------------------

      case AddList(name) =>
        if ListNameExists(m, name, None) then Err(DuplicateList)
        else
          var id := m.nextListId;
          Ok(Model(
            m.mode, m.owner, m.members,
            m.lists + [id],
            m.listNames[id := name],
            m.tasks[id := []],
            m.taskData, m.tags,
            m.nextListId + 1, m.nextTaskId, m.nextTagId
          ))

      case RenameList(listId, newName) =>
        if !SeqContains(m.lists, listId) then Err(MissingList)
        else if ListNameExists(m, newName, Some(listId)) then Err(DuplicateList)
        else Ok(Model(
          m.mode, m.owner, m.members, m.lists,
          m.listNames[listId := newName],
          m.tasks, m.taskData, m.tags,
          m.nextListId, m.nextTaskId, m.nextTagId
        ))

      case DeleteList(listId) =>
        if !SeqContains(m.lists, listId) then Ok(m)  // Idempotent
        else
          var tasksToRemove := set id | id in TaskList(m, listId) :: id;
          var newTaskData := map id | id in m.taskData && id !in tasksToRemove :: m.taskData[id];
          var newLists := RemoveFirst(m.lists, listId);
          var newListNames := m.listNames - {listId};
          var newTasks := m.tasks - {listId};
          Ok(Model(
            m.mode, m.owner, m.members, newLists, newListNames, newTasks, newTaskData, m.tags,
            m.nextListId, m.nextTaskId, m.nextTagId
          ))

      case MoveList(listId, listPlace) =>
        if !SeqContains(m.lists, listId) then Err(MissingList)
        else
          var lists1 := RemoveFirst(m.lists, listId);
          var pos := PosFromListPlace(lists1, listPlace);
          if pos < 0 then Err(BadAnchor)
          else
            var k := ClampPos(pos, |lists1|);
            var newLists := InsertAt(lists1, k, listId);
            Ok(Model(
              m.mode, m.owner, m.members, newLists, m.listNames, m.tasks, m.taskData, m.tags,
              m.nextListId, m.nextTaskId, m.nextTagId
            ))

      // -----------------------------------------------------------------------
      // Task CRUD
      // -----------------------------------------------------------------------

      case AddTask(listId, title) =>
        if !SeqContains(m.lists, listId) then Err(MissingList)
        else if TaskTitleExistsInList(m, listId, title, None) then Err(DuplicateTask)
        else
          var id := m.nextTaskId;
          var newTask := Task(title, "", false, false, None, {}, {}, false, None, None);
          Ok(Model(
            m.mode, m.owner, m.members, m.lists, m.listNames,
            m.tasks[listId := TaskList(m, listId) + [id]],
            m.taskData[id := newTask],
            m.tags,
            m.nextListId, m.nextTaskId + 1, m.nextTagId
          ))

      case EditTask(taskId, title, notes) =>
        if !(taskId in m.taskData) then Err(MissingTask)
        else if m.taskData[taskId].deleted then Err(TaskDeleted)
        else
          var currentList := FindListForTask(m, taskId);
          if currentList.Some? && TaskTitleExistsInList(m, currentList.value, title, Some(taskId))
          then Err(DuplicateTask)
          else
            var t := m.taskData[taskId];
            var updated := Task(title, notes, t.completed, t.starred, t.dueDate,
                                t.assignees, t.tags, t.deleted, t.deletedBy, t.deletedFromList);
            Ok(Model(
              m.mode, m.owner, m.members, m.lists, m.listNames, m.tasks,
              m.taskData[taskId := updated], m.tags,
              m.nextListId, m.nextTaskId, m.nextTagId
            ))

      case DeleteTask(taskId, userId) =>
        if !(taskId in m.taskData) then Ok(m)  // Idempotent
        else if m.taskData[taskId].deleted then Ok(m)  // Already deleted
        else
          // Soft delete: mark as deleted, record which list, remove from list
          var t := m.taskData[taskId];
          var fromList := FindListForTask(m, taskId);
          var updated := Task(t.title, t.notes, t.completed, t.starred, t.dueDate,
                              t.assignees, t.tags, true, Some(userId), fromList);
          var newTasks := map l | l in m.tasks :: RemoveFirst(m.tasks[l], taskId);
          Ok(Model(
            m.mode, m.owner, m.members, m.lists, m.listNames, newTasks,
            m.taskData[taskId := updated], m.tags,
            m.nextListId, m.nextTaskId, m.nextTagId
          ))

      case RestoreTask(taskId) =>
        if !(taskId in m.taskData) then Err(MissingTask)
        else if !m.taskData[taskId].deleted then Ok(m)  // Not deleted, idempotent
        else if |m.lists| == 0 then Err(MissingList)  // No lists to restore to
        else
          // Restore: clear deleted flag, add back to original list (or first if original gone)
          var t := m.taskData[taskId];
          // Try original list first, fall back to first list
          var targetList :=
            if t.deletedFromList.Some? && SeqContains(m.lists, t.deletedFromList.value)
            then t.deletedFromList.value
            else m.lists[0];
          // Check for duplicate title in target list
          if TaskTitleExistsInList(m, targetList, t.title, None) then Err(DuplicateTask)
          else
            var updated := Task(t.title, t.notes, t.completed, t.starred, t.dueDate,
                                t.assignees, t.tags, false, None, None);
            Ok(Model(
              m.mode, m.owner, m.members, m.lists, m.listNames,
              m.tasks[targetList := TaskList(m, targetList) + [taskId]],
              m.taskData[taskId := updated], m.tags,
              m.nextListId, m.nextTaskId, m.nextTagId
            ))

      case MoveTask(taskId, toList, taskPlace) =>
        if !(taskId in m.taskData) then Err(MissingTask)
        else if m.taskData[taskId].deleted then Err(TaskDeleted)
        else if !SeqContains(m.lists, toList) then Err(MissingList)
        // Check for duplicate title in destination list (exclude this task since it's moving)
        else if TaskTitleExistsInList(m, toList, m.taskData[taskId].title, Some(taskId))
        then Err(DuplicateTask)
        else
          var tasks1 := map l | l in m.tasks :: RemoveFirst(m.tasks[l], taskId);
          var tgt := Get(tasks1, toList, []);
          var pos := PosFromPlace(tgt, taskPlace);
          if pos < 0 then Err(BadAnchor)
          else
            var k := ClampPos(pos, |tgt|);
            var tgt2 := InsertAt(tgt, k, taskId);
            Ok(Model(
              m.mode, m.owner, m.members, m.lists, m.listNames,
              tasks1[toList := tgt2], m.taskData, m.tags,
              m.nextListId, m.nextTaskId, m.nextTagId
            ))

      // -----------------------------------------------------------------------
      // Task status
      // -----------------------------------------------------------------------

      case CompleteTask(taskId) =>
        if !(taskId in m.taskData) then Err(MissingTask)
        else if m.taskData[taskId].deleted then Err(TaskDeleted)
        else
          var t := m.taskData[taskId];
          var updated := Task(t.title, t.notes, true, t.starred, t.dueDate,
                              t.assignees, t.tags, t.deleted, t.deletedBy, t.deletedFromList);
          Ok(Model(
            m.mode, m.owner, m.members, m.lists, m.listNames, m.tasks,
            m.taskData[taskId := updated], m.tags,
            m.nextListId, m.nextTaskId, m.nextTagId
          ))

      case UncompleteTask(taskId) =>
        if !(taskId in m.taskData) then Err(MissingTask)
        else if m.taskData[taskId].deleted then Err(TaskDeleted)
        else
          var t := m.taskData[taskId];
          var updated := Task(t.title, t.notes, false, t.starred, t.dueDate,
                              t.assignees, t.tags, t.deleted, t.deletedBy, t.deletedFromList);
          Ok(Model(
            m.mode, m.owner, m.members, m.lists, m.listNames, m.tasks,
            m.taskData[taskId := updated], m.tags,
            m.nextListId, m.nextTaskId, m.nextTagId
          ))

      case StarTask(taskId) =>
        if !(taskId in m.taskData) then Err(MissingTask)
        else if m.taskData[taskId].deleted then Err(TaskDeleted)
        else
          var t := m.taskData[taskId];
          var updated := Task(t.title, t.notes, t.completed, true, t.dueDate,
                              t.assignees, t.tags, t.deleted, t.deletedBy, t.deletedFromList);
          Ok(Model(
            m.mode, m.owner, m.members, m.lists, m.listNames, m.tasks,
            m.taskData[taskId := updated], m.tags,
            m.nextListId, m.nextTaskId, m.nextTagId
          ))

      case UnstarTask(taskId) =>
        if !(taskId in m.taskData) then Err(MissingTask)
        else if m.taskData[taskId].deleted then Err(TaskDeleted)
        else
          var t := m.taskData[taskId];
          var updated := Task(t.title, t.notes, t.completed, false, t.dueDate,
                              t.assignees, t.tags, t.deleted, t.deletedBy, t.deletedFromList);
          Ok(Model(
            m.mode, m.owner, m.members, m.lists, m.listNames, m.tasks,
            m.taskData[taskId := updated], m.tags,
            m.nextListId, m.nextTaskId, m.nextTagId
          ))

      // -----------------------------------------------------------------------
      // Task due date
      // -----------------------------------------------------------------------

      case SetDueDate(taskId, dueDate) =>
        if !(taskId in m.taskData) then Err(MissingTask)
        else if m.taskData[taskId].deleted then Err(TaskDeleted)
        else if dueDate.Some? && !ValidDate(dueDate.value) then Err(InvalidDate)
        else
          var t := m.taskData[taskId];
          var updated := Task(t.title, t.notes, t.completed, t.starred, dueDate,
                              t.assignees, t.tags, t.deleted, t.deletedBy, t.deletedFromList);
          Ok(Model(
            m.mode, m.owner, m.members, m.lists, m.listNames, m.tasks,
            m.taskData[taskId := updated], m.tags,
            m.nextListId, m.nextTaskId, m.nextTagId
          ))

      // -----------------------------------------------------------------------
      // Task assignment
      // -----------------------------------------------------------------------

      case AssignTask(taskId, userId) =>
        if !(taskId in m.taskData) then Err(MissingTask)
        else if m.taskData[taskId].deleted then Err(TaskDeleted)
        else if !(userId in m.members) then Err(NotAMember)
        else
          var t := m.taskData[taskId];
          var updated := Task(t.title, t.notes, t.completed, t.starred, t.dueDate,
                              t.assignees + {userId}, t.tags, t.deleted, t.deletedBy, t.deletedFromList);
          Ok(Model(
            m.mode, m.owner, m.members, m.lists, m.listNames, m.tasks,
            m.taskData[taskId := updated], m.tags,
            m.nextListId, m.nextTaskId, m.nextTagId
          ))

      case UnassignTask(taskId, userId) =>
        if !(taskId in m.taskData) then Err(MissingTask)
        else if m.taskData[taskId].deleted then Err(TaskDeleted)
        else
          var t := m.taskData[taskId];
          var updated := Task(t.title, t.notes, t.completed, t.starred, t.dueDate,
                              t.assignees - {userId}, t.tags, t.deleted, t.deletedBy, t.deletedFromList);
          Ok(Model(
            m.mode, m.owner, m.members, m.lists, m.listNames, m.tasks,
            m.taskData[taskId := updated], m.tags,
            m.nextListId, m.nextTaskId, m.nextTagId
          ))

      // -----------------------------------------------------------------------
      // Tags on tasks
      // -----------------------------------------------------------------------

      case AddTagToTask(taskId, tagId) =>
        if !(taskId in m.taskData) then Err(MissingTask)
        else if m.taskData[taskId].deleted then Err(TaskDeleted)
        else if !(tagId in m.tags) then Err(MissingTag)
        else
          var t := m.taskData[taskId];
          var updated := Task(t.title, t.notes, t.completed, t.starred, t.dueDate,
                              t.assignees, t.tags + {tagId}, t.deleted, t.deletedBy, t.deletedFromList);
          Ok(Model(
            m.mode, m.owner, m.members, m.lists, m.listNames, m.tasks,
            m.taskData[taskId := updated], m.tags,
            m.nextListId, m.nextTaskId, m.nextTagId
          ))

      case RemoveTagFromTask(taskId, tagId) =>
        if !(taskId in m.taskData) then Err(MissingTask)
        else if m.taskData[taskId].deleted then Err(TaskDeleted)
        else
          var t := m.taskData[taskId];
          var updated := Task(t.title, t.notes, t.completed, t.starred, t.dueDate,
                              t.assignees, t.tags - {tagId}, t.deleted, t.deletedBy, t.deletedFromList);
          Ok(Model(
            m.mode, m.owner, m.members, m.lists, m.listNames, m.tasks,
            m.taskData[taskId := updated], m.tags,
            m.nextListId, m.nextTaskId, m.nextTagId
          ))

      // -----------------------------------------------------------------------
      // Tag CRUD
      // -----------------------------------------------------------------------

      case CreateTag(name) =>
        if TagNameExists(m, name, None) then Err(DuplicateTag)
        else
          var id := m.nextTagId;
          Ok(Model(
            m.mode, m.owner, m.members, m.lists, m.listNames, m.tasks, m.taskData,
            m.tags[id := Tag(name)],
            m.nextListId, m.nextTaskId, m.nextTagId + 1
          ))

      case RenameTag(tagId, newName) =>
        if !(tagId in m.tags) then Err(MissingTag)
        else if TagNameExists(m, newName, Some(tagId)) then Err(DuplicateTag)
        else Ok(Model(
          m.mode, m.owner, m.members, m.lists, m.listNames, m.tasks, m.taskData,
          m.tags[tagId := Tag(newName)],
          m.nextListId, m.nextTaskId, m.nextTagId
        ))

      case DeleteTag(tagId) =>
        if !(tagId in m.tags) then Ok(m)  // Idempotent
        else
          var newTaskData := RemoveTagFromAllTasks(m.taskData, tagId);
          var newTags := m.tags - {tagId};
          Ok(Model(
            m.mode, m.owner, m.members, m.lists, m.listNames, m.tasks, newTaskData, newTags,
            m.nextListId, m.nextTaskId, m.nextTagId
          ))

      // -----------------------------------------------------------------------
      // Project mode
      // -----------------------------------------------------------------------

      case MakeCollaborative =>
        if m.mode.Collaborative? then Ok(m)  // Already collaborative, idempotent
        else
          Ok(Model(
            Collaborative, m.owner, m.members, m.lists, m.listNames, m.tasks, m.taskData, m.tags,
            m.nextListId, m.nextTaskId, m.nextTagId
          ))

      // -----------------------------------------------------------------------
      // Membership
      // -----------------------------------------------------------------------

      case AddMember(userId) =>
        if m.mode.Personal? then Err(PersonalProject)
        else if userId in m.members then Ok(m)  // Idempotent
        else Ok(Model(
          m.mode, m.owner, m.members + {userId}, m.lists, m.listNames, m.tasks, m.taskData, m.tags,
          m.nextListId, m.nextTaskId, m.nextTagId
        ))

      case RemoveMember(userId) =>
        if userId == m.owner then Err(CannotRemoveOwner)
        else if !(userId in m.members) then Ok(m)  // Idempotent
        else
          // Clear assignments to removed user
          var newTaskData := ClearAssigneeFromAllTasks(m.taskData, userId);
          Ok(Model(
            m.mode, m.owner, m.members - {userId}, m.lists, m.listNames, m.tasks, newTaskData, m.tags,
            m.nextListId, m.nextTaskId, m.nextTagId
          ))
  }

  // ===========================================================================
  // Collaboration Hooks
  // ===========================================================================

  // Helper: degrade place to AtEnd if anchor is the moved task
  function DegradeIfAnchorMoved(movedId: TaskId, p: Place): Place
  {
    match p
      case AtEnd => AtEnd
      case Before(a) => if a == movedId then AtEnd else p
      case After(a) => if a == movedId then AtEnd else p
  }

  // Helper: degrade list place to AtEnd if anchor is the moved list
  function DegradeIfListAnchorMoved(movedId: ListId, p: ListPlace): ListPlace
  {
    match p
      case ListAtEnd => ListAtEnd
      case ListBefore(a) => if a == movedId then ListAtEnd else p
      case ListAfter(a) => if a == movedId then ListAtEnd else p
  }

  // Rebase: intent-aware transformation of local action given remote action
  function Rebase(remote: Action, local: Action): Action
  {
    match (remote, local)
      case (NoOp, _) => local
      case (_, NoOp) => NoOp

      // -----------------------------------------------------------------------
      // DeleteTask conflicts: honor delete, local op becomes NoOp
      // (app layer notifies both users of the conflict)
      // -----------------------------------------------------------------------
      case (DeleteTask(rid, _), EditTask(lid, _, _)) =>
        if rid == lid then NoOp else local
      case (DeleteTask(rid, _), MoveTask(lid, _, _)) =>
        if rid == lid then NoOp else local
      case (DeleteTask(rid, _), CompleteTask(lid)) =>
        if rid == lid then NoOp else local
      case (DeleteTask(rid, _), UncompleteTask(lid)) =>
        if rid == lid then NoOp else local
      case (DeleteTask(rid, _), StarTask(lid)) =>
        if rid == lid then NoOp else local
      case (DeleteTask(rid, _), UnstarTask(lid)) =>
        if rid == lid then NoOp else local
      case (DeleteTask(rid, _), SetDueDate(lid, _)) =>
        if rid == lid then NoOp else local
      case (DeleteTask(rid, _), AssignTask(lid, _)) =>
        if rid == lid then NoOp else local
      case (DeleteTask(rid, _), UnassignTask(lid, _)) =>
        if rid == lid then NoOp else local
      case (DeleteTask(rid, _), AddTagToTask(lid, _)) =>
        if rid == lid then NoOp else local
      case (DeleteTask(rid, _), RemoveTagFromTask(lid, _)) =>
        if rid == lid then NoOp else local

      // -----------------------------------------------------------------------
      // RemoveMember conflicts: member is removed, assignment becomes NoOp
      // -----------------------------------------------------------------------
      case (RemoveMember(ruid), AssignTask(taskId, luid)) =>
        if ruid == luid then NoOp else local

      // -----------------------------------------------------------------------
      // MoveList conflicts: remote wins, local becomes NoOp
      // (app layer warns local user their move couldn't be applied)
      // -----------------------------------------------------------------------
      case (MoveList(rid, _), MoveList(lid, _)) =>
        if rid == lid then NoOp else local

      // -----------------------------------------------------------------------
      // MoveTask conflicts: same task -> keep local (LWW), different -> degrade anchor
      // -----------------------------------------------------------------------
      case (MoveTask(rid, _, _), MoveTask(lid, ltoList, lplace)) =>
        if rid == lid then local
        else MoveTask(lid, ltoList, DegradeIfAnchorMoved(rid, lplace))

      // -----------------------------------------------------------------------
      // Task edits: keep local (LWW)
      // -----------------------------------------------------------------------
      case (EditTask(_, _, _), EditTask(_, _, _)) => local
      case (CompleteTask(_), CompleteTask(_)) => local
      case (UncompleteTask(_), UncompleteTask(_)) => local
      case (StarTask(_), StarTask(_)) => local
      case (UnstarTask(_), UnstarTask(_)) => local
      case (AssignTask(_, _), AssignTask(_, _)) => local
      case (UnassignTask(_, _), UnassignTask(_, _)) => local
      case (SetDueDate(_, _), SetDueDate(_, _)) => local

      // Default: keep local
      case (_, _) => local
  }

  // Ghost predicate: is candidate a meaning-preserving interpretation of orig?
  ghost predicate Explains(orig: Action, cand: Action)
  {
    match (orig, cand)
      // MoveTask: same task, same destination, placement is original or AtEnd
      case (MoveTask(oid, otoList, origPlace), MoveTask(cid, ctoList, candPlace)) =>
        oid == cid && otoList == ctoList &&
        (candPlace == origPlace || candPlace == AtEnd)

      // MoveList: same list, placement is original or AtEnd
      case (MoveList(oid, origPlace), MoveList(cid, candPlace)) =>
        oid == cid &&
        (candPlace == origPlace || candPlace == ListAtEnd)

      // All other actions: exact equality
      case (_, _) => orig == cand
  }

  // Candidates: list of actions to try for conflict resolution
  function Candidates(m: Model, a: Action): seq<Action>
  {
    match a
      case MoveTask(id, toList, taskPlace) =>
        var lane := TaskList(m, toList);
        if taskPlace == AtEnd then
          [MoveTask(id, toList, AtEnd)]
        else if |lane| == 0 then
          [MoveTask(id, toList, taskPlace), MoveTask(id, toList, AtEnd)]
        else
          var first := lane[0];
          [MoveTask(id, toList, taskPlace),
           MoveTask(id, toList, AtEnd),
           MoveTask(id, toList, Before(first))]

      case MoveList(id, listPlace) =>
        if listPlace == ListAtEnd then
          [MoveList(id, ListAtEnd)]
        else if |m.lists| == 0 then
          [MoveList(id, listPlace), MoveList(id, ListAtEnd)]
        else
          var first := m.lists[0];
          [MoveList(id, listPlace),
           MoveList(id, ListAtEnd),
           MoveList(id, ListBefore(first))]

      case _ =>
        [a]
  }

  // ===========================================================================
  // View Layer: Smart Lists and Aggregation (all compiled, not ghost)
  // ===========================================================================

  // ---------------------------------------------------------------------------
  // Types
  // ---------------------------------------------------------------------------

  type ProjectId = string   // Supabase project UUIDs

  datatype ViewMode =
    | SingleProject         // View one project at a time
    | AllProjects           // Aggregate view across all projects

  datatype SmartListType =
    | Priority              // Starred, not completed, not deleted
    | Logbook               // Completed, not deleted

  // ---------------------------------------------------------------------------
  // Smart List Predicates (compiled)
  // ---------------------------------------------------------------------------

  // A task appears in the Priority smart list if:
  // - It is starred
  // - It is NOT completed
  // - It is NOT deleted
  predicate IsPriorityTask(t: Task)
  {
    t.starred && !t.completed && !t.deleted
  }

  // A task appears in the Logbook smart list if:
  // - It IS completed
  // - It is NOT deleted
  predicate IsLogbookTask(t: Task)
  {
    t.completed && !t.deleted
  }

  // A task is visible (not soft-deleted)
  predicate IsVisibleTask(t: Task)
  {
    !t.deleted
  }

  // Check if a task matches a smart list filter
  predicate MatchesSmartList(t: Task, smartList: SmartListType)
  {
    match smartList
      case Priority => IsPriorityTask(t)
      case Logbook => IsLogbookTask(t)
  }

  // ---------------------------------------------------------------------------
  // Single-Project Query Functions (compiled)
  // ---------------------------------------------------------------------------

  // Get all visible (non-deleted) task IDs in a model
  function GetVisibleTaskIds(m: Model): set<TaskId>
  {
    set id | id in m.taskData && IsVisibleTask(m.taskData[id]) :: id
  }

  // Get all task IDs matching a smart list filter
  function GetSmartListTaskIds(m: Model, smartList: SmartListType): set<TaskId>
  {
    set id | id in m.taskData && MatchesSmartList(m.taskData[id], smartList) :: id
  }

  // Get priority task IDs
  function GetPriorityTaskIds(m: Model): set<TaskId>
  {
    set id | id in m.taskData && IsPriorityTask(m.taskData[id]) :: id
  }

  // Get logbook task IDs
  function GetLogbookTaskIds(m: Model): set<TaskId>
  {
    set id | id in m.taskData && IsLogbookTask(m.taskData[id]) :: id
  }

  // Get deleted task IDs (for trash view)
  function GetDeletedTaskIds(m: Model): set<TaskId>
  {
    set id | id in m.taskData && m.taskData[id].deleted :: id
  }

  // Count tasks matching a smart list filter
  function CountSmartListTasks(m: Model, smartList: SmartListType): nat
  {
    |GetSmartListTaskIds(m, smartList)|
  }

  // Count priority tasks
  function CountPriorityTasks(m: Model): nat
  {
    |GetPriorityTaskIds(m)|
  }

  // Count logbook tasks
  function CountLogbookTasks(m: Model): nat
  {
    |GetLogbookTaskIds(m)|
  }

  // Count visible tasks in a list
  function CountVisibleTasksInList(m: Model, listId: ListId): nat
  {
    if listId !in m.tasks then 0
    else CountVisibleInSeq(m.tasks[listId], m.taskData)
  }

  function CountVisibleInSeq(ids: seq<TaskId>, taskData: map<TaskId, Task>): nat
  {
    if |ids| == 0 then 0
    else
      var head := ids[0];
      var countHead := if head in taskData && IsVisibleTask(taskData[head]) then 1 else 0;
      countHead + CountVisibleInSeq(ids[1..], taskData)
  }

  // ---------------------------------------------------------------------------
  // Task Accessors (compiled)
  // ---------------------------------------------------------------------------

  // Get a task by ID (returns None if not found or deleted)
  function GetTask(m: Model, taskId: TaskId): Option<Task>
  {
    if taskId in m.taskData && IsVisibleTask(m.taskData[taskId])
    then Some(m.taskData[taskId])
    else None
  }

  // Get a task by ID including deleted (for trash view)
  function GetTaskIncludingDeleted(m: Model, taskId: TaskId): Option<Task>
  {
    if taskId in m.taskData then Some(m.taskData[taskId]) else None
  }

  // Get all tasks in a list (ordered, visible only)
  function GetTasksInList(m: Model, listId: ListId): seq<TaskId>
  {
    if listId !in m.tasks then []
    else FilterVisibleTasks(m.tasks[listId], m.taskData)
  }

  function FilterVisibleTasks(ids: seq<TaskId>, taskData: map<TaskId, Task>): seq<TaskId>
  {
    if |ids| == 0 then []
    else
      var head := ids[0];
      var rest := FilterVisibleTasks(ids[1..], taskData);
      if head in taskData && IsVisibleTask(taskData[head])
      then [head] + rest
      else rest
  }

  // Get list name
  function GetListName(m: Model, listId: ListId): Option<string>
  {
    if listId in m.listNames then Some(m.listNames[listId]) else None
  }

  // Get all list IDs (ordered)
  function GetLists(m: Model): seq<ListId>
  {
    m.lists
  }

  // Get tag name
  function GetTagName(m: Model, tagId: TagId): Option<string>
  {
    if tagId in m.tags then Some(m.tags[tagId].name) else None
  }

  // Get all tag IDs
  function GetTags(m: Model): set<TagId>
  {
    m.tags.Keys
  }

  // ===========================================================================
  // Proof Obligations (stubs)
  // ===========================================================================

  lemma InitSatisfiesInv()
    ensures Inv(Init())
  {
  }

  // StepPreservesInv is declared abstract in Domain.
  // Body provided by refinement (TodoDomain in TodoMultiCollaboration.dfy)

  lemma CandidatesComplete(m: Model, orig: Action, aGood: Action, m2: Model)
  {
  }
}

// =============================================================================
// MultiCollaboration kernel instantiation
// =============================================================================

abstract module {:compile false} TodoMultiCollaborationSpec refines MultiCollaboration {
  import D : TodoDomainSpec
}

// AppCore is in TodoMultiCollaboration.dfy (the refinement file)


// === End TodoMultiCollaborationSpec.dfy ===

// =============================================================================
// TodoDomain: Concrete refinement with proofs
// =============================================================================

module TodoDomain refines TodoDomainSpec {

 // ============================================================================
  // InitSatisfiesInv: The initial model satisfies the invariant
  // ============================================================================

  lemma InitSatisfiesInv()
    ensures Inv(Init())
  {
  }

  // ============================================================================
  // Helper Lemmas for Sequence Operations
  // ============================================================================

  lemma NoDupSeqAppend<T>(s: seq<T>, x: T)
    requires NoDupSeq(s)
    requires !SeqContains(s, x)
    ensures NoDupSeq(s + [x])
  {
  }

  lemma SeqContainsAppend<T>(s: seq<T>, x: T, y: T)
    ensures SeqContains(s + [x], y) <==> SeqContains(s, y) || y == x
  {
  }

  lemma RemoveFirstPreservesNoDup<T>(s: seq<T>, x: T)
    requires NoDupSeq(s)
    ensures NoDupSeq(RemoveFirst(s, x))
    decreases |s|
  {
  }

  // Helper: elements in RemoveFirst(s, x) are in s
  lemma RemoveFirstInOriginal<T>(s: seq<T>, x: T, y: T)
    requires SeqContains(RemoveFirst(s, x), y)
    ensures SeqContains(s, y)
    decreases |s|
  {
  }

  lemma RemoveFirstSeqContains<T>(s: seq<T>, x: T, y: T)
    requires NoDupSeq(s)
    ensures SeqContains(RemoveFirst(s, x), y) <==> (SeqContains(s, y) && y != x)
    decreases |s|
  {
  }

  lemma NoDupSeqTail<T>(s: seq<T>)
    requires |s| > 0
    requires NoDupSeq(s)
    ensures NoDupSeq(s[1..])
  {
  }

  lemma InsertAtPreservesNoDup<T>(s: seq<T>, i: nat, x: T)
    requires i <= |s|
    requires NoDupSeq(s)
    requires !SeqContains(s, x)
    ensures NoDupSeq(InsertAt(s, i, x))
  {
  }

  lemma InsertAtSeqContains<T>(s: seq<T>, i: nat, x: T, y: T)
    requires i <= |s|
    ensures SeqContains(InsertAt(s, i, x), y) <==> SeqContains(s, y) || y == x
  {
  }

  // ============================================================================
  // Helper Lemmas for Counting
  // ============================================================================

  // CountInListsHelper over empty sequence is 0
  lemma CountInListsHelper_Empty(tasks: map<ListId, seq<TaskId>>, id: TaskId)
    ensures CountInListsHelper([], tasks, id) == 0
  {
  }

  // Decomposition: count = head contribution + tail contribution
  lemma CountInListsHelper_Decompose(lists: seq<ListId>, tasks: map<ListId, seq<TaskId>>, id: TaskId)
    requires |lists| > 0
    ensures CountInListsHelper(lists, tasks, id) ==
            (if lists[0] in tasks && SeqContains(tasks[lists[0]], id) then 1 else 0) +
            CountInListsHelper(lists[1..], tasks, id)
  {
  }

  // If id is not in any list in the map, count is 0
  lemma CountInListsHelper_NotInAny(lists: seq<ListId>, tasks: map<ListId, seq<TaskId>>, id: TaskId)
    requires forall l :: l in tasks ==> !SeqContains(tasks[l], id)
    ensures CountInListsHelper(lists, tasks, id) == 0
    decreases |lists|
  {
  }

  // Effect of RemoveFirst on a single lane's contribution
  lemma RemoveFirst_NotContains<T>(s: seq<T>, x: T, y: T)
    requires NoDupSeq(s)
    requires x != y
    ensures SeqContains(RemoveFirst(s, x), y) == SeqContains(s, y)
    decreases |s|
  {
  }

  // Helper: contribution of a single list to the count
  function ListContrib(l: ListId, tasks: map<ListId, seq<TaskId>>, id: TaskId): nat
  {
    if l in tasks && SeqContains(tasks[l], id) then 1 else 0
  }

  // RemoveFirst from lists decreases count by the removed element's contribution
  lemma CountInListsHelper_RemoveFirst(lists: seq<ListId>, tasks: map<ListId, seq<TaskId>>, l: ListId, id: TaskId)
    requires NoDupSeq(lists)
    requires SeqContains(lists, l)
    ensures CountInListsHelper(RemoveFirst(lists, l), tasks, id) ==
            CountInListsHelper(lists, tasks, id) - ListContrib(l, tasks, id)
    decreases |lists|
  {
  }

  // InsertAt into lists increases count by the inserted element's contribution
  lemma CountInListsHelper_InsertAt(lists: seq<ListId>, k: nat, l: ListId, tasks: map<ListId, seq<TaskId>>, id: TaskId)
    requires k <= |lists|
    requires !SeqContains(lists, l)
    ensures CountInListsHelper(InsertAt(lists, k, l), tasks, id) ==
            CountInListsHelper(lists, tasks, id) + ListContrib(l, tasks, id)
    decreases |lists|
  {
  }

  // Moving an element (remove then insert) preserves count
  lemma CountInListsHelper_MovePreserves(lists: seq<ListId>, k: nat, l: ListId, tasks: map<ListId, seq<TaskId>>, id: TaskId)
    requires NoDupSeq(lists)
    requires SeqContains(lists, l)
    requires k <= |RemoveFirst(lists, l)|
    ensures CountInListsHelper(InsertAt(RemoveFirst(lists, l), k, l), tasks, id) ==
            CountInListsHelper(lists, tasks, id)
  {
  }

  // Helper: count is 0 when newTasks = map l | l in tasks :: RemoveFirst(tasks[l], id)
  // This lemma takes the computed map as a parameter to avoid map comprehension issues
  lemma CountAfterRemoveAll_Core(
    lists: seq<ListId>,
    tasks: map<ListId, seq<TaskId>>,
    newTasks: map<ListId, seq<TaskId>>,
    id: TaskId
  )
    requires forall l :: l in tasks ==> NoDupSeq(tasks[l])
    requires newTasks.Keys == tasks.Keys
    requires forall l :: l in newTasks ==> newTasks[l] == RemoveFirst(tasks[l], id)
    ensures CountInListsHelper(lists, newTasks, id) == 0
    decreases |lists|
  {
  }

  // Count when id appears in exactly one list at a specific position
  lemma CountInListsHelper_ExactlyInOne(
    lists: seq<ListId>,
    tasks: map<ListId, seq<TaskId>>,
    targetList: ListId,
    id: TaskId
  )
    requires NoDupSeq(lists)
    requires SeqContains(lists, targetList)
    requires targetList in tasks
    requires SeqContains(tasks[targetList], id)
    requires forall l :: l in tasks && l != targetList ==> !SeqContains(tasks[l], id)
    ensures CountInListsHelper(lists, tasks, id) == 1
    decreases |lists|
  {
  }

  // Helper: if targetList is not in lists, and id only in targetList, count is 0
  lemma CountInListsHelper_NotInAnyExceptTarget(
    lists: seq<ListId>,
    tasks: map<ListId, seq<TaskId>>,
    targetList: ListId,
    id: TaskId
  )
    requires !SeqContains(lists, targetList)
    requires forall l :: l in tasks && l != targetList ==> !SeqContains(tasks[l], id)
    ensures CountInListsHelper(lists, tasks, id) == 0
    decreases |lists|
  {
  }

  // Helper for SeqContains in tail
  lemma SeqContainsTail<T>(s: seq<T>, x: T, head: T)
    requires |s| > 0
    requires s[0] == head
    requires head != x
    requires SeqContains(s, x)
    ensures SeqContains(s[1..], x)
  {
  }

  // Connect sequence membership (x in s) to SeqContains
  lemma SeqMembershipEquivSeqContains<T>(s: seq<T>, x: T)
    ensures x in s <==> SeqContains(s, x)
  {
  }

  // Count after inserting id into exactly one list
  lemma CountAfterInsertOne(
    lists: seq<ListId>,
    tasks: map<ListId, seq<TaskId>>,
    targetList: ListId,
    id: TaskId,
    newLane: seq<TaskId>
  )
    requires NoDupSeq(lists)
    requires SeqContains(lists, targetList)
    requires forall l :: l in tasks ==> !SeqContains(tasks[l], id)
    requires SeqContains(newLane, id)
    requires forall l :: l in tasks && l != targetList ==> !SeqContains(tasks[l], id)
    ensures CountInListsHelper(lists, tasks[targetList := newLane], id) == 1
    decreases |lists|
  {
  }

  // Helper: count is 0 in tail after remove+insert
  lemma CountAfterRemoveAll_InTail(
    lists: seq<ListId>,
    origTasks: map<ListId, seq<TaskId>>,
    tasks1: map<ListId, seq<TaskId>>,
    tasks2: map<ListId, seq<TaskId>>,
    targetList: ListId,
    newLane: seq<TaskId>,
    id: TaskId
  )
    requires !SeqContains(lists, targetList)
    requires forall l :: l in origTasks ==> NoDupSeq(origTasks[l])
    requires tasks1 == map l | l in origTasks :: RemoveFirst(origTasks[l], id)
    requires tasks2 == tasks1[targetList := newLane]
    ensures CountInListsHelper(lists, tasks2, id) == 0
    decreases |lists|
  {
  }

  lemma CountInListsHelper_NotInTail(
    lists: seq<ListId>,
    tasks: map<ListId, seq<TaskId>>,
    targetList: ListId,
    id: TaskId
  )
    requires !SeqContains(lists, targetList)
    requires forall l :: l in tasks && l != targetList ==> !SeqContains(tasks[l], id)
    ensures CountInListsHelper(lists, tasks, id) == 0
    decreases |lists|
  {
  }

  lemma CountInListsHelper_NotInTail_AfterRemove(
    lists: seq<ListId>,
    origTasks: map<ListId, seq<TaskId>>,
    tasks: map<ListId, seq<TaskId>>,
    targetList: ListId,
    id: TaskId
  )
    requires !SeqContains(lists, targetList)
    requires forall l :: l in origTasks ==> NoDupSeq(origTasks[l])
    requires forall l :: l in tasks && l != targetList ==> l in origTasks
    requires forall l :: l in tasks && l != targetList ==>
               tasks[l] == RemoveFirst(origTasks[l], id)
    ensures CountInListsHelper(lists, tasks, id) == 0
    decreases |lists|
  {
  }

  // Deleted tasks have count 0 (they're not in any list)
  // This now follows directly from invariant D'
  lemma DeletedTaskNotInLists(m: Model, id: TaskId)
    requires Inv(m)
    requires id in m.taskData
    requires m.taskData[id].deleted
    ensures CountInLists(m, id) == 0
  {
  }

  // ============================================================================
  // Helper Lemmas for List Operations on Counting
  // ============================================================================

  // Adding an empty list at the end doesn't change count
  lemma CountInListsHelper_AppendEmpty(
    lists: seq<ListId>,
    tasks: map<ListId, seq<TaskId>>,
    newListId: ListId,
    id: TaskId
  )
    requires newListId !in tasks
    ensures CountInListsHelper(lists + [newListId], tasks[newListId := []], id) ==
            CountInListsHelper(lists, tasks, id)
    decreases |lists|
  {
  }

  // Count is unchanged when we update tasks map with same lane for a list
  lemma CountInListsHelper_MapUpdate(
    lists: seq<ListId>,
    tasks: map<ListId, seq<TaskId>>,
    listId: ListId,
    lane: seq<TaskId>,
    id: TaskId
  )
    requires listId in tasks
    requires tasks[listId] == lane
    ensures CountInListsHelper(lists, tasks[listId := lane], id) ==
            CountInListsHelper(lists, tasks, id)
    decreases |lists|
  {
  }

  // Count unchanged when adding a new list not in the current list sequence
  lemma CountUnchangedForNewList(
    m: Model,
    newListId: ListId,
    id: TaskId
  )
    requires !SeqContains(m.lists, newListId)
    requires newListId !in m.tasks
    ensures CountInListsHelper(m.lists + [newListId], m.tasks[newListId := []], id) ==
            CountInLists(m, id)
  {
  }

  // Count for other tasks unchanged when we append newId to one list
  lemma CountUnchangedForOtherTasks(
    lists: seq<ListId>,
    tasks: map<ListId, seq<TaskId>>,
    targetList: ListId,
    newId: TaskId,
    otherId: TaskId
  )
    requires targetList in tasks
    requires newId != otherId
    ensures CountInListsHelper(lists, tasks[targetList := tasks[targetList] + [newId]], otherId) ==
            CountInListsHelper(lists, tasks, otherId)
    decreases |lists|
  {
  }

  // New task appears in exactly one list when appended to targetList
  lemma NewTaskCountIsOne(
    lists: seq<ListId>,
    tasks: map<ListId, seq<TaskId>>,
    targetList: ListId,
    newId: TaskId
  )
    requires NoDupSeq(lists)
    requires SeqContains(lists, targetList)
    requires targetList in tasks
    requires forall l :: l in tasks ==> !SeqContains(tasks[l], newId)
    ensures CountInListsHelper(lists, tasks[targetList := tasks[targetList] + [newId]], newId) == 1
    decreases |lists|
  {
  }

  // Helper: count is 0 in tail for new task
  lemma NewTaskCountIsOne_Tail(
    lists: seq<ListId>,
    tasks: map<ListId, seq<TaskId>>,
    targetList: ListId,
    newId: TaskId
  )
    requires targetList in tasks
    requires !SeqContains(lists, targetList)
    requires forall l :: l in tasks ==> !SeqContains(tasks[l], newId)
    ensures CountInListsHelper(lists, tasks[targetList := tasks[targetList] + [newId]], newId) == 0
    decreases |lists|
  {
  }

  // Count unchanged for other tasks when we remove a specific task from all lists
  // Takes concrete newTasks map (avoids map comprehension in postcondition)
  // Uses extensional requires instead of map comprehension equality
  lemma CountUnchangedAfterRemove_Wrapper(
    lists: seq<ListId>,
    tasks: map<ListId, seq<TaskId>>,
    newTasks: map<ListId, seq<TaskId>>,
    removedId: TaskId,
    otherId: TaskId
  )
    requires removedId != otherId
    requires forall l :: l in tasks ==> NoDupSeq(tasks[l])
    // Extensional equality instead of map comprehension equality
    requires newTasks.Keys == tasks.Keys
    requires forall l :: l in newTasks ==> newTasks[l] == RemoveFirst(tasks[l], removedId)
    ensures CountInListsHelper(lists, newTasks, otherId) == CountInListsHelper(lists, tasks, otherId)
    decreases |lists|
  {
  }

  // Wrapper for CountAfterRemoveAll
  // Takes concrete newTasks map instead of map comprehension in postcondition
  lemma CountAfterRemoveAll_Wrapper(
    lists: seq<ListId>,
    tasks: map<ListId, seq<TaskId>>,
    newTasks: map<ListId, seq<TaskId>>,
    id: TaskId
  )
    requires forall l :: l in tasks ==> NoDupSeq(tasks[l])
    requires newTasks == map l | l in tasks :: RemoveFirst(tasks[l], id)
    ensures CountInListsHelper(lists, newTasks, id) == 0
    decreases |lists|
  {
  }

  // If task is in a list that's in the sequence, count is at least 1
  lemma CountInListsHelper_HasOne(
    lists: seq<ListId>,
    tasks: map<ListId, seq<TaskId>>,
    listId: ListId,
    id: TaskId
  )
    requires SeqContains(lists, listId)
    requires listId in tasks
    requires SeqContains(tasks[listId], id)
    ensures CountInListsHelper(lists, tasks, id) >= 1
    decreases |lists|
  {
  }

  // If a task is in two distinct lists that are both in the list sequence, count >= 2
  lemma CountInListsHelper_HasTwo(
    lists: seq<ListId>,
    tasks: map<ListId, seq<TaskId>>,
    listId1: ListId,
    listId2: ListId,
    id: TaskId
  )
    requires NoDupSeq(lists)
    requires listId1 != listId2
    requires SeqContains(lists, listId1)
    requires SeqContains(lists, listId2)
    requires listId1 in tasks
    requires listId2 in tasks
    requires SeqContains(tasks[listId1], id)
    requires SeqContains(tasks[listId2], id)
    ensures CountInListsHelper(lists, tasks, id) >= 2
    decreases |lists|
  {
  }

  // Wrapper for CountAfterMoveTask with concrete tasks1 map
  // Uses extensional requires instead of map comprehension equality
  lemma CountAfterMoveTask_Wrapper(
    lists: seq<ListId>,
    tasks: map<ListId, seq<TaskId>>,
    tasks1: map<ListId, seq<TaskId>>,
    targetList: ListId,
    id: TaskId,
    newLane: seq<TaskId>
  )
    requires NoDupSeq(lists)
    requires SeqContains(lists, targetList)
    requires forall l :: l in tasks ==> NoDupSeq(tasks[l])
    // Extensional equality instead of map comprehension equality
    requires tasks1.Keys == tasks.Keys
    requires forall l :: l in tasks1 ==> tasks1[l] == RemoveFirst(tasks[l], id)
    requires SeqContains(newLane, id)
    requires NoDupSeq(newLane)
    ensures CountInListsHelper(lists, tasks1[targetList := newLane], id) == 1
  {
  }

  // Helper: CountInListsHelper gives same result when maps agree on all elements in lists
  lemma CountInListsHelper_SameOnSubset(
    lists: seq<ListId>,
    tasks1: map<ListId, seq<TaskId>>,
    tasks2: map<ListId, seq<TaskId>>,
    excludedKey: ListId,
    id: TaskId
  )
    requires !SeqContains(lists, excludedKey)
    requires forall l :: l in lists && l in tasks1 ==> l in tasks2 && tasks2[l] == tasks1[l]
    requires forall l :: l in lists && l !in tasks1 ==> l !in tasks2
    ensures CountInListsHelper(lists, tasks1, id) == CountInListsHelper(lists, tasks2, id)
    decreases |lists|
  {
  }

  // Wrapper for CountUnchangedAfterRemove for MoveTask
  // Uses bidirectional preservation: otherId in newLane iff otherId in original tasks[targetList]
  lemma CountUnchangedAfterMoveTask_Wrapper(
    lists: seq<ListId>,
    tasks: map<ListId, seq<TaskId>>,
    tasks1: map<ListId, seq<TaskId>>,
    targetList: ListId,
    movedId: TaskId,
    otherId: TaskId,
    newLane: seq<TaskId>
  )
    requires movedId != otherId
    requires NoDupSeq(lists)
    requires SeqContains(lists, targetList)
    requires targetList in tasks
    requires forall l :: l in tasks ==> NoDupSeq(tasks[l])
    requires tasks1.Keys == tasks.Keys
    requires forall l :: l in tasks1 ==> tasks1[l] == RemoveFirst(tasks[l], movedId)
    requires NoDupSeq(newLane)
    // Bidirectional preservation of otherId
    requires SeqContains(newLane, otherId) <==> SeqContains(tasks[targetList], otherId)
    ensures CountInListsHelper(lists, tasks1[targetList := newLane], otherId) ==
            CountInListsHelper(lists, tasks, otherId)
    decreases |lists|
  {
  }

  // Count unchanged when we remove a list from the sequence (for tasks not in that list)
  lemma CountInLists_AfterRemoveList(m: Model, removedListId: ListId, tid: TaskId)
    requires Inv(m)
    requires SeqContains(m.lists, removedListId)
    requires removedListId in m.tasks
    requires !SeqContains(m.tasks[removedListId], tid)
    ensures CountInListsHelper(RemoveFirst(m.lists, removedListId), m.tasks - {
    }, tid) ==
            CountInLists(m, tid)
  {
    CountInListsHelper_RemoveList(m.lists, m.tasks, removedListId, tid);
  }

  // Helper for removing a list from the count
  lemma CountInListsHelper_RemoveList(
    lists: seq<ListId>,
    tasks: map<ListId, seq<TaskId>>,
    removedListId: ListId,
    tid: TaskId
  )
    requires NoDupSeq(lists)
    requires SeqContains(lists, removedListId)
    requires removedListId in tasks
    requires !SeqContains(tasks[removedListId], tid)
    ensures CountInListsHelper(RemoveFirst(lists, removedListId), tasks - {
    }, tid) ==
            CountInListsHelper(lists, tasks, tid)
    decreases |lists|
  {
    if |lists| == 0 {
      // Contradiction
    } else {
      var l := lists[0];
      var lists' := RemoveFirst(lists, removedListId);
      var tasks' := tasks - {removedListId};

      if l == removedListId {
        // lists' = lists[1..], and removedListId contributes 0 (tid not in it)
        assert !SeqContains(tasks[l], tid);
        // The head contributes 0 to the original count
        // lists' = lists[1..], so count over lists' with tasks' should equal count over lists[1..] with tasks'
        // But tasks' = tasks - {removedListId}, and removedListId not in lists[1..] (NoDupSeq)
        assert lists' == lists[1..];
        CountInListsHelper_TasksSubset(lists[1..], tasks, tasks', removedListId, tid);
      } else {
        // l != removedListId
        // l contributes the same to both counts
        NoDupSeqTail(lists);
        SeqContainsTail(lists, removedListId, l);

        // lists' = [l] + RemoveFirst(lists[1..], removedListId)
        assert lists' == [l] + RemoveFirst(lists[1..], removedListId);

        // Recursive call
        CountInListsHelper_RemoveList(lists[1..], tasks, removedListId, tid);

        // Show l's contribution is the same
        if l in tasks {
          assert l in tasks';
          assert tasks'[l] == tasks[l];
        }
      }
    }
  }

  // Helper: count unchanged when using subset of tasks map
  lemma CountInListsHelper_TasksSubset(
    lists: seq<ListId>,
    tasks: map<ListId, seq<TaskId>>,
    tasks': map<ListId, seq<TaskId>>,
    removedListId: ListId,
    tid: TaskId
  )
    requires !SeqContains(lists, removedListId)
    requires tasks' == tasks - {
    }
    ensures CountInListsHelper(lists, tasks', tid) == CountInListsHelper(lists, tasks, tid)
    decreases |lists|
  {
    if |lists| == 0 {
    } else {
      var l := lists[0];
      assert l != removedListId;
      if l in tasks {
        assert l in tasks';
        assert tasks'[l] == tasks[l];
      } else {
        assert l !in tasks';
      }
      CountInListsHelper_TasksSubset(lists[1..], tasks, tasks', removedListId, tid);
    }
  }

  // ============================================================================
  // StepPreservesInv: Each action preserves the invariant
  // ============================================================================

  lemma StepPreservesInv(m: Model, a: Action, m2: Model)
  {
  }

  // ============================================================================
  // Individual Action Preservation Lemmas
  // ============================================================================

  lemma AddListPreservesInv(m: Model, name: string, m2: Model)
    requires Inv(m)
    requires TryStep(m, AddList(name)) == Ok(m2)
    ensures Inv(m2)
  {
  }

  lemma RenameListPreservesInv(m: Model, listId: ListId, newName: string, m2: Model)
    requires Inv(m)
    requires TryStep(m, RenameList(listId, newName)) == Ok(m2)
    ensures Inv(m2)
  {
  }

  // Helper for DeleteListPreservesInv - proves invariant F
  // Elements in RemoveFirst are a subset of the original
  lemma DeleteListPreservesInvF(m: Model, listId: ListId, m2: Model)
    requires Inv(m)
    requires SeqContains(m.lists, listId)
    requires TryStep(m, DeleteList(listId)) == Ok(m2)
    ensures forall lid :: SeqContains(m2.lists, lid) ==> lid < m2.nextListId
  {
  }

  lemma DeleteListPreservesInv(m: Model, listId: ListId, m2: Model)
    requires Inv(m)
    requires TryStep(m, DeleteList(listId)) == Ok(m2)
    ensures Inv(m2)
  {
  }

  lemma MoveListPreservesInv(m: Model, listId: ListId, listPlace: ListPlace, m2: Model)
    requires Inv(m)
    requires TryStep(m, MoveList(listId, listPlace)) == Ok(m2)
    ensures Inv(m2)
  {
  }

  // Helper for MoveListPreservesInv - count invariants preserved when list order changes
  // m2.tasks = m.tasks, m2.taskData = m.taskData, so counts are identical
  lemma MoveListPreservesInvCount(m: Model, listId: ListId, listPlace: ListPlace, m2: Model)
    requires Inv(m)
    requires TryStep(m, MoveList(listId, listPlace)) == Ok(m2)
    ensures forall tid :: tid in m2.taskData && !m2.taskData[tid].deleted ==> CountInLists(m2, tid) == 1
    ensures forall tid :: tid in m2.taskData && m2.taskData[tid].deleted ==> CountInLists(m2, tid) == 0
  {
  }

  // Helper for MoveListPreservesInv - list IDs < nextListId preserved
  // Elements in m2.lists = InsertAt(RemoveFirst(m.lists, listId), k, listId) are same as m.lists
  lemma MoveListPreservesInvF(m: Model, listId: ListId, listPlace: ListPlace, m2: Model)
    requires Inv(m)
    requires TryStep(m, MoveList(listId, listPlace)) == Ok(m2)
    ensures forall lid :: SeqContains(m2.lists, lid) ==> lid < m2.nextListId
  {
  }

  // Helper: if lid in RemoveFirst(s, x), then lid in s
  lemma MoveListPreservesInvF_Helper(s: seq<ListId>, x: ListId, rf: seq<ListId>, lid: ListId)
    requires rf == RemoveFirst(s, x)
    requires SeqContains(rf, lid)
    ensures SeqContains(s, lid)
  {
  }

  lemma AddTaskPreservesInv(m: Model, listId: ListId, title: string, m2: Model)
    requires Inv(m)
    requires TryStep(m, AddTask(listId, title)) == Ok(m2)
    ensures Inv(m2)
  {
  }

  // Helper lemma to show FindListForTask properties
  lemma FindListForTaskInList(m: Model, taskId: TaskId, listId: ListId)
    requires FindListForTask(m, taskId) == Some(listId)
    ensures SeqContains(m.lists, listId)
    ensures listId in m.tasks
    ensures SeqContains(m.tasks[listId], taskId)
  {
  }

  lemma FindListForTaskHelperInList(lists: seq<ListId>, tasks: map<ListId, seq<TaskId>>, taskId: TaskId, listId: ListId)
    requires FindListForTaskHelper(lists, tasks, taskId) == Some(listId)
    ensures SeqContains(lists, listId)
    ensures listId in tasks
    ensures SeqContains(tasks[listId], taskId)
    decreases |lists|
  {
  }

  // If a task has count >= 1, FindListForTask returns Some
  lemma FindListForTaskIsSome(m: Model, taskId: TaskId)
    requires Inv(m)
    requires taskId in m.taskData
    requires !m.taskData[taskId].deleted
    ensures FindListForTask(m, taskId).Some?
  {
  }

  lemma FindListForTaskIsSomeHelper(lists: seq<ListId>, tasks: map<ListId, seq<TaskId>>, taskId: TaskId)
    requires CountInListsHelper(lists, tasks, taskId) >= 1
    ensures FindListForTaskHelper(lists, tasks, taskId).Some?
    decreases |lists|
  {
  }

  // If a task is deleted, FindListForTask returns None
  lemma FindListForTaskIsNoneForDeleted(m: Model, taskId: TaskId)
    requires Inv(m)
    requires taskId in m.taskData
    requires m.taskData[taskId].deleted
    ensures FindListForTask(m, taskId).None?
  {
  }

  lemma FindListForTaskIsNoneHelper(lists: seq<ListId>, tasks: map<ListId, seq<TaskId>>, taskId: TaskId)
    requires CountInListsHelper(lists, tasks, taskId) == 0
    ensures FindListForTaskHelper(lists, tasks, taskId).None?
    decreases |lists|
  {
  }

  // FindListForTask returns the unique list containing the task
  lemma FindListForTaskUnique(m: Model, taskId: TaskId, listId: ListId, otherListId: ListId)
    requires Inv(m)
    requires FindListForTask(m, taskId) == Some(listId)
    requires SeqContains(m.lists, otherListId) && otherListId in m.tasks
    requires SeqContains(m.tasks[otherListId], taskId)
    ensures listId == otherListId
  {
  }

  lemma EditTaskPreservesInv(m: Model, taskId: TaskId, title: string, notes: string, m2: Model)
    requires Inv(m)
    requires TryStep(m, EditTask(taskId, title, notes)) == Ok(m2)
    ensures Inv(m2)
  {
  }

  lemma DeleteTaskPreservesInv(m: Model, taskId: TaskId, userId: UserId, m2: Model)
    requires Inv(m)
    requires TryStep(m, DeleteTask(taskId, userId)) == Ok(m2)
    ensures Inv(m2)
  {
  }

  lemma RestoreTaskPreservesInv(m: Model, taskId: TaskId, m2: Model)
    requires Inv(m)
    requires TryStep(m, RestoreTask(taskId)) == Ok(m2)
    ensures Inv(m2)
  {
  }

  lemma MoveTaskPreservesInv(m: Model, taskId: TaskId, toList: ListId, taskPlace: Place, m2: Model)
    requires Inv(m)
    requires TryStep(m, MoveTask(taskId, toList, taskPlace)) == Ok(m2)
    ensures Inv(m2)
  {
  }

  lemma CompleteTaskPreservesInv(m: Model, taskId: TaskId, m2: Model)
    requires Inv(m)
    requires TryStep(m, CompleteTask(taskId)) == Ok(m2)
    ensures Inv(m2)
  {
  }

  lemma UncompleteTaskPreservesInv(m: Model, taskId: TaskId, m2: Model)
    requires Inv(m)
    requires TryStep(m, UncompleteTask(taskId)) == Ok(m2)
    ensures Inv(m2)
  {
  }

  lemma StarTaskPreservesInv(m: Model, taskId: TaskId, m2: Model)
    requires Inv(m)
    requires TryStep(m, StarTask(taskId)) == Ok(m2)
    ensures Inv(m2)
  {
  }

  lemma UnstarTaskPreservesInv(m: Model, taskId: TaskId, m2: Model)
    requires Inv(m)
    requires TryStep(m, UnstarTask(taskId)) == Ok(m2)
    ensures Inv(m2)
  {
  }

  lemma SetDueDatePreservesInv(m: Model, taskId: TaskId, dueDate: Option<Date>, m2: Model)
    requires Inv(m)
    requires TryStep(m, SetDueDate(taskId, dueDate)) == Ok(m2)
    ensures Inv(m2)
  {
  }

  lemma AssignTaskPreservesInv(m: Model, taskId: TaskId, userId: UserId, m2: Model)
    requires Inv(m)
    requires TryStep(m, AssignTask(taskId, userId)) == Ok(m2)
    ensures Inv(m2)
  {
  }

  lemma UnassignTaskPreservesInv(m: Model, taskId: TaskId, userId: UserId, m2: Model)
    requires Inv(m)
    requires TryStep(m, UnassignTask(taskId, userId)) == Ok(m2)
    ensures Inv(m2)
  {
  }

  lemma AddTagToTaskPreservesInv(m: Model, taskId: TaskId, tagId: TagId, m2: Model)
    requires Inv(m)
    requires TryStep(m, AddTagToTask(taskId, tagId)) == Ok(m2)
    ensures Inv(m2)
  {
  }

  lemma RemoveTagFromTaskPreservesInv(m: Model, taskId: TaskId, tagId: TagId, m2: Model)
    requires Inv(m)
    requires TryStep(m, RemoveTagFromTask(taskId, tagId)) == Ok(m2)
    ensures Inv(m2)
  {
  }

  lemma CreateTagPreservesInv(m: Model, name: string, m2: Model)
    requires Inv(m)
    requires TryStep(m, CreateTag(name)) == Ok(m2)
    ensures Inv(m2)
  {
  }

  lemma RenameTagPreservesInv(m: Model, tagId: TagId, newName: string, m2: Model)
    requires Inv(m)
    requires TryStep(m, RenameTag(tagId, newName)) == Ok(m2)
    ensures Inv(m2)
  {
  }

  lemma DeleteTagPreservesInv(m: Model, tagId: TagId, m2: Model)
    requires Inv(m)
    requires TryStep(m, DeleteTag(tagId)) == Ok(m2)
    ensures Inv(m2)
  {
  }

  lemma MakeCollaborativePreservesInv(m: Model, m2: Model)
    requires Inv(m)
    requires TryStep(m, MakeCollaborative) == Ok(m2)
    ensures Inv(m2)
  {
  }

  lemma AddMemberPreservesInv(m: Model, userId: UserId, m2: Model)
    requires Inv(m)
    requires TryStep(m, AddMember(userId)) == Ok(m2)
    ensures Inv(m2)
  {
  }

  lemma RemoveMemberPreservesInv(m: Model, userId: UserId, m2: Model)
    requires Inv(m)
    requires TryStep(m, RemoveMember(userId)) == Ok(m2)
    ensures Inv(m2)
  {
  }

  // ============================================================================
  // CandidatesComplete: All meaning-preserving successful actions are candidates
  // ============================================================================

  lemma CandidatesComplete(m: Model, orig: Action, aGood: Action, m2: Model)
  {
  }

  lemma NoDupSeqRemove<T>(s: seq<T>, i: nat)
    requires NoDupSeq(s)
    requires i < |s|
    ensures NoDupSeq(s[..i] + s[i+1..])
  {
  }

  lemma SeqContainsRemove<T>(s: seq<T>, i: nat, x: T)
    requires NoDupSeq(s)
    requires i < |s|
    ensures SeqContains(s[..i] + s[i+1..], x) <==> (SeqContains(s, x) && x != s[i])
  {
  }
}

// =============================================================================
// TodoMultiCollaboration: Concrete refinement
// =============================================================================

module TodoMultiCollaboration refines TodoMultiCollaborationSpec {
  // Refine the import to use concrete TodoDomain instead of abstract TodoDomainSpec
  import D = TodoDomain
}

// =============================================================================
// AppCore: Client-side API (compiled)
// =============================================================================

module TodoAppCore {
  import K = TodoDomain
  import MC = TodoMultiCollaboration

  type ClientState = MC.ClientState

  function InitServerWithOwner(mode: K.ProjectMode, ownerId: K.UserId): MC.ServerState
  {
    var initModel := K.Model(
      mode,
      ownerId,
      {ownerId},
      [],
      map[],
      map[],
      map[],
      map[],
      0,
      0,
      0
    );
    MC.ServerState(initModel, [], [])
  }

  function InitClientFromServer(server: MC.ServerState): ClientState
  {
    MC.InitClientFromServer(server)
  }

  function ClientLocalDispatch(client: ClientState, action: K.Action): ClientState
  {
    MC.ClientLocalDispatch(client, action)
  }

  function ServerVersion(server: MC.ServerState): nat { MC.Version(server) }
  function ServerModel(server: MC.ServerState): K.Model { server.present }
  function ClientModel(client: ClientState): K.Model { MC.ClientModel(client) }
  function ClientVersion(client: ClientState): nat { MC.ClientVersion(client) }
  function PendingCount(client: ClientState): nat { MC.PendingCount(client) }

  function InitClient(version: nat, model: K.Model): ClientState {
    MC.InitClient(version, model)
  }

  function HandleRealtimeUpdate(client: ClientState, serverVersion: nat, serverModel: K.Model): ClientState {
    MC.HandleRealtimeUpdate(client, serverVersion, serverModel)
  }
}
