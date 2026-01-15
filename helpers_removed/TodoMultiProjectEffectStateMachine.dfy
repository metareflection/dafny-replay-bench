// TodoMultiProjectEffectStateMachine: Verified multi-project effect orchestration for Todo
//
// Concrete refinement of MultiProjectEffectStateMachine for the Todo domain.
// This is compiled separately and used by MultiProjectEffectManager.js.

// === Inlined from ../kernels/MultiProjectEffectStateMachine.dfy ===
// MultiProjectEffectStateMachine: Verified model of multi-project client-side effect orchestration
//
// This module extends EffectStateMachine to handle cross-project operations.
// Key differences from single-project:
// - Tracks baseVersions per project (not single baseVersion)
// - Uses MultiAction (can touch multiple projects)
// - Commands include touched project IDs and their versions

// === Inlined from MultiProject.dfy ===
// MultiProject.dfy: Abstract module for cross-project operations
//
// This module extends MultiCollaboration to support operations that span
// multiple projects. Concrete domains refine this to add domain-specific
// cross-project actions (e.g., MoveTaskTo, CopyTaskTo).
//
// Pattern:
//   MultiCollaboration (single-project collaboration)
//       ↓ imports
//   MultiProject (cross-project operations)  ← this module
//       ↓ refines
//   TodoMultiProjectDomain (concrete)

// === Inlined from MultiCollaboration.dfy ===
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
  }


// === End MultiCollaboration.dfy ===

abstract module MultiProject {
  import MC : MultiCollaboration

  // Re-export types from MultiCollaboration
  type Model = MC.D.Model
  type Action = MC.D.Action
  type Err = MC.D.Err
  type ProjectId = string

  // MultiModel: collection of projects
  datatype MultiModel = MultiModel(projects: map<ProjectId, Model>)

  // Result type (reuse from Domain)
  datatype Result<T, E> = Ok(value: T) | Err(error: E)

  // ===========================================================================
  // MultiAction: Actions that can span multiple projects
  // ===========================================================================

  // Abstract: concrete modules define additional cross-project actions
  type MultiAction(==)

  // Every MultiAction must support wrapping a single-project action
  function SingleAction(pid: ProjectId, a: Action): MultiAction

  // Extract single-project action if this is a Single variant
  function GetSingleAction(ma: MultiAction): Option<(ProjectId, Action)>

  datatype Option<T> = None | Some(value: T)

  // ===========================================================================
  // Errors for multi-project operations
  // ===========================================================================

  datatype MultiErr =
    | MissingProject(projectId: ProjectId)
    | SingleProjectError(projectId: ProjectId, err: Err)
    | CrossProjectError(message: string)

  // ===========================================================================
  // TouchedProjects: Which projects does an action affect?
  // ===========================================================================

  function TouchedProjects(a: MultiAction): set<ProjectId>

  // Single actions touch exactly one project
  lemma SingleActionTouchesOne(pid: ProjectId, a: Action)
    ensures TouchedProjects(SingleAction(pid, a)) == {
    }

  // ===========================================================================
  // AllProjectsLoaded: Are all touched projects present?
  // ===========================================================================

  predicate AllProjectsLoaded(mm: MultiModel, a: MultiAction)
  {
    forall pid :: pid in TouchedProjects(a) ==> pid in mm.projects
  }

  // ===========================================================================
  // MultiStep: Apply a multi-action to a MultiModel
  // ===========================================================================

  function MultiStep(mm: MultiModel, a: MultiAction): Result<MultiModel, MultiErr>
    requires AllProjectsLoaded(mm, a)

  // Variant without precondition (checks internally, returns error if not loaded)
  function TryMultiStep(mm: MultiModel, a: MultiAction): Result<MultiModel, MultiErr>

  // TryMultiStep delegates to MultiStep when loaded
  lemma TryMultiStepEquivalence(mm: MultiModel, a: MultiAction)
    requires AllProjectsLoaded(mm, a)
    ensures TryMultiStep(mm, a) == MultiStep(mm, a)

  // ===========================================================================
  // ChangedProjects: Which projects were modified?
  // ===========================================================================

  function ChangedProjects(before: MultiModel, after: MultiModel): set<ProjectId>
  {
    set pid | pid in after.projects &&
              (pid !in before.projects || before.projects[pid] != after.projects[pid])
  }

  // ===========================================================================
  // MultiInv: All projects satisfy their individual invariants
  // ===========================================================================

  ghost predicate Inv(m: Model)

  ghost predicate MultiInv(mm: MultiModel)
  {
    forall pid :: pid in mm.projects ==> Inv(mm.projects[pid])
  }

  // ===========================================================================
  // Proof obligation: MultiStep preserves MultiInv
  // ===========================================================================

  lemma MultiStepPreservesInv(mm: MultiModel, a: MultiAction, mm2: MultiModel)
    requires MultiInv(mm)
    requires AllProjectsLoaded(mm, a)
    requires MultiStep(mm, a) == Ok(mm2)
    ensures MultiInv(mm2)

  // ===========================================================================
  // MultiRebase: Rebase a multi-action through concurrent changes
  // ===========================================================================

  function MultiRebase(
    projectLogs: map<ProjectId, seq<Action>>,
    baseVersions: map<ProjectId, nat>,
    a: MultiAction
  ): MultiAction

  // ===========================================================================
  // MultiCandidates: Generate fallback candidates for an action
  // ===========================================================================

  function MultiCandidates(mm: MultiModel, a: MultiAction): seq<MultiAction>

  // First candidate is always the original action
  lemma CandidatesStartWithOriginal(mm: MultiModel, a: MultiAction)
    requires AllProjectsLoaded(mm, a)
    requires |MultiCandidates(mm, a)| > 0
    ensures MultiCandidates(mm, a)[0] == a

  // ===========================================================================
  // MultiDispatch: Full reconciliation for cross-project operations
  // ===========================================================================

  // Rebase through suffix of each project's log
  function RebaseThroughLogs(
    projectLogs: map<ProjectId, seq<Action>>,
    baseVersions: map<ProjectId, nat>,
    a: MultiAction
  ): MultiAction
  {
    MultiRebase(projectLogs, baseVersions, a)
  }

  // Try candidates until one succeeds
  function TryCandidates(mm: MultiModel, candidates: seq<MultiAction>): Result<(MultiModel, MultiAction), MultiErr>
    requires forall i :: 0 <= i < |candidates| ==> AllProjectsLoaded(mm, candidates[i])
    decreases |candidates|
  {
    if |candidates| == 0 then
      Err(CrossProjectError("No candidate succeeded"))
    else
      var result := MultiStep(mm, candidates[0]);
      match result
      case Ok(mm2) => Ok((mm2, candidates[0]))
      case Err(_) => TryCandidates(mm, candidates[1..])
  }
}


// === End MultiProject.dfy ===

abstract module MultiProjectEffectStateMachine {
  import MP : MultiProject

  // Re-export types from MultiProject
  type Model = MP.Model
  type Action = MP.MC.D.Action
  type MultiModel = MP.MultiModel
  type MultiAction = MP.MultiAction
  type ProjectId = MP.ProjectId

  // ===========================================================================
  // Multi-Project Client State
  // ===========================================================================

  // Client state tracks versions per project
  datatype MultiClientState = MultiClientState(
    baseVersions: map<ProjectId, nat>,   // Last synced version per project
    present: MultiModel,                  // Current local model (optimistic)
    pending: seq<MultiAction>             // Actions waiting to be flushed
  )

  // ===========================================================================
  // Effect State
  // ===========================================================================

  datatype NetworkStatus = Online | Offline

  datatype EffectMode =
    | Idle
    | Dispatching(retries: nat)

  datatype EffectState = EffectState(
    network: NetworkStatus,
    mode: EffectMode,
    client: MultiClientState
  )

  const MaxRetries: nat := 5

  // ===========================================================================
  // Events (inputs to the state machine)
  // ===========================================================================

  datatype Event =
    | UserAction(action: MultiAction)
    | DispatchAccepted(
        newVersions: map<ProjectId, nat>,   // Updated versions for touched projects
        newModels: map<ProjectId, Model>    // Updated models for touched projects
      )
    | DispatchConflict(
        freshVersions: map<ProjectId, nat>,
        freshModels: map<ProjectId, Model>
      )
    | DispatchRejected(
        freshVersions: map<ProjectId, nat>,
        freshModels: map<ProjectId, Model>
      )
    | RealtimeUpdate(
        projectId: ProjectId,               // Which project was updated by another client
        version: nat,                       // New version from server
        model: Model                        // New model from server
      )
    | NetworkError
    | NetworkRestored
    | ManualGoOffline
    | ManualGoOnline
    | Tick

  // ===========================================================================
  // Commands (outputs / side effects to perform)
  // ===========================================================================

  datatype Command =
    | NoOp
    | SendDispatch(
        touchedProjects: set<ProjectId>,
        baseVersions: map<ProjectId, nat>,  // Versions for touched projects only
        action: MultiAction
      )
    | FetchFreshState(projects: set<ProjectId>)

  // ===========================================================================
  // Client State Helpers
  // ===========================================================================

  function PendingCount(es: EffectState): nat
  {
    |es.client.pending|
  }

  function HasPending(es: EffectState): bool
  {
    PendingCount(es) > 0
  }

  function IsOnline(es: EffectState): bool
  {
    es.network == Online
  }

  function IsIdle(es: EffectState): bool
  {
    es.mode == Idle
  }

  function CanStartDispatch(es: EffectState): bool
  {
    IsOnline(es) && IsIdle(es) && HasPending(es)
  }

  function FirstPendingAction(es: EffectState): MultiAction
    requires HasPending(es)
  {
    es.client.pending[0]
  }

  // Get base versions for touched projects
  function BaseVersionsForAction(client: MultiClientState, action: MultiAction): map<ProjectId, nat>
  {
    var touched := MP.TouchedProjects(action);
    map pid | pid in touched && pid in client.baseVersions :: client.baseVersions[pid]
  }

  // ===========================================================================
  // Client State Management
  // ===========================================================================

  // Initialize client from versions and models
  function InitClient(versions: map<ProjectId, nat>, models: map<ProjectId, Model>): MultiClientState
  {
    MultiClientState(versions, MP.MultiModel(models), [])
  }

  // Local dispatch (optimistic update)
  function ClientLocalDispatch(client: MultiClientState, action: MultiAction): MultiClientState
  {
    if !MP.AllProjectsLoaded(client.present, action) then
      // Can't apply - just enqueue for server to handle
      MultiClientState(client.baseVersions, client.present, client.pending + [action])
    else
      var result := MP.MultiStep(client.present, action);
      match result
      case Ok(newModel) =>
        MultiClientState(client.baseVersions, newModel, client.pending + [action])
      case Err(_) =>
        // Optimistic failure: still enqueue (server might accept with fallback)
        MultiClientState(client.baseVersions, client.present, client.pending + [action])
  }

  // Re-apply pending actions to a model
  function ReapplyPending(mm: MultiModel, pending: seq<MultiAction>): MultiModel
    decreases |pending|
  {
    if |pending| == 0 then mm
    else
      var newMM := if MP.AllProjectsLoaded(mm, pending[0]) then
        var result := MP.MultiStep(mm, pending[0]);
        match result
        case Ok(m) => m
        case Err(_) => mm
      else mm;
      ReapplyPending(newMM, pending[1..])
  }

  // Merge updated project models and versions into client state
  function MergeVersions(
    base: map<ProjectId, nat>,
    updates: map<ProjectId, nat>
  ): map<ProjectId, nat>
  {
    map pid | pid in base.Keys + updates.Keys ::
      if pid in updates then updates[pid] else base[pid]
  }

  function MergeModels(
    base: map<ProjectId, Model>,
    updates: map<ProjectId, Model>
  ): map<ProjectId, Model>
  {
    map pid | pid in base.Keys + updates.Keys ::
      if pid in updates then updates[pid] else base[pid]
  }

  function MergeUpdates(
    client: MultiClientState,
    newVersions: map<ProjectId, nat>,
    newModels: map<ProjectId, Model>
  ): (map<ProjectId, nat>, MultiModel)
  {
    var mergedVersions := MergeVersions(client.baseVersions, newVersions);
    var mergedProjects := MergeModels(client.present.projects, newModels);
    (mergedVersions, MP.MultiModel(mergedProjects))
  }

  // Handle accepted reply
  function ClientAcceptReply(
    client: MultiClientState,
    newVersions: map<ProjectId, nat>,
    newModels: map<ProjectId, Model>
  ): MultiClientState
  {
    if |client.pending| == 0 then
      var (mergedV, mergedM) := MergeUpdates(client, newVersions, newModels);
      MultiClientState(mergedV, mergedM, [])
    else
      var rest := client.pending[1..];
      var (mergedV, mergedM) := MergeUpdates(client, newVersions, newModels);
      var reappliedModel := ReapplyPending(mergedM, rest);
      MultiClientState(mergedV, reappliedModel, rest)
  }

  // Handle rejected reply
  function ClientRejectReply(
    client: MultiClientState,
    freshVersions: map<ProjectId, nat>,
    freshModels: map<ProjectId, Model>
  ): MultiClientState
  {
    if |client.pending| == 0 then
      var (mergedV, mergedM) := MergeUpdates(client, freshVersions, freshModels);
      MultiClientState(mergedV, mergedM, [])
    else
      var rest := client.pending[1..];
      var (mergedV, mergedM) := MergeUpdates(client, freshVersions, freshModels);
      var reappliedModel := ReapplyPending(mergedM, rest);
      MultiClientState(mergedV, reappliedModel, rest)
  }

  // Handle conflict (realtime update while dispatch in flight)
  function HandleConflict(
    client: MultiClientState,
    freshVersions: map<ProjectId, nat>,
    freshModels: map<ProjectId, Model>
  ): MultiClientState
  {
    var (mergedV, mergedM) := MergeUpdates(client, freshVersions, freshModels);
    var reappliedModel := ReapplyPending(mergedM, client.pending);
    MultiClientState(mergedV, reappliedModel, client.pending)
  }

  // Handle realtime update from another client (preserves pending actions)
  function HandleRealtimeUpdate(
    client: MultiClientState,
    projectId: ProjectId,
    version: nat,
    model: Model
  ): MultiClientState
  {
    var newVersions := map[projectId := version];
    var newModels := map[projectId := model];
    var (mergedV, mergedM) := MergeUpdates(client, newVersions, newModels);
    var reappliedModel := ReapplyPending(mergedM, client.pending);
    MultiClientState(mergedV, reappliedModel, client.pending)
  }

  // ===========================================================================
  // State Transitions
  // ===========================================================================

  function Step(es: EffectState, event: Event): (EffectState, Command)
  {
    match event {
      case UserAction(action) =>
        var newClient := ClientLocalDispatch(es.client, action);
        var newState := es.(client := newClient);
        if CanStartDispatch(newState) then
          var firstAction := FirstPendingAction(newState);
          var touched := MP.TouchedProjects(firstAction);
          var versions := BaseVersionsForAction(newState.client, firstAction);
          (newState.(mode := Dispatching(0)),
           SendDispatch(touched, versions, firstAction))
        else
          (newState, NoOp)

      case DispatchAccepted(newVersions, newModels) =>
        if es.mode.Dispatching? then
          var newClient := ClientAcceptReply(es.client, newVersions, newModels);
          var newState := EffectState(es.network, Idle, newClient);
          if CanStartDispatch(newState) then
            var firstAction := FirstPendingAction(newState);
            var touched := MP.TouchedProjects(firstAction);
            var versions := BaseVersionsForAction(newState.client, firstAction);
            (newState.(mode := Dispatching(0)),
             SendDispatch(touched, versions, firstAction))
          else
            (newState, NoOp)
        else
          (es, NoOp)

      case DispatchConflict(freshVersions, freshModels) =>
        if es.mode.Dispatching? then
          var retries := es.mode.retries;
          if retries >= MaxRetries then
            (es.(mode := Idle), NoOp)
          else
            var newClient := HandleConflict(es.client, freshVersions, freshModels);
            var newState := EffectState(es.network, Dispatching(retries + 1), newClient);
            if HasPending(newState) then
              var firstAction := FirstPendingAction(newState);
              var touched := MP.TouchedProjects(firstAction);
              var versions := BaseVersionsForAction(newState.client, firstAction);
              (newState, SendDispatch(touched, versions, firstAction))
            else
              (newState.(mode := Idle), NoOp)
        else
          (es, NoOp)

      case DispatchRejected(freshVersions, freshModels) =>
        if es.mode.Dispatching? then
          var newClient := ClientRejectReply(es.client, freshVersions, freshModels);
          var newState := EffectState(es.network, Idle, newClient);
          if CanStartDispatch(newState) then
            var firstAction := FirstPendingAction(newState);
            var touched := MP.TouchedProjects(firstAction);
            var versions := BaseVersionsForAction(newState.client, firstAction);
            (newState.(mode := Dispatching(0)),
             SendDispatch(touched, versions, firstAction))
          else
            (newState, NoOp)
        else
          (es, NoOp)

      case NetworkError =>
        (es.(network := Offline, mode := Idle), NoOp)

      case NetworkRestored =>
        var newState := es.(network := Online);
        if CanStartDispatch(newState) then
          var firstAction := FirstPendingAction(newState);
          var touched := MP.TouchedProjects(firstAction);
          var versions := BaseVersionsForAction(newState.client, firstAction);
          (newState.(mode := Dispatching(0)),
           SendDispatch(touched, versions, firstAction))
        else
          (newState, NoOp)

      case ManualGoOffline =>
        (es.(network := Offline, mode := Idle), NoOp)

      case ManualGoOnline =>
        var newState := es.(network := Online);
        if CanStartDispatch(newState) then
          var firstAction := FirstPendingAction(newState);
          var touched := MP.TouchedProjects(firstAction);
          var versions := BaseVersionsForAction(newState.client, firstAction);
          (newState.(mode := Dispatching(0)),
           SendDispatch(touched, versions, firstAction))
        else
          (newState, NoOp)

      case RealtimeUpdate(projectId, version, model) =>
        // Skip realtime updates while dispatching - dispatch response will bring fresh state
        if es.mode.Dispatching? then
          (es, NoOp)
        else
          // Merge update and reapply pending actions (preserving them)
          var newClient := HandleRealtimeUpdate(es.client, projectId, version, model);
          (es.(client := newClient), NoOp)

      case Tick =>
        if CanStartDispatch(es) then
          var firstAction := FirstPendingAction(es);
          var touched := MP.TouchedProjects(firstAction);
          var versions := BaseVersionsForAction(es.client, firstAction);
          (es.(mode := Dispatching(0)),
           SendDispatch(touched, versions, firstAction))
        else
          (es, NoOp)
    }
  }

  // ===========================================================================
  // Invariants
  // ===========================================================================

  predicate ModeConsistent(es: EffectState)
  {
    es.mode.Dispatching? ==> HasPending(es)
  }

  predicate RetriesBounded(es: EffectState)
  {
    es.mode.Dispatching? ==> es.mode.retries <= MaxRetries
  }

  predicate Inv(es: EffectState)
  {
    ModeConsistent(es) && RetriesBounded(es)
  }

  // ===========================================================================
  // Key Properties
  // ===========================================================================

  function Pending(es: EffectState): seq<MultiAction>
  {
    es.client.pending
  }

  lemma RetriesAreBounded(es: EffectState, event: Event)
    requires Inv(es)
    ensures RetriesBounded(Step(es, event).0)
  {
  }

  lemma TickStartsDispatch(es: EffectState)
    requires Inv(es)
    requires IsOnline(es) && IsIdle(es) && HasPending(es)
    ensures Step(es, Tick).0.mode.Dispatching?
    ensures Step(es, Tick).1.SendDispatch?
  {
  }

  lemma PendingNeverLost(es: EffectState, event: Event)
    requires Inv(es)
    ensures var (es', _) := Step(es, event);
            match event {
              case UserAction(_) => PendingCount(es') >= PendingCount(es)
              case DispatchAccepted(_, _) => PendingCount(es') >= PendingCount(es) - 1
              case DispatchRejected(_, _) => PendingCount(es') >= PendingCount(es) - 1
              case DispatchConflict(_, _) => PendingCount(es') == PendingCount(es)
              case RealtimeUpdate(_, _, _) => PendingCount(es') == PendingCount(es)
              case NetworkError => PendingCount(es') == PendingCount(es)
              case NetworkRestored => PendingCount(es') == PendingCount(es)
              case ManualGoOffline => PendingCount(es') == PendingCount(es)
              case ManualGoOnline => PendingCount(es') == PendingCount(es)
              case Tick => PendingCount(es') == PendingCount(es)
            }
  {}

  lemma ConflictPreservesPendingExactly(es: EffectState, freshVersions: map<ProjectId, nat>, freshModels: map<ProjectId, Model>)
    requires Inv(es)
    requires es.mode.Dispatching?
    ensures var (es', _) := Step(es, DispatchConflict(freshVersions, freshModels));
            Pending(es') == Pending(es)
  {}

  // Property: RealtimeUpdate preserves pending exactly
  lemma RealtimeUpdatePreservesPendingExactly(es: EffectState, projectId: ProjectId, version: nat, model: Model)
    requires Inv(es)
    ensures var (es', _) := Step(es, RealtimeUpdate(projectId, version, model));
            Pending(es') == Pending(es)
  {}

  // Property: Conflict never empties pending (the "else" branch in Step is dead code)
  lemma ConflictNeverEmptiesPending(es: EffectState, freshVersions: map<ProjectId, nat>, freshModels: map<ProjectId, Model>)
    requires Inv(es)
    requires es.mode.Dispatching?
    ensures var (es', _) := Step(es, DispatchConflict(freshVersions, freshModels));
            HasPending(es')
  {
    // Follows from ConflictPreservesPendingExactly + ModeConsistent (Dispatching => HasPending)
    ConflictPreservesPendingExactly(es, freshVersions, freshModels);
  }

  // Property: DispatchAccepted transitions to Idle (or continues dispatching)
  lemma AcceptedGoesIdleOrContinues(es: EffectState, newVersions: map<ProjectId, nat>, newModels: map<ProjectId, Model>)
    requires es.mode.Dispatching?
    ensures var (es', cmd) := Step(es, DispatchAccepted(newVersions, newModels));
            es'.mode.Idle? || es'.mode.Dispatching?
  {
    // Direct from Step definition
  }

  // Property: MaxRetries exceeded leads to Idle
  lemma MaxRetriesLeadsToIdle(es: EffectState, freshVersions: map<ProjectId, nat>, freshModels: map<ProjectId, Model>)
    requires es.mode.Dispatching? && es.mode.retries >= MaxRetries
    ensures Step(es, DispatchConflict(freshVersions, freshModels)).0.mode.Idle?
  {
  }

  // Property: The tail of pending is exactly preserved on accept/reject
  lemma PendingTailPreserved(es: EffectState, event: Event)
    requires Inv(es)
    requires event.DispatchAccepted? || event.DispatchRejected?
    requires es.mode.Dispatching?  // Must be in dispatching mode to process reply
    ensures var (es', _) := Step(es, event);
            // The remaining pending actions are exactly pending[1..]
            |Pending(es')| == |Pending(es)| - 1
  {
    // Follows from ClientAcceptReply and ClientRejectReply removing only first element
    // Note: ModeConsistent ensures HasPending when Dispatching
  }

  // Property: Exact sequence preservation on accept/reject
  lemma PendingSequencePreserved(es: EffectState, event: Event)
    requires Inv(es)
    requires es.mode.Dispatching?
    requires event.DispatchAccepted? || event.DispatchRejected?
    ensures var (es', _) := Step(es, event);
            Pending(es') == Pending(es)[1..]  // Exact sequence equality
  {
    // ClientAcceptReply and ClientRejectReply both set pending to rest = pending[1..]
    // The model is reapplied but the pending sequence is exactly preserved
  }

  // Property: UserAction always appends exactly one action
  lemma UserActionAppendsOne(es: EffectState, action: MultiAction)
    requires Inv(es)
    ensures var (es', _) := Step(es, UserAction(action));
            |Pending(es')| == |Pending(es)| + 1
  {
    // ClientLocalDispatch always appends action to pending
  }

  // Property: UserAction appends the exact action (strongest form)
  lemma UserActionAppendsExact(es: EffectState, action: MultiAction)
    requires Inv(es)
    ensures var (es', _) := Step(es, UserAction(action));
            Pending(es') == Pending(es) + [action]  // Exact sequence
  {
    // ClientLocalDispatch does: client.pending + [action] in both Ok and Err cases
  }

  // ===========================================================================
  // Progress Property (Liveness)
  // ===========================================================================

  // Define a measure for progress: (isDispatching, retries, pendingCount)
  // This decreases on successful dispatch, bounded by retries on conflict
  function ProgressMeasure(es: EffectState): (bool, nat, nat)
    requires RetriesBounded(es)
  {
    (es.mode.Dispatching?,
     if es.mode.Dispatching? && es.mode.retries <= MaxRetries
       then MaxRetries - es.mode.retries
       else 0,
     PendingCount(es))
  }

  // Lexicographic ordering for progress
  // Tuple is (isDispatching: bool, retriesRemaining: nat, pendingCount: nat)
  predicate ProgressLt(m1: (bool, nat, nat), m2: (bool, nat, nat)) {
    // Primary: pendingCount decreases
    m1.2 < m2.2 ||
    // Secondary: if pending same, prefer going from dispatching to idle
    (m1.2 == m2.2 && !m1.0 && m2.0) ||
    // Tertiary: if both dispatching with same pending, retries remaining decreases
    (m1.2 == m2.2 && m1.0 == m2.0 && m1.1 < m2.1)
  }

  // ===========================================================================
  // Initialization
  // ===========================================================================

  function Init(versions: map<ProjectId, nat>, models: map<ProjectId, Model>): EffectState
  {
    EffectState(Online, Idle, InitClient(versions, models))
  }

  // ===========================================================================
  // Invariant Preservation
  // ===========================================================================

  }


// === End ../kernels/MultiProjectEffectStateMachine.dfy ===
// === Inlined from TodoMultiProjectDomain.dfy ===
// TodoMultiProjectDomain: Cross-project operations for Todo
//
// This module refines the abstract MultiProject module to add Todo-specific
// cross-project operations like MoveTaskTo and CopyTaskTo.
//
// Pattern:
//   MultiProject (abstract)
//       ↓ refines
//   TodoMultiProjectDomain (this module)

// === Inlined from ../kernels/MultiProject.dfy ===
// MultiProject.dfy: Abstract module for cross-project operations
//
// This module extends MultiCollaboration to support operations that span
// multiple projects. Concrete domains refine this to add domain-specific
// cross-project actions (e.g., MoveTaskTo, CopyTaskTo).
//
// Pattern:
//   MultiCollaboration (single-project collaboration)
//       ↓ imports
//   MultiProject (cross-project operations)  ← this module
//       ↓ refines
//   TodoMultiProjectDomain (concrete)

// === Inlined from MultiCollaboration.dfy ===
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
  }


// === End MultiCollaboration.dfy ===

abstract module MultiProject {
  import MC : MultiCollaboration

  // Re-export types from MultiCollaboration
  type Model = MC.D.Model
  type Action = MC.D.Action
  type Err = MC.D.Err
  type ProjectId = string

  // MultiModel: collection of projects
  datatype MultiModel = MultiModel(projects: map<ProjectId, Model>)

  // Result type (reuse from Domain)
  datatype Result<T, E> = Ok(value: T) | Err(error: E)

  // ===========================================================================
  // MultiAction: Actions that can span multiple projects
  // ===========================================================================

  // Abstract: concrete modules define additional cross-project actions
  type MultiAction(==)

  // Every MultiAction must support wrapping a single-project action
  function SingleAction(pid: ProjectId, a: Action): MultiAction

  // Extract single-project action if this is a Single variant
  function GetSingleAction(ma: MultiAction): Option<(ProjectId, Action)>

  datatype Option<T> = None | Some(value: T)

  // ===========================================================================
  // Errors for multi-project operations
  // ===========================================================================

  datatype MultiErr =
    | MissingProject(projectId: ProjectId)
    | SingleProjectError(projectId: ProjectId, err: Err)
    | CrossProjectError(message: string)

  // ===========================================================================
  // TouchedProjects: Which projects does an action affect?
  // ===========================================================================

  function TouchedProjects(a: MultiAction): set<ProjectId>

  // Single actions touch exactly one project
  lemma SingleActionTouchesOne(pid: ProjectId, a: Action)
    ensures TouchedProjects(SingleAction(pid, a)) == {
    }

  // ===========================================================================
  // AllProjectsLoaded: Are all touched projects present?
  // ===========================================================================

  predicate AllProjectsLoaded(mm: MultiModel, a: MultiAction)
  {
    forall pid :: pid in TouchedProjects(a) ==> pid in mm.projects
  }

  // ===========================================================================
  // MultiStep: Apply a multi-action to a MultiModel
  // ===========================================================================

  function MultiStep(mm: MultiModel, a: MultiAction): Result<MultiModel, MultiErr>
    requires AllProjectsLoaded(mm, a)

  // Variant without precondition (checks internally, returns error if not loaded)
  function TryMultiStep(mm: MultiModel, a: MultiAction): Result<MultiModel, MultiErr>

  // TryMultiStep delegates to MultiStep when loaded
  lemma TryMultiStepEquivalence(mm: MultiModel, a: MultiAction)
    requires AllProjectsLoaded(mm, a)
    ensures TryMultiStep(mm, a) == MultiStep(mm, a)

  // ===========================================================================
  // ChangedProjects: Which projects were modified?
  // ===========================================================================

  function ChangedProjects(before: MultiModel, after: MultiModel): set<ProjectId>
  {
    set pid | pid in after.projects &&
              (pid !in before.projects || before.projects[pid] != after.projects[pid])
  }

  // ===========================================================================
  // MultiInv: All projects satisfy their individual invariants
  // ===========================================================================

  ghost predicate Inv(m: Model)

  ghost predicate MultiInv(mm: MultiModel)
  {
    forall pid :: pid in mm.projects ==> Inv(mm.projects[pid])
  }

  // ===========================================================================
  // Proof obligation: MultiStep preserves MultiInv
  // ===========================================================================

  lemma MultiStepPreservesInv(mm: MultiModel, a: MultiAction, mm2: MultiModel)
    requires MultiInv(mm)
    requires AllProjectsLoaded(mm, a)
    requires MultiStep(mm, a) == Ok(mm2)
    ensures MultiInv(mm2)

  // ===========================================================================
  // MultiRebase: Rebase a multi-action through concurrent changes
  // ===========================================================================

  function MultiRebase(
    projectLogs: map<ProjectId, seq<Action>>,
    baseVersions: map<ProjectId, nat>,
    a: MultiAction
  ): MultiAction

  // ===========================================================================
  // MultiCandidates: Generate fallback candidates for an action
  // ===========================================================================

  function MultiCandidates(mm: MultiModel, a: MultiAction): seq<MultiAction>

  // First candidate is always the original action
  lemma CandidatesStartWithOriginal(mm: MultiModel, a: MultiAction)
    requires AllProjectsLoaded(mm, a)
    requires |MultiCandidates(mm, a)| > 0
    ensures MultiCandidates(mm, a)[0] == a

  // ===========================================================================
  // MultiDispatch: Full reconciliation for cross-project operations
  // ===========================================================================

  // Rebase through suffix of each project's log
  function RebaseThroughLogs(
    projectLogs: map<ProjectId, seq<Action>>,
    baseVersions: map<ProjectId, nat>,
    a: MultiAction
  ): MultiAction
  {
    MultiRebase(projectLogs, baseVersions, a)
  }

  // Try candidates until one succeeds
  function TryCandidates(mm: MultiModel, candidates: seq<MultiAction>): Result<(MultiModel, MultiAction), MultiErr>
    requires forall i :: 0 <= i < |candidates| ==> AllProjectsLoaded(mm, candidates[i])
    decreases |candidates|
  {
    if |candidates| == 0 then
      Err(CrossProjectError("No candidate succeeded"))
    else
      var result := MultiStep(mm, candidates[0]);
      match result
      case Ok(mm2) => Ok((mm2, candidates[0]))
      case Err(_) => TryCandidates(mm, candidates[1..])
  }
}


// === End ../kernels/MultiProject.dfy ===
// === Inlined from TodoMultiCollaboration.dfy ===
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

  // StepPreservesInv is declared abstract in Domain.
  // Body provided by refinement (TodoDomain in TodoMultiCollaboration.dfy)

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

  // ============================================================================
  // Helper Lemmas for Sequence Operations
  // ============================================================================

  // Helper: elements in RemoveFirst(s, x) are in s
  // ============================================================================
  // Helper Lemmas for Counting
  // ============================================================================

  // CountInListsHelper over empty sequence is 0
  lemma CountInListsHelper_Empty(tasks: map<ListId, seq<TaskId>>, id: TaskId)
    ensures CountInListsHelper([], tasks, id) == 0
  {
  }

  // Decomposition: count = head contribution + tail contribution
  // If id is not in any list in the map, count is 0
  lemma CountInListsHelper_NotInAny(lists: seq<ListId>, tasks: map<ListId, seq<TaskId>>, id: TaskId)
    requires forall l :: l in tasks ==> !SeqContains(tasks[l], id)
    ensures CountInListsHelper(lists, tasks, id) == 0
    decreases |lists|
  {
  }

  // Effect of RemoveFirst on a single lane's contribution
  // Helper: contribution of a single list to the count
  function ListContrib(l: ListId, tasks: map<ListId, seq<TaskId>>, id: TaskId): nat
  {
    if l in tasks && SeqContains(tasks[l], id) then 1 else 0
  }

  // RemoveFirst from lists decreases count by the removed element's contribution
  // InsertAt into lists increases count by the inserted element's contribution
  // Moving an element (remove then insert) preserves count
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
  // Helper: if targetList is not in lists, and id only in targetList, count is 0
  // Helper for SeqContains in tail
  // Connect sequence membership (x in s) to SeqContains
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
  // Count for other tasks unchanged when we append newId to one list
  // New task appears in exactly one list when appended to targetList
  // Helper: count is 0 in tail for new task
  // Count unchanged for other tasks when we remove a specific task from all lists
  // Takes concrete newTasks map (avoids map comprehension in postcondition)
  // Uses extensional requires instead of map comprehension equality
  // Wrapper for CountAfterRemoveAll
  // Takes concrete newTasks map instead of map comprehension in postcondition
  // If task is in a list that's in the sequence, count is at least 1
  // If a task is in two distinct lists that are both in the list sequence, count >= 2
  // Wrapper for CountAfterMoveTask with concrete tasks1 map
  // Uses extensional requires instead of map comprehension equality
  // Helper: CountInListsHelper gives same result when maps agree on all elements in lists
  // Wrapper for CountUnchangedAfterRemove for MoveTask
  // Uses bidirectional preservation: otherId in newLane iff otherId in original tasks[targetList]
  // Count unchanged when we remove a list from the sequence (for tasks not in that list)
  , tid) ==
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

  // ============================================================================
  // Individual Action Preservation Lemmas
  // ============================================================================

  // Helper for DeleteListPreservesInv - proves invariant F
  // Elements in RemoveFirst are a subset of the original
  // Helper for MoveListPreservesInv - count invariants preserved when list order changes
  // m2.tasks = m.tasks, m2.taskData = m.taskData, so counts are identical
  // Helper for MoveListPreservesInv - list IDs < nextListId preserved
  // Elements in m2.lists = InsertAt(RemoveFirst(m.lists, listId), k, listId) are same as m.lists
  // Helper: if lid in RemoveFirst(s, x), then lid in s
  // Helper lemma to show FindListForTask properties
  // If a task has count >= 1, FindListForTask returns Some
  // If a task is deleted, FindListForTask returns None
  lemma FindListForTaskIsNoneForDeleted(m: Model, taskId: TaskId)
    requires Inv(m)
    requires taskId in m.taskData
    requires m.taskData[taskId].deleted
    ensures FindListForTask(m, taskId).None?
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

  // ============================================================================
  // CandidatesComplete: All meaning-preserving successful actions are candidates
  // ============================================================================

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

// === End TodoMultiCollaboration.dfy ===

module TodoMultiProjectDomain refines MultiProject {
  import MC = TodoMultiCollaboration

  // Re-export domain types for convenience
  type Task = MC.D.Task
  type TaskId = MC.D.TaskId
  type ListId = MC.D.ListId
  type Place = MC.D.Place
  type UserId = MC.D.UserId

  // ===========================================================================
  // MultiAction: Concrete cross-project actions for Todo
  // ===========================================================================

  datatype MultiAction =
    // Wrap a single-project action (most common case)
    | Single(project: ProjectId, action: Action)

    // Cross-project: Move task from one project to another
    | MoveTaskTo(
        srcProject: ProjectId,
        dstProject: ProjectId,
        taskId: TaskId,
        dstList: ListId,
        anchor: Place
      )

    // Cross-project: Copy task to another project (keeps original)
    | CopyTaskTo(
        srcProject: ProjectId,
        dstProject: ProjectId,
        taskId: TaskId,
        dstList: ListId
      )

    // Cross-project: Move entire list to another project
    // Note: Tags and assignees are cleared (project-scoped data)
    | MoveListTo(
        srcProject: ProjectId,
        dstProject: ProjectId,
        listId: ListId
      )

  // ===========================================================================
  // Required by MultiProject: SingleAction and GetSingleAction
  // ===========================================================================

  function SingleAction(pid: ProjectId, a: Action): MultiAction
  {
    Single(pid, a)
  }

  function GetSingleAction(ma: MultiAction): Option<(ProjectId, Action)>
  {
    match ma
    case Single(pid, a) => Some((pid, a))
    case _ => None
  }

  // ===========================================================================
  // Required by MultiProject: TouchedProjects
  // ===========================================================================

  function TouchedProjects(a: MultiAction): set<ProjectId>
  {
    match a
    case Single(pid, _) => {pid}
    case MoveTaskTo(src, dst, _, _, _) => {src, dst}
    case CopyTaskTo(src, dst, _, _) => {src, dst}
    case MoveListTo(src, dst, _) => {src, dst}
  }

  lemma SingleActionTouchesOne(pid: ProjectId, a: Action)
    ensures TouchedProjects(SingleAction(pid, a)) == {
    }
  {}

  // ===========================================================================
  // Required by MultiProject: Inv (delegates to domain Inv)
  // ===========================================================================

  ghost predicate Inv(m: Model)
  {
    MC.D.Inv(m)
  }

  // ===========================================================================
  // Domain-specific error types
  // ===========================================================================

  // Extend MultiErr with Todo-specific errors
  datatype TodoMultiErr =
    | BaseError(err: MultiErr)
    | TaskNotInSource
    | DestListMissing

  // ===========================================================================
  // Helper: Extract task data from a project
  // ===========================================================================

  function ExtractTaskData(m: Model, taskId: TaskId): Result<Task, TodoMultiErr>
  {
    if taskId !in m.taskData then Err(TaskNotInSource)
    else if m.taskData[taskId].deleted then Err(TaskNotInSource)
    else Ok(m.taskData[taskId])
  }

  // Helper: Remove task from source project
  function RemoveTaskFromProject(m: Model, taskId: TaskId, userId: UserId): MC.D.Result<Model, MC.D.Err>
  {
    MC.D.TryStep(m, MC.D.Action.DeleteTask(taskId, userId))
  }

  // Helper: Add task to destination project
  function AddTaskToProject(m: Model, listId: ListId, task: Task, anchor: Place): MC.D.Result<Model, MC.D.Err>
  {
    // Note: This function chains multiple TryStep calls.
    // AddTaskToProjectPreservesInv below proves invariant preservation.
    // First add a basic task
    var addResult := MC.D.TryStep(m, MC.D.Action.AddTask(listId, task.title));
    if addResult.Err? then addResult
    else
      var m1 := addResult.value;
      var newTaskId := m.nextTaskId;

      // Copy over additional properties
      var editResult := MC.D.TryStep(m1, MC.D.Action.EditTask(newTaskId, task.title, task.notes));
      if editResult.Err? then editResult
      else
        var m2 := editResult.value;

        // Copy starred status
        var m3 := if task.starred then
          (match MC.D.TryStep(m2, MC.D.Action.StarTask(newTaskId))
           case Ok(m) => m
           case Err(_) => m2)
        else m2;

        // Copy completed status
        var m4 := if task.completed then
          (match MC.D.TryStep(m3, MC.D.Action.CompleteTask(newTaskId))
           case Ok(m) => m
           case Err(_) => m3)
        else m3;

        // Copy due date
        var m5 := if task.dueDate.Some? then
          (match MC.D.TryStep(m4, MC.D.Action.SetDueDate(newTaskId, task.dueDate))
           case Ok(m) => m
           case Err(_) => m4)
        else m4;

        MC.D.Result.Ok(m5)
  }

  // ===========================================================================
  // Helpers for MoveListTo
  // ===========================================================================

  // Helper: Extract all non-deleted tasks from a list as sequence of (TaskId, Task)
  function ExtractListTasks(m: Model, listId: ListId): seq<Task>
  {
    if listId !in m.tasks then []
    else ExtractTasksFromSeq(m.tasks[listId], m.taskData)
  }

  function ExtractTasksFromSeq(taskIds: seq<TaskId>, taskData: map<TaskId, Task>): seq<Task>
  {
    if |taskIds| == 0 then []
    else
      var id := taskIds[0];
      var rest := ExtractTasksFromSeq(taskIds[1..], taskData);
      if id in taskData && !taskData[id].deleted
      then [taskData[id]] + rest
      else rest
  }

  // Helper: Create a "clean" task for cross-project move (clear tags and assignees)
  function CleanTaskForMove(task: Task): Task
  {
    MC.D.Task(
      task.title, task.notes, task.completed, task.starred,
      task.dueDate,
      {},  // Clear assignees (project-scoped)
      {},  // Clear tags (project-scoped)
      false, MC.D.Option.None, MC.D.Option.None
    )
  }

  // Helper: Add multiple tasks to a list in destination project
  function AddTasksToList(m: Model, listId: ListId, tasks: seq<Task>): MC.D.Result<Model, MC.D.Err>
    decreases |tasks|
  {
    if |tasks| == 0 then MC.D.Result.Ok(m)
    else
      var task := tasks[0];
      var cleanTask := CleanTaskForMove(task);
      var addResult := AddTaskToProject(m, listId, cleanTask, MC.D.Place.AtEnd);
      if addResult.Err? then addResult
      else AddTasksToList(addResult.value, listId, tasks[1..])
  }

  // Helper: Create list and add tasks to destination project
  function AddListWithTasks(m: Model, listName: string, tasks: seq<Task>): MC.D.Result<Model, MC.D.Err>
  {
    // First create the list
    var addListResult := MC.D.TryStep(m, MC.D.Action.AddList(listName));
    if addListResult.Err? then addListResult
    else
      var m1 := addListResult.value;
      var newListId := m.nextListId;
      // Add each task to the new list
      AddTasksToList(m1, newListId, tasks)
  }

  // Helper: Check if list was deleted in a log suffix
  function ListDeletedInLog(suffix: seq<Action>, listId: ListId): bool
  {
    if |suffix| == 0 then false
    else
      match suffix[0]
      case DeleteList(id) => id == listId || ListDeletedInLog(suffix[1..], listId)
      case _ => ListDeletedInLog(suffix[1..], listId)
  }

  // ===========================================================================
  // Required by MultiProject: MultiStep
  // ===========================================================================

  function MultiStep(mm: MultiModel, a: MultiAction): Result<MultiModel, MultiErr>
  {
    match a
    case Single(pid, action) =>
      var model := mm.projects[pid];
      var result := MC.D.TryStep(model, action);
      (match result
       case Ok(newModel) => Ok(MultiModel(mm.projects[pid := newModel]))
       case Err(e) => Err(SingleProjectError(pid, e)))

    case MoveTaskTo(src, dst, taskId, dstList, anchor) =>
      var srcModel := mm.projects[src];
      var dstModel := mm.projects[dst];

      // Extract task data from source
      var extractResult := ExtractTaskData(srcModel, taskId);
      if extractResult.Err? then Err(CrossProjectError("Task not in source"))
      else
        var taskData := extractResult.value;

        // Check destination list exists
        if !MC.D.SeqContains(dstModel.lists, dstList) then Err(CrossProjectError("Destination list missing"))
        else
          // Remove from source (soft delete)
          var removeResult := RemoveTaskFromProject(srcModel, taskId, "");
          if removeResult.Err? then Err(SingleProjectError(src, removeResult.error))
          else
            var newSrc := removeResult.value;

            // Add to destination
            var addResult := AddTaskToProject(dstModel, dstList, taskData, anchor);
            if addResult.Err? then Err(SingleProjectError(dst, addResult.error))
            else
              var newDst := addResult.value;
              Ok(MultiModel(mm.projects[src := newSrc][dst := newDst]))

    case CopyTaskTo(src, dst, taskId, dstList) =>
      var srcModel := mm.projects[src];
      var dstModel := mm.projects[dst];

      // Extract task data from source (don't remove it)
      var extractResult := ExtractTaskData(srcModel, taskId);
      if extractResult.Err? then Err(CrossProjectError("Task not in source"))
      else
        var taskData := extractResult.value;

        // Check destination list exists
        if !MC.D.SeqContains(dstModel.lists, dstList) then Err(CrossProjectError("Destination list missing"))
        else
          // Add to destination (source unchanged)
          var addResult := AddTaskToProject(dstModel, dstList, taskData, MC.D.Place.AtEnd);
          if addResult.Err? then Err(SingleProjectError(dst, addResult.error))
          else
            var newDst := addResult.value;
            Ok(MultiModel(mm.projects[dst := newDst]))

    case MoveListTo(src, dst, listId) =>
      var srcModel := mm.projects[src];
      var dstModel := mm.projects[dst];

      // Check source list exists (and has a name in the map)
      if !MC.D.SeqContains(srcModel.lists, listId) then
        Err(CrossProjectError("Source list missing"))
      else if listId !in srcModel.listNames then
        Err(CrossProjectError("Source list name missing"))  // Should never happen if invariant holds
      else
        var listName := srcModel.listNames[listId];

        // Check destination doesn't have list with same name
        if MC.D.ListNameExists(dstModel, listName, MC.D.Option.None) then
          Err(CrossProjectError("Duplicate list name in destination"))
        else
          // Extract tasks from source list
          var tasks := ExtractListTasks(srcModel, listId);

          // Delete list from source (removes list and its tasks)
          var deleteResult := MC.D.TryStep(srcModel, MC.D.Action.DeleteList(listId));
          if deleteResult.Err? then Err(SingleProjectError(src, deleteResult.error))
          else
            var newSrc := deleteResult.value;

            // Add list with tasks to destination
            var addResult := AddListWithTasks(dstModel, listName, tasks);
            if addResult.Err? then Err(SingleProjectError(dst, addResult.error))
            else
              var newDst := addResult.value;
              Ok(MultiModel(mm.projects[src := newSrc][dst := newDst]))
  }

  // ===========================================================================
  // Required by MultiProject: TryMultiStep
  // ===========================================================================

  function TryMultiStep(mm: MultiModel, a: MultiAction): Result<MultiModel, MultiErr>
  {
    if !AllProjectsLoaded(mm, a) then
      match a
      case Single(pid, _) => Err(MissingProject(pid))
      case MoveTaskTo(src, dst, _, _, _) =>
        if src !in mm.projects then Err(MissingProject(src))
        else Err(MissingProject(dst))
      case CopyTaskTo(src, dst, _, _) =>
        if src !in mm.projects then Err(MissingProject(src))
        else Err(MissingProject(dst))
      case MoveListTo(src, dst, _) =>
        if src !in mm.projects then Err(MissingProject(src))
        else Err(MissingProject(dst))
    else
      MultiStep(mm, a)
  }

  lemma TryMultiStepEquivalence(mm: MultiModel, a: MultiAction)
    ensures AllProjectsLoaded(mm, a) ==> TryMultiStep(mm, a) == MultiStep(mm, a)
  {
  }

  // ===========================================================================
  // Required by MultiProject: MultiStepPreservesInv
  // ===========================================================================

  lemma MultiStepPreservesInv(mm: MultiModel, a: MultiAction, mm2: MultiModel)
  {
  }

  // ===========================================================================
  // Required by MultiProject: MultiRebase
  // ===========================================================================

  function MultiRebase(
    projectLogs: map<ProjectId, seq<Action>>,
    baseVersions: map<ProjectId, nat>,
    a: MultiAction
  ): MultiAction
  {
    match a
    case Single(pid, action) =>
      if pid !in projectLogs || pid !in baseVersions then a
      else
        var suffix := GetSuffix(projectLogs, baseVersions, pid);
        var rebased := RebaseThroughSuffix(suffix, action);
        Single(pid, rebased)

    case MoveTaskTo(src, dst, taskId, dstList, anchor) =>
      var srcSuffix := GetSuffix(projectLogs, baseVersions, src);
      if TaskDeletedInLog(srcSuffix, taskId) then
        Single(src, MC.D.Action.NoOp)
      else
        var dstSuffix := GetSuffix(projectLogs, baseVersions, dst);
        var newAnchor := RebaseAnchor(dstSuffix, anchor);
        MoveTaskTo(src, dst, taskId, dstList, newAnchor)

    case CopyTaskTo(src, dst, taskId, dstList) =>
      var srcSuffix := GetSuffix(projectLogs, baseVersions, src);
      if TaskDeletedInLog(srcSuffix, taskId) then
        Single(src, MC.D.Action.NoOp)
      else
        a

    case MoveListTo(src, dst, listId) =>
      var srcSuffix := GetSuffix(projectLogs, baseVersions, src);
      // If list was deleted in source, become NoOp
      if ListDeletedInLog(srcSuffix, listId) then
        Single(src, MC.D.Action.NoOp)
      else
        a  // Keep as-is (list always placed at end)
  }

  // Helper: Get log suffix for a project
  function GetSuffix(logs: map<ProjectId, seq<Action>>, versions: map<ProjectId, nat>, pid: ProjectId): seq<Action>
  {
    if pid !in logs || pid !in versions then []
    else if versions[pid] >= |logs[pid]| then []
    else logs[pid][versions[pid]..]
  }

  // Helper: Check if task was deleted in a log suffix
  function TaskDeletedInLog(suffix: seq<Action>, taskId: TaskId): bool
  {
    if |suffix| == 0 then false
    else
      match suffix[0]
      case DeleteTask(id, _) => id == taskId || TaskDeletedInLog(suffix[1..], taskId)
      case _ => TaskDeletedInLog(suffix[1..], taskId)
  }

  // Helper: Rebase through a suffix
  function RebaseThroughSuffix(suffix: seq<Action>, local: Action): Action
  {
    if |suffix| == 0 then local
    else
      var rebased := MC.D.Rebase(suffix[0], local);
      RebaseThroughSuffix(suffix[1..], rebased)
  }

  // Helper: Rebase an anchor through concurrent moves
  function RebaseAnchor(suffix: seq<Action>, anchor: Place): Place
  {
    if |suffix| == 0 then anchor
    else
      match suffix[0]
      case MoveTask(movedId, _, _) =>
        var degraded := MC.D.DegradeIfAnchorMoved(movedId, anchor);
        RebaseAnchor(suffix[1..], degraded)
      case _ => RebaseAnchor(suffix[1..], anchor)
  }

  // ===========================================================================
  // Required by MultiProject: MultiCandidates
  // ===========================================================================

  function MultiCandidates(mm: MultiModel, a: MultiAction): seq<MultiAction>
  {
    match a
    case Single(pid, action) =>
      if pid !in mm.projects then [a]
      else
        var candidates := MC.D.Candidates(mm.projects[pid], action);
        seq(|candidates|, i requires 0 <= i < |candidates| => Single(pid, candidates[i]))

    case MoveTaskTo(src, dst, taskId, dstList, anchor) =>
      if dst !in mm.projects then [a]
      else
        var dstModel := mm.projects[dst];
        if !MC.D.SeqContains(dstModel.lists, dstList) then
          if |dstModel.lists| > 0 then
            [a, MoveTaskTo(src, dst, taskId, dstModel.lists[0], MC.D.Place.AtEnd)]
          else
            [a]
        else if anchor == MC.D.Place.AtEnd then
          [a]
        else
          [a, MoveTaskTo(src, dst, taskId, dstList, MC.D.Place.AtEnd)]

    case CopyTaskTo(src, dst, taskId, dstList) =>
      if dst !in mm.projects then [a]
      else
        var dstModel := mm.projects[dst];
        if !MC.D.SeqContains(dstModel.lists, dstList) then
          if |dstModel.lists| > 0 then
            [a, CopyTaskTo(src, dst, taskId, dstModel.lists[0])]
          else
            [a]
        else
          [a]

    case MoveListTo(src, dst, listId) =>
      // No fallback candidates for MoveListTo - either it works or it doesn't
      // (list name conflict in destination is a hard error)
      [a]
  }

  lemma CandidatesStartWithOriginal(mm: MultiModel, a: MultiAction)
  {
  }

  // ===========================================================================
  // View Layer: Multi-Project Queries (compiled)
  // ===========================================================================
  //
  // These functions query across all loaded projects. They use the single
  // MultiModel definition from MultiProject (no separate definition needed).

  // Re-export SmartListType for convenience
  type SmartListType = MC.D.SmartListType

  // Tagged task ID: includes project context
  datatype TaggedTaskId = TaggedTaskId(projectId: ProjectId, taskId: TaskId)

  // Get all priority tasks across all projects
  function GetAllPriorityTasks(mm: MultiModel): set<TaggedTaskId>
  {
    set pid, tid | pid in mm.projects && tid in MC.D.GetPriorityTaskIds(mm.projects[pid])
      :: TaggedTaskId(pid, tid)
  }

  // Get all logbook tasks across all projects
  function GetAllLogbookTasks(mm: MultiModel): set<TaggedTaskId>
  {
    set pid, tid | pid in mm.projects && tid in MC.D.GetLogbookTaskIds(mm.projects[pid])
      :: TaggedTaskId(pid, tid)
  }

  // Get all visible (non-deleted) tasks across all projects
  function GetAllVisibleTasks(mm: MultiModel): set<TaggedTaskId>
  {
    set pid, tid | pid in mm.projects && tid in MC.D.GetVisibleTaskIds(mm.projects[pid])
      :: TaggedTaskId(pid, tid)
  }

  // Get all deleted tasks across all projects (for trash view)
  function GetAllDeletedTasks(mm: MultiModel): set<TaggedTaskId>
  {
    set pid, tid | pid in mm.projects && tid in MC.D.GetDeletedTaskIds(mm.projects[pid])
      :: TaggedTaskId(pid, tid)
  }

  // Count all visible tasks across all projects
  function CountAllVisibleTasks(mm: MultiModel): nat
  {
    |GetAllVisibleTasks(mm)|
  }

  // Get all tasks matching a smart list across all projects
  function GetAllSmartListTasks(mm: MultiModel, smartList: SmartListType): set<TaggedTaskId>
  {
    match smartList
      case Priority => GetAllPriorityTasks(mm)
      case Logbook => GetAllLogbookTasks(mm)
  }

  // Count priority tasks across all projects
  function CountAllPriorityTasks(mm: MultiModel): nat
  {
    |GetAllPriorityTasks(mm)|
  }

  // Count logbook tasks across all projects
  function CountAllLogbookTasks(mm: MultiModel): nat
  {
    |GetAllLogbookTasks(mm)|
  }

  // Count tasks matching a smart list across all projects
  function CountAllSmartListTasks(mm: MultiModel, smartList: SmartListType): nat
  {
    |GetAllSmartListTasks(mm, smartList)|
  }

  // ---------------------------------------------------------------------------
  // MultiModel Helpers (compiled)
  // ---------------------------------------------------------------------------

  // Get a project from the multi-model
  function GetProject(mm: MultiModel, projectId: ProjectId): Option<Model>
  {
    if projectId in mm.projects then Some(mm.projects[projectId]) else None
  }

  // Get all project IDs
  function GetProjectIds(mm: MultiModel): set<ProjectId>
  {
    mm.projects.Keys
  }

  // Count projects
  function CountProjects(mm: MultiModel): nat
  {
    |mm.projects|
  }

  // ===========================================================================
  // Authorization Layer (compiled, separate from domain logic)
  // ===========================================================================
  //
  // This predicate checks whether a user is authorized to perform an action.
  // It's separate from MultiStep so domain logic stays pure.
  // The edge function should call IsAuthorized before calling MultiStep.

  predicate IsAuthorized(mm: MultiModel, actingUser: UserId, a: MultiAction)
  {
    match a
    // MoveListTo: only source project owner can move lists out
    case MoveListTo(src, dst, listId) =>
      src in mm.projects && actingUser == mm.projects[src].owner

    // Single-project actions: allowed for now (could add per-action checks later)
    case Single(pid, action) => true

    // MoveTaskTo: allowed for any member (task-level, less sensitive than list)
    case MoveTaskTo(src, dst, taskId, dstList, anchor) => true

    // CopyTaskTo: allowed for any member (non-destructive)
    case CopyTaskTo(src, dst, taskId, dstList) => true
  }

  // Wrapper for JS: returns string reason if not authorized, empty string if OK
  function CheckAuthorization(mm: MultiModel, actingUser: UserId, a: MultiAction): string
  {
    if IsAuthorized(mm, actingUser, a) then ""
    else match a
      case MoveListTo(_, _, _) => "Only project owner can move lists"
      case _ => "Not authorized"
  }

  // ===========================================================================
  // Error Conversion (compiled, for JS interop)
  // ===========================================================================

  // Convert MultiErr to human-readable string
  function MultiErrToString(err: MultiErr): string
  {
    match err
    case MissingProject(pid) => "Project not found: " + pid
    case SingleProjectError(pid, e) => "Error in project " + pid + ": " + MC.D.ErrToString(e)
    case CrossProjectError(msg) => msg
  }

  // ===========================================================================
  // Effective Actions (compiled, for applied_log storage)
  // ===========================================================================
  //
  // Returns the single-project action to store in each project's applied_log.
  // This is needed because:
  // 1. Single-project dispatch parses applied_log using single-project Action type
  // 2. Rebasing needs to detect deleted tasks/lists via the log
  //
  // For cross-project actions, we return the actual action applied to each project:
  // - Source project gets the "destructive" action (DeleteTask, DeleteList)
  // - Destination project gets the "constructive" action (AddTask, AddList)

  function GetEffectiveAction(mm: MultiModel, a: MultiAction, projectId: ProjectId): Action
  {
    match a
    case Single(pid, action) =>
      if pid == projectId then action else MC.D.Action.NoOp

    case MoveTaskTo(src, dst, taskId, dstList, anchor) =>
      if projectId == src then
        MC.D.Action.DeleteTask(taskId, "")
      else if projectId == dst then
        // Get task title from source model
        if src in mm.projects && taskId in mm.projects[src].taskData then
          var task := mm.projects[src].taskData[taskId];
          MC.D.Action.AddTask(dstList, task.title)
        else
          MC.D.Action.NoOp
      else
        MC.D.Action.NoOp

    case CopyTaskTo(src, dst, taskId, dstList) =>
      if projectId == dst then
        // Get task title from source model
        if src in mm.projects && taskId in mm.projects[src].taskData then
          var task := mm.projects[src].taskData[taskId];
          MC.D.Action.AddTask(dstList, task.title)
        else
          MC.D.Action.NoOp
      else
        // Source unchanged
        MC.D.Action.NoOp

    case MoveListTo(src, dst, listId) =>
      if projectId == src then
        MC.D.Action.DeleteList(listId)
      else if projectId == dst then
        // Get list name from source model
        if src in mm.projects && listId in mm.projects[src].listNames then
          var listName := mm.projects[src].listNames[listId];
          MC.D.Action.AddList(listName)
        else
          MC.D.Action.NoOp
      else
        MC.D.Action.NoOp
  }
}

// === End TodoMultiProjectDomain.dfy ===

module TodoMultiProjectEffectStateMachine refines MultiProjectEffectStateMachine {
  import MP = TodoMultiProjectDomain
}

// Extend with compiled entry points for JavaScript
module TodoMultiProjectEffectAppCore {
  import E = TodoMultiProjectEffectStateMachine
  import MP = TodoMultiProjectDomain
  import TD = TodoDomain

  // Re-export types
  type ProjectId = E.ProjectId
  type Model = E.Model
  type MultiModel = E.MultiModel
  type Action = E.Action
  type MultiAction = E.MultiAction
  type EffectState = E.EffectState
  type EffectEvent = E.Event
  type EffectCommand = E.Command
  type MultiClientState = E.MultiClientState

  // ===========================================================================
  // Initialization
  // ===========================================================================

  function EffectInit(versions: map<ProjectId, nat>, models: map<ProjectId, Model>): EffectState
  {
    E.Init(versions, models)
  }

  // ===========================================================================
  // State Machine Step
  // ===========================================================================

  function EffectStep(es: EffectState, event: EffectEvent): (EffectState, EffectCommand)
  {
    E.Step(es, event)
  }

  // ===========================================================================
  // State Accessors
  // ===========================================================================

  function EffectIsOnline(es: EffectState): bool { E.IsOnline(es) }
  function EffectIsIdle(es: EffectState): bool { E.IsIdle(es) }
  function EffectHasPending(es: EffectState): bool { E.HasPending(es) }
  function EffectPendingCount(es: EffectState): nat { E.PendingCount(es) }
  function EffectIsDispatching(es: EffectState): bool { es.mode.Dispatching? }
  function EffectGetClient(es: EffectState): MultiClientState { es.client }

  // Get current MultiModel from client state
  function EffectGetMultiModel(es: EffectState): MultiModel { es.client.present }

  // Get base versions map
  function EffectGetBaseVersions(es: EffectState): map<ProjectId, nat> { es.client.baseVersions }

  // Get pending actions
  function EffectGetPending(es: EffectState): seq<MultiAction> { es.client.pending }

  // ===========================================================================
  // Event Constructors
  // ===========================================================================

  function EffectUserAction(action: MultiAction): EffectEvent
  {
    E.Event.UserAction(action)
  }

  // Single-project action convenience wrapper
  function EffectSingleUserAction(projectId: ProjectId, action: Action): EffectEvent
  {
    E.Event.UserAction(MP.MultiAction.Single(projectId, action))
  }

  // ===========================================================================
  // Single-Project Query Accessors (for JS interop)
  // ===========================================================================

  // Get deleted task IDs (for trash view)
  function GetDeletedTaskIds(m: Model): set<TD.TaskId>
  {
    MP.MC.D.GetDeletedTaskIds(m)
  }

  function EffectDispatchAccepted(newVersions: map<ProjectId, nat>, newModels: map<ProjectId, Model>): EffectEvent
  {
    E.Event.DispatchAccepted(newVersions, newModels)
  }

  function EffectDispatchConflict(freshVersions: map<ProjectId, nat>, freshModels: map<ProjectId, Model>): EffectEvent
  {
    E.Event.DispatchConflict(freshVersions, freshModels)
  }

  function EffectDispatchRejected(freshVersions: map<ProjectId, nat>, freshModels: map<ProjectId, Model>): EffectEvent
  {
    E.Event.DispatchRejected(freshVersions, freshModels)
  }

  function EffectRealtimeUpdate(projectId: ProjectId, version: nat, model: Model): EffectEvent
  {
    E.Event.RealtimeUpdate(projectId, version, model)
  }

  function EffectNetworkError(): EffectEvent { E.Event.NetworkError }
  function EffectNetworkRestored(): EffectEvent { E.Event.NetworkRestored }
  function EffectManualGoOffline(): EffectEvent { E.Event.ManualGoOffline }
  function EffectManualGoOnline(): EffectEvent { E.Event.ManualGoOnline }
  function EffectTick(): EffectEvent { E.Event.Tick }

  // ===========================================================================
  // Command Inspection
  // ===========================================================================

  function EffectIsNoOp(cmd: EffectCommand): bool { cmd.NoOp? }
  function EffectIsSendDispatch(cmd: EffectCommand): bool { cmd.SendDispatch? }
  function EffectIsFetchFreshState(cmd: EffectCommand): bool { cmd.FetchFreshState? }

  function EffectGetTouchedProjects(cmd: EffectCommand): set<ProjectId>
    requires cmd.SendDispatch?
  { cmd.touchedProjects }

  function EffectGetBaseVersionsFromCmd(cmd: EffectCommand): map<ProjectId, nat>
    requires cmd.SendDispatch?
  { cmd.baseVersions }

  function EffectGetMultiAction(cmd: EffectCommand): MultiAction
    requires cmd.SendDispatch?
  { cmd.action }

  // ===========================================================================
  // MultiAction Constructors
  // ===========================================================================

  function MakeSingleAction(projectId: ProjectId, action: Action): MultiAction
  {
    MP.MultiAction.Single(projectId, action)
  }

  function MakeMoveTaskTo(
    srcProject: ProjectId,
    dstProject: ProjectId,
    taskId: TD.TaskId,
    dstList: TD.ListId,
    anchor: TD.Place
  ): MultiAction
  {
    MP.MultiAction.MoveTaskTo(srcProject, dstProject, taskId, dstList, anchor)
  }

  function MakeCopyTaskTo(
    srcProject: ProjectId,
    dstProject: ProjectId,
    taskId: TD.TaskId,
    dstList: TD.ListId
  ): MultiAction
  {
    MP.MultiAction.CopyTaskTo(srcProject, dstProject, taskId, dstList)
  }

  function MakeMoveListTo(
    srcProject: ProjectId,
    dstProject: ProjectId,
    listId: TD.ListId
  ): MultiAction
  {
    MP.MultiAction.MoveListTo(srcProject, dstProject, listId)
  }

  // ===========================================================================
  // MultiAction Inspection
  // ===========================================================================

  function IsSingleAction(ma: MultiAction): bool { ma.Single? }
  function IsMoveTaskTo(ma: MultiAction): bool { ma.MoveTaskTo? }
  function IsCopyTaskTo(ma: MultiAction): bool { ma.CopyTaskTo? }
  function IsMoveListTo(ma: MultiAction): bool { ma.MoveListTo? }

  function GetTouchedProjects(ma: MultiAction): set<ProjectId>
  {
    MP.TouchedProjects(ma)
  }

  // ===========================================================================
  // MultiModel Helpers
  // ===========================================================================

  function GetProjectModel(mm: MultiModel, projectId: ProjectId): Model
    requires projectId in mm.projects
  {
    mm.projects[projectId]
  }

  // ===========================================================================
  // Single-Project Query Helpers
  // ===========================================================================

  // Find which list contains a task
  function FindListForTask(m: Model, taskId: TD.TaskId): TD.Option<TD.ListId>
  {
    TD.FindListForTask(m, taskId)
  }

  function HasProject(mm: MultiModel, projectId: ProjectId): bool
  {
    projectId in mm.projects
  }

  function GetProjectIds(mm: MultiModel): set<ProjectId>
  {
    mm.projects.Keys
  }

  // ===========================================================================
  // Direct MultiStep access (for server-side use)
  // ===========================================================================

  function TryMultiStep(mm: MultiModel, action: MultiAction): MP.Result<MultiModel, MP.MultiErr>
  {
    MP.TryMultiStep(mm, action)
  }

  function MultiRebase(
    projectLogs: map<ProjectId, seq<Action>>,
    baseVersions: map<ProjectId, nat>,
    action: MultiAction
  ): MultiAction
  {
    MP.MultiRebase(projectLogs, baseVersions, action)
  }

  function MultiCandidates(mm: MultiModel, action: MultiAction): seq<MultiAction>
  {
    MP.MultiCandidates(mm, action)
  }
}
