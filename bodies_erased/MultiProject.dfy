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
  lemma ChooseCandidateFindsGood(m: D.Model, cs: seq<D.Action>, aGood: D.Action, m2: D.Model)
    requires aGood in cs
    requires D.TryStep(m, aGood) == D.Ok(m2)
    ensures  ChooseCandidate(m, cs).Ok?
    decreases |cs|
  {
  }
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
