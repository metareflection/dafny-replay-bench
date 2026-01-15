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

  lemma InitSatisfiesInv(versions: map<ProjectId, nat>, models: map<ProjectId, Model>)
    ensures Inv(Init(versions, models))
  {
  }

  // ===========================================================================
  // Invariant Preservation
  // ===========================================================================

  lemma StepPreservesInv(es: EffectState, event: Event)
    requires Inv(es)
    ensures Inv(Step(es, event).0)
  {
  }
}
