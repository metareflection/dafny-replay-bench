// RealtimeCollaboration.dfy
// Models the coordination between flush and realtime updates
// Based on the JavaScript fix: skip realtime updates while flushing
//
// This module EXTENDS MultiCollaboration with mode-aware client state.
// It uses MC.ReapplyPending and MC.HandleRealtimeUpdate for the core logic,
// adding mode awareness (Normal | Flushing | Offline) on top.

// It is not used in compiled JS, just for modeling.

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

abstract module RealtimeCollaboration {
  import MC : MultiCollaboration

  // Use MC.D for all domain types (to avoid type mismatches)
  type Model = MC.D.Model
  type Action = MC.D.Action

  // Local Option type
  datatype Option<T> = None | Some(value: T)

  // ==========================================================================
  // Client state with flush mode (extends MC.ClientState)
  // ==========================================================================

  datatype ClientMode = Normal | Flushing | Offline

  // Extended client state: wraps MC.ClientState + mode
  datatype ClientState = ClientState(
    base: MC.ClientState,       // Core client state (version, model, pending)
    mode: ClientMode            // Normal, Flushing, or Offline
  )

  // Accessors that delegate to base
  function BaseVersion(client: ClientState): nat { client.base.baseVersion }
  function Present(client: ClientState): Model { client.base.present }
  function Pending(client: ClientState): seq<Action> { client.base.pending }

  // ==========================================================================
  // Client initialization
  // ==========================================================================

  function InitClient(version: nat, model: Model): ClientState
  {
    ClientState(MC.InitClient(version, model), Normal)
  }

  function Sync(server: MC.ServerState): ClientState
  {
    ClientState(MC.Sync(server), Normal)
  }

  // ==========================================================================
  // Local dispatch (optimistic update)
  // ==========================================================================

  function LocalDispatch(client: ClientState, action: Action): ClientState
  {
    // Delegate to MC.ClientLocalDispatch, preserve mode
    var newBase := MC.ClientLocalDispatch(client.base, action);
    ClientState(newBase, client.mode)
  }

  // ==========================================================================
  // Realtime update handling - THE KEY FIX
  // ==========================================================================

  // Handle a realtime update from the server
  // KEY PROPERTIES:
  // - Skip when flushing or offline
  // - Preserve pending actions by re-applying to new server model (via MC.HandleRealtimeUpdate)
  function HandleRealtimeUpdate(client: ClientState, serverVersion: nat, serverModel: Model): ClientState
  {
    if client.mode == Flushing || client.mode == Offline then
      // Skip realtime updates while flushing or offline
      // - Flushing: we'll sync at the end
      // - Offline: user doesn't expect to see network updates
      client
    else
      // Delegate to MC.HandleRealtimeUpdate for the actual logic
      var newBase := MC.HandleRealtimeUpdate(client.base, serverVersion, serverModel);
      ClientState(newBase, Normal)
  }

  // ==========================================================================
  // Flush operations
  // ==========================================================================

  // Enter flushing mode
  function EnterFlushMode(client: ClientState): ClientState
  {
    ClientState(client.base, Flushing)
  }

  // Exit flushing mode (after sync)
  function ExitFlushMode(client: ClientState, server: MC.ServerState): ClientState
  {
    Sync(server)
  }

  datatype FlushOneResult = FlushOneResult(
    server: MC.ServerState,
    client: ClientState,
    reply: MC.Reply
  )

  // Flush one pending action
  function FlushOne(server: MC.ServerState, client: ClientState): Option<FlushOneResult>
    requires BaseVersion(client) <= MC.Version(server)
    requires MC.D.Inv(server.present)
  {
    if |Pending(client)| == 0 then None
    else
      var action := Pending(client)[0];
      var rest := Pending(client)[1..];

      var (newServer, reply) := MC.Dispatch(server, BaseVersion(client), action);

      match reply
        case Accepted(newVersion, newPresent, applied, noChange) =>
          var newBase := MC.ClientState(newVersion, newPresent, rest);
          var newClient := ClientState(newBase, client.mode);
          Some(FlushOneResult(newServer, newClient, reply))

        case Rejected(reason, rebased) =>
          var newBase := MC.ClientState(MC.Version(server), server.present, rest);
          var newClient := ClientState(newBase, client.mode);
          Some(FlushOneResult(newServer, newClient, reply))
  }

  datatype FlushAllResult = FlushAllResult(
    server: MC.ServerState,
    client: ClientState,
    replies: seq<MC.Reply>
  )

  // Flush all pending actions (recursive)
  function FlushAll(server: MC.ServerState, client: ClientState): FlushAllResult
    requires BaseVersion(client) <= MC.Version(server)
    requires MC.D.Inv(server.present)
    requires client.mode == Flushing
    ensures MC.D.Inv(FlushAll(server, client).server.present)
    ensures FlushAll(server, client).client.mode == Flushing
    ensures |FlushAll(server, client).replies| == |Pending(client)|  // no silent data loss
    ensures Pending(FlushAll(server, client).client) == []  // all actions processed
    decreases |Pending(client)|
  {
    if |Pending(client)| == 0 then
      FlushAllResult(server, client, [])
    else
      var flushResult := FlushOne(server, client);
      if flushResult.None? then
        FlushAllResult(server, client, [])
      else
        var result := flushResult.value;
        if BaseVersion(result.client) <= MC.Version(result.server) then
          var rest := FlushAll(result.server, result.client);
          FlushAllResult(rest.server, rest.client, [result.reply] + rest.replies)
        else
          FlushAllResult(result.server, result.client, [result.reply])
  }

  // ==========================================================================
  // Complete flush cycle: enter flush mode, flush all, sync
  // ==========================================================================

  datatype FlushCycleResult = FlushCycleResult(
    server: MC.ServerState,
    client: ClientState,
    replies: seq<MC.Reply>
  )

  function FlushCycle(server: MC.ServerState, client: ClientState): FlushCycleResult
    requires BaseVersion(client) <= MC.Version(server)
    requires MC.D.Inv(server.present)
    ensures MC.D.Inv(FlushCycle(server, client).server.present)
    ensures FlushCycle(server, client).client.mode == Normal
    ensures Pending(FlushCycle(server, client).client) == []
  {
    // 1. Enter flushing mode
    var flushingClient := EnterFlushMode(client);

    // 2. Flush all pending actions
    var flushResult := FlushAll(server, flushingClient);

    // 3. Exit flushing mode with final sync
    var finalClient := ExitFlushMode(flushResult.client, flushResult.server);

    FlushCycleResult(flushResult.server, finalClient, flushResult.replies)
  }

  // ==========================================================================
  // KEY THEOREM: Realtime updates during flush don't affect final state
  // ==========================================================================

  // Model an interleaved execution where realtime updates arrive during flush
  // We prove that the final state is the same as if we skipped them

  // A "realtime event" that might arrive during flush
  datatype RealtimeEvent = RealtimeEvent(version: nat, model: Model)

  // Process flush with interleaved realtime events
  // Since HandleRealtimeUpdate skips during Flushing mode, events have no effect
  function FlushWithRealtimeEvents(
    server: MC.ServerState,
    client: ClientState,
    events: seq<RealtimeEvent>
  ): FlushCycleResult
    requires BaseVersion(client) <= MC.Version(server)
    requires MC.D.Inv(server.present)
    ensures MC.D.Inv(FlushWithRealtimeEvents(server, client, events).server.present)
    ensures FlushWithRealtimeEvents(server, client, events).client.mode == Normal
    ensures Pending(FlushWithRealtimeEvents(server, client, events).client) == []
  {
    // 1. Enter flushing mode
    var flushingClient := EnterFlushMode(client);

    // 2. Process realtime events (all skipped because mode == Flushing)
    var afterEvents := ProcessRealtimeEvents(flushingClient, events);

    // 3. Flush all pending actions
    var flushResult := FlushAll(server, afterEvents);

    // 4. Exit flushing mode with final sync
    var finalClient := ExitFlushMode(flushResult.client, flushResult.server);

    FlushCycleResult(flushResult.server, finalClient, flushResult.replies)
  }

  function ProcessRealtimeEvents(client: ClientState, events: seq<RealtimeEvent>): ClientState
    ensures client.mode == Flushing ==> ProcessRealtimeEvents(client, events) == client
    decreases |events|
  {
    if |events| == 0 then client
    else
      var e := events[0];
      var newClient := HandleRealtimeUpdate(client, e.version, e.model);
      // When flushing, newClient == client, so mode stays Flushing
      ProcessRealtimeEvents(newClient, events[1..])
  }

  // THE KEY LEMMA: Realtime events have no effect during flush
  lemma RealtimeEventsSkippedDuringFlush(client: ClientState, events: seq<RealtimeEvent>)
    requires client.mode == Flushing
    ensures ProcessRealtimeEvents(client, events) == client
  {
  }

  // MAIN THEOREM: Flush with realtime events gives same result as flush without
  lemma FlushWithRealtimeEventsEquivalent(
    server: MC.ServerState,
    client: ClientState,
    events: seq<RealtimeEvent>
  )
    requires BaseVersion(client) <= MC.Version(server)
    requires MC.D.Inv(server.present)
    ensures FlushWithRealtimeEvents(server, client, events) == FlushCycle(server, client)
  {
  }

  // ==========================================================================
  // Additional property: After flush cycle, client is synced with server
  // ==========================================================================

  lemma FlushCycleClientSynced(server: MC.ServerState, client: ClientState)
    requires BaseVersion(client) <= MC.Version(server)
    requires MC.D.Inv(server.present)
    ensures var result := FlushCycle(server, client);
            Present(result.client) == result.server.present &&
            BaseVersion(result.client) == MC.Version(result.server)
  {
    // Follows from ExitFlushMode calling Sync
  }
}
