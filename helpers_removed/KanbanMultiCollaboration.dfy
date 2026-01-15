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

module KanbanDomain refines Domain {
  type CardId = nat
  type ColId  = string

  datatype Card = Card(title: string)

  datatype Model = Model(
    cols: seq<ColId>,                 // authoritative order
    lanes: map<ColId, seq<CardId>>,   // col -> ordered ids
    wip: map<ColId, nat>,             // col -> limit
    cards: map<CardId, Card>,         // id -> payload
    nextId: nat                       // allocator (optional if you want server-only ids)
  )

  datatype Err =
    | MissingColumn
    | MissingCard
    | WipExceeded
    | BadAnchor
    | Rejected  // Used by kernel when no candidate succeeds

  // Distinguished error for rejection
  function RejectErr(): Err { Rejected }

  datatype Option<T> = None | Some(value: T)

  // Less positional move: anchor-based intent
  datatype Place =
    | AtEnd
    | Before(anchor: CardId)
    | After(anchor: CardId)

  datatype Action =
    | NoOp
    | AddColumn(col: ColId, limit: nat)
    | SetWip(col: ColId, limit: nat)
    | AddCard(col: ColId, title: string)     // allocates nextId
    | MoveCard(id: CardId, toCol: ColId, place: Place)
    | EditTitle(id: CardId, title: string)

  // --- Invariant helpers ---

  // No duplicates in a sequence
  predicate NoDupSeq<T(==)>(s: seq<T>)
  {
    forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j]
  }

  // Flatten all lanes along cols order into a single sequence of CardIds
  function AllIds(m: Model): seq<CardId>
  {
    AllIdsHelper(m.cols, m.lanes)
  }

  function AllIdsHelper(cols: seq<ColId>, lanes: map<ColId, seq<CardId>>): seq<CardId>
  {
    if |cols| == 0 then []
    else
      var c := cols[0];
      var lane := if c in lanes then lanes[c] else [];
      lane + AllIdsHelper(cols[1..], lanes)
  }

  // Check if id occurs in any lane
  predicate OccursInLanes(m: Model, id: CardId)
  {
    exists c :: c in m.lanes && SeqContains(m.lanes[c], id)
  }

  // Count occurrences of id across all lanes
  function CountInLanes(m: Model, id: CardId): nat
  {
    CountInLanesHelper(m.cols, m.lanes, id)
  }

  function CountInLanesHelper(cols: seq<ColId>, lanes: map<ColId, seq<CardId>>, id: CardId): nat
  {
    if |cols| == 0 then 0
    else
      var c := cols[0];
      var lane := if c in lanes then lanes[c] else [];
      var here := if SeqContains(lane, id) then 1 else 0;
      here + CountInLanesHelper(cols[1..], lanes, id)
  }

  // --- Real invariant ---
  ghost predicate Inv(m: Model)
  {
    // A: Columns are unique
    NoDupSeq(m.cols)

    // B: lanes and wip defined exactly on cols
    && (forall c :: c in m.lanes <==> SeqContains(m.cols, c))
    && (forall c :: c in m.wip <==> SeqContains(m.cols, c))

    // C: Every id in any lane exists in cards
    && (forall c, id :: c in m.lanes && SeqContains(m.lanes[c], id) ==> id in m.cards)

    // D: Every card id occurs in exactly one lane (no duplicates, no orphans)
    && (forall id :: id in m.cards ==> CountInLanes(m, id) == 1)

    // E: No duplicate ids within any single lane
    && (forall c :: c in m.lanes ==> NoDupSeq(m.lanes[c]))

    // F: WIP respected: each lane length <= its limit
    && (forall c :: c in m.cols && c in m.lanes && c in m.wip ==> |m.lanes[c]| <= m.wip[c])

    // G: Allocator fresh: all card ids are < nextId
    && (forall id :: id in m.cards ==> id < m.nextId)
  }

  // --- Initial model ---
  function Init(): Model {
    Model([], map[], map[], map[], 0)
  }

  // --- Helpers ---
  function Get<K,V>(mp: map<K,V>, k: K, d: V): V { if k in mp then mp[k] else d }
  function Lane(m: Model, c: ColId): seq<CardId> { Get(m.lanes, c, []) }
  function Wip(m: Model, c: ColId): nat { Get(m.wip, c, 0) }

  function SeqContains<T(==)>(s: seq<T>, x: T): bool { exists i :: 0 <= i < |s| && s[i] == x }

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

  // Compute candidate position from an anchor intent *in the current lane*.
  function PosFromPlace(lane: seq<CardId>, p: Place): int
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

  // --- Semantics ---
  function TryStep(m: Model, a: Action): Result<Model, Err>
  {
    match a
      case NoOp => Ok(m)

      case AddColumn(col, limit) =>
        if col in m.cols then Ok(m)
        else Ok(Model(m.cols + [col],
                      m.lanes[col := []],
                      m.wip[col := limit],
                      m.cards,
                      m.nextId))

      case SetWip(col, limit) =>
        if !(col in m.cols) then Err(MissingColumn)
        else if limit < |Lane(m,col)| then Err(WipExceeded)
        else Ok(Model(m.cols, m.lanes, m.wip[col := limit], m.cards, m.nextId))

      case AddCard(col, title) =>
        if !(col in m.cols) then Err(MissingColumn)
        else if |Lane(m,col)| + 1 > Wip(m,col) then Err(WipExceeded)
        else
          var id := m.nextId;
          Ok(Model(m.cols,
                   m.lanes[col := Lane(m,col) + [id]],
                   m.wip,
                   m.cards[id := Card(title)],
                   m.nextId + 1))

      case EditTitle(id, title) =>
        if !(id in m.cards) then Err(MissingCard)
        else Ok(Model(m.cols, m.lanes, m.wip, m.cards[id := Card(title)], m.nextId))

      case MoveCard(id, toCol, place) =>
        if !(id in m.cards) then Err(MissingCard)
        else if !(toCol in m.cols) then Err(MissingColumn)
        else if |Lane(m,toCol)| + (if SeqContains(Lane(m,toCol), id) then 0 else 1) > Wip(m,toCol) then Err(WipExceeded)
        else
          // remove from all lanes, then insert into toCol
          var lanes1 := map c | c in m.lanes :: RemoveFirst(m.lanes[c], id);
          var tgt := Get(lanes1, toCol, []);
          var pos := PosFromPlace(tgt, place);
          if pos < 0 then Err(BadAnchor)
          else
            var k := ClampPos(pos, |tgt|);
            var tgt2 := InsertAt(tgt, k, id);
            Ok(Model(m.cols, lanes1[toCol := tgt2], m.wip, m.cards, m.nextId))
  }

  // --- Collaboration hooks ---

  // Helper: extract anchor from a Place
  function PlaceAnchor(p: Place): Option<CardId>
  {
    match p
      case AtEnd => None
      case Before(a) => Some(a)
      case After(a) => Some(a)
  }

  // Helper: degrade place to AtEnd if anchor is the moved card
  function DegradeIfAnchorMoved(movedId: CardId, p: Place): Place
  {
    match p
      case AtEnd => AtEnd
      case Before(a) => if a == movedId then AtEnd else p
      case After(a) => if a == movedId then AtEnd else p
  }

  // Rebase: intent-aware transformation of local action given remote action.
  // For Kanban:
  // - Title edits commute with moves.
  // - Same-card move/move: keep local (LWW-by-arrival).
  // - If remote moved the anchor card, degrade local's place to AtEnd.
  function Rebase(remote: Action, local: Action): Action
  {
    match (remote, local)
      case (NoOp, _) => local
      case (_, NoOp) => NoOp

      // Same card move: keep local (LWW).
      case (MoveCard(rid, _, _), MoveCard(lid, ltoCol, lplace)) =>
        if rid == lid then local
        // Remote moved anchor card: degrade local's placement
        else MoveCard(lid, ltoCol, DegradeIfAnchorMoved(rid, lplace))

      // Edits: keep local (LWW).
      case (EditTitle(_, _), EditTitle(_, _)) => local

      // Remote move might affect local move's anchor
      case (MoveCard(rid, _, _), _) => local

      // AddColumn doesn't affect other actions
      case (AddColumn(_, _), _) => local

      // SetWip doesn't affect other actions
      case (SetWip(_, _), _) => local

      // AddCard doesn't affect other actions (new id won't collide)
      case (AddCard(_, _), _) => local

      // EditTitle doesn't affect other actions
      case (EditTitle(_, _), _) => local
  }

  // "Explains": candidate is a meaning-preserving interpretation of orig.
  // For Kanban:
  // - Non-move actions: exact equality
  // - MoveCard: same card + same destination column; placement can be:
  //   (1) same as original, or (2) AtEnd fallback
  //
  // NOTE: This definition is deliberately restrictive. The minimal-reject
  // guarantee we prove is: "If origPlace OR AtEnd would succeed, server
  // won't reject." The server also tries Before(first) as a heuristic,
  // but that's not covered by this guarantee. See BeforeFirstImpliesAtEnd
  // for why Before(first) success implies AtEnd success anyway.
  ghost predicate Explains(orig: Action, cand: Action)
  {
    match (orig, cand)
      // MoveCard: same card, same destination column, and placement is either
      // the original placement or AtEnd (the universal fallback)
      case (MoveCard(oid, otoCol, origPlace), MoveCard(cid, ctoCol, candPlace)) =>
        oid == cid && otoCol == ctoCol &&
        (candPlace == origPlace || candPlace == AtEnd)

      // All other actions: exact equality
      case (_, _) => orig == cand
  }

  // Candidates: give a small list that avoids coarse rejection.
  // For MoveCard, try:
  //  1. Original placement (anchor-resolved)
  //  2. AtEnd fallback (if anchor missing or for resilience)
  //  3. AtStart (Before first card) for less disruption if lane non-empty
  function Candidates(m: Model, a: Action): seq<Action>
  {
    match a
      case MoveCard(id, toCol, place) =>
        var lane := Lane(m, toCol);
        if place == AtEnd then
          // Already AtEnd, just try it
          [MoveCard(id, toCol, AtEnd)]
        else if |lane| == 0 then
          // Empty lane: AtEnd is the only sensible placement
          [MoveCard(id, toCol, place), MoveCard(id, toCol, AtEnd)]
        else
          // Try: original, AtEnd, and Before(first) for front placement
          var first := lane[0];
          [MoveCard(id, toCol, place),
           MoveCard(id, toCol, AtEnd),
           MoveCard(id, toCol, Before(first))]
      case _ =>
        [a]
  }

  lemma StepPreservesInv(m: Model, a: Action, m2: Model)
  {
  }

  // Helper to establish preconditions more explicitly
  // --- Helper lemmas for StepPreservesInv ---

  lemma CountInLanesHelperFreshId(cols: seq<ColId>, lanes: map<ColId, seq<CardId>>, id: CardId, m: Model)
    requires Inv(m)
    requires id == m.nextId
    requires forall c :: c in cols && c in lanes ==> (forall x :: SeqContains(lanes[c], x) ==> x in m.cards)
    ensures CountInLanesHelper(cols, lanes, id) == 0
  {
  }

  lemma MoveCardPreservesInv(m: Model, id: CardId, toCol: ColId, place: Place, m2: Model)
    requires Inv(m)
    requires id in m.cards
    requires toCol in m.cols
    requires |Lane(m, toCol)| + (if SeqContains(Lane(m, toCol), id) then 0 else 1) <= Wip(m, toCol)
    requires var lanes1 := map c | c in m.lanes :: RemoveFirst(m.lanes[c], id);
             var tgt := Get(lanes1, toCol, []);
             var pos := PosFromPlace(tgt, place);
             pos >= 0 &&
             m2 == Model(m.cols, lanes1[toCol := InsertAt(tgt, ClampPos(pos, |tgt|), id)], m.wip, m.cards, m.nextId)
    ensures Inv(m2)
  {
    var lanes1 := map c | c in m.lanes :: RemoveFirst(m.lanes[c], id);
    var tgt := Get(lanes1, toCol, []);
    var pos := PosFromPlace(tgt, place);
    var k := ClampPos(pos, |tgt|);
    var tgt2 := InsertAt(tgt, k, id);
    var lanes2 := lanes1[toCol := tgt2];

    // m2 is given by the precondition; connect to our local variables
    // The precondition establishes m2 == Model(m.cols, lanes1[toCol := InsertAt(tgt, ClampPos(pos, |tgt|), id)], ...)
    // Since k == ClampPos(pos, |tgt|), we have lanes2 == m2.lanes
    assert k == ClampPos(pos, |tgt|);
    assert tgt2 == InsertAt(tgt, ClampPos(pos, |tgt|), id);
    assert lanes2 == lanes1[toCol := tgt2];
    assert lanes2 == lanes1[toCol := InsertAt(tgt, ClampPos(pos, |tgt|), id)];

    // A: cols unchanged

    // B: lanes keys unchanged
    assert forall c :: c in m2.lanes <==> SeqContains(m2.cols, c) by {
      forall c
        ensures c in m2.lanes <==> SeqContains(m2.cols, c)
      {
        assert c in lanes1 <==> c in m.lanes;
        assert c in m.lanes <==> SeqContains(m.cols, c);
      }
    }

    // C: Every id in lanes exists in cards
    assert forall c, cid :: c in m2.lanes && SeqContains(m2.lanes[c], cid) ==> cid in m2.cards by {
      forall c, cid | c in m2.lanes && SeqContains(m2.lanes[c], cid)
        ensures cid in m2.cards
      {
        if c == toCol {
          // m2.lanes[toCol] = tgt2 = InsertAt(tgt, k, id)
          assert m2.lanes[toCol] == tgt2;
          assert tgt2 == InsertAt(tgt, k, id);
          assert SeqContains(m2.lanes[toCol], cid);
          SeqContainsInsertAt(tgt, k, id, cid);
          if cid == id {
            assert id in m.cards;
          } else {
            // By SeqContainsInsertAt: SeqContains(InsertAt(tgt, k, id), cid) <==> (cid == id || SeqContains(tgt, cid))
            // Since cid != id and SeqContains(tgt2, cid), we have SeqContains(tgt, cid)
            assert SeqContains(tgt, cid);
            // tgt = lanes1[toCol] = RemoveFirst(m.lanes[toCol], id)
            assert tgt == lanes1[toCol];
            assert lanes1[toCol] == RemoveFirst(m.lanes[toCol], id);
            SeqContainsRemoveFirst(m.lanes[toCol], id, cid);
            assert SeqContains(m.lanes[toCol], cid);
            assert cid in m.cards;
          }
        } else {
          // m2.lanes[c] = lanes1[c] = RemoveFirst(m.lanes[c], id)
          assert lanes1[c] == RemoveFirst(m.lanes[c], id);
          if cid == id {
            // But id was removed from all lanes, so it shouldn't be here
            RemoveFirstRemoves(m.lanes[c], id);
            assert !SeqContains(lanes1[c], id);
            assert false;
          } else {
            SeqContainsRemoveFirst(m.lanes[c], id, cid);
            assert SeqContains(m.lanes[c], cid);
            assert cid in m.cards;
          }
        }
      }
    }

    // D: CountInLanes for each card == 1
    forall cid | cid in m2.cards
      ensures CountInLanes(m2, cid) == 1
    {
      MoveCardCountInLanes(m, id, toCol, lanes1, tgt, k, cid);
    }

    // E: No duplicates in lanes
    forall c | c in m2.lanes
      ensures NoDupSeq(m2.lanes[c])
    {
      if c == toCol {
        // Need NoDupSeq(tgt2) where tgt2 = InsertAt(tgt, k, id)
        // tgt = RemoveFirst(m.lanes[toCol], id), which has no dups and doesn't contain id
        RemoveFirstNoDup(m.lanes[toCol], id);
        RemoveFirstRemoves(m.lanes[toCol], id);
        NoDupSeqInsertAt(tgt, k, id);
      } else {
        RemoveFirstNoDup(m.lanes[c], id);
      }
    }

    // F: WIP respected
    assert forall c :: c in m.cols && c in m2.lanes && c in m.wip ==> |m2.lanes[c]| <= m.wip[c] by {
      forall c | c in m.cols && c in m2.lanes && c in m.wip
        ensures |m2.lanes[c]| <= m.wip[c]
      {
        if c == toCol {
          assert |tgt2| == |tgt| + 1;
          RemoveFirstLength(m.lanes[toCol], id);
          if SeqContains(m.lanes[toCol], id) {
            assert |tgt| == |m.lanes[toCol]| - 1;
            assert |tgt2| == |m.lanes[toCol]|;
          } else {
            assert |tgt| == |m.lanes[toCol]|;
            assert |tgt2| == |m.lanes[toCol]| + 1;
          }
        } else {
          RemoveFirstLength(m.lanes[c], id);
        }
      }
    }

    // G: Allocator fresh (cards unchanged)
  }

  lemma RemoveFirstNoDup<T>(s: seq<T>, x: T)
    requires NoDupSeq(s)
    ensures NoDupSeq(RemoveFirst(s, x))
  {
  }

  lemma NoDupSeqInsertAt<T>(s: seq<T>, i: nat, x: T)
    requires i <= |s|
    requires NoDupSeq(s)
    requires !SeqContains(s, x)
    ensures NoDupSeq(InsertAt(s, i, x))
  {
  }

  lemma RemoveFirstLength<T>(s: seq<T>, x: T)
    ensures |RemoveFirst(s, x)| == if SeqContains(s, x) then |s| - 1 else |s|
  {
  }

  lemma MoveCardCountInLanes(m: Model, id: CardId, toCol: ColId, lanes1: map<ColId, seq<CardId>>, tgt: seq<CardId>, k: nat, cid: CardId)
    requires Inv(m)
    requires id in m.cards
    requires toCol in m.cols
    requires lanes1 == map c | c in m.lanes :: RemoveFirst(m.lanes[c], id)
    requires tgt == Get(lanes1, toCol, [])
    requires k <= |tgt|
    requires cid in m.cards
    ensures CountInLanes(Model(m.cols, lanes1[toCol := InsertAt(tgt, k, id)], m.wip, m.cards, m.nextId), cid) == 1
  {
  }

  // Helper lemma: when toCol is not in cols, lanes2 and lanes1 agree on cols,
  // and lanes1 differs from lanes only by RemoveFirst on id (which != cid), counts are equal
  // Before(first) is a heuristic candidate in Candidates, but not in Explains.
  // This lemma shows that Before(first) success implies AtEnd success, so
  // the heuristic never helps avoid rejection—it only affects final position.
  //
  // Proof: TryStep failure modes are:
  //   1. MissingCard   - same for all placements
  //   2. MissingColumn - same for all placements
  //   3. WipExceeded   - same for all placements (depends on lane size, not placement)
  //   4. BadAnchor     - only for Before/After when anchor not found
  // AtEnd never fails due to (4), so if Before(first) passes (1)-(4), AtEnd passes (1)-(3).
  lemma BeforeFirstImpliesAtEnd(m: Model, id: CardId, toCol: ColId, anchor: CardId, m2: Model)
    requires TryStep(m, MoveCard(id, toCol, Before(anchor))).Ok?
    ensures  TryStep(m, MoveCard(id, toCol, AtEnd)).Ok?
  {
  }
}

module KanbanMultiCollaboration refines MultiCollaboration {
  import D = KanbanDomain
}

// =============================================================================
// AppCore: JS-friendly wrappers around MultiCollaboration client operations
// =============================================================================
module KanbanAppCore {
  import K = KanbanDomain
  import MC = KanbanMultiCollaboration

  // -------------------------------------------------------------------------
  // Re-export ClientState from MultiCollaboration
  // -------------------------------------------------------------------------
  type ClientState = MC.ClientState

  // Constructor wrapper for JS
  function MakeClientState(baseVersion: nat, present: K.Model, pending: seq<K.Action>): ClientState
  {
    MC.ClientState(baseVersion, present, pending)
  }

  // -------------------------------------------------------------------------
  // Initialization
  // -------------------------------------------------------------------------

  // Create initial server state with verified default model
  function Init(): MC.ServerState
  {
    MC.InitServer()
  }

  // Create initial server state from a custom model
  // Note: caller is responsible for ensuring model satisfies K.Inv
  function InitServerWithModel(initModel: K.Model): MC.ServerState
  {
    MC.ServerState(initModel, [], [])
  }

  // Create client state synced to server
  function InitClientFromServer(server: MC.ServerState): ClientState
  {
    MC.InitClientFromServer(server)
  }

  // -------------------------------------------------------------------------
  // Client operations (delegated to MultiCollaboration)
  // -------------------------------------------------------------------------

  function ClientLocalDispatch(client: ClientState, action: K.Action): ClientState
  {
    MC.ClientLocalDispatch(client, action)
  }

  function HandleRealtimeUpdate(client: ClientState, serverVersion: nat, serverModel: K.Model): ClientState
  {
    MC.HandleRealtimeUpdate(client, serverVersion, serverModel)
  }

  function ClientAcceptReply(client: ClientState, newVersion: nat, newPresent: K.Model): ClientState
  {
    MC.ClientAcceptReply(client, newVersion, newPresent)
  }

  function Sync(server: MC.ServerState): ClientState
  {
    MC.Sync(server)
  }

  // -------------------------------------------------------------------------
  // Inspection helpers
  // -------------------------------------------------------------------------

  function ServerVersion(server: MC.ServerState): nat
  {
    MC.Version(server)
  }

  function ServerModel(server: MC.ServerState): K.Model
  {
    server.present
  }

  function AuditLength(server: MC.ServerState): nat
  {
    |server.auditLog|
  }

  function PendingCount(client: ClientState): nat
  {
    MC.PendingCount(client)
  }

  function ClientModel(client: ClientState): K.Model
  {
    MC.ClientModel(client)
  }

  function ClientVersion(client: ClientState): nat
  {
    MC.ClientVersion(client)
  }

  // Check if reply was accepted
  function IsAccepted(reply: MC.Reply): bool
  {
    reply.Accepted?
  }

  // Check if reply was rejected
  function IsRejected(reply: MC.Reply): bool
  {
    reply.Rejected?
  }
}

