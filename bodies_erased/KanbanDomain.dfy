// === Inlined from ../kernels/Replay.dfy ===
abstract module {:compile false} Domain {
  type Model
  type Action

  ghost predicate Inv(m: Model)

  function Init(): Model
  function Apply(m: Model, a: Action): Model
    requires Inv(m)
  function Normalize(m: Model): Model

  lemma InitSatisfiesInv()
    ensures Inv(Init())

  lemma StepPreservesInv(m: Model, a: Action)
    requires Inv(m)
    ensures Inv(Normalize(Apply(m,a)))
}

abstract module {:compile false} Kernel {
  import D : Domain

  function Step(m: D.Model, a: D.Action): D.Model
  requires D.Inv(m)
  {
    D.Normalize(D.Apply(m, a))
  }

  function InitHistory(): History {
    History([], D.Init(), [])
  }

  datatype History =
    History(past: seq<D.Model>, present: D.Model, future: seq<D.Model>)

  function Do(h: History, a: D.Action): History
  requires D.Inv(h.present)
  {
    History(h.past + [h.present], Step(h.present, a), [])
  }

  // Apply action without recording to history (for live preview during drag)
  function Preview(h: History, a: D.Action): History
  requires D.Inv(h.present)
  {
    History(h.past, Step(h.present, a), h.future)
  }

  // Commit current state, recording baseline to history (for end of drag)
  function CommitFrom(h: History, baseline: D.Model): History {
    History(h.past + [baseline], h.present, [])
  }

  function Undo(h: History): History {
    if |h.past| == 0 then h
    else
      var i := |h.past| - 1;
      History(h.past[..i], h.past[i], [h.present] + h.future)
  }

  function Redo(h: History): History {
    if |h.future| == 0 then h
    else
      History(h.past + [h.present], h.future[0], h.future[1..])
  }

  lemma DoPreservesInv(h: History, a: D.Action)
    requires D.Inv(h.present)
    ensures  D.Inv(Do(h, a).present)
  {
  }

  ghost predicate HistInv(h: History) {
    (forall i | 0 <= i < |h.past| :: D.Inv(h.past[i])) &&
    D.Inv(h.present) &&
    (forall j | 0 <= j < |h.future| :: D.Inv(h.future[j]))
  }

  lemma InitHistorySatisfiesInv()
    ensures HistInv(InitHistory())
  {
  }

  lemma UndoPreservesHistInv(h: History)
    requires HistInv(h)
    ensures  HistInv(Undo(h))
  {
  }

  lemma RedoPreservesHistInv(h: History)
    requires HistInv(h)
    ensures  HistInv(Redo(h))
  {
  }

  lemma DoPreservesHistInv(h: History, a: D.Action)
    requires HistInv(h)
    ensures  HistInv(Do(h, a))
  {
  }

  lemma PreviewPreservesHistInv(h: History, a: D.Action)
    requires HistInv(h)
    ensures  HistInv(Preview(h, a))
  {
  }

  lemma CommitFromPreservesHistInv(h: History, baseline: D.Model)
    requires HistInv(h)
    requires D.Inv(baseline)
    ensures  HistInv(CommitFrom(h, baseline))
  {
  }

  // proxy for linear undo: after a new action, there is no redo branch
  lemma DoHasNoRedoBranch(h: History, a: D.Action)
  requires HistInv(h)
  ensures Redo(Do(h, a)) == Do(h, a)
  {
  }
  // round-tripping properties
  lemma UndoRedoRoundTrip(h: History)
  requires |h.past| > 0
  ensures Redo(Undo(h)) == h
  {
  }
  lemma RedoUndoRoundTrip(h: History)
  requires |h.future| > 0
  ensures Undo(Redo(h)) == h
  {
  }
  // idempotence at boundaries
  lemma UndoAtBeginningIsNoOp(h: History)
  requires |h.past| == 0
  ensures Undo(h) == h
  {
  }
  lemma RedoAtEndIsNoOp(h: History)
  requires |h.future| == 0
  ensures Redo(h) == h
  {
  }
}

// === End ../kernels/Replay.dfy ===

// Goal: prove preservation of
// - A1 (exact partition, no duplicates)
// - B (WIP limits)
// for a dynamic-column Kanban reducer under undo/redo replay.

module KanbanDomain refines Domain {
  // user facing
  type ColId = string
  // allocated by model
  type CardId = nat

  datatype Card = Card(title: string)

  datatype Model = Model(
    cols: seq<ColId>,                 // authoritative list of columns
    lanes: map<ColId, seq<CardId>>,   // column -> ordered card ids
    wip: map<ColId, nat>,             // column -> limit (nat); use a large number for "unlimited"
    cards: map<CardId, Card>,         // id -> payload
    nextId: nat                       // fresh allocator
  )

  datatype Action =
    | AddColumn(col: ColId, limit: nat)
    | SetWip(col: ColId, limit: nat)
    | AddCard(col: ColId, title: string)          // allocates nextId if succeeds
    | MoveCard(id: CardId, toCol: ColId, pos: int)

  // --------------------------
  // Helpers (sequence reasoning)
  // --------------------------

  function get<K,V>(s: map<K, V>, c: K, default: V): V
  {
    if c in s then s[c] else default
  }

  function Lane(lanes: map<ColId, seq<CardId>>, c: ColId): seq<CardId>
  {
    get(lanes, c, [])
  }

  function Wip(wip: map<ColId, nat>, c: ColId): nat
  {
    get(wip, c, 0)
  }

  ghost predicate NoDupSeq<T>(s: seq<T>)
  {
    forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j]
  }

  function ClampPos(pos: int, n: int): nat
    requires n >= 0
  {
    if pos <= 0 then 0
    else if pos >= n then n as nat
    else pos as nat
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

  function FlatColsPosition(cols: seq<ColId>, lanes: map<ColId, seq<CardId>>, c: nat, i: nat): nat
    requires c < |cols|
    requires i < |Lane(lanes, cols[c])|
  {
    if c == 0 then i
    else |Lane(lanes, cols[0])| + FlatColsPosition(cols[1..], lanes, c-1, i)
  }

  // Flatten lanes in the order of cols
  function AllIds(m: Model): seq<CardId>
  {
    match m
    case Model(cols, lanes, wip, cards, nextId) =>
      FlattenCols(cols, lanes)
  }

  function FlattenCols(cols: seq<ColId>, lanes: map<ColId, seq<CardId>>): seq<CardId>
  {
    if |cols| == 0 then []
    else Lane(lanes, cols[0]) + FlattenCols(cols[1..], lanes)
  }

  // Does a card id occur in some lane?
  predicate OccursInLanes(m: Model, id: CardId)
  {
    exists i :: 0 <= i < |m.cols| && (exists j :: 0 <= j < |Lane(m.lanes, m.cols[i])| && Lane(m.lanes, m.cols[i])[j] == id)
  }

  // --------------------------
  // Invariant (A1 + B + column well-formedness)
  // --------------------------
  ghost predicate Inv(m: Model)
  {
    // Column list well-formed
    NoDupSeq(m.cols) &&

    // Lanes/wip defined exactly on existing columns
    (forall i :: 0 <= i < |m.cols| ==> m.cols[i] in m.lanes && m.cols[i] in m.wip) &&
    (forall c :: c in m.lanes ==> c in m.cols) &&
    (forall c :: c in m.wip ==> c in m.cols) &&

    // A1: exact partition (no disappear / no duplicate)
    NoDupSeq(AllIds(m)) &&
    (forall id :: id in m.cards <==> OccursInLanes(m, id)) &&

    // B: WIP limits
    (forall i :: 0 <= i < |m.cols| ==> |m.lanes[m.cols[i]]| <= m.wip[m.cols[i]]) &&

    // Allocator is fresh
    (forall id :: id in m.cards ==> id < m.nextId)
  }

  // --------------------------
  // Init
  // --------------------------
  function Init(): Model {
    Model([], map[], map[], map[], 0)
  }

  // --------------------------
  // Normalize
  // --------------------------
  // For now, Normalize is the identity.
  // That keeps semantics simple and makes "no-op on violation" exact.
  //
  // If you later want Normalize to "repair" (e.g., drop unknown columns,
  // clamp positions, etc.), this is the hook point.
  function Normalize(m: Model): Model { m }

  // --------------------------
  // Apply
  // --------------------------
  function Apply(m: Model, a: Action): Model
  {
    match m
    case Model(cols, lanes, wip, cards, nextId) =>
      match a
      case AddColumn(col, limit) =>
        if col in cols then m
        else
          // add an empty lane and a wip entry
          Model(cols + [col],
                lanes[col := []],
                wip[col := limit],
                cards,
                nextId)

      case SetWip(col, limit) =>
        if !(col in cols) then m
        else if limit < |Lane(lanes, col)| then m
        else Model(cols, lanes, wip[col := limit], cards, nextId)

      case AddCard(col, title) =>
        if !(col in cols) then m
        else if |Lane(lanes, col)| + 1 > (Wip(wip, col)) then m
        else
          var id := nextId;
          Model(cols,
                lanes[col := Lane(lanes, col) + [id]],
                wip,
                cards[id := Card(title)],
                nextId + 1)

      case MoveCard(id, toCol, pos) =>
        if !(toCol in cols) then m
        else if !(id in cards) then m
        else
          // Find the source column by scanning cols
          var src := FindColumnOf(cols, lanes, id);
          if src == "" then m // should be impossible under Inv; safe fallback
          else if src == toCol then
            // reorder within same column (still checks WIP trivially)
            var s := Lane(lanes, src);
            var s1 := RemoveFirst(s, id);
            var k := ClampPos(pos, |s1|);
            Model(cols, lanes[src := InsertAt(s1, k, id)], wip, cards, nextId)
          else
            // cross-column move: check WIP of destination
            if |Lane(lanes, toCol)| + 1 > (Wip(wip, toCol)) then m
            else
              var s := Lane(lanes, src);
              var t := Lane(lanes, toCol);
              var s1 := RemoveFirst(s, id);
              var k := ClampPos(pos, |t|);
              var t1 := InsertAt(t, k, id);
              Model(cols, lanes[src := s1][toCol := t1], wip, cards, nextId)
  }

  // Helper: find which column contains id; returns "" if not found.
  function FindColumnOf(cols: seq<ColId>, lanes: map<ColId, seq<CardId>>, id: CardId): ColId
  {
    if |cols| == 0 then ""
    else if SeqContains(Lane(lanes, cols[0]), id) then cols[0]
    else FindColumnOf(cols[1..], lanes, id)
  }

  function SeqContains<T(==)>(s: seq<T>, x: T): bool
  {
    exists i :: 0 <= i < |s| && s[i] == x
  }

  // --------------------------
  // The required lemmas for dafny-replay
  // --------------------------

  lemma InitSatisfiesInv()
    ensures Inv(Init())
  {
  }

  //
  // This is the only thing the replay kernel needs from the domain:
  // Step preserves Inv (possibly after Normalize, but Normalize is identity here).
  //
  // Proof strategy:
  // - case split on action
  // - every branch is either "no-op" (model unchanged) or a local update
  // - show:
  //   * column keys preserved
  //   * cards moved/added without duplication
  //   * WIP checked before insertion
  //
  lemma StepPreservesInv(m: Model, a: Action)
  {
  }

  // --------------------------
  // Helper lemmas
  // --------------------------

   // RemoveFirst lemmas
  // When NoDupSeq, removing x gives us everything except x
  lemma RemoveFirstNoDupContains<T>(s: seq<T>, x: T, y: T)
    requires NoDupSeq(s)
    ensures SeqContains(RemoveFirst(s, x), y) <==> (SeqContains(s, y) && y != x)
  {
  }

  lemma RemoveFirstPreservesNoDup<T>(s: seq<T>, x: T)
    requires NoDupSeq(s)
    ensures NoDupSeq(RemoveFirst(s, x))
  {
  }

  lemma RemoveFirstIndex<T>(s: seq<T>, x: T, i: nat, j: nat)
    requires NoDupSeq(s)
    requires i < j < |RemoveFirst(s, x)|
    ensures RemoveFirst(s, x)[i] != RemoveFirst(s, x)[j]
  {
  }

  lemma RemoveFirstInOriginal<T>(s: seq<T>, x: T, y: T)
    requires NoDupSeq(s)
    requires SeqContains(RemoveFirst(s, x), y)
    ensures SeqContains(s, y)
  {
  }

  lemma RemoveFirstLength<T>(s: seq<T>, x: T)
    ensures SeqContains(s, x) ==> |RemoveFirst(s, x)| == |s| - 1
    ensures !SeqContains(s, x) ==> RemoveFirst(s, x) == s
  {
  }

  // InsertAt lemmas
  lemma InsertAtContains<T>(s: seq<T>, i: nat, x: T, y: T)
    requires i <= |s|
    ensures SeqContains(InsertAt(s, i, x), y) <==> SeqContains(s, y) || y == x
  {
  }

  lemma InsertAtPreservesNoDup<T>(s: seq<T>, i: nat, x: T)
    requires i <= |s|
    requires NoDupSeq(s)
    requires !SeqContains(s, x)
    ensures NoDupSeq(InsertAt(s, i, x))
  {
  }

  lemma InsertAtLength<T>(s: seq<T>, i: nat, x: T)
    requires i <= |s|
    ensures |InsertAt(s, i, x)| == |s| + 1
  {
  }

  // Key lemma for same-column reorder: removing and reinserting same element preserves NoDup
  lemma RemoveInsertPreservesNoDup<T>(s: seq<T>, x: T, k: nat)
    requires NoDupSeq(s)
    requires SeqContains(s, x)
    requires k <= |RemoveFirst(s, x)|
    ensures NoDupSeq(InsertAt(RemoveFirst(s, x), k, x))
  {
  }

  // Contents after remove-insert is the same
  lemma RemoveInsertContents<T>(s: seq<T>, x: T, k: nat, y: T)
    requires NoDupSeq(s)
    requires SeqContains(s, x)
    requires k <= |RemoveFirst(s, x)|
    ensures SeqContains(InsertAt(RemoveFirst(s, x), k, x), y) <==> SeqContains(s, y)
  {
  }

  // FlattenCols when one lane changes by remove-insert (same column reorder)
  lemma FlattenColsSameColReorder(cols: seq<ColId>, lanes: map<ColId, seq<CardId>>, col: ColId, id: CardId, k: nat)
    requires NoDupSeq(cols)
    requires col in cols
    requires col in lanes
    requires SeqContains(Lane(lanes, col), id)
    requires k <= |RemoveFirst(Lane(lanes, col), id)|
    requires NoDupSeq(FlattenCols(cols, lanes))
    ensures NoDupSeq(FlattenCols(cols, lanes[col := InsertAt(RemoveFirst(Lane(lanes, col), id), k, id)]))
    ensures forall y :: SeqContains(FlattenCols(cols, lanes[col := InsertAt(RemoveFirst(Lane(lanes, col), id), k, id)]), y)
                   <==> SeqContains(FlattenCols(cols, lanes), y)
  {
  }

  lemma LaneNoDupFromFlattened(cols: seq<ColId>, lanes: map<ColId, seq<CardId>>, col: ColId)
    requires col in cols
    requires NoDupSeq(FlattenCols(cols, lanes))
    ensures NoDupSeq(Lane(lanes, col))
  {
  }

  lemma FlattenColsUpdateOneLane(cols: seq<ColId>, lanes: map<ColId, seq<CardId>>, lanes': map<ColId, seq<CardId>>, col: ColId)
    requires NoDupSeq(cols)
    requires col in cols
    requires forall c :: c in cols && c != col ==> Lane(lanes', c) == Lane(lanes, c)
    requires forall y :: SeqContains(Lane(lanes', col), y) <==> SeqContains(Lane(lanes, col), y)
    requires NoDupSeq(FlattenCols(cols, lanes))
    requires NoDupSeq(Lane(lanes', col))
    ensures NoDupSeq(FlattenCols(cols, lanes'))
    ensures forall y :: SeqContains(FlattenCols(cols, lanes'), y) <==> SeqContains(FlattenCols(cols, lanes), y)
  {
  }

  lemma ConcatNoDupDisjoint<T>(a: seq<T>, b: seq<T>)
    requires NoDupSeq(a)
    requires NoDupSeq(b)
    requires forall x :: SeqContains(a, x) ==> !SeqContains(b, x)
    ensures NoDupSeq(a + b)
  {
  }

  // FlattenCols for cross-column move: remove from src, insert into dest
  lemma FlattenColsCrossColMove(cols: seq<ColId>, lanes: map<ColId, seq<CardId>>, src: ColId, toCol: ColId, id: CardId, k: nat)
    requires NoDupSeq(cols)
    requires src in cols && toCol in cols
    requires src != toCol
    requires src in lanes && toCol in lanes
    requires SeqContains(Lane(lanes, src), id)
    requires k <= |Lane(lanes, toCol)|
    requires NoDupSeq(FlattenCols(cols, lanes))
    ensures NoDupSeq(FlattenCols(cols, lanes[src := RemoveFirst(Lane(lanes, src), id)][toCol := InsertAt(Lane(lanes, toCol), k, id)]))
    ensures forall y :: SeqContains(FlattenCols(cols, lanes[src := RemoveFirst(Lane(lanes, src), id)][toCol := InsertAt(Lane(lanes, toCol), k, id)]), y)
                   <==> SeqContains(FlattenCols(cols, lanes), y)
  {
  }

  lemma FlatColsUnique(cols: seq<ColId>, lanes: map<ColId, seq<CardId>>, col1: ColId, col2: ColId, id: CardId)
    requires NoDupSeq(cols)
    requires col1 in cols && col2 in cols
    requires col1 != col2
    requires NoDupSeq(FlattenCols(cols, lanes))
    requires SeqContains(Lane(lanes, col1), id)
    ensures !SeqContains(Lane(lanes, col2), id)
  {
  }

  lemma FlatColsPositions(cols: seq<ColId>, lanes: map<ColId, seq<CardId>>, c1: nat, i1: nat, c2: nat, i2: nat)
    requires c1 < |cols| && c2 < |cols| && c1 != c2
    requires i1 < |Lane(lanes, cols[c1])| && i2 < |Lane(lanes, cols[c2])|
    requires Lane(lanes, cols[c1])[i1] == Lane(lanes, cols[c2])[i2]
    requires NoDupSeq(FlattenCols(cols, lanes))
    ensures false
  {
  }

  lemma FlatColsPositionValid(cols: seq<ColId>, lanes: map<ColId, seq<CardId>>, c: nat, i: nat)
    requires c < |cols|
    requires i < |Lane(lanes, cols[c])|
    ensures FlatColsPosition(cols, lanes, c, i) < |FlattenCols(cols, lanes)|
    ensures FlattenCols(cols, lanes)[FlatColsPosition(cols, lanes, c, i)] == Lane(lanes, cols[c])[i]
  {
  }

  lemma FlatColsPositionOrder(cols: seq<ColId>, lanes: map<ColId, seq<CardId>>, c1: nat, i1: nat, c2: nat, i2: nat)
    requires c1 < c2 < |cols|
    requires i1 < |Lane(lanes, cols[c1])|
    requires i2 < |Lane(lanes, cols[c2])|
    ensures FlatColsPosition(cols, lanes, c1, i1) < FlatColsPosition(cols, lanes, c2, i2)
  {
  }

  lemma FlatColsPositionNonNeg(cols: seq<ColId>, lanes: map<ColId, seq<CardId>>, c: nat, i: nat)
    requires c < |cols|
    requires i < |Lane(lanes, cols[c])|
    ensures FlatColsPosition(cols, lanes, c, i) >= 0
  {
  }

  lemma FlattenColsTwoLaneUpdate(cols: seq<ColId>, lanes: map<ColId, seq<CardId>>, lanes': map<ColId, seq<CardId>>, src: ColId, toCol: ColId, id: CardId)
    requires NoDupSeq(cols)
    requires src in cols && toCol in cols
    requires src != toCol
    requires src in lanes && toCol in lanes
    requires NoDupSeq(FlattenCols(cols, lanes))
    requires SeqContains(Lane(lanes, src), id)
    requires !SeqContains(Lane(lanes, toCol), id)
    requires NoDupSeq(Lane(lanes, src))
    requires NoDupSeq(Lane(lanes, toCol))
    requires NoDupSeq(Lane(lanes', src))
    requires NoDupSeq(Lane(lanes', toCol))
    requires forall c :: c in cols && c != src && c != toCol ==> Lane(lanes', c) == Lane(lanes, c)
    requires forall y :: SeqContains(Lane(lanes', src), y) <==> SeqContains(Lane(lanes, src), y) && y != id
    requires forall y :: SeqContains(Lane(lanes', toCol), y) <==> SeqContains(Lane(lanes, toCol), y) || y == id
    ensures NoDupSeq(FlattenCols(cols, lanes'))
    ensures forall y :: SeqContains(FlattenCols(cols, lanes'), y) <==> SeqContains(FlattenCols(cols, lanes), y)
  {
  }

  // Helper for FindColumnOf
  lemma FindColumnOfFound(cols: seq<ColId>, lanes: map<ColId, seq<CardId>>, id: CardId)
    requires exists i :: 0 <= i < |cols| && SeqContains(Lane(lanes, cols[i]), id)
    ensures FindColumnOf(cols, lanes, id) in cols
    ensures SeqContains(Lane(lanes, FindColumnOf(cols, lanes, id)), id)
  {
  }

  lemma FindColumnOfInv(m: Model, id: CardId)
    requires Inv(m)
    requires id in m.cards
    ensures FindColumnOf(m.cols, m.lanes, id) in m.cols
    ensures SeqContains(Lane(m.lanes, FindColumnOf(m.cols, m.lanes, id)), id)
  {
  }

  lemma OccursInLanesEquivSeqContains(m: Model, id: CardId)
    ensures OccursInLanes(m, id) <==> (exists i :: 0 <= i < |m.cols| && SeqContains(Lane(m.lanes, m.cols[i]), id))
  {
  }

  lemma OccursInLanesEquivSeqContainsLanes(cols: seq<ColId>, lanes: map<ColId, seq<CardId>>, id: CardId)
    ensures (exists i :: 0 <= i < |cols| && SeqContains(Lane(lanes, cols[i]), id)) <==> SeqContains(FlattenCols(cols, lanes), id)
  {
  }

  // Single lane update: add id to one lane
  lemma FlattenColsSingleLaneAdd(cols: seq<ColId>, lanes: map<ColId, seq<CardId>>, lanes': map<ColId, seq<CardId>>, toCol: ColId, id: CardId)
    requires NoDupSeq(cols)
    requires toCol in cols
    requires NoDupSeq(FlattenCols(cols, lanes))
    requires !SeqContains(FlattenCols(cols, lanes), id)  // id not currently in any lane
    requires NoDupSeq(Lane(lanes', toCol))
    requires forall c :: c in cols && c != toCol ==> Lane(lanes', c) == Lane(lanes, c)
    requires forall y :: SeqContains(Lane(lanes', toCol), y) <==> SeqContains(Lane(lanes, toCol), y) || y == id
    ensures NoDupSeq(FlattenCols(cols, lanes'))
    ensures forall y :: SeqContains(FlattenCols(cols, lanes'), y) <==> SeqContains(FlattenCols(cols, lanes), y) || y == id
  {
  }

  // Single lane update: remove id from one lane
  lemma FlattenColsSingleLaneRemove(cols: seq<ColId>, lanes: map<ColId, seq<CardId>>, lanes': map<ColId, seq<CardId>>, src: ColId, id: CardId)
    requires NoDupSeq(cols)
    requires src in cols
    requires NoDupSeq(FlattenCols(cols, lanes))
    requires SeqContains(Lane(lanes, src), id)  // id is in the source lane
    requires NoDupSeq(Lane(lanes', src))
    requires forall c :: c in cols && c != src ==> Lane(lanes', c) == Lane(lanes, c)
    requires forall y :: SeqContains(Lane(lanes', src), y) <==> SeqContains(Lane(lanes, src), y) && y != id
    ensures NoDupSeq(FlattenCols(cols, lanes'))
    ensures forall y :: SeqContains(FlattenCols(cols, lanes'), y) <==> SeqContains(FlattenCols(cols, lanes), y) && y != id
  {
  }

  lemma FlatColsUniqueInLane(cols: seq<ColId>, lanes: map<ColId, seq<CardId>>, col: ColId, id: CardId)
    requires NoDupSeq(cols)
    requires col in cols
    requires NoDupSeq(FlattenCols(cols, lanes))
    requires SeqContains(Lane(lanes, col), id)
    ensures forall c :: c in cols && c != col ==> !SeqContains(Lane(lanes, c), id)
  {
  }

  lemma FlattenColsTwoLaneUpdateHelper(cols: seq<ColId>, lanes: map<ColId, seq<CardId>>, lanes': map<ColId, seq<CardId>>, src: ColId, toCol: ColId, id: CardId)
    requires NoDupSeq(cols)
    requires src in cols && toCol in cols
    requires src != toCol
    requires NoDupSeq(FlattenCols(cols, lanes))
    requires SeqContains(Lane(lanes, src), id)
    requires !SeqContains(Lane(lanes, toCol), id)
    requires NoDupSeq(Lane(lanes', src))
    requires NoDupSeq(Lane(lanes', toCol))
    requires forall c :: c in cols && c != src && c != toCol ==> Lane(lanes', c) == Lane(lanes, c)
    requires forall y :: SeqContains(Lane(lanes', src), y) <==> SeqContains(Lane(lanes, src), y) && y != id
    requires forall y :: SeqContains(Lane(lanes', toCol), y) <==> SeqContains(Lane(lanes, toCol), y) || y == id
    ensures NoDupSeq(FlattenCols(cols, lanes'))
    ensures forall y :: SeqContains(FlattenCols(cols, lanes'), y) <==> SeqContains(FlattenCols(cols, lanes), y)
    decreases |cols|
  {
  }

  // Helper lemma: if id is in a sequence, it's contained
  lemma SeqContainsWitness<T>(s: seq<T>, x: T, idx: nat)
    requires idx < |s|
    requires s[idx] == x
    ensures SeqContains(s, x)
  {
  }

  // Helper: OccursInLanes with a witness
  lemma OccursInLanesWitness(m: Model, id: CardId, colIdx: nat, posIdx: nat)
    requires colIdx < |m.cols|
    requires posIdx < |Lane(m.lanes, m.cols[colIdx])|
    requires Lane(m.lanes, m.cols[colIdx])[posIdx] == id
    ensures OccursInLanes(m, id)
  {
  }

  // AllIds contains exactly what's in the lanes
  lemma AllIdsContains(cols: seq<ColId>, lanes: map<ColId, seq<CardId>>, id: CardId)
    ensures SeqContains(FlattenCols(cols, lanes), id) <==>
            exists i :: 0 <= i < |cols| && SeqContains(Lane(lanes, cols[i]), id)
  {
  }

  lemma SeqContainsMeansInSeq<T>(s: seq<T>, x: T)
    requires SeqContains(s, x)
    ensures exists k :: 0 <= k < |s| && s[k] == x
  {
  }

  lemma ConcatContains<T>(a: seq<T>, b: seq<T>, x: T)
    ensures SeqContains(a + b, x) <==> SeqContains(a, x) || SeqContains(b, x)
  {
  }

  // If head of NoDupSeq equals x, then x is not in tail
  lemma NoDupSeqNotInTail<T>(s: seq<T>, x: T)
    requires |s| > 0
    requires NoDupSeq(s)
    requires s[0] == x
    ensures forall c :: c in s[1..] ==> c != x
  {
  }

  // NoDupSeq preserved when appending a fresh element
  lemma NoDupSeqAppend<T>(s: seq<T>, x: T)
    requires NoDupSeq(s)
    requires !SeqContains(s, x)
    ensures NoDupSeq(s + [x])
  {
  }

  // Helper for updating a single lane
  lemma FlattenColsUpdateLane(cols: seq<ColId>, lanes: map<ColId, seq<CardId>>, col: ColId, newLane: seq<CardId>)
    requires col in lanes
    requires col in cols
    ensures forall c :: c in cols && c != col ==> Lane(lanes[col := newLane], c) == Lane(lanes, c)
  {
  }

  lemma FlattenColsAppendToLane(cols: seq<ColId>, lanes: map<ColId, seq<CardId>>, col: ColId, x: CardId)
    requires col in lanes
    requires col in cols
    requires NoDupSeq(cols)
    requires NoDupSeq(FlattenCols(cols, lanes))
    requires !SeqContains(FlattenCols(cols, lanes), x)
    ensures NoDupSeq(FlattenCols(cols, lanes[col := Lane(lanes, col) + [x]]))
  {
  }

  lemma FlattenColsAppendToLaneHelper(cols: seq<ColId>, lanes: map<ColId, seq<CardId>>, col: ColId, x: CardId)
    requires col in lanes
    requires col in cols
    requires NoDupSeq(cols)
    requires NoDupSeq(FlattenCols(cols, lanes))
    requires !SeqContains(FlattenCols(cols, lanes), x)
    ensures NoDupSeq(FlattenCols(cols, lanes[col := Lane(lanes, col) + [x]]))
  {
  }

  lemma ConcatDisjoint<T>(a: seq<T>, b: seq<T>)
    requires NoDupSeq(a + b)
    ensures forall x :: SeqContains(a, x) ==> !SeqContains(b, x)
  {
  }

  lemma ConcatNoDupFreshSubset<T>(a: seq<T>, b: seq<T>, b': seq<T>, x: T)
    requires NoDupSeq(a + b)
    requires NoDupSeq(b')
    requires !SeqContains(a, x)
    requires forall y :: SeqContains(b', y) <==> SeqContains(b, y) || y == x
    ensures NoDupSeq(a + b')
  {
  }

  lemma FlattenColsUnchanged(cols: seq<ColId>, lanes: map<ColId, seq<CardId>>, lanes': map<ColId, seq<CardId>>, col: ColId)
    requires forall c :: c in cols ==> c != col
    requires forall c :: c in cols ==> Lane(lanes', c) == Lane(lanes, c)
    ensures FlattenCols(cols, lanes') == FlattenCols(cols, lanes)
  {
  }

  lemma ConcatNoDup<T>(a: seq<T>, b: seq<T>)
    requires NoDupSeq(a + b)
    ensures NoDupSeq(a) && NoDupSeq(b)
  {
  }

  lemma NoDupSeqInsert<T>(a: seq<T>, b: seq<T>, x: T)
    requires NoDupSeq(a + b)
    requires !SeqContains(a, x)
    requires !SeqContains(b, x)
    ensures NoDupSeq((a + [x]) + b)
  {
  }

  lemma FlattenColsAppendContent(cols: seq<ColId>, lanes: map<ColId, seq<CardId>>, col: ColId, x: CardId)
    requires col in cols
    requires col in lanes
    ensures forall y :: SeqContains(FlattenCols(cols, lanes[col := Lane(lanes, col) + [x]]), y) <==>
                        SeqContains(FlattenCols(cols, lanes), y) || y == x
  {
  }

  lemma ColInColsWitness(cols: seq<ColId>, col: ColId)
    requires col in cols
    ensures exists i :: 0 <= i < |cols| && cols[i] == col
  {
  }

  lemma ConcatNoDupWithFreshAppend<T>(a: seq<T>, b: seq<T>, x: T)
    requires NoDupSeq(a + b)
    requires !SeqContains(a, x)
    requires !SeqContains(b, x)
    ensures NoDupSeq(a + (b + [x]))
  {
  }

  // NoDupSeq when appending an element not in the sequence
  lemma NoDupSeqAppendFresh<T>(s: seq<T>, x: T)
    requires NoDupSeq(s)
    requires !(x in s)
    ensures NoDupSeq(s + [x])
  {
  }

  // FlattenCols with appended empty lane
  lemma FlattenColsAppendEmpty(cols: seq<ColId>, lanes: map<ColId, seq<CardId>>, col: ColId)
    requires col in lanes
    requires Lane(lanes, col) == []
    ensures FlattenCols(cols + [col], lanes) == FlattenCols(cols, lanes)
  {
  }

  // FlattenCols is the same when lanes agree on all columns
  lemma FlattenColsSameLanes(cols: seq<ColId>, lanes1: map<ColId, seq<CardId>>, lanes2: map<ColId, seq<CardId>>)
    requires forall c :: c in cols ==> Lane(lanes1, c) == Lane(lanes2, c)
    ensures FlattenCols(cols, lanes1) == FlattenCols(cols, lanes2)
  {
  }

  // freshId not in AllIds when >= nextId and Inv holds
  lemma FreshIdNotInAllIds(m: Model, freshId: CardId)
    requires Inv(m)
    requires freshId >= m.nextId
    ensures !SeqContains(AllIds(m), freshId)
  {
  }
}

module KanbanKernel refines Kernel {
  import D = KanbanDomain
}

module KanbanAppCore {
  import K = KanbanKernel
  import D = KanbanDomain

  function Init(): K.History {
    K.InitHistory()
  }

  // Action constructors
  function AddColumn(col: string, limit: nat): D.Action { D.AddColumn(col, limit) }
  function SetWip(col: string, limit: nat): D.Action { D.SetWip(col, limit) }
  function AddCard(col: string, title: string): D.Action { D.AddCard(col, title) }
  function MoveCard(id: nat, toCol: string, pos: int): D.Action { D.MoveCard(id, toCol, pos) }

  // State transitions
  function Dispatch(h: K.History, a: D.Action): K.History requires K.HistInv(h) { K.Do(h, a) }
  function Undo(h: K.History): K.History { K.Undo(h) }
  function Redo(h: K.History): K.History { K.Redo(h) }

  // Selectors
  function Present(h: K.History): D.Model { h.present }
  function CanUndo(h: K.History): bool { |h.past| > 0 }
  function CanRedo(h: K.History): bool { |h.future| > 0 }

  // Model accessors for JavaScript
  function GetCols(m: D.Model): seq<string> { m.cols }
  function GetLane(m: D.Model, col: string): seq<nat> { D.Lane(m.lanes, col) }
  function GetWip(m: D.Model, col: string): nat { D.Wip(m.wip, col) }
  function GetCardTitle(m: D.Model, id: nat): string {
    if id in m.cards then m.cards[id].title else ""
  }
}
