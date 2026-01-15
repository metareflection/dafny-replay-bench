// ClearSplitMultiCollaboration: Verified expense splitting with multi-user collaboration
//
// This wraps the ClearSplit domain with MultiCollaboration support.
// Since AddExpense and AddSettlement are append-only operations,
// reconciliation is trivially simple: no conflicts can occur.

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
// === Inlined from ClearSplit.dfy ===
// Expense splitting with verified conservation of money

// =============================
// Abstract Specification Module
// =============================
// This module defines the user-facing API and guarantees.
// All types, predicates, functions, and key lemma signatures are here.

abstract module ClearSplitSpec {

  // -----------------------------
  // Money + identifiers
  // -----------------------------
  type Money = int  // cents

  // For MVP, keep IDs as strings.
  type PersonId = string

  // -----------------------------
  // Core data types
  // -----------------------------
  datatype Expense = Expense(
    paidBy: PersonId,
    amount: Money,
    // Each entry is how much that person "consumed" from this expense.
    // Convention: shares are >= 0 and sum(shares) = amount.
    shares: map<PersonId, Money>,
    // Keys for iterating over shares (for compiled code)
    shareKeys: seq<PersonId>
  )

  datatype Settlement = Settlement(
    from: PersonId,
    to: PersonId,
    amount: Money
  )

  datatype Model = Model(
    members: set<PersonId>,
    memberList: seq<PersonId>,  // For compiled iteration, must match members
    expenses: seq<Expense>,
    settlements: seq<Settlement>
  )

  datatype Result<T, E> = Ok(value: T) | Error(error: E)

  datatype Err =
    | NotMember(p: PersonId)
    | BadExpense
    | BadSettlement

  datatype Action =
    | AddExpense(e: Expense)
    | AddSettlement(s: Settlement)

  datatype Certificate = Certificate(
    memberCount: nat,
    expenseCount: nat,
    settlementCount: nat,
    conservationHolds: bool  // Always true when Inv holds
  )

  // -----------------------------
  // Core predicates
  // -----------------------------

  // Sequence has no duplicates
  predicate NoDuplicates(s: seq<PersonId>)
  {
    forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j]
  }

  // Ghost spec: non-deterministic sum over map values
  ghost function SumValues(m: map<PersonId, Money>): Money
    decreases |m|
    ensures |m| > 0 ==> exists k :: k in m && SumValues(m) == m[k] + SumValues(m - {k})

  // Compilable version: iterate over a sequence of keys
  function SumValuesSeq(m: map<PersonId, Money>, keys: seq<PersonId>): Money
    decreases |keys|
  {
    if |keys| == 0 then 0
    else
      var k := keys[0];
      var rest := keys[1..];
      if k in m then m[k] + SumValuesSeq(m - {k}, rest)
      else SumValuesSeq(m, rest)
  }

  // Sequence bijectively matches set
  ghost predicate SeqMatchesSet(s: seq<PersonId>, set_: set<PersonId>)
  {
    |s| == |set_|
    && NoDuplicates(s)
    && (forall p :: p in s <==> p in set_)
  }

  // shareKeys bijectively matches shares.Keys (ghost spec)
  ghost predicate ShareKeysConsistent(e: Expense)
  {
    |e.shareKeys| == |e.shares|
    && NoDuplicates(e.shareKeys)
    && (forall k :: k in e.shareKeys <==> k in e.shares.Keys)
  }

  // Compilable check: all shareKeys are in shares and sizes match
  predicate ShareKeysOk(e: Expense)
  {
    |e.shareKeys| == |e.shares|
    && NoDuplicates(e.shareKeys)
    && (forall i :: 0 <= i < |e.shareKeys| ==> e.shareKeys[i] in e.shares)
  }

  // Helper: check that all keys in sequence are members with non-negative shares
  predicate AllSharesValid(members: set<PersonId>, shares: map<PersonId, Money>, keys: seq<PersonId>)
  {
    forall i :: 0 <= i < |keys| ==> keys[i] in members && keys[i] in shares && shares[keys[i]] >= 0
  }

  // Compilable version: check expense validity using shareKeys
  predicate ValidExpenseCheck(members: set<PersonId>, e: Expense)
  {
    ShareKeysOk(e)
    && e.amount >= 0
    && e.paidBy in members
    && AllSharesValid(members, e.shares, e.shareKeys)
    && SumValuesSeq(e.shares, e.shareKeys) == e.amount
  }

  predicate ValidSettlement(members: set<PersonId>, s: Settlement)
  {
    s.amount >= 0
    && s.from in members
    && s.to in members
    && s.from != s.to
  }

  // Ghost spec for valid expense (semantic validity)
  ghost predicate ValidExpense(members: set<PersonId>, e: Expense)
  {
    e.amount >= 0
    && e.paidBy in members
    && (forall p :: p in e.shares ==> p in members)
    && (forall p :: p in e.shares ==> e.shares[p] >= 0)
    && SumValues(e.shares) == e.amount
  }

  // Well-formed expense: semantic + structural (shareKeys consistent)
  ghost predicate WellFormedExpense(members: set<PersonId>, e: Expense)
  {
    ShareKeysConsistent(e) && ValidExpense(members, e)
  }

  // -----------------------------
  // THE Rep Invariant
  // -----------------------------
  ghost predicate Inv(model: Model)
  {
    // 1. MemberList consistency: memberList bijectively matches members
    SeqMatchesSet(model.memberList, model.members)
    // 2. All expenses are well-formed
    && (forall i :: 0 <= i < |model.expenses| ==> WellFormedExpense(model.members, model.expenses[i]))
    // 3. All settlements are valid
    && (forall i :: 0 <= i < |model.settlements| ==> ValidSettlement(model.members, model.settlements[i]))
  }

  // -----------------------------
  // Balance computation
  // -----------------------------

  function AddToMap(b: map<PersonId, Money>, p: PersonId, delta: Money): map<PersonId, Money>
  {
    if p in b then b[p := b[p] + delta] else b[p := delta]
  }

  // Compilable version: iterate over a sequence
  function ZeroBalancesSeq(memberList: seq<PersonId>): map<PersonId, Money>
    decreases |memberList|
    ensures forall p :: p in memberList ==> p in ZeroBalancesSeq(memberList)
    ensures forall p :: p in ZeroBalancesSeq(memberList) ==> ZeroBalancesSeq(memberList)[p] == 0
  {
    if |memberList| == 0 then map[]
    else
      var p := memberList[0];
      ZeroBalancesSeq(memberList[1..])[p := 0]
  }

  // Helper: apply shares to balances using a sequence of keys
  function ApplySharesSeq(
      b: map<PersonId, Money>,
      shares: map<PersonId, Money>,
      keys: seq<PersonId>
    ): map<PersonId, Money>
    decreases |keys|
  {
    if |keys| == 0 then b
    else
      var p := keys[0];
      var rest := keys[1..];
      if p in shares then
        ApplySharesSeq(AddToMap(b, p, -shares[p]), shares, rest)
      else
        ApplySharesSeq(b, shares, rest)
  }

  function ApplyExpenseToBalances(
      b: map<PersonId, Money>,
      e: Expense
    ): map<PersonId, Money>
  {
    var b' := AddToMap(b, e.paidBy, e.amount);
    ApplySharesSeq(b', e.shares, e.shareKeys)
  }

  function ApplySettlementToBalances(
      b: map<PersonId, Money>,
      s: Settlement
    ): map<PersonId, Money>
  {
    var b' := AddToMap(b, s.from, s.amount);
    AddToMap(b', s.to, -s.amount)
  }

  // Fold over expenses
  function ApplyExpensesSeq(
      b: map<PersonId, Money>,
      expenses: seq<Expense>
    ): map<PersonId, Money>
    decreases |expenses|
  {
    if |expenses| == 0 then b
    else
      var b' := ApplyExpenseToBalances(b, expenses[0]);
      ApplyExpensesSeq(b', expenses[1..])
  }

  // Fold over settlements
  function ApplySettlementsSeq(
      b: map<PersonId, Money>,
      settlements: seq<Settlement>
    ): map<PersonId, Money>
    decreases |settlements|
  {
    if |settlements| == 0 then b
    else
      var b' := ApplySettlementToBalances(b, settlements[0]);
      ApplySettlementsSeq(b', settlements[1..])
  }

  // Balances: the main projection function (compilable)
  function Balances(model: Model): map<PersonId, Money>
  {
    var b := ZeroBalancesSeq(model.memberList);
    var b' := ApplyExpensesSeq(b, model.expenses);
    ApplySettlementsSeq(b', model.settlements)
  }

  // Get balance for a specific person
  function GetBalance(model: Model, p: PersonId): Money
  {
    var b := Balances(model);
    if p in b then b[p] else 0
  }

  // -----------------------------
  // History explanation functions
  // -----------------------------

  function SumSeq(s: seq<Money>): Money
    decreases |s|
  {
    if |s| == 0 then 0
    else s[0] + SumSeq(s[1..])
  }

  function ExpenseDeltaForPerson(e: Expense, p: PersonId): Money
  {
    var payerDelta := if p == e.paidBy then e.amount else 0;
    var shareDelta := if p in e.shares then -e.shares[p] else 0;
    payerDelta + shareDelta
  }

  function ExpenseDeltas(expenses: seq<Expense>, p: PersonId): seq<Money>
    decreases |expenses|
  {
    if |expenses| == 0 then []
    else [ExpenseDeltaForPerson(expenses[0], p)] + ExpenseDeltas(expenses[1..], p)
  }

  function SettlementDeltaForPerson(s: Settlement, p: PersonId): Money
  {
    var fromDelta := if p == s.from then s.amount else 0;
    var toDelta := if p == s.to then -s.amount else 0;
    fromDelta + toDelta
  }

  function SettlementDeltas(settlements: seq<Settlement>, p: PersonId): seq<Money>
    decreases |settlements|
  {
    if |settlements| == 0 then []
    else [SettlementDeltaForPerson(settlements[0], p)] + SettlementDeltas(settlements[1..], p)
  }

  function ExplainExpenses(model: Model, p: PersonId): seq<Money>
  {
    ExpenseDeltas(model.expenses, p) + SettlementDeltas(model.settlements, p)
  }

  // =============================
  // USER-FACING GUARANTEES
  // =============================

  // THE CONSERVATION THEOREM: Sum of all balances is always zero
  lemma Conservation(model: Model)
    requires Inv(model)
    ensures SumValues(Balances(model)) == 0

  // AddExpense delta law: how adding an expense affects balances
  lemma AddExpenseDelta(model: Model, e: Expense, model': Model)
    requires Inv(model)
    requires ValidExpenseCheck(model.members, e)
    requires model' == Model(model.members, model.memberList, model.expenses + [e], model.settlements)
    ensures Inv(model')
    // Payer gains amount (when not a share owner)
    ensures e.paidBy !in e.shares ==>
      GetBalance(model', e.paidBy) == GetBalance(model, e.paidBy) + e.amount
    // Share owners (not payer) lose their share
    ensures forall p :: p in e.shares && p != e.paidBy ==>
      GetBalance(model', p) == GetBalance(model, p) - e.shares[p]
    // Payer who is also a share owner: net change is amount - share
    ensures e.paidBy in e.shares ==>
      GetBalance(model', e.paidBy) == GetBalance(model, e.paidBy) + e.amount - e.shares[e.paidBy]
    // Others unchanged
    ensures forall p :: p !in e.shares && p != e.paidBy ==>
      GetBalance(model', p) == GetBalance(model, p)
    // Conservation preserved
    ensures SumValues(Balances(model')) == 0

  // AddSettlement delta law: how adding a settlement affects balances
  lemma AddSettlementDelta(model: Model, s: Settlement, model': Model)
    requires Inv(model)
    requires ValidSettlement(model.members, s)
    requires model' == Model(model.members, model.memberList, model.expenses, model.settlements + [s])
    ensures Inv(model')
    // From gains amount (owes less)
    ensures s.from != s.to ==> GetBalance(model', s.from) == GetBalance(model, s.from) + s.amount
    // To loses amount (is owed less)
    ensures s.from != s.to ==> GetBalance(model', s.to) == GetBalance(model, s.to) - s.amount
    // Others unchanged
    ensures forall p :: p != s.from && p != s.to ==>
      GetBalance(model', p) == GetBalance(model, p)
    // Conservation preserved
    ensures SumValues(Balances(model')) == 0

  // ExplainSumsToBalance: the sum of all deltas for a person equals their balance
  lemma ExplainSumsToBalance(model: Model, p: PersonId)
    requires Inv(model)
    requires p in model.members
    ensures SumSeq(ExplainExpenses(model, p)) == GetBalance(model, p)

  // -----------------------------
  // State transition methods
  // -----------------------------

  // Step: the only state mutator - total reducer (no ghost preconditions)
  method Step(model: Model, a: Action) returns (result: Result<Model, Err>)
    requires Inv(model)
    ensures result.Ok? ==> Inv(result.value)

  // Initialize a new model with the given members
  method Init(memberList: seq<PersonId>) returns (result: Result<Model, Err>)
    ensures result.Ok? ==> Inv(result.value)

  // Get a certificate for the current model
  method GetCertificate(model: Model) returns (cert: Certificate)
    requires Inv(model)
}


// =============================
// Implementation Module
// =============================
// This module provides proofs of all the guarantees.

module ClearSplit refines ClearSplitSpec {

  // -----------------------------
  // SumValues implementation
  // -----------------------------
  ghost function SumValues(m: map<PersonId, Money>): Money
  {
    if |m| == 0 then 0
    else
      var k :| k in m;
      m[k] + SumValues(m - {k})
  }

  // -----------------------------
  // Helper lemmas for SumValues
  // -----------------------------

  // Key lemma: SumValues(m) can be computed by removing any key p first
  )
  {
    if |m| == 1 {
      assert m.Keys == {p};
    } else {
      assert |m| > 0;
      var k :| k in m && SumValues(m) == m[k] + SumValues(m - {k});
      if k == p {
      } else {
        SumValuesAnyKey(m, p, k);
      }
    }
  }

  // Commutativity: any two decompositions give the same result
  lemma SumValuesAnyKey(m: map<PersonId, Money>, p: PersonId, q: PersonId)
    requires p in m
    requires q in m
    requires p != q
    decreases |m|, 0
    ensures m[p] + SumValues(m - {
    }) == m[q] + SumValues(m - {q})
  {
    var mp := m - {p};
    var mq := m - {q};
    var mpq := m - {p} - {q};

    assert q in mp;
    assert p in mq;
    assert mp - {q} == mpq;
    assert mq - {p} == mpq;

    SumValuesRemoveKey(mp, q);
    SumValuesRemoveKey(mq, p);
  }

  // SumValues of a map where all values are zero is zero
  // Helper: AddToMap changes sum by delta
  lemma {:vcs_split_on_every_assert} AddToMapSumChange(b: map<PersonId, Money>, p: PersonId, delta: Money)
    ensures SumValues(AddToMap(b, p, delta)) == SumValues(b) + delta
  {
    var b' := AddToMap(b, p, delta);
    if p in b {
      SumValuesRemoveKey(b, p);
      SumValuesRemoveKey(b', p);
      assert b' - {p} == b - {p};
    } else {
      SumValuesRemoveKey(b', p);
      assert b' - {p} == b;
    }
  }

  // -----------------------------
  // Sequence/set helpers
  // -----------------------------

  lemma SeqNoDuplicates(keys: seq<PersonId>, m: map<PersonId, Money>)
    requires forall k :: k in m.Keys <==> k in keys
    requires |keys| == |m|
    ensures forall i, j :: 0 <= i < j < |keys| ==> keys[i] != keys[j]
  {
  }

  lemma NoDupSeqToSetSize(s: seq<PersonId>)
    requires forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j]
    ensures |set i | 0 <= i < |s| :: s[i]| == |s|
    decreases |s|
  {
  }

  // Helper: equal-size subset of finite set is the whole set
  lemma SubsetEqualSize<T>(a: set<T>, b: set<T>)
    requires a <= b
    requires |a| == |b|
    ensures a == b
  {
  }

  // Equivalence: ShareKeysOk implies ShareKeysConsistent
  lemma ShareKeysOkImpliesConsistent(e: Expense)
    requires ShareKeysOk(e)
    ensures ShareKeysConsistent(e)
  {
  }

  // Equivalence lemma: ValidExpenseCheck implies WellFormedExpense
  lemma {:vcs_split_on_every_assert} ValidExpenseCheckImpliesWellFormed(members: set<PersonId>, e: Expense)
    requires ValidExpenseCheck(members, e)
    ensures WellFormedExpense(members, e)
  {
    ShareKeysOkImpliesConsistent(e);
    SumValuesSeqEquiv(e.shares, e.shareKeys);
    forall p | p in e.shares
      ensures p in members && e.shares[p] >= 0
    {
      assert p in e.shareKeys;
      var i :| 0 <= i < |e.shareKeys| && e.shareKeys[i] == p;
      assert e.shareKeys[i] in members;
    }
  }

  // -----------------------------
  // SumValuesSeq equivalence
  // -----------------------------

  lemma {:vcs_split_on_every_assert} SumValuesSeqEquiv(m: map<PersonId, Money>, keys: seq<PersonId>)
    requires forall k :: k in m.Keys <==> k in keys
    requires |keys| == |m|
    decreases |keys|
    ensures SumValuesSeq(m, keys) == SumValues(m)
  {
    if |keys| == 0 {
    } else {
      var k := keys[0];
      var rest := keys[1..];
      var m' := m - {k};

      SeqNoDuplicates(keys, m);
      SumValuesRemoveKey(m, k);
      RestCoversMapMinus(keys, m, k);
      SumValuesSeqEquiv(m', rest);
    }
  }

  lemma RestCoversMapMinus(keys: seq<PersonId>, m: map<PersonId, Money>, k: PersonId)
    requires |keys| > 0
    requires k == keys[0]
    requires k in m
    requires forall x :: x in m.Keys <==> x in keys
    requires |keys| == |m|
    ensures forall x :: x in (m - {
    }).Keys <==> x in keys[1..]
    ensures |keys[1..]| == |m - {k}|
  {
    var rest := keys[1..];
    var m' := m - {k};
    SeqNoDuplicates(keys, m);

    forall x | x in m'.Keys
      ensures x in rest
    {
      assert x in m.Keys && x != k;
      assert x in keys;
      var i :| 0 <= i < |keys| && keys[i] == x;
      assert i != 0;
    }

    forall x | x in rest
      ensures x in m'.Keys
    {
      var i :| 0 <= i < |rest| && rest[i] == x;
      assert keys[i+1] == x;
      assert x in keys;
      assert x in m.Keys;
      assert x != k;
    }
  }

  // -----------------------------
  // ZeroBalances equivalence
  // -----------------------------

  ghost function ZeroBalances(members: set<PersonId>): map<PersonId, Money>
    decreases |members|
    ensures forall p :: p in members ==> p in ZeroBalances(members)
    ensures forall p :: p in ZeroBalances(members) ==> p in members
    ensures forall p :: p in ZeroBalances(members) ==> ZeroBalances(members)[p] == 0
  {
    if |members| == 0 then map[]
    else
      var p :| p in members;
      ZeroBalances(members - {p})[p := 0]
  }

  // Ghost version for equivalence proofs
  ghost function BalancesGhost(model: Model): map<PersonId, Money>
    requires Inv(model)
  {
    var b := ZeroBalances(model.members);
    var b' := ApplyExpensesSeq(b, model.expenses);
    ApplySettlementsSeq(b', model.settlements)
  }

  // -----------------------------
  // Sum preservation helpers
  // -----------------------------

  , keys)
    decreases |keys|
  {
    if |keys| == 0 {
    } else {
      var k := keys[0];
      var rest := keys[1..];
      assert p !in rest;
      if k in m {
        if k in (m - {p}) {
          assert m[k] == (m - {p})[k];
          SumValuesSeqRemoveNonMember(m - {k}, p, rest);
          assert (m - {k}) - {p} == (m - {p}) - {k};
        } else {
          assert k == p;
          assert false;
        }
      } else {
        if k in (m - {p}) {
          assert false;
        } else {
          SumValuesSeqRemoveNonMember(m, p, rest);
        }
      }
    }
  }

  == AddToMap(b - {k}, p, delta)
  {}

  // -----------------------------
  // CONSERVATION THEOREM PROOF
  // -----------------------------
  // -----------------------------
  // Delta law helpers
  // -----------------------------

  function GetFromMap(b: map<PersonId, Money>, p: PersonId): Money
  {
    if p in b then b[p] else 0
  }

  // -----------------------------
  // DELTA LAW PROOFS
  // -----------------------------

  lemma AddExpenseDelta(model: Model, e: Expense, model': Model)
  {
  }

  lemma AddSettlementDelta(model: Model, s: Settlement, model': Model)
  {
  }

  // -----------------------------
  // EXPLAIN SUMS TO BALANCE PROOF
  // -----------------------------

  lemma ExplainSumsToBalance(model: Model, p: PersonId)
  {
  }

  // -----------------------------
  // METHOD IMPLEMENTATIONS
  // -----------------------------

  method Step(model: Model, a: Action) returns (result: Result<Model, Err>)
  {
    match a
    case AddExpense(e) =>
      if ValidExpenseCheck(model.members, e) {
        ValidExpenseCheckImpliesWellFormed(model.members, e);
        result := Ok(Model(model.members, model.memberList, model.expenses + [e], model.settlements));
      } else {
        result := Error(BadExpense);
      }

    case AddSettlement(s) =>
      if ValidSettlement(model.members, s) {
        result := Ok(Model(model.members, model.memberList, model.expenses, model.settlements + [s]));
      } else {
        result := Error(BadSettlement);
      }
  }

  method Init(memberList: seq<PersonId>) returns (result: Result<Model, Err>)
  {
    if !NoDuplicates(memberList) {
      result := Error(BadExpense);
      return;
    }
    var members := set i | 0 <= i < |memberList| :: memberList[i];
    NoDupSeqToSetSizeGeneral(memberList);
    result := Ok(Model(members, memberList, [], []));
  }

  method GetCertificate(model: Model) returns (cert: Certificate)
  {
    Conservation(model);
    cert := Certificate(
      |model.members|,
      |model.expenses|,
      |model.settlements|,
      true
    );
  }
}


// =============================
// AppCore: JS-facing API (delegation only)
// =============================
module ClearSplitAppCore {
  import C = ClearSplit

  // Type aliases
  type Model = C.Model
  type Action = C.Action
  type Money = C.Money
  type PersonId = C.PersonId
  type Certificate = C.Certificate

  // Initialize
  method Init(memberList: seq<PersonId>) returns (result: C.Result<Model, C.Err>)
    ensures result.Ok? ==> C.Inv(result.value)
  {
    result := C.Init(memberList);
  }

  // Action constructors
  function AddExpense(e: C.Expense): Action { C.AddExpense(e) }
  function AddSettlement(s: C.Settlement): Action { C.AddSettlement(s) }

  // Data constructors
  function MakeExpense(paidBy: PersonId, amount: Money, shares: map<PersonId, Money>, shareKeys: seq<PersonId>): C.Expense
  { C.Expense(paidBy, amount, shares, shareKeys) }

  function MakeSettlement(from: PersonId, to: PersonId, amount: Money): C.Settlement
  { C.Settlement(from, to, amount) }

  // Dispatch
  method Dispatch(model: Model, a: Action) returns (result: C.Result<Model, C.Err>)
    requires C.Inv(model)
    ensures result.Ok? ==> C.Inv(result.value)
  {
    result := C.Step(model, a);
  }

  // Projections
  function Balances(model: Model): map<PersonId, Money> { C.Balances(model) }
  function GetBalance(model: Model, p: PersonId): Money { C.GetBalance(model, p) }
  function Members(model: Model): seq<PersonId> { model.memberList }
  function Expenses(model: Model): seq<C.Expense> { model.expenses }
  function Settlements(model: Model): seq<C.Settlement> { model.settlements }

  // Certificate
  method GetCertificate(model: Model) returns (cert: Certificate)
    requires C.Inv(model)
  {
    cert := C.GetCertificate(model);
  }
}

// === End ClearSplit.dfy ===

module ClearSplitDomain refines Domain {
  import C = ClearSplit

  // The Model is just the ClearSplit Model
  // Note: We assume a pre-initialized model (members already set)
  type Model = C.Model

  // Actions are the ClearSplit actions
  datatype Action = AddExpense(e: C.Expense) | AddSettlement(s: C.Settlement)

  // Errors
  datatype Err = BadExpense | BadSettlement | Rejected

  function RejectErr(): Err { Rejected }

  // Invariant delegates to ClearSplit
  ghost predicate Inv(m: Model) {
    C.Inv(m)
  }

  // Initial model (empty with no members - real apps initialize with members)
  function Init(): Model {
    C.Model({}, [], [], [])
  }

  // Apply action
  function TryStep(m: Model, a: Action): Result<Model, Err> {
    match a
      case AddExpense(e) =>
        if C.ValidExpenseCheck(m.members, e) then
          Ok(C.Model(m.members, m.memberList, m.expenses + [e], m.settlements))
        else
          Err(BadExpense)
      case AddSettlement(s) =>
        if C.ValidSettlement(m.members, s) then
          Ok(C.Model(m.members, m.memberList, m.expenses, m.settlements + [s]))
        else
          Err(BadSettlement)
  }

  // Lemmas

  lemma StepPreservesInv(m: Model, a: Action, m2: Model)
  {
  }

  // --- Collaboration hooks ---

  // Rebase: Since expenses and settlements are append-only and don't reference
  // each other, there are no conflicts. Rebasing is just identity.
  function Rebase(remote: Action, local: Action): Action {
    local  // No transformation needed
  }

  // Explains: Since rebasing is identity, a candidate explains the original
  // if and only if they are equal.
  ghost predicate Explains(orig: Action, cand: Action) {
    orig == cand
  }

  // Candidates: Just the action itself. Append-only operations don't need
  // fallback candidates - they either succeed (members valid) or fail.
  function Candidates(m: Model, a: Action): seq<Action> {
    [a]
  }

  }

module ClearSplitMultiCollaboration refines MultiCollaboration {
  import D = ClearSplitDomain
}

// =============================================================================
// ClearSplitMultiAppCore: JS-friendly wrappers
// =============================================================================
module ClearSplitMultiAppCore {
  import C = ClearSplit
  import D = ClearSplitDomain
  import MC = ClearSplitMultiCollaboration

  // Re-export types
  type Model = D.Model
  type Action = D.Action
  type ClientState = MC.ClientState
  type ServerState = MC.ServerState
  type Reply = MC.Reply
  type Money = C.Money
  type PersonId = C.PersonId

  // --- Initialization ---

  // Create initial server state with given members
  function InitServerWithMembers(memberList: seq<PersonId>): ServerState
    requires C.NoDuplicates(memberList)
  {
    var members := set i | 0 <= i < |memberList| :: memberList[i];
    var model := C.Model(members, memberList, [], []);
    MC.ServerState(model, [], [])
  }

  // Initialize client from server
  function InitClientFromServer(server: ServerState): ClientState {
    MC.InitClientFromServer(server)
  }

  // Initialize client from version and model
  function InitClient(version: nat, model: Model): ClientState {
    MC.InitClient(version, model)
  }

  // --- Action constructors ---

  function MakeExpense(paidBy: PersonId, amount: Money, shares: map<PersonId, Money>, shareKeys: seq<PersonId>): C.Expense {
    C.Expense(paidBy, amount, shares, shareKeys)
  }

  function MakeSettlement(from: PersonId, to: PersonId, amount: Money): C.Settlement {
    C.Settlement(from, to, amount)
  }

  function AddExpense(e: C.Expense): Action {
    D.AddExpense(e)
  }

  function AddSettlement(s: C.Settlement): Action {
    D.AddSettlement(s)
  }

  // --- Client operations ---

  function ClientLocalDispatch(client: ClientState, action: Action): ClientState {
    MC.ClientLocalDispatch(client, action)
  }

  function HandleRealtimeUpdate(client: ClientState, serverVersion: nat, serverModel: Model): ClientState {
    MC.HandleRealtimeUpdate(client, serverVersion, serverModel)
  }

  function ClientAcceptReply(client: ClientState, newVersion: nat, newPresent: Model): ClientState {
    MC.ClientAcceptReply(client, newVersion, newPresent)
  }

  function ClientRejectReply(client: ClientState, freshVersion: nat, freshModel: Model): ClientState {
    MC.ClientRejectReply(client, freshVersion, freshModel)
  }

  // --- Server operations (for Edge Function) ---

  function ServerDispatch(server: ServerState, baseVersion: nat, action: Action): (ServerState, Reply)
    requires baseVersion <= MC.Version(server)
    requires D.Inv(server.present)
  {
    MC.Dispatch(server, baseVersion, action)
  }

  function ServerVersion(server: ServerState): nat {
    MC.Version(server)
  }

  // --- Accessors ---

  function ClientModel(client: ClientState): Model {
    MC.ClientModel(client)
  }

  function ClientVersion(client: ClientState): nat {
    MC.ClientVersion(client)
  }

  function PendingCount(client: ClientState): nat {
    MC.PendingCount(client)
  }

  function IsAccepted(reply: Reply): bool {
    reply.Accepted?
  }

  function IsRejected(reply: Reply): bool {
    reply.Rejected?
  }

  // --- Model accessors (delegate to ClearSplit) ---

  function Balances(model: Model): map<PersonId, Money> {
    C.Balances(model)
  }

  function GetBalance(model: Model, p: PersonId): Money {
    C.GetBalance(model, p)
  }

  function Members(model: Model): seq<PersonId> {
    model.memberList
  }

  function Expenses(model: Model): seq<C.Expense> {
    model.expenses
  }

  function Settlements(model: Model): seq<C.Settlement> {
    model.settlements
  }

  // Get first pending action (for dispatch)
  function GetFirstPending(client: ClientState): Action
    requires |client.pending| > 0
  {
    client.pending[0]
  }

  function HasPending(client: ClientState): bool {
    |client.pending| > 0
  }
}
