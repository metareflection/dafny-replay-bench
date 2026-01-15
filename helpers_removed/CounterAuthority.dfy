// === Inlined from ../kernels/Authority.dfy ===
// Abstract protocol + server kernel (compile false), parameterized by a Domain.

abstract module {:compile false} Domain {
  type Model
  type Action

  ghost predicate Inv(m: Model)

  function Init(): Model

  // A partial step: either returns an updated model, or an invalid-action message.
  datatype TryStepResult =
    | Ok(m': Model)
    | Invalid(msg: string)

  function TryStep(m: Model, a: Action): TryStepResult

  lemma InitSatisfiesInv()
    ensures Inv(Init())

  lemma TryStepOkPreservesInv(m: Model, a: Action)
    requires Inv(m)
    ensures  TryStep(m,a).Ok? ==> Inv(TryStep(m,a).m')
}

abstract module {:compile false} ServerKernel {
  import D : Domain

  // Protocol types (nested to share D)
  datatype FailureReason =
    | Stale
    | InvalidAction(msg: string)

  datatype Result =
    | Success(present: D.Model)
    | Failure(reason: FailureReason)

  // Always returns the authoritative version;
  // present is returned only on Success.
  datatype Response =
    Response(ver: nat, res: Result)

  datatype SyncResponse =
    SyncResponse(ver: nat, present: D.Model)

  // Server state (single shared doc)
  datatype S =
    S(ver: nat, present: D.Model)

  // Total snapshot endpoint
  function Sync(s: S): SyncResponse
    ensures Sync(s).ver == s.ver
    ensures Sync(s).present == s.present
  {
    SyncResponse(s.ver, s.present)
  }

  // Dispatch: protocol + domain partiality.
  // - stale version => Failure(Stale), state unchanged
  // - invalid action => Failure(InvalidAction(msg)), state unchanged
  // - ok => Success(newPresent), state updated, version incremented
  function Dispatch(s: S, clientVer: nat, a: D.Action): (S, Response)
  {
    if clientVer != s.ver then
      (s, Response(s.ver, Failure(Stale)))
    else
      match D.TryStep(s.present, a)
        case Ok(m') =>
          (S(s.ver + 1, m'), Response(s.ver + 1, Success(m')))
        case Invalid(msg) =>
          (s, Response(s.ver, Failure(InvalidAction(msg))))
  }

  // Server invariant lifted from Domain.Inv
  ghost predicate SInv(s: S) {
    D.Inv(s.present)
  }

  // Initialize server with domain's initial model
  function InitServer(): S {
    S(0, D.Init())
  }

  lemma InitServerSatisfiesSInv()
    ensures SInv(InitServer())
  {
  }

  // Main preservation lemma: Dispatch keeps server invariant.
  lemma DispatchPreservesSInv(s: S, clientVer: nat, a: D.Action)
    requires SInv(s)
    ensures  SInv(Dispatch(s, clientVer, a).0)
  {
  }
}

// === End ../kernels/Authority.dfy ===

module CounterDomain refines Domain {
  type Model = int
  datatype Action = Inc | Dec

  predicate Inv(m: Model) { m >= 0 }

  function Init(): Model { 0 }

  function TryStep(m: Model, a: Action): TryStepResult {
    match a
      case Inc => Ok(m + 1)
      case Dec =>
        if m == 0 then Invalid("cannot decrement at 0")
        else Ok(m - 1)
  }

  }

module CounterServer refines ServerKernel {
  import D = CounterDomain
}

// AppCore exposes server API for JavaScript
module AppCore {
  import S = CounterServer
  import D = CounterDomain

  // Server state type alias
  type ServerState = S.S

  // Initialize server with default (verified) initial state
  function Init(): S.S {
    S.InitServer()
  }

  // Initialize server with custom starting value (self-healing: clamps negative to 0)
  function InitServerWithValue(initial: int): S.S {
    S.S(0, if initial >= 0 then initial else 0)
  }

  // Action constructors
  function Inc(): D.Action { D.Inc }
  function Dec(): D.Action { D.Dec }

  // Sync endpoint - get current state
  function Sync(s: S.S): S.SyncResponse {
    S.Sync(s)
  }

  // Dispatch endpoint - process action from client
  function Dispatch(s: S.S, clientVer: nat, a: D.Action): (S.S, S.Response) {
    S.Dispatch(s, clientVer, a)
  }

  // Helper to extract version from server state
  function GetVersion(s: S.S): nat { s.ver }

  // Helper to extract present value from server state
  function GetPresent(s: S.S): int { s.present }

  // Response inspection helpers
  function IsSuccess(r: S.Response): bool { r.res.Success? }
  function IsStale(r: S.Response): bool { r.res.Failure? && r.res.reason.Stale? }
  function IsInvalid(r: S.Response): bool { r.res.Failure? && r.res.reason.InvalidAction? }
  function GetInvalidMsg(r: S.Response): string
    requires IsInvalid(r)
  { r.res.reason.msg }
  function GetResponseVersion(r: S.Response): nat { r.ver }
  function GetSuccessValue(r: S.Response): int
    requires IsSuccess(r)
  { r.res.present }
}
