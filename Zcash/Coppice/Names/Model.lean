namespace Zcash.Coppice.Names

abbrev Height := Nat
abbrev Name := Nat
abbrev Ua := Nat
abbrev Nullifier := Nat

structure Parameters where
  leaseBlocks : Nat
  cooldownBlocks : Nat
  deriving DecidableEq, Repr

inductive RetentionPolicy where
  | retainClaimable
  | compactClaimable
  deriving DecidableEq, Repr

inductive Lifecycle where
  | missing
  | active
  | cooldown
  | claimable
  deriving DecidableEq, Repr

structure StateRef where
  height : Height
  txIndex : Nat
  actionIndex : Nat
  deriving DecidableEq, Repr

structure Head where
  name : Name
  ua : Ua
  producer : StateRef
  futureNullifier : Nullifier
  producerEpoch : Nat
  expiryHeight : Height
  terminalHeight : Option Height
  deriving DecidableEq, Repr

structure State where
  head : Option Head
  deriving DecidableEq, Repr

def Head.terminalAt (head : Head) : Height :=
  head.terminalHeight.getD head.expiryHeight

/-!
The current undeployed v2 semantics use `retainClaimable`. The
`compactClaimable` parameter is the refinement seam for PR-04: it changes only
the representation at the claimable boundary, not the active or cooldown
predicates.
-/

def lifecycle (parameters : Parameters) (policy : RetentionPolicy)
    (height : Height) (head : Option Head) : Lifecycle :=
  match head with
  | none => .missing
  | some current =>
      let terminal := current.terminalAt
      if height < terminal then
        .active
      else if height < terminal + parameters.cooldownBlocks then
        .cooldown
      else
        match policy with
        | .retainClaimable => .claimable
        | .compactClaimable => .missing

def resolvedUa (parameters : Parameters) (policy : RetentionPolicy)
    (height : Height) (state : State) : Option Ua :=
  match lifecycle parameters policy height state.head, state.head with
  | .active, some head => some head.ua
  | _, _ => none

/-!
Authenticated host facts and proof verdicts are explicit Boolean inputs. This
keeps the reducer model independent from both the Rust implementation and the
cryptographic implementation while making its assumptions visible.
-/

structure Reveal where
  name : Name
  producer : StateRef
  inclusionEpoch : Nat
  ua : Ua
  successorFutureNullifier : Nullifier
  inWindow : Bool
  commitExists : Bool
  commitMature : Bool
  commitUnexpired : Bool
  actionExists : Bool
  proofValid : Bool
  deriving DecidableEq, Repr

structure Refresh where
  name : Name
  predecessor : StateRef
  producer : StateRef
  inclusionEpoch : Nat
  ua : Ua
  successorFutureNullifier : Nullifier
  inWindow : Bool
  actionExists : Bool
  actionSpendsPredecessor : Bool
  proofValid : Bool
  deriving DecidableEq, Repr

inductive Operation where
  | inert
  | reveal (candidate : Reveal)
  | refresh (candidate : Refresh)
  deriving DecidableEq, Repr

structure Transaction where
  actionNullifiers : List Nullifier
  operation : Operation
  deriving DecidableEq, Repr

structure Event where
  height : Height
  transaction : Transaction
  deriving DecidableEq, Repr

def revealEligible (parameters : Parameters) (target : Name) (height : Height)
    (state : State) (candidate : Reveal) : Bool :=
  candidate.name == target &&
  candidate.inWindow &&
  candidate.commitExists &&
  candidate.commitMature &&
  candidate.commitUnexpired &&
  candidate.actionExists &&
  candidate.proofValid &&
  match lifecycle parameters .retainClaimable height state.head with
  | .missing | .claimable => true
  | .active | .cooldown => false

def refreshEligible (parameters : Parameters) (target : Name) (height : Height)
    (state : State) (transaction : Transaction) (candidate : Refresh) : Bool :=
  candidate.name == target &&
  candidate.inWindow &&
  candidate.actionExists &&
  candidate.actionSpendsPredecessor &&
  candidate.proofValid &&
  match state.head with
  | none => false
  | some current =>
      lifecycle parameters .retainClaimable height state.head == .active &&
      candidate.predecessor == current.producer &&
      decide (current.producerEpoch < candidate.inclusionEpoch) &&
      transaction.actionNullifiers.contains current.futureNullifier

def revealHead (parameters : Parameters) (height : Height) (candidate : Reveal) : Head :=
  {
    name := candidate.name
    ua := candidate.ua
    producer := candidate.producer
    futureNullifier := candidate.successorFutureNullifier
    producerEpoch := candidate.inclusionEpoch
    expiryHeight := height + parameters.leaseBlocks
    terminalHeight := none
  }

def refreshHead (parameters : Parameters) (height : Height) (candidate : Refresh) : Head :=
  {
    name := candidate.name
    ua := candidate.ua
    producer := candidate.producer
    futureNullifier := candidate.successorFutureNullifier
    producerEpoch := candidate.inclusionEpoch
    expiryHeight := height + parameters.leaseBlocks
    terminalHeight := none
  }

def applyOperation (parameters : Parameters) (target : Name) (height : Height)
    (state : State) (transaction : Transaction) : State :=
  match transaction.operation with
  | .inert => state
  | .reveal candidate =>
      if revealEligible parameters target height state candidate then
        { head := some (revealHead parameters height candidate) }
      else
        state
  | .refresh candidate =>
      if refreshEligible parameters target height state transaction candidate then
        { head := some (refreshHead parameters height candidate) }
      else
        state

def spendsHead (actionNullifiers : List Nullifier) (head : Head) : Bool :=
  actionNullifiers.contains head.futureNullifier

def terminateIfStillCurrent (height : Height) (old : Option Head)
    (afterOperation : State) (spent : Bool) : State :=
  match old, afterOperation.head with
  | some previous, some current =>
      if spent && current.producer == previous.producer then
        { head := some { current with terminalHeight := some height } }
      else
        afterOperation
  | _, _ => afterOperation

def applyTransaction (parameters : Parameters) (target : Name) (height : Height)
    (state : State) (transaction : Transaction) : State :=
  let spent := state.head.any (spendsHead transaction.actionNullifiers)
  let afterOperation := applyOperation parameters target height state transaction
  terminateIfStillCurrent height state.head afterOperation spent

inductive Step (parameters : Parameters) (target : Name) (height : Height) :
    State → Transaction → State → Prop where
  | canonical (state : State) (transaction : Transaction) :
      Step parameters target height state transaction
        (applyTransaction parameters target height state transaction)

def Operation.name? : Operation → Option Name
  | .inert => none
  | .reveal candidate => some candidate.name
  | .refresh candidate => some candidate.name

def filterExact (target : Name) (transaction : Transaction) : Transaction :=
  match transaction.operation.name? with
  | some name =>
      if name == target then transaction else { transaction with operation := .inert }
  | none => transaction

def replay (parameters : Parameters) (target : Name) (initial : State)
    (events : List Event) : State :=
  events.foldl
    (fun state event =>
      applyTransaction parameters target event.height state event.transaction)
    initial

def replayExact (parameters : Parameters) (target : Name) (initial : State)
    (events : List Event) : State :=
  replay parameters target initial
    (events.map fun event =>
      { event with transaction := filterExact target event.transaction })

structure Candidate where
  producer : StateRef
  valid : Bool
  deriving DecidableEq, Repr

def firstCanonicalValid : List Candidate → Option StateRef
  | [] => none
  | candidate :: rest =>
      if candidate.valid then some candidate.producer else firstCanonicalValid rest

structure Applied where
  state : State
  undo : State
  deriving DecidableEq, Repr

def applyWithUndo (parameters : Parameters) (target : Name) (event : Event)
    (state : State) : Applied :=
  {
    state := applyTransaction parameters target event.height state event.transaction
    undo := state
  }

def rollback (applied : Applied) : State := applied.undo

end Zcash.Coppice.Names
