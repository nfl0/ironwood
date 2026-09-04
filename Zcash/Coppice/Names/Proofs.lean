import Zcash.Coppice.Names.Model
import Std.Tactic

namespace Zcash.Coppice.Names

theorem step_deterministic {parameters : Parameters} {target : Name} {height : Height}
    {state : State} {transaction : Transaction} {left right : State}
    (hleft : Step parameters target height state transaction left)
    (hright : Step parameters target height state transaction right) : left = right := by
  cases hleft
  cases hright
  rfl

theorem first_canonical_valid_unique {candidates : List Candidate} {left right : StateRef}
    (hleft : firstCanonicalValid candidates = some left)
    (hright : firstCanonicalValid candidates = some right) : left = right := by
  rw [hleft] at hright
  exact Option.some.inj hright

theorem first_canonical_valid_accepts_head (producer : StateRef) (rest : List Candidate) :
    firstCanonicalValid ({ producer := producer, valid := true } :: rest) = some producer := by
  rfl

theorem first_canonical_valid_skips_rejected (producer : StateRef) (rest : List Candidate) :
    firstCanonicalValid ({ producer := producer, valid := false } :: rest) =
      firstCanonicalValid rest := by
  rfl

theorem lifecycle_terminal_boundary (parameters : Parameters) (head : Head) (terminal : Height)
    (hterminal : head.terminalHeight = some terminal)
    (hcooldown : 0 < parameters.cooldownBlocks) :
    lifecycle parameters terminal (some head) = .cooldown := by
  have hbefore : terminal < terminal + parameters.cooldownBlocks :=
    Nat.lt_add_of_pos_right hcooldown
  simp [lifecycle, Head.terminalAt, hterminal, hbefore]

theorem lifecycle_last_cooldown_block (parameters : Parameters) (head : Head) (terminal : Height)
    (hterminal : head.terminalHeight = some terminal)
    (hcooldown : 0 < parameters.cooldownBlocks) :
    lifecycle parameters
      (terminal + (parameters.cooldownBlocks - 1)) (some head) = .cooldown := by
  have hstart : terminal ≤ terminal + (parameters.cooldownBlocks - 1) :=
    Nat.le_add_right terminal _
  have hsub : parameters.cooldownBlocks - 1 < parameters.cooldownBlocks :=
    Nat.sub_lt_of_pos_le (by decide) hcooldown
  have hbefore : terminal + (parameters.cooldownBlocks - 1) <
      terminal + parameters.cooldownBlocks := Nat.add_lt_add_left hsub terminal
  simp [lifecycle, Head.terminalAt, hterminal, Nat.not_lt_of_ge hstart, hbefore]

theorem lifecycle_first_missing_block (parameters : Parameters) (head : Head)
    (terminal : Height) (hterminal : head.terminalHeight = some terminal) :
    lifecycle parameters
      (terminal + parameters.cooldownBlocks) (some head) = .missing := by
  simp [lifecycle, Head.terminalAt, hterminal]

theorem compact_at_first_missing_block (parameters : Parameters) (head : Head)
    (terminal : Height) (hterminal : head.terminalHeight = some terminal) :
    compactHead parameters (terminal + parameters.cooldownBlocks) (some head) = none := by
  simp [compactHead, claimable, Head.terminalAt, hterminal]

theorem compact_preserves_last_cooldown_block (parameters : Parameters) (head : Head)
    (terminal : Height) (hterminal : head.terminalHeight = some terminal)
    (hcooldown : 0 < parameters.cooldownBlocks) :
    compactHead parameters (terminal + (parameters.cooldownBlocks - 1)) (some head) =
      some head := by
  have hsub : parameters.cooldownBlocks - 1 < parameters.cooldownBlocks :=
    Nat.sub_lt_of_pos_le (by decide) hcooldown
  have hbefore : terminal + (parameters.cooldownBlocks - 1) <
      terminal + parameters.cooldownBlocks := Nat.add_lt_add_left hsub terminal
  simp [compactHead, claimable, Head.terminalAt, hterminal, Nat.not_le_of_gt hbefore]

theorem terminal_head_compaction_preserves_resolution (parameters : Parameters)
    (height : Height) (state : State) :
    resolvedUa parameters height (normalizeAtBlockStart parameters height state) =
      resolvedUa parameters height state := by
  cases state with
  | mk head =>
      cases head with
      | none => rfl
      | some current =>
          simp only [normalizeAtBlockStart, compactHead]
          by_cases hclaimable : claimable parameters height current
          · have hboundary : current.terminalAt + parameters.cooldownBlocks ≤ height := by
              simpa [claimable] using hclaimable
            have hterminal : current.terminalAt ≤ height :=
              Nat.le_trans (Nat.le_add_right current.terminalAt parameters.cooldownBlocks) hboundary
            simp [hclaimable, resolvedUa, lifecycle, Nat.not_lt_of_ge hterminal,
              Nat.not_lt_of_ge hboundary]
          · simp [hclaimable]

theorem stale_lineage_rejected (parameters : Parameters) (target : Name) (height : Height)
    (current : Head) (transaction : Transaction) (candidate : Refresh)
    (hstale : candidate.predecessor ≠ current.producer) :
    refreshEligible parameters target height { head := some current } transaction candidate = false := by
  simp [refreshEligible, hstale]

theorem same_epoch_refresh_rejected (parameters : Parameters) (target : Name) (height : Height)
    (current : Head) (transaction : Transaction) (candidate : Refresh)
    (hepoch : candidate.inclusionEpoch ≤ current.producerEpoch) :
    refreshEligible parameters target height { head := some current } transaction candidate = false := by
  simp [refreshEligible]
  omega

theorem spent_current_head_becomes_terminal (height : Height) (head : Head) :
    terminateIfStillCurrent height (some head) { head := some head } true =
      { head := some { head with terminalHeight := some height } } := by
  simp [terminateIfStillCurrent]

theorem rejected_bulletin_does_not_hide_spend (parameters : Parameters) (target : Name)
    (height : Height) (head : Head) (nullifiers : List Nullifier)
    (hspent : nullifiers.contains head.futureNullifier = true)
    (hretained : claimable parameters height head = false) :
    applyTransaction parameters target height { head := some head }
      { actionNullifiers := nullifiers, operation := .inert } =
      { head := some { head with terminalHeight := some height } } := by
  have hmember : head.futureNullifier ∈ nullifiers := by
    simpa using hspent
  simp [applyTransaction, normalizeAtBlockStart, compactHead, hretained,
    applyOperation, spendsHead, hmember, terminateIfStillCurrent]

theorem accepted_replacement_survives_old_spend (height : Height) (old replacement : Head)
    (hdifferent : replacement.producer ≠ old.producer) :
    terminateIfStillCurrent height (some old) { head := some replacement } true =
      { head := some replacement } := by
  simp [terminateIfStillCurrent, hdifferent]

theorem rollback_apply_equivalence (parameters : Parameters) (target : Name)
    (event : Event) (state : State) :
    rollback (applyWithUndo parameters target event state) = state := by
  rfl

theorem rollback_reapply_equivalence (parameters : Parameters) (target : Name)
    (event : Event) (state : State) :
    (applyWithUndo parameters target event
      (rollback (applyWithUndo parameters target event state))).state =
      (applyWithUndo parameters target event state).state := by
  rfl

theorem filter_exact_preserves_transaction (parameters : Parameters) (target : Name)
    (height : Height) (state : State) (transaction : Transaction) :
    applyTransaction parameters target height state (filterExact target transaction) =
      applyTransaction parameters target height state transaction := by
  cases transaction with
  | mk nullifiers operation =>
      cases operation with
      | inert => rfl
      | reveal candidate =>
          simp only [filterExact, Operation.name?]
          by_cases hname : candidate.name = target
          · simp [hname]
          · simp [hname, applyTransaction, applyOperation, revealEligible]
      | refresh candidate =>
          simp only [filterExact, Operation.name?]
          by_cases hname : candidate.name = target
          · simp [hname]
          · simp [hname, applyTransaction, applyOperation, refreshEligible]

theorem full_exact_replay_equivalence (parameters : Parameters) (target : Name)
    (initial : State) (events : List Event) :
    replayExact parameters target initial events = replay parameters target initial events := by
  induction events generalizing initial with
  | nil => rfl
  | cons event rest inductionHypothesis =>
      simp only [replayExact, replay, List.map_cons, List.foldl_cons]
      rw [filter_exact_preserves_transaction]
      exact inductionHypothesis _

end Zcash.Coppice.Names
