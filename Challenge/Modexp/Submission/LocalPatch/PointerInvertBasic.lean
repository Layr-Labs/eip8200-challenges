import Challenge.Modexp.Submission.LocalPatch.PointerStates

set_option warningAsError true
set_option linter.unusedSimpArgs false

/-! Necessary affordability and post-state, inverted from actual source
transitions. These are not consequences inferred from sufficient GasSteps. -/
namespace Challenge.Modexp.Submission.LocalPatch.PointerSub32
open EvmSemantics EvmSemantics.EVM
open Transport

theorem invert_dup1 {s t : State}
    (hd : s.decodedOp = some (.Dup ⟨0, by decide⟩))
    (hn : NoException t) (hs : StepRunning s t) :
    ∃ p tail, s.stack = p :: tail ∧ 3 ≤ s.gasAvailable ∧
      tail.length + 1 < 1024 ∧
      t = { s with
          pc := s.pc.succ
          stack := p :: p :: tail
          gasAvailable := s.gasAvailable - 3 } := by
  cases hs
  case dup n v h_op h_gas h_get h_cap =>
    have hi : n = ⟨0, by decide⟩ := by simpa using h_op.symm.trans hd
    subst n
    cases hstk : s.stack with
    | nil => simp [hstk] at h_get
    | cons p tail =>
      have hv : v = p := by simpa [hstk] using h_get.symm
      subst v
      exact ⟨p, tail, rfl, by simpa [Gas.baseCost] using h_gas,
        by simpa [hstk] using h_cap, by simp [Gas.baseCost]⟩
  all_goals simp_all [NoException, State.decodedOp]

theorem invert_push31 {s t : State}
    (hd : s.decoded = some (.Push ⟨1, by decide⟩, some (UInt256.ofNat 31, 1)))
    (hn : NoException t) (hs : StepRunning s t) :
    3 ≤ s.gasAvailable ∧ s.stack.length < 1024 ∧
      t = { s with
          pc := s.pc + UInt256.ofNat 2
          stack := UInt256.ofNat 31 :: s.stack
          gasAvailable := s.gasAvailable - 3 } := by
  have hop : s.decodedOp = some (.Push ⟨1, by decide⟩) :=
    congrArg (fun d => d.map Prod.fst) hd
  cases hs
  case pushN k data width hk h_op h_gas h_cap =>
    have hp := Option.some.inj (h_op.symm.trans hd)
    have hi : k = ⟨1, by decide⟩ := by simpa using congrArg Prod.fst hp
    have ha : data = UInt256.ofNat 31 ∧ width = 1 := by
      simpa using congrArg Prod.snd hp
    rcases ha with ⟨rfl, rfl⟩
    subst k
    exact ⟨h_gas, h_cap, rfl⟩
  all_goals simp_all [NoException, State.decodedOp]

theorem invert_not {s t : State} (x : UInt256) (rest : List UInt256)
    (hstack : s.stack = x :: rest) (hd : s.decodedOp = some .NOT)
    (hn : NoException t) (hs : StepRunning s t) :
    3 ≤ s.gasAvailable ∧
      t = { s with
          pc := s.pc.succ
          stack := UInt256.lnot x :: rest
          gasAvailable := s.gasAvailable - 3 } := by
  cases hs
  case not a tail h_op h_gas h_stack h_cap =>
    have ha : a = x ∧ tail = rest := List.cons.inj (h_stack.symm.trans hstack)
    rcases ha with ⟨rfl, rfl⟩
    exact ⟨h_gas, rfl⟩
  all_goals simp_all [NoException, State.decodedOp]

theorem invert_add {s t : State} (x y : UInt256) (rest : List UInt256)
    (hstack : s.stack = x :: y :: rest) (hd : s.decodedOp = some .ADD)
    (hn : NoException t) (hs : StepRunning s t) :
    3 ≤ s.gasAvailable ∧
      t = { s with
          pc := s.pc.succ
          stack := (x + y) :: rest
          gasAvailable := s.gasAvailable - 3 } := by
  cases hs
  case add a b tail h_op h_gas h_stack h_cap =>
    have ha : a = x ∧ b = y ∧ tail = rest := by
      simpa only [List.cons.injEq] using h_stack.symm.trans hstack
    rcases ha with ⟨rfl, rfl, rfl⟩
    exact ⟨h_gas, rfl⟩
  all_goals simp_all [NoException, State.decodedOp]

theorem invert_swap1 {s t : State} (x y : UInt256) (rest : List UInt256)
    (hstack : s.stack = x :: y :: rest)
    (hd : s.decodedOp = some (.Swap ⟨0, by decide⟩))
    (hn : NoException t) (hs : StepRunning s t) :
    3 ≤ s.gasAvailable ∧
      t = { s with
          pc := s.pc.succ
          stack := y :: x :: rest
          gasAvailable := s.gasAvailable - 3 } := by
  cases hs
  case swap n stk h_op h_gas h_swap h_cap =>
    have hi : n = ⟨0, by decide⟩ := by simpa using h_op.symm.trans hd
    subst n
    have hst : stk = y :: x :: rest := by
      simpa [hstack, List.exchange] using h_swap.symm
    subst stk
    exact ⟨h_gas, rfl⟩
  all_goals simp_all [NoException, State.decodedOp]

end Challenge.Modexp.Submission.LocalPatch.PointerSub32
