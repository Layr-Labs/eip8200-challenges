import Challenge.Modexp.Submission.LocalPatch.TransportStep

set_option warningAsError true
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.LocalPatch.Transport
open EvmSemantics EvmSemantics.EVM

/-- Target-predicate adapter for a macro whose internal PUSH boundary changes.
The existing ordinary opcode families are reused unchanged. This extension
reconstructs only the control family, accepting a proved all-target equality
rather than demanding the stronger equal-PUSH-shape Boolean. -/
theorem control_running_targets {code : ByteArray} {credit counter : Nat} {s t : State}
    (hwindow : LocalDecode.checkAt s.executionEnv.code code s.pc.toNat = true)
    (htargets : ∀ target, Decode.isValidJumpDest s.executionEnv.code target =
      Decode.isValidJumpDest code target)
    (hallowed : Has control s) (hnormal : NoException t)
    (hstep : StepRunning s t) :
    StepRunning (liftState code credit counter s) (liftState code credit counter t) := by
  cases hstep
  case jump dest rest h_op h_gas h_stack h_valid h_cap =>
    have hv : Decode.isValidJumpDest (liftState code credit counter s).executionEnv.code
        dest.toNat = true :=
      (htargets dest.toNat).symm.trans h_valid
    have h := StepRunning.jump (liftState code credit counter s) dest rest
      ((decodedOp_lift (credit := credit) (counter := counter) hwindow).trans h_op)
      (afford_credit credit h_gas) h_stack hv h_cap
    simpa only [liftState, State.fork, subtract_credit credit h_gas] using h
  case jumpi_taken dest cond rest h_op h_gas h_stack h_cond h_valid h_cap =>
    have hv : Decode.isValidJumpDest (liftState code credit counter s).executionEnv.code
        dest.toNat = true :=
      (htargets dest.toNat).symm.trans h_valid
    have h := StepRunning.jumpi_taken (liftState code credit counter s) dest cond rest
      ((decodedOp_lift (credit := credit) (counter := counter) hwindow).trans h_op)
      (afford_credit credit h_gas) h_stack h_cond hv h_cap
    simpa only [liftState, State.fork, subtract_credit credit h_gas] using h
  case jumpi_notTaken dest cond rest h_op h_gas h_stack h_cond h_cap =>
    have h := StepRunning.jumpi_notTaken (liftState code credit counter s) dest cond rest
      ((decodedOp_lift (credit := credit) (counter := counter) hwindow).trans h_op) (afford_credit credit h_gas) h_stack h_cond h_cap
    simpa only [liftState, State.fork, subtract_credit credit h_gas] using h
  case jumpdest h_op h_gas h_cap =>
    have h := StepRunning.jumpdest (liftState code credit counter s) 
      ((decodedOp_lift (credit := credit) (counter := counter) hwindow).trans h_op) (afford_credit credit h_gas) h_cap
    simpa only [liftState, State.fork, subtract_credit credit h_gas] using h
  case pc h_op h_gas h_cap =>
    have h := StepRunning.pc (liftState code credit counter s) 
      ((decodedOp_lift (credit := credit) (counter := counter) hwindow).trans h_op) (afford_credit credit h_gas) h_cap
    simpa only [liftState, State.fork, subtract_credit credit h_gas] using h
  case stop h_op h_cap =>
    have h := StepRunning.stop (liftState code credit counter s)
      ((decodedOp_lift (credit := credit) (counter := counter) hwindow).trans h_op) h_cap
    simpa only [liftState] using h
  case return_ offset size rest h_op h_stack h_gas h_cap =>
    have hc : Gas.returnTotal (liftState code credit counter s) offset size =
        Gas.returnTotal s offset size := rfl
    have h := StepRunning.return_ (liftState code credit counter s) offset size rest
      ((decodedOp_lift (credit := credit) (counter := counter) hwindow).trans h_op)
      h_stack (afford_credit credit h_gas) h_cap
    rw [hc] at h
    simpa only [liftState, State.activeWordsAfterUInt256,
      subtract_credit credit h_gas] using h
  all_goals
    simp_all [Has, control, NoException, State.decodedOp]


/-- The original family implementations are reused without modifications. -/
theorem ordinary_running_targets {code : ByteArray} {credit counter : Nat} {s t : State}
    (hwindow : LocalDecode.checkAt s.executionEnv.code code s.pc.toNat = true)
    (htargets : ∀ n, Decode.isValidJumpDest s.executionEnv.code n =
      Decode.isValidJumpDest code n)
    (hallowed : Has ordinary s) (hnormal : NoException t)
    (hstep : StepRunning s t) :
    StepRunning (liftState code credit counter s) (liftState code credit counter t) := by
  rcases ordinary_cases hallowed with h | h | h | h | h
  · exact arithmetic_running hwindow h hnormal hstep
  · exact bitwise_running hwindow h hnormal hstep
  · exact stack_running hwindow h hnormal hstep
  · exact memoryInput_running hwindow h hnormal hstep
  · exact control_running_targets hwindow htargets h hnormal hstep

/-- Same ordinary-step result, with an all-target certificate that permits
repacking a no-entry macro. No sensitive opcode or gas assumption is relaxed. -/
theorem ordinary_step_targets {code : ByteArray} {credit counter : Nat} {s t : State}
    (hwindow : LocalDecode.checkAt s.executionEnv.code code s.pc.toNat = true)
    (htargets : ∀ n, Decode.isValidJumpDest s.executionEnv.code n =
      Decode.isValidJumpDest code n)
    (hallowed : Has ordinary s) (hcall : s.callStack = [])
    (hnp : NonPrecompile s) (hstep : Step s t)
    (hsuffix : ∃ output : ByteArray, Eval t (.returned output)) :
    Step (liftState code credit counter s) (liftState code credit counter t) := by
  obtain ⟨hr, hs⟩ := running_of_step hcall hnp hstep
  have hc := (ordinary_context hs hallowed).2.2.2.1
  have hn := noException_of_successful (hc.trans hcall) hsuffix
  exact Step.running hr hnp
    (ordinary_running_targets hwindow htargets hallowed hn hs)

end Challenge.Modexp.Submission.LocalPatch.Transport

