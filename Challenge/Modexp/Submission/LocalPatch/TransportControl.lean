import Challenge.Modexp.Submission.LocalPatch.TransportDomain

set_option warningAsError true
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.LocalPatch.Transport
open EvmSemantics EvmSemantics.EVM

/-- Jumps use the compiled all-target layout theorem. RETURN is transported
with the actual dynamic memory charge and no PC increment. -/
theorem control_running {code : ByteArray} {credit counter : Nat} {s t : State}
    (hwindow : LocalDecode.checkAt s.executionEnv.code code s.pc.toNat = true)
    (hlayout : JumpDestLayout.check s.executionEnv.code code = true)
    (hallowed : Has control s) (hnormal : NoException t)
    (hstep : StepRunning s t) :
    StepRunning (liftState code credit counter s) (liftState code credit counter t) := by
  cases hstep
  case jump dest rest h_op h_gas h_stack h_valid h_cap =>
    have hv : Decode.isValidJumpDest (liftState code credit counter s).executionEnv.code
        dest.toNat = true := JumpDestLayout.valid_of_check hlayout h_valid
    have h := StepRunning.jump (liftState code credit counter s) dest rest
      ((decodedOp_lift (credit := credit) (counter := counter) hwindow).trans h_op)
      (afford_credit credit h_gas) h_stack hv h_cap
    simpa only [liftState, State.fork, subtract_credit credit h_gas] using h
  case jumpi_taken dest cond rest h_op h_gas h_stack h_cond h_valid h_cap =>
    have hv : Decode.isValidJumpDest (liftState code credit counter s).executionEnv.code
        dest.toNat = true := JumpDestLayout.valid_of_check hlayout h_valid
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

end Challenge.Modexp.Submission.LocalPatch.Transport
