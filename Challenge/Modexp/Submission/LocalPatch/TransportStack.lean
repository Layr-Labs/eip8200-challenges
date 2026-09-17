import Challenge.Modexp.Submission.LocalPatch.TransportDomain

set_option warningAsError true
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.LocalPatch.Transport
open EvmSemantics EvmSemantics.EVM

/-- Transport actual successful stackOps rules. All other constructors are
eliminated by their decoded opcode or their exceptional output, not assumed
away by a whole-step-equivalence premise. -/
theorem stack_running {code : ByteArray} {credit counter : Nat} {s t : State}
    (hwindow : LocalDecode.checkAt s.executionEnv.code code s.pc.toNat = true)
    (hallowed : Has stackOps s) (hnormal : NoException t)
    (hstep : StepRunning s t) :
    StepRunning (liftState code credit counter s) (liftState code credit counter t) := by
  cases hstep
  case pop a rest h_op h_gas h_stack h_cap =>
    have h := StepRunning.pop (liftState code credit counter s) a rest
      ((decodedOp_lift (credit := credit) (counter := counter) hwindow).trans h_op) (afford_credit credit h_gas) h_stack h_cap
    simpa only [liftState, State.fork, subtract_credit credit h_gas] using h
  case push0 h_op h_gas h_cap =>
    have h := StepRunning.push0 (liftState code credit counter s) 
      ((decodedOp_lift (credit := credit) (counter := counter) hwindow).trans h_op) (afford_credit credit h_gas) h_cap
    simpa only [liftState, State.fork, subtract_credit credit h_gas] using h
  case pushN k data immWidth h_k_pos h_op h_gas h_cap =>
    have h := StepRunning.pushN (liftState code credit counter s) k data immWidth h_k_pos
      ((decoded_lift (credit := credit) (counter := counter) hwindow).trans h_op)
      (afford_credit credit h_gas) h_cap
    simpa only [liftState, State.fork, subtract_credit credit h_gas] using h
  case dup n v h_op h_gas h_get h_cap =>
    have h := StepRunning.dup (liftState code credit counter s) n v
      ((decodedOp_lift (credit := credit) (counter := counter) hwindow).trans h_op) (afford_credit credit h_gas) h_get h_cap
    simpa only [liftState, State.fork, subtract_credit credit h_gas] using h
  case swap n stk' h_op h_gas h_swap h_cap =>
    have h := StepRunning.swap (liftState code credit counter s) n stk'
      ((decodedOp_lift (credit := credit) (counter := counter) hwindow).trans h_op) (afford_credit credit h_gas) h_swap h_cap
    simpa only [liftState, State.fork, subtract_credit credit h_gas] using h
  case dupN n v h_op h_gas h_get h_cap =>
    have h := StepRunning.dupN (liftState code credit counter s) n v
      ((decodedOp_lift (credit := credit) (counter := counter) hwindow).trans h_op) (afford_credit credit h_gas) h_get h_cap
    simpa only [liftState, State.fork, subtract_credit credit h_gas] using h
  case swapN n stk' h_op h_gas h_swap h_cap =>
    have h := StepRunning.swapN (liftState code credit counter s) n stk'
      ((decodedOp_lift (credit := credit) (counter := counter) hwindow).trans h_op) (afford_credit credit h_gas) h_swap h_cap
    simpa only [liftState, State.fork, subtract_credit credit h_gas] using h
  case exchange b stk' h_op h_gas h_swap h_cap =>
    have h := StepRunning.exchange (liftState code credit counter s) b stk'
      ((decodedOp_lift (credit := credit) (counter := counter) hwindow).trans h_op) (afford_credit credit h_gas) h_swap h_cap
    simpa only [liftState, State.fork, subtract_credit credit h_gas] using h
  all_goals
    simp_all [Has, stackOps, NoException, State.decodedOp]

end Challenge.Modexp.Submission.LocalPatch.Transport
