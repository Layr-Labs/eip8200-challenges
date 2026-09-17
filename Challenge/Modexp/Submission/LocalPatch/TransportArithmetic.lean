import Challenge.Modexp.Submission.LocalPatch.TransportDomain

set_option warningAsError true
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.LocalPatch.Transport
open EvmSemantics EvmSemantics.EVM

/-- Transport actual successful arithmetic rules. All other constructors are
eliminated by their decoded opcode or their exceptional output, not assumed
away by a whole-step-equivalence premise. -/
theorem arithmetic_running {code : ByteArray} {credit counter : Nat} {s t : State}
    (hwindow : LocalDecode.checkAt s.executionEnv.code code s.pc.toNat = true)
    (hallowed : Has arithmetic s) (hnormal : NoException t)
    (hstep : StepRunning s t) :
    StepRunning (liftState code credit counter s) (liftState code credit counter t) := by
  cases hstep
  case add a b rest h_op h_gas h_stack h_cap =>
    have h := StepRunning.add (liftState code credit counter s) a b rest
      ((decodedOp_lift (credit := credit) (counter := counter) hwindow).trans h_op) (afford_credit credit h_gas) h_stack h_cap
    simpa only [liftState, State.fork, subtract_credit credit h_gas] using h
  case mul a b rest h_op h_gas h_stack h_cap =>
    have h := StepRunning.mul (liftState code credit counter s) a b rest
      ((decodedOp_lift (credit := credit) (counter := counter) hwindow).trans h_op) (afford_credit credit h_gas) h_stack h_cap
    simpa only [liftState, State.fork, subtract_credit credit h_gas] using h
  case sub a b rest h_op h_gas h_stack h_cap =>
    have h := StepRunning.sub (liftState code credit counter s) a b rest
      ((decodedOp_lift (credit := credit) (counter := counter) hwindow).trans h_op) (afford_credit credit h_gas) h_stack h_cap
    simpa only [liftState, State.fork, subtract_credit credit h_gas] using h
  case div a b rest h_op h_gas h_stack h_cap =>
    have h := StepRunning.div (liftState code credit counter s) a b rest
      ((decodedOp_lift (credit := credit) (counter := counter) hwindow).trans h_op) (afford_credit credit h_gas) h_stack h_cap
    simpa only [liftState, State.fork, subtract_credit credit h_gas] using h
  case sdiv a b rest h_op h_gas h_stack h_cap =>
    have h := StepRunning.sdiv (liftState code credit counter s) a b rest
      ((decodedOp_lift (credit := credit) (counter := counter) hwindow).trans h_op) (afford_credit credit h_gas) h_stack h_cap
    simpa only [liftState, State.fork, subtract_credit credit h_gas] using h
  case mod a b rest h_op h_gas h_stack h_cap =>
    have h := StepRunning.mod (liftState code credit counter s) a b rest
      ((decodedOp_lift (credit := credit) (counter := counter) hwindow).trans h_op) (afford_credit credit h_gas) h_stack h_cap
    simpa only [liftState, State.fork, subtract_credit credit h_gas] using h
  case smod a b rest h_op h_gas h_stack h_cap =>
    have h := StepRunning.smod (liftState code credit counter s) a b rest
      ((decodedOp_lift (credit := credit) (counter := counter) hwindow).trans h_op) (afford_credit credit h_gas) h_stack h_cap
    simpa only [liftState, State.fork, subtract_credit credit h_gas] using h
  case addmod a b n rest h_op h_gas h_stack h_cap =>
    have h := StepRunning.addmod (liftState code credit counter s) a b n rest
      ((decodedOp_lift (credit := credit) (counter := counter) hwindow).trans h_op) (afford_credit credit h_gas) h_stack h_cap
    simpa only [liftState, State.fork, subtract_credit credit h_gas] using h
  case mulmod a b n rest h_op h_gas h_stack h_cap =>
    have h := StepRunning.mulmod (liftState code credit counter s) a b n rest
      ((decodedOp_lift (credit := credit) (counter := counter) hwindow).trans h_op) (afford_credit credit h_gas) h_stack h_cap
    simpa only [liftState, State.fork, subtract_credit credit h_gas] using h
  case signextend b x rest h_op h_gas h_stack h_cap =>
    have h := StepRunning.signextend (liftState code credit counter s) b x rest
      ((decodedOp_lift (credit := credit) (counter := counter) hwindow).trans h_op) (afford_credit credit h_gas) h_stack h_cap
    simpa only [liftState, State.fork, subtract_credit credit h_gas] using h
  case exp a b rest h_op h_gas h_stack h_cap =>
    have hb : Gas.baseCost s.fork .EXP ≤ s.gasAvailable := by omega
    have hd : Gas.expByteCost s.fork b ≤ s.gasAvailable - Gas.baseCost s.fork .EXP := by omega
    have h := StepRunning.exp (liftState code credit counter s) a b rest
      ((decodedOp_lift (credit := credit) (counter := counter) hwindow).trans h_op)
      (afford_credit credit h_gas) h_stack h_cap
    simpa only [liftState, State.fork, subtract_credit credit hb,
      subtract_credit credit hd] using h
  all_goals
    simp_all [Has, arithmetic, NoException, State.decodedOp]

end Challenge.Modexp.Submission.LocalPatch.Transport
