import Challenge.Modexp.Submission.LocalPatch.TransportDomain

set_option warningAsError true
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.LocalPatch.Transport
open EvmSemantics EvmSemantics.EVM

/-- Transport actual successful bitwise rules. All other constructors are
eliminated by their decoded opcode or their exceptional output, not assumed
away by a whole-step-equivalence premise. -/
theorem bitwise_running {code : ByteArray} {credit counter : Nat} {s t : State}
    (hwindow : LocalDecode.checkAt s.executionEnv.code code s.pc.toNat = true)
    (hallowed : Has bitwise s) (hnormal : NoException t)
    (hstep : StepRunning s t) :
    StepRunning (liftState code credit counter s) (liftState code credit counter t) := by
  cases hstep
  case lt a b rest h_op h_gas h_stack h_cap =>
    have h := StepRunning.lt (liftState code credit counter s) a b rest
      ((decodedOp_lift (credit := credit) (counter := counter) hwindow).trans h_op) (afford_credit credit h_gas) h_stack h_cap
    simpa only [liftState, State.fork, subtract_credit credit h_gas] using h
  case gt a b rest h_op h_gas h_stack h_cap =>
    have h := StepRunning.gt (liftState code credit counter s) a b rest
      ((decodedOp_lift (credit := credit) (counter := counter) hwindow).trans h_op) (afford_credit credit h_gas) h_stack h_cap
    simpa only [liftState, State.fork, subtract_credit credit h_gas] using h
  case slt a b rest h_op h_gas h_stack h_cap =>
    have h := StepRunning.slt (liftState code credit counter s) a b rest
      ((decodedOp_lift (credit := credit) (counter := counter) hwindow).trans h_op) (afford_credit credit h_gas) h_stack h_cap
    simpa only [liftState, State.fork, subtract_credit credit h_gas] using h
  case sgt a b rest h_op h_gas h_stack h_cap =>
    have h := StepRunning.sgt (liftState code credit counter s) a b rest
      ((decodedOp_lift (credit := credit) (counter := counter) hwindow).trans h_op) (afford_credit credit h_gas) h_stack h_cap
    simpa only [liftState, State.fork, subtract_credit credit h_gas] using h
  case eq a b rest h_op h_gas h_stack h_cap =>
    have h := StepRunning.eq (liftState code credit counter s) a b rest
      ((decodedOp_lift (credit := credit) (counter := counter) hwindow).trans h_op) (afford_credit credit h_gas) h_stack h_cap
    simpa only [liftState, State.fork, subtract_credit credit h_gas] using h
  case iszero a rest h_op h_gas h_stack h_cap =>
    have h := StepRunning.iszero (liftState code credit counter s) a rest
      ((decodedOp_lift (credit := credit) (counter := counter) hwindow).trans h_op) (afford_credit credit h_gas) h_stack h_cap
    simpa only [liftState, State.fork, subtract_credit credit h_gas] using h
  case and a b rest h_op h_gas h_stack h_cap =>
    have h := StepRunning.and (liftState code credit counter s) a b rest
      ((decodedOp_lift (credit := credit) (counter := counter) hwindow).trans h_op) (afford_credit credit h_gas) h_stack h_cap
    simpa only [liftState, State.fork, subtract_credit credit h_gas] using h
  case or a b rest h_op h_gas h_stack h_cap =>
    have h := StepRunning.or (liftState code credit counter s) a b rest
      ((decodedOp_lift (credit := credit) (counter := counter) hwindow).trans h_op) (afford_credit credit h_gas) h_stack h_cap
    simpa only [liftState, State.fork, subtract_credit credit h_gas] using h
  case xor_ a b rest h_op h_gas h_stack h_cap =>
    have h := StepRunning.xor_ (liftState code credit counter s) a b rest
      ((decodedOp_lift (credit := credit) (counter := counter) hwindow).trans h_op) (afford_credit credit h_gas) h_stack h_cap
    simpa only [liftState, State.fork, subtract_credit credit h_gas] using h
  case not a rest h_op h_gas h_stack h_cap =>
    have h := StepRunning.not (liftState code credit counter s) a rest
      ((decodedOp_lift (credit := credit) (counter := counter) hwindow).trans h_op) (afford_credit credit h_gas) h_stack h_cap
    simpa only [liftState, State.fork, subtract_credit credit h_gas] using h
  case clz a rest h_op h_gas h_stack h_cap =>
    have h := StepRunning.clz (liftState code credit counter s) a rest
      ((decodedOp_lift (credit := credit) (counter := counter) hwindow).trans h_op) (afford_credit credit h_gas) h_stack h_cap
    simpa only [liftState, State.fork, subtract_credit credit h_gas] using h
  case byte_ i x rest h_op h_gas h_stack h_cap =>
    have h := StepRunning.byte_ (liftState code credit counter s) i x rest
      ((decodedOp_lift (credit := credit) (counter := counter) hwindow).trans h_op) (afford_credit credit h_gas) h_stack h_cap
    simpa only [liftState, State.fork, subtract_credit credit h_gas] using h
  case shl shift v rest h_op h_gas h_stack h_cap =>
    have h := StepRunning.shl (liftState code credit counter s) shift v rest
      ((decodedOp_lift (credit := credit) (counter := counter) hwindow).trans h_op) (afford_credit credit h_gas) h_stack h_cap
    simpa only [liftState, State.fork, subtract_credit credit h_gas] using h
  case shr shift v rest h_op h_gas h_stack h_cap =>
    have h := StepRunning.shr (liftState code credit counter s) shift v rest
      ((decodedOp_lift (credit := credit) (counter := counter) hwindow).trans h_op) (afford_credit credit h_gas) h_stack h_cap
    simpa only [liftState, State.fork, subtract_credit credit h_gas] using h
  case sar shift v rest h_op h_gas h_stack h_cap =>
    have h := StepRunning.sar (liftState code credit counter s) shift v rest
      ((decodedOp_lift (credit := credit) (counter := counter) hwindow).trans h_op) (afford_credit credit h_gas) h_stack h_cap
    simpa only [liftState, State.fork, subtract_credit credit h_gas] using h
  all_goals
    simp_all [Has, bitwise, NoException, State.decodedOp]

end Challenge.Modexp.Submission.LocalPatch.Transport
