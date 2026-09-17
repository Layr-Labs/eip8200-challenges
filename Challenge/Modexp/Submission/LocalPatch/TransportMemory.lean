import Challenge.Modexp.Submission.LocalPatch.TransportDomain

set_option warningAsError true
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.LocalPatch.Transport
open EvmSemantics EvmSemantics.EVM

/-- Transport actual successful memoryInput rules. All other constructors are
eliminated by their decoded opcode or their exceptional output, not assumed
away by a whole-step-equivalence premise. -/
theorem memoryInput_running {code : ByteArray} {credit counter : Nat} {s t : State}
    (hwindow : LocalDecode.checkAt s.executionEnv.code code s.pc.toNat = true)
    (hallowed : Has memoryInput s) (hnormal : NoException t)
    (hstep : StepRunning s t) :
    StepRunning (liftState code credit counter s) (liftState code credit counter t) := by
  cases hstep
  case mload offset rest h_op h_stack h_gas h_cap =>
    have hc : Gas.mloadTotal (liftState code credit counter s) offset =
        Gas.mloadTotal s offset := rfl
    have h := StepRunning.mload (liftState code credit counter s) offset rest
      ((decodedOp_lift (credit := credit) (counter := counter) hwindow).trans h_op)
      h_stack (afford_credit credit h_gas) h_cap
    rw [hc] at h
    simpa only [liftState, State.activeWordsAfterUInt256,
      subtract_credit credit h_gas] using h
  case mstore offset value rest h_op h_stack h_gas h_cap =>
    have hc : Gas.mstoreTotal (liftState code credit counter s) offset =
        Gas.mstoreTotal s offset := rfl
    have h := StepRunning.mstore (liftState code credit counter s) offset value rest
      ((decodedOp_lift (credit := credit) (counter := counter) hwindow).trans h_op)
      h_stack (afford_credit credit h_gas) h_cap
    rw [hc] at h
    simpa only [liftState, State.activeWordsAfterUInt256,
      subtract_credit credit h_gas] using h
  case mstore8 offset value rest h_op h_stack h_gas h_cap =>
    have hc : Gas.mstore8Total (liftState code credit counter s) offset =
        Gas.mstore8Total s offset := rfl
    have h := StepRunning.mstore8 (liftState code credit counter s) offset value rest
      ((decodedOp_lift (credit := credit) (counter := counter) hwindow).trans h_op)
      h_stack (afford_credit credit h_gas) h_cap
    rw [hc] at h
    simpa only [liftState, State.activeWordsAfterUInt256,
      subtract_credit credit h_gas] using h
  case mcopy destOff srcOff sz rest h_op h_stack h_gas h_cap =>
    have hc : Gas.mcopyTotal (liftState code credit counter s) destOff srcOff sz =
        Gas.mcopyTotal s destOff srcOff sz := rfl
    have h := StepRunning.mcopy (liftState code credit counter s) destOff srcOff sz rest
      ((decodedOp_lift (credit := credit) (counter := counter) hwindow).trans h_op)
      h_stack (afford_credit credit h_gas) h_cap
    rw [hc] at h
    simpa only [liftState, State.activeWordsAfterUInt256_2,
      subtract_credit credit h_gas] using h
  case calldatacopy destOff srcOff sz rest h_op h_stack h_gas h_cap =>
    have hc : Gas.calldatacopyTotal (liftState code credit counter s) destOff sz =
        Gas.calldatacopyTotal s destOff sz := rfl
    have h := StepRunning.calldatacopy (liftState code credit counter s) destOff srcOff sz rest
      ((decodedOp_lift (credit := credit) (counter := counter) hwindow).trans h_op)
      h_stack (afford_credit credit h_gas) h_cap
    rw [hc] at h
    simpa only [liftState, State.activeWordsAfterUInt256,
      subtract_credit credit h_gas] using h
  case calldataload i rest h_op h_gas h_stack h_cap =>
    have h := StepRunning.calldataload (liftState code credit counter s) i rest
      ((decodedOp_lift (credit := credit) (counter := counter) hwindow).trans h_op) (afford_credit credit h_gas) h_stack h_cap
    simpa only [liftState, State.fork, subtract_credit credit h_gas] using h
  case calldatasize h_op h_gas h_cap =>
    have h := StepRunning.calldatasize (liftState code credit counter s) 
      ((decodedOp_lift (credit := credit) (counter := counter) hwindow).trans h_op) (afford_credit credit h_gas) h_cap
    simpa only [liftState, State.fork, subtract_credit credit h_gas] using h
  case msize h_op h_gas h_cap =>
    have hm : MachineState.msize (liftState code credit counter s).toMachineState =
        MachineState.msize s.toMachineState := rfl
    have h := StepRunning.msize (liftState code credit counter s)
      ((decodedOp_lift (credit := credit) (counter := counter) hwindow).trans h_op)
      (afford_credit credit h_gas) h_cap
    rw [hm] at h
    simpa only [liftState, State.fork, subtract_credit credit h_gas] using h
  all_goals
    simp_all [Has, memoryInput, NoException, State.decodedOp]

end Challenge.Modexp.Submission.LocalPatch.Transport
