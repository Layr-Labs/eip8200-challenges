import Challenge.Ripemd160.Submission.Proofs.Bytecode.ColdHighLowTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ColdHighPaddingTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ColdHighNormalTrace
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 300000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.ColdHighTrace
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open PersistentStaggerIteration StaggerPersistentFrame

noncomputable opaque gasSteps_setup (input : ByteArray) (hfit : CalldataFits input)
    (hpositive : 0 < input.size) (i : Nat) (hi : i < DriverTrace.blockCount input)
    (hh : input.size = DriverTrace.blockOffset i) (hlarge : 5199 ≤ input.size) :
    GasSteps
      {states input i with
        pc := UInt256.ofNat 4688
        stack := frame (hashes input i) (DriverTrace.blockOffsetWord i)
          (LoopCompletionControl.limit input) maskRho}
      {tableState input i with
        pc := UInt256.ofNat 861
        stack := frame (hashes input i) (DriverTrace.blockOffsetWord i)
          (Padding.paddedWord input) maskRho} :=
  ColdTraceCompose.two (gasSteps_lowRoute input hfit hpositive i hi hh hlarge)
    (ColdTraceCompose.two (gasSteps_padding input hfit (by omega) i)
      (gasSteps_normal input hfit hpositive i hi))

#print axioms gasSteps_setup
end Challenge.Ripemd160.Submission.Proofs.Bytecode.ColdHighTrace
