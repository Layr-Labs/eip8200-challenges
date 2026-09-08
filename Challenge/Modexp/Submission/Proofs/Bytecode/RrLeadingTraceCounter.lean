import Challenge.Modexp.Submission.Proofs.Bytecode.RrLeadingTraceCore

set_option warningAsError true
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.RrLeadingTraceCore

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler

theorem run_counter (template : State) (mem : ByteArray)
    (n bsize esize msize : Nat) (_hn2 : 2 ≤ n) (hn32 : n ≤ 32) :
    runInstructions counterProgram (copiedState template mem n bsize esize msize) =
      some (counterState template mem n bsize esize msize) := by
  have hpc :
      (((((UInt256.ofNat 3583).succ + UInt256.ofNat 2).succ.succ +
          UInt256.ofNat 2).succ.succ + UInt256.ofNat 2).succ.succ +
          UInt256.ofNat 2).succ.succ.succ.succ = UInt256.ofNat 3602 := by
    decide
  simp [counterProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    copiedState, counterState, outer, counterWord n hn32, hpc]

end Challenge.Modexp.Submission.Proofs.Fast.RrLeadingTraceCore
