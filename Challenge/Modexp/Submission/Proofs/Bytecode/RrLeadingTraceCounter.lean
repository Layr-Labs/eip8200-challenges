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
  simp (config := { maxSteps := 600000 })
    [counterProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
      copiedState, counterState, outer, counterLookup n _hn2 hn32,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod]

end Challenge.Modexp.Submission.Proofs.Fast.RrLeadingTraceCore
