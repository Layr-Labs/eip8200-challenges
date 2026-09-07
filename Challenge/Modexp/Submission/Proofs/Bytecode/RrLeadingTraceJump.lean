import Challenge.Modexp.Submission.Proofs.Bytecode.RrLeadingTraceCounter

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Fast.RrLeadingTraceCore

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler

theorem run_jump (template : State) (mem : ByteArray)
    (n bsize esize msize : Nat)
    (hjump : Decode.isValidJumpDest template.executionEnv.code 1569 = true) :
    runInstructions jumpProgram (counterState template mem n bsize esize msize) =
      some (exitState template mem n bsize esize msize) := by
  simp [jumpProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    counterState, exitState, copiedMemory, copiedActiveWords,
    outer, hjump, Challenge.EvmProof.Word.word_toNat_ofNat]

end Challenge.Modexp.Submission.Proofs.Fast.RrLeadingTraceCore
