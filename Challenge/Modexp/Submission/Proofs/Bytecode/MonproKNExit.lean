import Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNRowPrograms
import Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNRowFrames

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNExit

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open WindowNibbleKernel MonproKNCache MonproKNRowPrograms

theorem run_exit (s : State) (pbi paEnd pbEnd dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1007)
    (htarget : Decode.isValidJumpDest s.executionEnv.code 2655 = true) :
    runInstructions exitProgram
      (framed s (UInt256.ofNat 2471) ([pbi, paEnd, pbEnd, negative32, allOnes, dst, ret] ++ rest)) =
    some (framed s (UInt256.ofNat 2655) ([dst, ret] ++ rest)) := by
  have hc3 : rest.length+3 < 1024 := by omega
  have hc4 : rest.length+4 < 1024 := by omega
  have hc5 : rest.length+5 < 1024 := by omega
  have hc6 : rest.length+6 < 1024 := by omega
  have hc7 : rest.length+7 < 1024 := by omega
  have hc2 : rest.length+2 < 1024 := by omega
  simp [exitProgram, framed, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    hc2, hc3, hc4, hc5, hc6, hc7, htarget,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat]

theorem run_stub (s : State) (stack : List UInt256) (hcap : stack.length+1 < 1024)
    (htarget : Decode.isValidJumpDest s.executionEnv.code 4070 = true) :
    runInstructions stubProgram (framed s (UInt256.ofNat 2003) stack) =
    some (framed s (UInt256.ofNat 4070) stack) := by
  have hc0 : stack.length < 1024 := by omega
  simp [stubProgram, framed, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    hc0, hcap, htarget, Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat]

end Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNExit
