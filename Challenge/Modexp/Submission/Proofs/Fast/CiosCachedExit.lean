import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedTailDefs
import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedPrograms
import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedRowFrames

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 200000


namespace Challenge.Modexp.Submission.Proofs.Fast.CiosCachedExit

open Challenge.Modexp.Submission.Proofs.Bytecode
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open CiosCachedTailDefs
open WindowNibbleKernel CiosCachedMacCore CiosCached CiosCached

theorem run_exit (s : State) (pbi paEnd pbEnd flag dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1006)
    (htarget : Decode.isValidJumpDest s.executionEnv.code 2304 = true) :
    runInstructions exitProgram
      (framed s (UInt256.ofNat 5168) ([pbi, paEnd, pbEnd, flag, negative32, allOnes, dst, ret] ++ rest)) =
    some (framed s (UInt256.ofNat 2304) ([dst, ret] ++ rest)) := by
  have hc3 : rest.length+4 < 1024 := by omega
  have hc4 : rest.length+5 < 1024 := by omega
  have hc5 : rest.length+6 < 1024 := by omega
  have hc6 : rest.length+7 < 1024 := by omega
  have hc7 : rest.length+8 < 1024 := by omega
  have hc2 : rest.length+3 < 1024 := by omega
  have hc2new : rest.length+2 < 1024 := by omega
  simp [exitProgram, CiosCached.tailProgram, framed, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    hc2new, hc2, hc3, hc4, hc5, hc6, hc7, htarget,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat]

end Challenge.Modexp.Submission.Proofs.Fast.CiosCachedExit
