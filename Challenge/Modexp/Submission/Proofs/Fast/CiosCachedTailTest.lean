import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedTailDefs

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 200000
set_option linter.unusedSimpArgs false


namespace Challenge.Modexp.Submission.Proofs.Fast.CiosCachedTailTest

open Challenge.Modexp.Submission.Proofs.Bytecode
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open WindowNibbleKernel CiosCachedMacCore CiosCached CiosCached CiosCachedTailDefs

/-- The loop test reads `NOT 31` from frame slot 11 now that the window exchange
moved it there, so the four slots above it are named explicitly. -/
theorem run_test (s : State) (pbi paEnd pbEnd flag dst ret w7 w8 w9 w10 : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1006)
    (htarget : Decode.isValidJumpDest s.executionEnv.code paEnd.toNat = true) :
    runInstructions testProgram
      (framed s (UInt256.ofNat 4102)
        (baseStack pbi paEnd pbEnd flag dst ret (w7 :: w8 :: w9 :: w10 :: negative32 :: rest))) =
    some (framed s
      (if UInt256.isTrue (UInt256.gt (negative32+pbi) pbEnd) then paEnd
        else UInt256.ofNat 4109)
      (baseStack (negative32+pbi) paEnd pbEnd flag dst ret
        (w7 :: w8 :: w9 :: w10 :: negative32 :: rest))) := by
  have hc7 : rest.length+12 < 1024 := by omega
  have hc8 : rest.length+13 < 1024 := by omega
  have hc9 : rest.length+14 < 1024 := by omega
  by_cases ht : UInt256.isTrue (UInt256.gt (negative32+pbi) pbEnd) <;>
    simp [testProgram, tailLoopProgram, CiosCached.tailProgram, baseStack, framed, runInstructions,
      Challenge.EvmProof.Stepper.runInstr, hc7, hc8, hc9, ht, htarget,
      Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

end Challenge.Modexp.Submission.Proofs.Fast.CiosCachedTailTest
