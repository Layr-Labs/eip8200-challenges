import Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNTailDefs

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNTailTest

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open WindowNibbleKernel MonproKNCache MonproKNRowPrograms MonproKNTailDefs

theorem run_test (s : State) (pbi paEnd pbEnd dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1007)
    (htarget : Decode.isValidJumpDest s.executionEnv.code 1982 = true) :
    runInstructions testProgram
      (framed s (UInt256.ofNat 2462) (baseStack pbi paEnd pbEnd dst ret rest)) =
    some (framed s
      (if UInt256.isTrue (UInt256.gt (negative32+pbi) pbEnd) then UInt256.ofNat 1982
        else UInt256.ofNat 2471)
      (baseStack (negative32+pbi) paEnd pbEnd dst ret rest)) := by
  have hc7 : rest.length+7 < 1024 := by omega
  have hc8 : rest.length+8 < 1024 := by omega
  have hc9 : rest.length+9 < 1024 := by omega
  by_cases ht : UInt256.isTrue (UInt256.gt (negative32+pbi) pbEnd) <;>
    simp [testProgram, tailProgram, baseStack, framed, runInstructions,
      Challenge.EvmProof.Stepper.runInstr, hc7, hc8, hc9, ht, htarget,
      Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

end Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNTailTest
