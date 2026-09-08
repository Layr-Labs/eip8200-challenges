import Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNCache

set_option warningAsError true

/-! Exact post-copy tests. Taken and non-taken paths remain separate traces. -/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNLoopTests

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open WindowNibbleKernel MonproKNCache

def l1TestProgram : List Instr :=
  [.op (.Dup ⟨5, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .GT,
   .push 2 4089, .op .JUMPI]

def l1ExitProgram : List Instr := [.push 2 2008, .op .JUMP]

def l2TestProgram : List Instr :=
  [.push 2 8224, .op (.Dup ⟨2, by decide⟩), .op .GT,
   .push 2 2098, .op .JUMPI]

theorem run_l1_test (template : State) (stack : List UInt256)
    (paj paEnd : UInt256) (hcap : stack.length + 2 < 1024)
    (hpa : stack[0]? = some paj) (hend : stack[5]? = some paEnd)
    (htarget : Decode.isValidJumpDest template.executionEnv.code 4089 = true) :
    runInstructions l1TestProgram (framed template (UInt256.ofNat 4393) stack) =
    some (framed template
      (if UInt256.isTrue (UInt256.gt paj paEnd) then UInt256.ofNat 4089
        else UInt256.ofNat 4400) stack) := by
  have hcap0 : stack.length < 1024 := by omega
  have hcap1 : stack.length + 1 < 1024 := by omega
  by_cases ht : UInt256.isTrue (UInt256.gt paj paEnd) <;>
    simp [runInstructions, l1TestProgram, framed, Challenge.EvmProof.Stepper.runInstr,
      hcap0, hcap1, hcap, hpa, hend, ht, htarget,
      Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

theorem run_l1_exit (template : State) (stack : List UInt256)
    (hcap : stack.length + 1 < 1024)
    (htarget : Decode.isValidJumpDest template.executionEnv.code 2008 = true) :
    runInstructions l1ExitProgram (framed template (UInt256.ofNat 4400) stack) =
    some (framed template (UInt256.ofNat 2008) stack) := by
  have hcap0 : stack.length < 1024 := by omega
  simp [runInstructions, l1ExitProgram, framed, Challenge.EvmProof.Stepper.runInstr,
    hcap0, hcap, htarget, Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat]

theorem run_l2_test (template : State) (stack : List UInt256)
    (ptj : UInt256) (hcap : stack.length + 2 < 1024)
    (hpt : stack[1]? = some ptj)
    (htarget : Decode.isValidJumpDest template.executionEnv.code 2098 = true) :
    runInstructions l2TestProgram (framed template (UInt256.ofNat 2426) stack) =
    some (framed template
      (if UInt256.isTrue (UInt256.gt ptj (UInt256.ofNat 8224)) then UInt256.ofNat 2098
        else UInt256.ofNat 2435) stack) := by
  have hcap0 : stack.length < 1024 := by omega
  have hcap1 : stack.length + 1 < 1024 := by omega
  by_cases ht : UInt256.isTrue (UInt256.gt ptj (UInt256.ofNat 8224)) <;>
    simp [runInstructions, l2TestProgram, framed, Challenge.EvmProof.Stepper.runInstr,
      hcap0, hcap1, hcap, hpt, ht, htarget,
      Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

end Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNLoopTests
