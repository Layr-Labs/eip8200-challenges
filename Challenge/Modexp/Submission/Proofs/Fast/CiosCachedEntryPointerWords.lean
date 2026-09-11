import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedEntryDefs
import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedMacWords

set_option warningAsError true
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.Proofs.Fast.CiosCachedEntryPointerWords

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast CiosCached CiosCachedMacCore

def firstProgram : List Instr :=
  [.op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op .ADD,
   .op (.Dup ⟨5, by decide⟩), .op .ADD]

def middleProgram : List Instr :=
  [.op (.Swap ⟨2, by decide⟩), .op (.Dup ⟨5, by decide⟩), .op .ADD, .op (.Swap ⟨2, by decide⟩)]

def lastProgram : List Instr :=
  [.op (.Swap ⟨0, by decide⟩), .op .POP]

private theorem negative32_add (x : UInt256) :
    negative32 + x = x - UInt256.ofNat 32 := by
  have hn : negative32.val = -(UInt256.ofNat 32).val := by decide
  change UInt256.mk (negative32.val + x.val) = UInt256.mk (x.val - (UInt256.ofNat 32).val)
  rw [hn, sub_eq_add_neg, add_comm]

theorem program_eq : pointersProgram = (firstProgram ++ middleProgram) ++ lastProgram := rfl

theorem run_first (s : State) (width pa pb flag dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1006) :
    runInstructions firstProgram
      (framed s (UInt256.ofNat 4239) ([width, pa, pb, flag, negative32, allOnes, dst, ret] ++ rest)) =
    some (framed s (UInt256.ofNat 4244)
      ([pb+width-UInt256.ofNat 32, width, pa, pb, flag, negative32, allOnes, dst, ret] ++ rest)) := by
  have hc7 : rest.length+8 < 1024 := by omega
  have hc8 : rest.length+9 < 1024 := by omega
  have hc9 : rest.length+10 < 1024 := by omega
  have h32 : (32 : UInt256) = UInt256.ofNat 32 := by decide
  simp [firstProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    framed, hc7, hc8, hc9, h32, List.exchange, negative32_add,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

theorem run_middle (s : State) (pbi width pa pb flag dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1006) :
    runInstructions middleProgram
      (framed s (UInt256.ofNat 4244) ([pbi, width, pa, pb, flag, negative32, allOnes, dst, ret] ++ rest)) =
    some (framed s (UInt256.ofNat 4248)
      ([pbi, width, pa, pb-UInt256.ofNat 32, flag, negative32, allOnes, dst, ret] ++ rest)) := by
  have hc8 : rest.length+9 < 1024 := by omega
  have hc9 : rest.length+10 < 1024 := by omega
  have hc10 : rest.length+11 < 1024 := by omega
  have h32 : (32 : UInt256) = UInt256.ofNat 32 := by decide
  simp [middleProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    framed, hc8, hc9, hc10, h32, List.exchange, negative32_add,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

theorem run_last (s : State) (pbi width pa pbEnd flag dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1006) :
    runInstructions lastProgram
      (framed s (UInt256.ofNat 4248) ([pbi, width, pa, pbEnd, flag, negative32, allOnes, dst, ret] ++ rest)) =
    some (framed s (UInt256.ofNat 4250)
      ([pbi, pa, pbEnd, flag, negative32, allOnes, dst, ret] ++ rest)) := by
  have hc9 : rest.length+9 < 1024 := by omega
  simp [lastProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    framed, hc9, List.exchange,
    Challenge.EvmProof.Word.succ_ofNat_mod]

theorem run_words (s : State) (width pa pb flag dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1006) :
    runInstructions pointersProgram
      (framed s (UInt256.ofNat 4239) ([width, pa, pb, flag, negative32, allOnes, dst, ret] ++ rest)) =
    some (framed s (UInt256.ofNat 4250)
      ([pb+width-UInt256.ofNat 32, pa, pb-UInt256.ofNat 32,
        flag, negative32, allOnes, dst, ret] ++ rest)) := by
  rw [program_eq]
  exact runInstructions_append_some _ _ _ _ _
    (runInstructions_append_some _ _ _ _ _
      (run_first s width pa pb flag dst ret rest hcap)
      (run_middle s (pb+width-UInt256.ofNat 32) width pa pb flag dst ret rest hcap))
    (run_last s (pb+width-UInt256.ofNat 32) width pa (pb-UInt256.ofNat 32) flag dst ret rest hcap)

#print axioms run_first
#print axioms run_middle
#print axioms run_last
#print axioms run_words
end Challenge.Modexp.Submission.Proofs.Fast.CiosCachedEntryPointerWords
