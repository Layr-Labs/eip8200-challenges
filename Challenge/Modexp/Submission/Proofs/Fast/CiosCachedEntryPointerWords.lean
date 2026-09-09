import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedEntryDefs
import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedMacWords

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Fast.CiosCachedEntryPointerWords

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast CiosCached CiosCachedMacCore

def firstProgram : List Instr :=
  [.op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op .ADD,
   .push 1 32, .op (.Swap ⟨0, by decide⟩), .op .SUB]

def middleProgram : List Instr :=
  [.push 1 32, .op (.Dup ⟨4, by decide⟩), .op .SUB, .op (.Swap ⟨3, by decide⟩),
   .op .POP, .op (.Swap ⟨1, by decide⟩), .op .ADD, .op (.Swap ⟨0, by decide⟩)]

def lastProgram : List Instr :=
  [.push 1 32, .op (.Dup ⟨2, by decide⟩), .op .SUB,
   .op (.Swap ⟨1, by decide⟩), .op .POP]

theorem program_eq : pointersProgram = (firstProgram ++ middleProgram) ++ lastProgram := rfl

theorem run_first (s : State) (width pa pb flag dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1006) :
    runInstructions firstProgram
      (framed s (UInt256.ofNat 4542) ([width, pa, pb, flag, negative32, allOnes, dst, ret] ++ rest)) =
    some (framed s (UInt256.ofNat 4549)
      ([pb+width-UInt256.ofNat 32, width, pa, pb, flag, negative32, allOnes, dst, ret] ++ rest)) := by
  have hc7 : rest.length+8 < 1024 := by omega
  have hc8 : rest.length+9 < 1024 := by omega
  have hc9 : rest.length+10 < 1024 := by omega
  have h32 : (32 : UInt256) = UInt256.ofNat 32 := by decide
  simp [firstProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    framed, hc7, hc8, hc9, h32, List.exchange,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

theorem run_middle (s : State) (pbi width pa pb flag dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1006) :
    runInstructions middleProgram
      (framed s (UInt256.ofNat 4549) ([pbi, width, pa, pb, flag, negative32, allOnes, dst, ret] ++ rest)) =
    some (framed s (UInt256.ofNat 4558)
      ([pbi, pa+width, pb-UInt256.ofNat 32, flag, negative32, allOnes, dst, ret] ++ rest)) := by
  have hc7 : rest.length+8 < 1024 := by omega
  have hc8 : rest.length+9 < 1024 := by omega
  have hc9 : rest.length+10 < 1024 := by omega
  have hc10 : rest.length+11 < 1024 := by omega
  have h32 : (32 : UInt256) = UInt256.ofNat 32 := by decide
  simp [middleProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    framed, hc7, hc8, hc9, hc10, h32, List.exchange,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

theorem run_last (s : State) (pbi pa pbEnd flag dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1006) :
    runInstructions lastProgram
      (framed s (UInt256.ofNat 4558) ([pbi, pa, pbEnd, flag, negative32, allOnes, dst, ret] ++ rest)) =
    some (framed s (UInt256.ofNat 4564)
      ([pbi, pa-UInt256.ofNat 32, pbEnd, flag, negative32, allOnes, dst, ret] ++ rest)) := by
  have hc7 : rest.length+8 < 1024 := by omega
  have hc8 : rest.length+9 < 1024 := by omega
  have hc9 : rest.length+10 < 1024 := by omega
  have h32 : (32 : UInt256) = UInt256.ofNat 32 := by decide
  simp [lastProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    framed, hc7, hc8, hc9, h32, List.exchange,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

theorem run_words (s : State) (width pa pb flag dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1006) :
    runInstructions pointersProgram
      (framed s (UInt256.ofNat 4542) ([width, pa, pb, flag, negative32, allOnes, dst, ret] ++ rest)) =
    some (framed s (UInt256.ofNat 4564)
      ([pb+width-UInt256.ofNat 32, pa+width-UInt256.ofNat 32, pb-UInt256.ofNat 32,
        flag, negative32, allOnes, dst, ret] ++ rest)) := by
  rw [program_eq]
  exact runInstructions_append_some _ _ _ _ _
    (runInstructions_append_some _ _ _ _ _
      (run_first s width pa pb flag dst ret rest hcap)
      (run_middle s (pb+width-UInt256.ofNat 32) width pa pb flag dst ret rest hcap))
    (run_last s (pb+width-UInt256.ofNat 32) (pa+width) (pb-UInt256.ofNat 32) flag dst ret rest hcap)

end Challenge.Modexp.Submission.Proofs.Fast.CiosCachedEntryPointerWords
