import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedEntryDefs
import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedMacWords

set_option warningAsError true
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000

namespace Challenge.Modexp.Submission.Proofs.Fast.CiosCachedEntryPointerWords

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast CiosCached CiosCachedMacCore

/-- Retain all subsequent byte positions and instruction indices with four
one-gas JUMPDESTs, then compute both pointers in seven instructions. -/
def program : List Instr :=
  [.op .JUMPDEST, .op .JUMPDEST, .op .JUMPDEST, .op .JUMPDEST,
   .op (.Dup ⟨2, by decide⟩), .op (.Dup ⟨5, by decide⟩), .op .ADD,
   .op (.Swap ⟨2, by decide⟩), .op .ADD,
   .op (.Dup ⟨4, by decide⟩), .op .ADD]

theorem program_eq : pointersProgram = program := rfl

private theorem negative32_add (x : UInt256) :
    negative32 + x = x - UInt256.ofNat 32 := by
  have hn : negative32.val = -(UInt256.ofNat 32).val := by decide
  change UInt256.mk (negative32.val + x.val) =
    UInt256.mk (x.val - (UInt256.ofNat 32).val)
  rw [hn, sub_eq_add_neg, add_comm]

theorem run_words (s : State) (width pa pb flag dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1006) :
    runInstructions pointersProgram
      (framed s (UInt256.ofNat 4148)
        ([width, pa, pb, flag, negative32, allOnes, dst, ret] ++ rest)) =
    some (framed s (UInt256.ofNat 4159)
      ([pb + width - UInt256.ofNat 32, pa, pb - UInt256.ofNat 32,
        flag, negative32, allOnes, dst, ret] ++ rest)) := by
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  rw [program_eq]
  simp [program, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    framed, hc8, hc9, hc10, List.exchange, negative32_add,
    Challenge.EvmProof.Word.succ_ofNat_mod]

#print axioms run_words

end Challenge.Modexp.Submission.Proofs.Fast.CiosCachedEntryPointerWords
