import Challenge.Modexp.Submission.Proofs.Fast.CarryRowModel
import Challenge.Modexp.Submission.Proofs.Fast.CarryRowPrograms
import Challenge.Modexp.Submission.Proofs.Fast.CiosEndAroundCarry
import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedMidMemory
import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedTailTest

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.Proofs.Fast.CarryRowTrace
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast
open Monpro CiosCached CiosCachedMacCore CarryRowModel

theorem run_middleStore (s : State) (c bi pbi pa pb flag dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1006) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions CarryRowPrograms.middleStore
      (framed s (UInt256.ofNat 3750)
        ([c,bi,pbi,pa,pb,flag,negative32,allOnes,dst,ret] ++ rest)) =
    some (framed {s with memory := midMem1 s.memory c} (UInt256.ofNat 3764)
      ([overflow s.memory c,pbi,pa,pb,flag,negative32,allOnes,dst,ret] ++ rest)) := by
  have hc8 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hc9 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hc10 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hc11 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hc12 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hc13 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hactN := activeWords_fix s 2080 32 (by decide) (by omega) hact
  have haddr : (2080 : UInt256).toNat = 2080 := by decide
  simp (config := {maxSteps := 100000}) [ CarryRowPrograms.middleStore, runInstructions, framed,
    Challenge.EvmProof.Stepper.runInstr, hc8, hc9, hc10, hc11, hc12, hc13, midMem1, overflow,
    haddr, hactN, State.activeWordsAfterUInt256, List.exchange,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

/-- The store of the shared ladder's middle block, whose first address is a `PUSH4`.
Same pushed value and same gas as the narrow form; only `Instr.bytes.length` differs,
so the store ends at 3656 rather than 3654.  The proof is the narrow one verbatim --
no program counter occurs in it. -/
theorem run_middleStoreWide (s : State) (c bi pbi pa pb flag dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1006) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions CarryRowPrograms.middleStoreWide
      (framed s (UInt256.ofNat 3750)
        ([c,bi,pbi,pa,pb,flag,negative32,allOnes,dst,ret] ++ rest)) =
    some (framed {s with memory := midMem1 s.memory c} (UInt256.ofNat 3766)
      ([overflow s.memory c,pbi,pa,pb,flag,negative32,allOnes,dst,ret] ++ rest)) := by
  have hc8 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hc9 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hc10 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hc11 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hc12 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hc13 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hactN := activeWords_fix s 2080 32 (by decide) (by omega) hact
  have haddr : (2080 : UInt256).toNat = 2080 := by decide
  simp (config := {maxSteps := 100000}) [ CarryRowPrograms.middleStoreWide, runInstructions, framed,
    Challenge.EvmProof.Stepper.runInstr, hc8, hc9, hc10, hc11, hc12, hc13, midMem1, overflow,
    haddr, hactN, State.activeWordsAfterUInt256, List.exchange,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

/-- The same store inside the private ladder copy at 5283.  The copy is a byte copy of
base 3528-3665, so it still carries the narrow `PUSH2` and advances by 14 bytes. -/
theorem run_middleStoreCopy (s : State) (c bi pbi pa pb flag dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1006) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions CarryRowPrograms.middleStore
      (framed s (UInt256.ofNat 5394)
        ([c,bi,pbi,pa,pb,flag,negative32,allOnes,dst,ret] ++ rest)) =
    some (framed {s with memory := midMem1 s.memory c} (UInt256.ofNat 5408)
      ([overflow s.memory c,pbi,pa,pb,flag,negative32,allOnes,dst,ret] ++ rest)) := by
  have hc8 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hc9 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hc10 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hc11 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hc12 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hc13 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hactN := activeWords_fix s 2080 32 (by decide) (by omega) hact
  have haddr : (2080 : UInt256).toNat = 2080 := by decide
  simp (config := {maxSteps := 100000}) [ CarryRowPrograms.middleStore, runInstructions, framed,
    Challenge.EvmProof.Stepper.runInstr, hc8, hc9, hc10, hc11, hc12, hc13, midMem1, overflow,
    haddr, hactN, State.activeWordsAfterUInt256, List.exchange,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

theorem run_tailStore (s : State) (c f pbi pa pb flag dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1006) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions CarryRowPrograms.tailStore
      (framed s (UInt256.ofNat 4026)
        ([c,f,pbi,pa,pb,flag,negative32,allOnes,dst,ret] ++ rest)) =
    some (framed {s with memory := tailCarry s.memory c f} (UInt256.ofNat 4043)
      ([pbi,pa,pb,flag,negative32,allOnes,dst,ret] ++ rest)) := by
  have hc8 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hc9 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hc10 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hc11 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hc12 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hc13 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hactN := activeWords_fix s 2080 32 (by decide) (by omega) hact
  have hactT := activeWords_fix s 2112 32 (by decide) (by omega) hact
  have hn : (2080 : UInt256).toNat = 2080 := by decide
  have ht : (2112 : UInt256).toNat = 2112 := by decide
  simp (config := {maxSteps := 100000}) [ CarryRowPrograms.tailStore, runInstructions, framed,
    Challenge.EvmProof.Stepper.runInstr, hc8, hc9, hc10, hc11, hc12, hc13, tailCarry, tailMem1,
    hn, ht, hactN, hactT, State.activeWordsAfterUInt256, List.exchange,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

  simp only [Nat.add_comm]

#print axioms run_middleStore
#print axioms run_tailStore
end Challenge.Modexp.Submission.Proofs.Fast.CarryRowTrace
