import Challenge.Modexp.Submission.Proofs.Fast.CarryRowModel
import Challenge.Modexp.Submission.Proofs.Fast.CarryRowPrograms
import Challenge.Modexp.Submission.Proofs.Fast.CiosEndAroundCarry
import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedMidMemory
import Challenge.Modexp.Submission.Proofs.Fast.SquareTop

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
    (rest : List UInt256) (hcap : rest.length ≤ 1006) (hact : 91 ≤ s.activeWords.toNat)
    (hzero : MachineState.readWord s.memory 2368 = UInt256.ofNat 0) :
    runInstructions CarryRowPrograms.middleStore
      (framed s (UInt256.ofNat 4470)
        ([c,bi,pbi,pa,pb,flag,negative32,allOnes,dst,ret] ++ rest)) =
    some (framed {s with memory := midMem1 s.memory c} (UInt256.ofNat 4500)
      ([overflow s.memory c,pbi,pa,pb,flag,negative32,allOnes,dst,ret] ++ rest)) := by
  have h := SquareTop.run_top s s.memory c bi
    ([pbi,pa,pb,flag,negative32,allOnes,dst,ret] ++ rest)
    (by simp only [List.length_append, List.length_cons, List.length_nil]; omega) hact
  simpa only [hzero, SquareTop.mul_zero, SquareTop.memory_zero, SquareTop.flag_zero,
    SquareInit.stateAt, framed, overflow, List.cons_append] using h

theorem run_tailStore (s : State) (c mu f pbi pa pb flag dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1006) (hact : 91 ≤ s.activeWords.toNat) :
    runInstructions CarryRowPrograms.tailStore
      (framed s (UInt256.ofNat 4765)
        ([c,mu,f,pbi,pa,pb,flag,negative32,allOnes,dst,ret] ++ rest)) =
    some (framed {s with memory := tailCarry s.memory c f} (UInt256.ofNat 4784)
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
