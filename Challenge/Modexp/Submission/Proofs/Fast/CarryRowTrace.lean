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

/-- The shared ladder's row head at 3770 (E1): the carry channel is the frame cell
`cy`; no memory access.  `[c, bi, …, cy, ret]` becomes `[lt (cy + c) c, …, cy + c, ret]`. -/
theorem run_middleStore (s : State) (c bi pbi pa pb flag cy ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1006) :
    runInstructions CarryRowPrograms.middleStore
      (framed s (UInt256.ofNat 3770)
        ([c,bi,pbi,pa,pb,flag,negative32,allOnes,cy,ret] ++ rest)) =
    some (framed s (UInt256.ofNat 3779)
      ([slotOverflow cy c,pbi,pa,pb,flag,negative32,allOnes,cy + c,ret] ++ rest)) := by
  have hc8 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hc9 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hc10 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hc11 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hc12 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  simp (config := {maxSteps := 100000}) [ CarryRowPrograms.middleStore, runInstructions, framed,
    Challenge.EvmProof.Stepper.runInstr, hc8, hc9, hc10, hc11, hc12, slotOverflow,
    List.exchange,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

/-- The same head inside the private four-limb ladder copy at 5408 (E3; byte-identical). -/
theorem run_middleStoreCopy (s : State) (c bi pbi pa pb flag cy ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1006) :
    runInstructions CarryRowPrograms.middleStore
      (framed s (UInt256.ofNat 5408)
        ([c,bi,pbi,pa,pb,flag,negative32,allOnes,cy,ret] ++ rest)) =
    some (framed s (UInt256.ofNat 5417)
      ([slotOverflow cy c,pbi,pa,pb,flag,negative32,allOnes,cy + c,ret] ++ rest)) := by
  have hc8 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hc9 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hc10 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hc11 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hc12 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  simp (config := {maxSteps := 100000}) [ CarryRowPrograms.middleStore, runInstructions, framed,
    Challenge.EvmProof.Stepper.runInstr, hc8, hc9, hc10, hc11, hc12, slotOverflow,
    List.exchange,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

/-- The row writeback at 4039 (E2): `t[n-1] := cy + c` and the cell becomes the row's
carry out `lt (cy + c) c + f`; `mem[2080]` is not written. -/
theorem run_tailStore (s : State) (c f pbi pa pb flag cy ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1006) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions CarryRowPrograms.tailStore
      (framed s (UInt256.ofNat 4039)
        ([c,f,pbi,pa,pb,flag,negative32,allOnes,cy,ret] ++ rest)) =
    some (framed {s with memory := tailMemS s.memory cy c} (UInt256.ofNat 4051)
      ([pbi,pa,pb,flag,negative32,allOnes,slotOverflow cy c + f,ret] ++ rest)) := by
  have hc8 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hc9 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hc10 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hc11 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hc12 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hc13 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hactT := activeWords_fix s 2112 32 (by decide) (by omega) hact
  have ht : (2112 : UInt256).toNat = 2112 := by decide
  simp (config := {maxSteps := 100000}) [ CarryRowPrograms.tailStore, runInstructions, framed,
    Challenge.EvmProof.Stepper.runInstr, hc8, hc9, hc10, hc11, hc12, hc13, tailMemS, slotOverflow,
    ht, hactT, State.activeWordsAfterUInt256, List.exchange,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

#print axioms run_middleStore
#print axioms run_tailStore
end Challenge.Modexp.Submission.Proofs.Fast.CarryRowTrace
