import Challenge.Modexp.Submission.Proofs.Fast.CarryRowTrace
import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedPointers

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.Proofs.Fast.CarryRowRun
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast
open Monpro CiosCached CiosCachedMacCore CarryRowModel CarryScratchAgreement
open CiosCachedMidMemory

theorem run_middle (s : State) (mem : ByteArray) (c bi : UInt256)
    (pa pb n i : Nat) (dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) (hact : 296 ≤ s.activeWords.toNat)
    (hn : 2 ≤ n) (hn32 : n ≤ 32)
    (hml : MachineState.readWord mem 9408 = UInt256.ofNat (32*n-32))
    (htl : MachineState.readWord mem 9440 = UInt256.ofNat (8224+32*n))
    (hminv : inverseInvariant mem n) :
    runInstructions CarryRowPrograms.middle (midState s mem c bi pa pb n i dst ret rest) =
    some (l2At 4576 s (midMem1 mem c) (overflow mem c) (rowMu mem n) (rowC0 mem n)
      pa pb n i 0 dst ret rest) := by
  have hml' : MachineState.readWord (midMem1 mem c) 9408 = UInt256.ofNat (32*n-32) :=
    (readWord_midMem1 mem c 9408 (Or.inr (by decide))).trans hml
  have htl' : MachineState.readWord (midMem1 mem c) 9440 = UInt256.ofNat (8224+32*n) :=
    (readWord_midMem1 mem c 9440 (Or.inr (by decide))).trans htl
  have hminv' : inverseInvariant (midMem1 mem c) n := by
    unfold inverseInvariant
    rw [readWord_midMem1 mem c (32*n-32) (Or.inl (by omega)),
      readWord_midMem1 mem c 9376 (Or.inr (by decide))]
    exact hminv
  have hmem := middle_agree mem mem (refl mem) c
  have hmu : rowMu (midMem1 mem c) n = rowMu mem n :=
    (CarryRowModel.rowMu_eq _ _ hmem n).trans (rowMu_mid mem c n hn)
  have hc0 : rowC0 (midMem1 mem c) n = rowC0 mem n :=
    (CarryRowModel.rowC0_eq _ _ hmem n hn32).trans (rowC0_mid mem c n hn hn32)
  have hs := CarryRowTrace.run_middleStore {s with memory := mem} c bi
    (UInt256.ofNat (ptrAt (pb+32*n-32) i)) (UInt256.ofNat pa) (UInt256.ofNat (pb-32))
    (l1Target n) (l2Target n) dst (ret :: rest) (by simp only [List.length_cons]; omega) hact
  have hp := CiosCachedMidProduct.run_product {s with memory := midMem1 mem c} n (overflow mem c)
    (UInt256.ofNat (ptrAt (pb+32*n-32) i)) (UInt256.ofNat pa) (UInt256.ofNat (pb-32))
    (l1Target n) (l2Target n) dst (ret :: rest) (by simp only [List.length_cons]; omega) hact hn hn32 hml' htl' hminv'
  have ht := runInstructions_append_some _ _ _ _ _ hs hp
  simpa only [CarryRowPrograms.middle, CiosCachedMidDefs.productProgram,
    CiosCachedMidDefs.product, CiosCachedMidDefs.baseStack, midState,
    framed, l2At, l2Step, hmu, hc0, List.append_assoc, List.cons_append, List.nil_append] using ht

theorem run_tail (s : State) (c mu f pbi pa pb flag dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1006) (hact : 296 ≤ s.activeWords.toNat)
    (htarget : Decode.isValidJumpDest s.executionEnv.code 4237 = true) :
    runInstructions CarryRowPrograms.tail
      (framed s (UInt256.ofNat 4835)
        ([c,mu,f,pbi,pa,pb,flag,negative32,allOnes,dst,ret] ++ rest)) =
    some (framed {s with memory := tailCarry s.memory c f}
      (if UInt256.isTrue (UInt256.gt (negative32+pbi) pb) then UInt256.ofNat 4237 else UInt256.ofNat 4868)
      ([negative32+pbi,pa,pb,flag,negative32,allOnes,dst,ret] ++ rest)) := by
  have h1 := CarryRowTrace.run_tailStore s c mu f pbi pa pb flag dst ret rest hcap hact
  have h2 := CiosCachedTailTest.run_test {s with memory := tailCarry s.memory c f}
    pbi pa pb flag dst ret rest hcap htarget
  have h := runInstructions_append_some _ _ _ _ _ h1 h2
  simpa only [CarryRowPrograms.tail, CiosCachedTailDefs.testProgram,
    CiosCachedTailDefs.tailLoopProgram, CiosCachedTailDefs.baseStack, List.drop_take] using h

end Challenge.Modexp.Submission.Proofs.Fast.CarryRowRun
