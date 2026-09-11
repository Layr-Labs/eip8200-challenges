import Challenge.Modexp.Submission.Proofs.Fast.CarryRowTrace
import Challenge.Modexp.Submission.Proofs.Fast.CiosReadonlyTraces

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.Proofs.Fast.CarryReadonlyRun
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast
open Monpro CiosCached CiosCachedMacCore CarryRowModel CarryScratchAgreement
open CiosCachedMidMemory CiosReadonly

theorem run_middle (s : State) (mem : ByteArray) (c bi : UInt256)
    (pa pb n i : Nat) (tl inv m0 aEnd m96 m64 m32 dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 296 ≤ s.activeWords.toNat)
    (hn : 2 ≤ n) (hn32 : n ≤ 32)
    (hc : ReadonlyCache mem n tl inv m0) (hminv : inverseInvariant mem n) :
    runInstructions CarryRowPrograms.middle
      (CiosCached.midState s mem c bi pa pb n i inv m0
        (tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest)) =
    some (CiosCached.l2At 4578 s (midMem1 mem c) (overflow mem c)
      (rowMu mem n) (rowC0 mem n) pa pb n i 0 inv m0
      (tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest)) := by
  have hmem := middle_agree mem mem (refl mem) c
  have hmu : rowMu (midMem1 mem c) n = rowMu mem n :=
    (CarryRowModel.rowMu_eq _ _ hmem n).trans (rowMu_mid mem c n hn)
  have hc0 : rowC0 (midMem1 mem c) n = rowC0 mem n :=
    (CarryRowModel.rowC0_eq _ _ hmem n hn32).trans (rowC0_mid mem c n hn hn32)
  have hcache : ReadonlyCache (midMem1 mem c) n tl inv m0 :=
    hc.of_preserved
      (readWord_midMem1 mem c 9376 (Or.inr (by decide)))
      (readWord_midMem1 mem c (32*n-32) (Or.inl (by omega)))
  have hminv' : inverseInvariant (midMem1 mem c) n := by
    unfold inverseInvariant
    rw [readWord_midMem1 mem c (32*n-32) (Or.inl (by omega)),
      readWord_midMem1 mem c 9376 (Or.inr (by decide))]
    exact hminv
  have hs := CarryRowTrace.run_middleStore {s with memory := mem} c bi
    (UInt256.ofNat (ptrAt (pb+32*n-32) i)) (UInt256.ofNat pa)
    (UInt256.ofNat (pb-32)) (l1Target n) (l2Target n) inv
    (m0 :: tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest)
    (by simp only [List.length_cons]; omega) hact
  have hp := run_cachedProduct_model {s with memory := midMem1 mem c}
    (overflow mem c) (UInt256.ofNat (ptrAt (pb+32*n-32) i)) (UInt256.ofNat pa)
    (UInt256.ofNat (pb-32)) (l1Target n) (l2Target n) tl inv m0 aEnd m96 m64 m32
    dst ret n rest hcap hn32 hact hcache hminv'
  have h := runInstructions_append_some _ _ _ _ _ hs hp
  simpa only [CarryRowPrograms.middle, CiosCached.midState, CiosCached.l2At,
    l2Step, cacheStack, CiosCachedMidDefs.baseStack, framed, hmu, hc0, List.append_assoc,
    List.cons_append, List.nil_append] using h

#print axioms run_middle
end Challenge.Modexp.Submission.Proofs.Fast.CarryReadonlyRun
