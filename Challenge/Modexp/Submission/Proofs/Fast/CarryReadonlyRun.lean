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

/-- The shared ladder's middle block at 3769: the carry merge on the cell (E1) and the
cached product, falling through into the second-loop join `JUMPDEST` 3791.  The memory
is untouched; the cell advances from `cy` to `cy + c`. -/
theorem run_middle (s : State) (mem : ByteArray) (c bi : UInt256)
    (pb n i : Nat) (hd ent cy tl inv m0 aEnd m96 m64 m32 dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat)
    (_hn : 2 ≤ n) (hn32 : n ≤ 8)
    (hc : ReadonlyCache mem n tl inv m0) (hminv : inverseInvariant mem n) :
    runInstructions CarryRowPrograms.middleBlock
      (CiosCached.midState s mem c bi pb n i hd ent cy inv m0
        (tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest)) =
    some (CiosCached.l2At 3791 s mem (slotOverflow cy c)
      (rowMu mem n) (rowC0 mem n) pb n i 0 hd ent (cy + c) inv m0
      (tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest)) := by
  have hc18 : rest.length + 18 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hjd : runInstructions [.op .JUMPDEST]
      (CiosCached.midState s mem c bi pb n i hd ent cy inv m0
        (tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest)) =
      some (framed {s with memory := mem} (UInt256.ofNat 3770)
        ([c,bi,UInt256.ofNat (ptrAt (pb+32*n-32) i),hd,
          UInt256.ofNat (pb-32),ent,negative32,allOnes,cy,inv] ++
          (m0 :: tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest))) := by
    simp [runInstructions, Challenge.EvmProof.Stepper.runInstr, CiosCached.midState, framed,
      hc18, hc17, Challenge.EvmProof.Word.succ_ofNat_mod]
  have hs := CarryRowTrace.run_middleStore {s with memory := mem} c bi
    (UInt256.ofNat (ptrAt (pb+32*n-32) i)) hd
    (UInt256.ofNat (pb-32)) ent cy inv
    (m0 :: tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest)
    (by simp only [List.length_cons]; omega)
  have hp := run_cachedProduct_modelWide {s with memory := mem}
    (slotOverflow cy c) (UInt256.ofNat (ptrAt (pb+32*n-32) i)) hd
    (UInt256.ofNat (pb-32)) ent (cy + c) tl inv m0 aEnd m96 m64 m32
    dst ret n rest hcap hn32 hact hc hminv
  have h := runInstructions_append_some _ _ _ _ _ hs hp
  have h2 := runInstructions_append_some _ _ _ _ _ hjd h
  simpa only [CarryRowPrograms.middleBlock, CarryRowPrograms.middle, CiosCached.l2At,
    l2Step, cacheStack, CiosCachedMidDefs.baseStack, framed, List.append_assoc,
    List.cons_append, List.nil_append] using h2

#print axioms run_middle

/-- The private four-limb ladder copy's middle block at 5407 (E3), ending at 5429 where
the copy's own `PUSH2 0x0f63 JUMP` leaves for 3939. -/
theorem run_middleCopy (s : State) (mem : ByteArray) (c bi : UInt256)
    (pb n i : Nat) (hd ent cy tl inv m0 aEnd m96 m64 m32 dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat)
    (_hn : 2 ≤ n) (hn32 : n ≤ 8)
    (hc : ReadonlyCache mem n tl inv m0) (hminv : inverseInvariant mem n) :
    runInstructions CarryRowPrograms.middleBlock
      (CiosCached.midStateAt 5407 s mem c bi pb n i hd ent cy inv m0
        (tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest)) =
    some (CiosCached.l2At 5429 s mem (slotOverflow cy c)
      (rowMu mem n) (rowC0 mem n) pb n i 0 hd ent (cy + c) inv m0
      (tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest)) := by
  have hc18 : rest.length + 18 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hjd : runInstructions [.op .JUMPDEST]
      (CiosCached.midStateAt 5407 s mem c bi pb n i hd ent cy inv m0
        (tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest)) =
      some (framed {s with memory := mem} (UInt256.ofNat 5408)
        ([c,bi,UInt256.ofNat (ptrAt (pb+32*n-32) i),hd,
          UInt256.ofNat (pb-32),ent,negative32,allOnes,cy,inv] ++
          (m0 :: tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest))) := by
    simp [runInstructions, Challenge.EvmProof.Stepper.runInstr, CiosCached.midStateAt, framed,
      hc18, hc17, Challenge.EvmProof.Word.succ_ofNat_mod]
  have hs := CarryRowTrace.run_middleStoreCopy {s with memory := mem} c bi
    (UInt256.ofNat (ptrAt (pb+32*n-32) i)) hd
    (UInt256.ofNat (pb-32)) ent cy inv
    (m0 :: tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest)
    (by simp only [List.length_cons]; omega)
  have hp := run_cachedProduct_modelCopy {s with memory := mem}
    (slotOverflow cy c) (UInt256.ofNat (ptrAt (pb+32*n-32) i)) hd
    (UInt256.ofNat (pb-32)) ent (cy + c) tl inv m0 aEnd m96 m64 m32
    dst ret n rest hcap hn32 hact hc hminv
  have h := runInstructions_append_some _ _ _ _ _ hs hp
  have h2 := runInstructions_append_some _ _ _ _ _ hjd h
  simpa only [CarryRowPrograms.middleBlock, CarryRowPrograms.middle, CiosCached.l2At,
    l2Step, cacheStack, CiosCachedMidDefs.baseStack, framed, List.append_assoc,
    List.cons_append, List.nil_append] using h2

#print axioms run_middleCopy
end Challenge.Modexp.Submission.Proofs.Fast.CarryReadonlyRun
