import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairStoreGap
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairStoreMerge
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Pair13WriterRaw

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Pair13Memory
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open PairedScheduleMemory

private theorem prefix_gap (memory : ByteArray) (words : Nat → UInt256)
    (j : Nat) (hj : j ∈ PairStoreGap.lowerPairSlots) (hgap : PairStoreGap.GapClear memory) :
    ∀ i, 18 * (j + 1) - 4 ≤ i → i < 18 * (j + 1) →
      (StaggerTableMemory.storeDescending memory (StaggerTableLayout.tableWords words)
        (j + 2) (59 - j))[i]?.getD 0 = 0 := by
  intro i hi0 hi1
  rw [StaggerTableMemory.getD_storeDescending_outside _ _ _ _ _
    (by intro k hk0 hk1; left; omega)]
  have hz := hgap j hj (i - 18 * j) (by omega) (by omega)
  simpa only [Nat.add_sub_of_le (by omega : 18 * j ≤ i)] using hz

private theorem coefficient_eq : Pair13PoolRaw.coefficient =
    UInt256.ofNat (2 ^ 144 + 1) := by
  unfold Pair13PoolRaw.coefficient
  congr 1

/-- The table image the writer leaves once the mask at pc 873 is gone: exactly
`StaggerTableLayout.resultMemory` except that slot 0, the lowest, keeps the dual lane the
mask used to clear.  `storeDescending memory f 0 61` is definitionally
`writeWord (storeDescending memory f 1 60) 0 (f 0)`, so this is that chain with the one
value replaced.  Bytes 10..13 of address 0 are the only difference, and no round read
covers them: every round reads at `18 * pairIndices[r]` with `1 <= pairIndices[r]`. -/
def resultMemoryD (memory : ByteArray) (words : Nat → UInt256) : ByteArray :=
  writeWord (StaggerTableMemory.storeDescending memory
      (StaggerTableLayout.tableWords words) 1 60) 0
    (Pair13WriterRaw.dualW words 6)

/-- Writing the same slot twice keeps only the second value. -/
theorem writeWord_overwrite (memory : ByteArray) (a : Nat) (x y : UInt256) :
    writeWord (writeWord memory a x) a y = writeWord memory a y := by
  apply ByteArray.ext_getElem
  · simp only [writeWord_size]; omega
  · intro i hi hj
    rw [← Memory.getD0_eq_getElem _ _ hi, ← Memory.getD0_eq_getElem _ _ hj]
    simp only [writeWord, MachineState.writeBytes_getElem?_getD,
      YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
    by_cases ha : a ≤ i ∧ i < a + 32
    · rw [if_pos ha, if_pos ha]
    · rw [if_neg ha, if_neg ha, if_neg ha]

/-- `absorb` for an arbitrary value that agrees below bit 144: the store eighteen bytes
below keeps only bits `0..143` of the slot above. -/
theorem absorb_mod (memory : ByteArray) (a b : Nat) (hab : b + 18 = a) (v w u : UInt256)
    (h : v.toNat % 2 ^ 144 = w.toNat % 2 ^ 144) :
    writeWord (writeWord memory a v) b u = writeWord (writeWord memory a w) b u := by
  apply ByteArray.ext_getElem
  · simp only [writeWord_size]
  · intro i hi hj
    rw [← Memory.getD0_eq_getElem _ _ hi, ← Memory.getD0_eq_getElem _ _ hj]
    simp only [writeWord, MachineState.writeBytes_getElem?_getD,
      YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
    by_cases hb : b ≤ i ∧ i < b + 32
    · rw [if_pos hb, if_pos hb]
    · rw [if_neg hb, if_neg hb]
      by_cases ha : a ≤ i ∧ i < a + 32
      · rw [if_pos ha, if_pos ha]
        exact StaggerTableLayout.byte_of_mod v w h (i - a) (by omega) (by omega)
      · rw [if_neg ha, if_neg ha]

/-- Two descending table chains that agree on every word below bit 144 leave the same image,
provided something is stored eighteen bytes below the lowest slot. -/
theorem storeDescending_congr_mod (memory : ByteArray) (f g : Nat → UInt256) (count : Nat) :
    ∀ (first : Nat) (v : UInt256), 0 < first →
      (∀ j, first ≤ j → j < first + count →
        (f j).toNat % 2 ^ 144 = (g j).toNat % 2 ^ 144) →
      writeWord (StaggerTableMemory.storeDescending memory f first count) (18 * first - 18) v
        = writeWord (StaggerTableMemory.storeDescending memory g first count)
            (18 * first - 18) v := by
  induction count with
  | zero => intro first v _ _; rfl
  | succ n ih =>
    intro first v hfirst h
    show writeWord (writeWord (StaggerTableMemory.storeDescending memory f (first + 1) n)
        (18 * first) (f first)) (18 * first - 18) v
      = writeWord (writeWord (StaggerTableMemory.storeDescending memory g (first + 1) n)
        (18 * first) (g first)) (18 * first - 18) v
    rw [absorb_mod _ (18 * first) (18 * first - 18) (by omega) (f first) (g first) v
      (h first (by omega) (by omega))]
    have hih := ih (first + 1) (g first) (by omega)
      (fun j h1 h2 => h j (by omega) (by omega))
    rw [show 18 * (first + 1) - 18 = 18 * first by omega] at hih
    rw [hih]

/-- Two table images built from word functions that agree below bit 144 (and exactly at the
slot-0 word) are equal: slot 0 is the only slot nothing is written beneath. -/
theorem resultMemoryD_congr_mod (memory : ByteArray) (u w : Nat → UInt256)
    (h6 : Pair13WriterRaw.dualW u 6 = Pair13WriterRaw.dualW w 6)
    (h : ∀ j, 1 ≤ j → j < 61 →
      (StaggerTableLayout.tableWords u j).toNat % 2 ^ 144
        = (StaggerTableLayout.tableWords w j).toNat % 2 ^ 144) :
    resultMemoryD memory u = resultMemoryD memory w := by
  have hs := storeDescending_congr_mod memory (StaggerTableLayout.tableWords u)
    (StaggerTableLayout.tableWords w) 60 1 (Pair13WriterRaw.dualW w 6) (by omega)
    (fun j h1 h2 => h j h1 (by omega))
  rw [show 18 * 1 - 18 = 0 from rfl] at hs
  rw [resultMemoryD, resultMemoryD, h6]
  exact hs

/-- `resultMemoryD` in the form downstream consumers want: the ordinary table with a single
extra store at address 0.  Every read at an address `>= 32` is then discharged by
`read_writeWord_disjoint`, and only the read at 0 needs an argument of its own. -/
theorem dualW_eq_dualLane (words : Nat → UInt256) (hw : (words 6).toNat < 2 ^ 32) :
    Pair13WriterRaw.dualW words 6 = StaggerTableLayout.dualLane (words 6) := by
  apply Word.word_ext
  rw [Pair13WriterRaw.dualW,
    Pair13PoolRaw.mul_coefficient_toNat _ hw, StaggerTableLayout.dualLane_toNat _ hw]

theorem resultMemoryD_eq (memory : ByteArray) (words : Nat → UInt256)
    (hw : (words 6).toNat < 2 ^ 32) :
    resultMemoryD memory words = StaggerTableLayout.resultMemory0 memory words := by
  rw [resultMemoryD, StaggerTableLayout.resultMemory0, dualW_eq_dualLane words hw]
  show writeWord _ 0 (StaggerTableLayout.dualLane (words 6)) =
    writeWord (writeWord (StaggerTableMemory.storeDescending memory
      (StaggerTableLayout.tableWords words) 1 60) 0
      (StaggerTableLayout.tableWords words 0)) 0
      (StaggerTableLayout.dualLane (words 6))
  rw [writeWord_overwrite]

/-- Byte 54 -- value index 18 of the word at 36 -- is zero in the clean table, because a
schedule word below `2 ^ 104` has nothing above its low thirteen bytes.  It sits OUTSIDE the
exposed gap [50,54), so the byte-level theorem carries it to the writer's image, where it is
the single zero byte `PoolFacts.zero_byte_slack` needs. -/
theorem resultMemory0_byte54 (memory : ByteArray) (words : Nat → UInt256)
    (hw : ∀ i, i < 16 → (words i).toNat < 2 ^ 96) :
    (StaggerTableLayout.resultMemory0 memory words)[54]?.getD 0 = 0 := by
  rw [StaggerTableLayout.resultMemory0]
  simp only [writeWord, MachineState.writeBytes_getElem?_getD,
    YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  rw [if_neg (by omega)]
  change (StaggerTableMemory.storeDescending memory
    (StaggerTableLayout.tableWords words) 0 61)[18 * 2 + 18]?.getD 0 = 0
  rw [StaggerTableMemory.getD_pair _ _ _ _ _ _ (by omega) (by omega) (by omega),
    if_neg (by omega)]
  exact PairStoreMerge.prefix_zero_at _ 18 (by decide)
    (Nat.lt_of_lt_of_le (hw _ (StaggerTableLayout.slots_lt 2 (by decide))) (by norm_num))

/-- The emitted48-store writer equals the previous61-store table under precisely
13clean source-word bounds and the four-byte exposed-gap invariant. -/
theorem writerMemory_getD_resultMemoryD (memory : ByteArray) (words : Nat → UInt256)
    (hclean : ∀ i, i < 16 → (words i).toNat < 2 ^ 112)
    (hgap : PairStoreGap.GapClear memory) (q : Nat) (hq : q < 50 ∨ 54 ≤ q) :
    (Pair13WriterRaw.writerMemory memory words)[q]?.getD 0
      = (resultMemoryD memory words)[q]?.getD 0 := by
  symm
  change (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord memory 1080 (words 5)) 1062 (words 13)) 1044 (words 6)) 1026 (words 6)) 1008 (words 15)) 990 (words 15)) 972 (words 3)) 954 (words 3)) 936 (words 8)) 918 (words 8)) 900 (words 9)) 882 (words 3)) 864 (words 11)) 846 (words 3)) 828 (words 9)) 810 (words 9)) 792 (words 1)) 774 (words 1)) 756 (words 9)) 738 (words 8)) 720 (words 5)) 702 (words 5)) 684 (words 6)) 666 (words 14)) 648 (words 15)) 630 (words 10)) 612 (words 15)) 594 (words 11)) 576 (words 11)) 558 (words 8)) 540 (words 1)) 522 (words 0)) 504 (words 1)) 486 (words 5)) 468 (words 1)) 450 (words 12)) 432 (words 12)) 414 (words 6)) 396 (words 4)) 378 (words 4)) 360 (words 2)) 342 (words 2)) 324 (words 10)) 306 (words 10)) 288 (words 7)) 270 (words 15)) 252 (words 7)) 234 (words 7)) 216 (words 10)) 198 (words 13)) 180 (words 13)) 162 (words 14)) 144 (words 14)) 126 (words 11)) 108 (words 5)) 90 (words 12)) 72 (words 4)) 54 (words 0)) 36 (words 0)) 18 (words 4)) 0 (Pair13WriterRaw.dualW words 6))[q]?.getD 0 = (Pair13WriterRaw.writerMemory memory words)[q]?.getD 0
  have hm162 := PairStoreMerge.three_store_merge
    (StaggerTableMemory.storeDescending memory (StaggerTableLayout.tableWords words) 10 51)
    162 (words 14) (words 11)
    (by decide) (hclean 14 (by decide))
    (by simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub] using
      prefix_gap memory words 8 (by decide) hgap)
  change (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord memory 1080 (words 5)) 1062 (words 13)) 1044 (words 6)) 1026 (words 6)) 1008 (words 15)) 990 (words 15)) 972 (words 3)) 954 (words 3)) 936 (words 8)) 918 (words 8)) 900 (words 9)) 882 (words 3)) 864 (words 11)) 846 (words 3)) 828 (words 9)) 810 (words 9)) 792 (words 1)) 774 (words 1)) 756 (words 9)) 738 (words 8)) 720 (words 5)) 702 (words 5)) 684 (words 6)) 666 (words 14)) 648 (words 15)) 630 (words 10)) 612 (words 15)) 594 (words 11)) 576 (words 11)) 558 (words 8)) 540 (words 1)) 522 (words 0)) 504 (words 1)) 486 (words 5)) 468 (words 1)) 450 (words 12)) 432 (words 12)) 414 (words 6)) 396 (words 4)) 378 (words 4)) 360 (words 2)) 342 (words 2)) 324 (words 10)) 306 (words 10)) 288 (words 7)) 270 (words 15)) 252 (words 7)) 234 (words 7)) 216 (words 10)) 198 (words 13)) 180 (words 13)) 162 (words 14)) 144 (words 14)) 126 (words 11)) = (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord memory 1080 (words 5)) 1062 (words 13)) 1044 (words 6)) 1026 (words 6)) 1008 (words 15)) 990 (words 15)) 972 (words 3)) 954 (words 3)) 936 (words 8)) 918 (words 8)) 900 (words 9)) 882 (words 3)) 864 (words 11)) 846 (words 3)) 828 (words 9)) 810 (words 9)) 792 (words 1)) 774 (words 1)) 756 (words 9)) 738 (words 8)) 720 (words 5)) 702 (words 5)) 684 (words 6)) 666 (words 14)) 648 (words 15)) 630 (words 10)) 612 (words 15)) 594 (words 11)) 576 (words 11)) 558 (words 8)) 540 (words 1)) 522 (words 0)) 504 (words 1)) 486 (words 5)) 468 (words 1)) 450 (words 12)) 432 (words 12)) 414 (words 6)) 396 (words 4)) 378 (words 4)) 360 (words 2)) 342 (words 2)) 324 (words 10)) 306 (words 10)) 288 (words 7)) 270 (words 15)) 252 (words 7)) 234 (words 7)) 216 (words 10)) 198 (words 13)) 180 (words 13)) 162 (UInt256.mul (words 14) (UInt256.ofNat (2 ^ 144 + 1)))) 126 (words 11)) at hm162
  rw [hm162]
  have hm198 := PairStoreMerge.three_store_merge
    (StaggerTableMemory.storeDescending memory (StaggerTableLayout.tableWords words) 12 49)
    198 (words 13) (UInt256.mul (words 14) (UInt256.ofNat (2 ^ 144 + 1)))
    (by decide) (hclean 13 (by decide))
    (by simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub] using
      prefix_gap memory words 10 (by decide) hgap)
  change (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord memory 1080 (words 5)) 1062 (words 13)) 1044 (words 6)) 1026 (words 6)) 1008 (words 15)) 990 (words 15)) 972 (words 3)) 954 (words 3)) 936 (words 8)) 918 (words 8)) 900 (words 9)) 882 (words 3)) 864 (words 11)) 846 (words 3)) 828 (words 9)) 810 (words 9)) 792 (words 1)) 774 (words 1)) 756 (words 9)) 738 (words 8)) 720 (words 5)) 702 (words 5)) 684 (words 6)) 666 (words 14)) 648 (words 15)) 630 (words 10)) 612 (words 15)) 594 (words 11)) 576 (words 11)) 558 (words 8)) 540 (words 1)) 522 (words 0)) 504 (words 1)) 486 (words 5)) 468 (words 1)) 450 (words 12)) 432 (words 12)) 414 (words 6)) 396 (words 4)) 378 (words 4)) 360 (words 2)) 342 (words 2)) 324 (words 10)) 306 (words 10)) 288 (words 7)) 270 (words 15)) 252 (words 7)) 234 (words 7)) 216 (words 10)) 198 (words 13)) 180 (words 13)) 162 (UInt256.mul (words 14) (UInt256.ofNat (2 ^ 144 + 1)))) = (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord memory 1080 (words 5)) 1062 (words 13)) 1044 (words 6)) 1026 (words 6)) 1008 (words 15)) 990 (words 15)) 972 (words 3)) 954 (words 3)) 936 (words 8)) 918 (words 8)) 900 (words 9)) 882 (words 3)) 864 (words 11)) 846 (words 3)) 828 (words 9)) 810 (words 9)) 792 (words 1)) 774 (words 1)) 756 (words 9)) 738 (words 8)) 720 (words 5)) 702 (words 5)) 684 (words 6)) 666 (words 14)) 648 (words 15)) 630 (words 10)) 612 (words 15)) 594 (words 11)) 576 (words 11)) 558 (words 8)) 540 (words 1)) 522 (words 0)) 504 (words 1)) 486 (words 5)) 468 (words 1)) 450 (words 12)) 432 (words 12)) 414 (words 6)) 396 (words 4)) 378 (words 4)) 360 (words 2)) 342 (words 2)) 324 (words 10)) 306 (words 10)) 288 (words 7)) 270 (words 15)) 252 (words 7)) 234 (words 7)) 216 (words 10)) 198 (UInt256.mul (words 13) (UInt256.ofNat (2 ^ 144 + 1)))) 162 (UInt256.mul (words 14) (UInt256.ofNat (2 ^ 144 + 1)))) at hm198
  rw [hm198]
  have hm252 := PairStoreMerge.three_store_merge
    (StaggerTableMemory.storeDescending memory (StaggerTableLayout.tableWords words) 15 46)
    252 (words 7) (words 10)
    (by decide) (hclean 7 (by decide))
    (by simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub] using
      prefix_gap memory words 13 (by decide) hgap)
  change (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord memory 1080 (words 5)) 1062 (words 13)) 1044 (words 6)) 1026 (words 6)) 1008 (words 15)) 990 (words 15)) 972 (words 3)) 954 (words 3)) 936 (words 8)) 918 (words 8)) 900 (words 9)) 882 (words 3)) 864 (words 11)) 846 (words 3)) 828 (words 9)) 810 (words 9)) 792 (words 1)) 774 (words 1)) 756 (words 9)) 738 (words 8)) 720 (words 5)) 702 (words 5)) 684 (words 6)) 666 (words 14)) 648 (words 15)) 630 (words 10)) 612 (words 15)) 594 (words 11)) 576 (words 11)) 558 (words 8)) 540 (words 1)) 522 (words 0)) 504 (words 1)) 486 (words 5)) 468 (words 1)) 450 (words 12)) 432 (words 12)) 414 (words 6)) 396 (words 4)) 378 (words 4)) 360 (words 2)) 342 (words 2)) 324 (words 10)) 306 (words 10)) 288 (words 7)) 270 (words 15)) 252 (words 7)) 234 (words 7)) 216 (words 10)) = (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord memory 1080 (words 5)) 1062 (words 13)) 1044 (words 6)) 1026 (words 6)) 1008 (words 15)) 990 (words 15)) 972 (words 3)) 954 (words 3)) 936 (words 8)) 918 (words 8)) 900 (words 9)) 882 (words 3)) 864 (words 11)) 846 (words 3)) 828 (words 9)) 810 (words 9)) 792 (words 1)) 774 (words 1)) 756 (words 9)) 738 (words 8)) 720 (words 5)) 702 (words 5)) 684 (words 6)) 666 (words 14)) 648 (words 15)) 630 (words 10)) 612 (words 15)) 594 (words 11)) 576 (words 11)) 558 (words 8)) 540 (words 1)) 522 (words 0)) 504 (words 1)) 486 (words 5)) 468 (words 1)) 450 (words 12)) 432 (words 12)) 414 (words 6)) 396 (words 4)) 378 (words 4)) 360 (words 2)) 342 (words 2)) 324 (words 10)) 306 (words 10)) 288 (words 7)) 270 (words 15)) 252 (UInt256.mul (words 7) (UInt256.ofNat (2 ^ 144 + 1)))) 216 (words 10)) at hm252
  rw [hm252]
  have hm324 := PairStoreMerge.three_store_merge
    (StaggerTableMemory.storeDescending memory (StaggerTableLayout.tableWords words) 19 42)
    324 (words 10) (words 7)
    (by decide) (hclean 10 (by decide))
    (by simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub] using
      prefix_gap memory words 17 (by decide) hgap)
  change (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord memory 1080 (words 5)) 1062 (words 13)) 1044 (words 6)) 1026 (words 6)) 1008 (words 15)) 990 (words 15)) 972 (words 3)) 954 (words 3)) 936 (words 8)) 918 (words 8)) 900 (words 9)) 882 (words 3)) 864 (words 11)) 846 (words 3)) 828 (words 9)) 810 (words 9)) 792 (words 1)) 774 (words 1)) 756 (words 9)) 738 (words 8)) 720 (words 5)) 702 (words 5)) 684 (words 6)) 666 (words 14)) 648 (words 15)) 630 (words 10)) 612 (words 15)) 594 (words 11)) 576 (words 11)) 558 (words 8)) 540 (words 1)) 522 (words 0)) 504 (words 1)) 486 (words 5)) 468 (words 1)) 450 (words 12)) 432 (words 12)) 414 (words 6)) 396 (words 4)) 378 (words 4)) 360 (words 2)) 342 (words 2)) 324 (words 10)) 306 (words 10)) 288 (words 7)) = (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord memory 1080 (words 5)) 1062 (words 13)) 1044 (words 6)) 1026 (words 6)) 1008 (words 15)) 990 (words 15)) 972 (words 3)) 954 (words 3)) 936 (words 8)) 918 (words 8)) 900 (words 9)) 882 (words 3)) 864 (words 11)) 846 (words 3)) 828 (words 9)) 810 (words 9)) 792 (words 1)) 774 (words 1)) 756 (words 9)) 738 (words 8)) 720 (words 5)) 702 (words 5)) 684 (words 6)) 666 (words 14)) 648 (words 15)) 630 (words 10)) 612 (words 15)) 594 (words 11)) 576 (words 11)) 558 (words 8)) 540 (words 1)) 522 (words 0)) 504 (words 1)) 486 (words 5)) 468 (words 1)) 450 (words 12)) 432 (words 12)) 414 (words 6)) 396 (words 4)) 378 (words 4)) 360 (words 2)) 342 (words 2)) 324 (UInt256.mul (words 10) (UInt256.ofNat (2 ^ 144 + 1)))) 288 (words 7)) at hm324
  rw [hm324]
  have hm360 := PairStoreMerge.three_store_merge
    (StaggerTableMemory.storeDescending memory (StaggerTableLayout.tableWords words) 21 40)
    360 (words 2) (UInt256.mul (words 10) (UInt256.ofNat (2 ^ 144 + 1)))
    (by decide) (hclean 2 (by decide))
    (by simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub] using
      prefix_gap memory words 19 (by decide) hgap)
  change (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord memory 1080 (words 5)) 1062 (words 13)) 1044 (words 6)) 1026 (words 6)) 1008 (words 15)) 990 (words 15)) 972 (words 3)) 954 (words 3)) 936 (words 8)) 918 (words 8)) 900 (words 9)) 882 (words 3)) 864 (words 11)) 846 (words 3)) 828 (words 9)) 810 (words 9)) 792 (words 1)) 774 (words 1)) 756 (words 9)) 738 (words 8)) 720 (words 5)) 702 (words 5)) 684 (words 6)) 666 (words 14)) 648 (words 15)) 630 (words 10)) 612 (words 15)) 594 (words 11)) 576 (words 11)) 558 (words 8)) 540 (words 1)) 522 (words 0)) 504 (words 1)) 486 (words 5)) 468 (words 1)) 450 (words 12)) 432 (words 12)) 414 (words 6)) 396 (words 4)) 378 (words 4)) 360 (words 2)) 342 (words 2)) 324 (UInt256.mul (words 10) (UInt256.ofNat (2 ^ 144 + 1)))) = (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord memory 1080 (words 5)) 1062 (words 13)) 1044 (words 6)) 1026 (words 6)) 1008 (words 15)) 990 (words 15)) 972 (words 3)) 954 (words 3)) 936 (words 8)) 918 (words 8)) 900 (words 9)) 882 (words 3)) 864 (words 11)) 846 (words 3)) 828 (words 9)) 810 (words 9)) 792 (words 1)) 774 (words 1)) 756 (words 9)) 738 (words 8)) 720 (words 5)) 702 (words 5)) 684 (words 6)) 666 (words 14)) 648 (words 15)) 630 (words 10)) 612 (words 15)) 594 (words 11)) 576 (words 11)) 558 (words 8)) 540 (words 1)) 522 (words 0)) 504 (words 1)) 486 (words 5)) 468 (words 1)) 450 (words 12)) 432 (words 12)) 414 (words 6)) 396 (words 4)) 378 (words 4)) 360 (UInt256.mul (words 2) (UInt256.ofNat (2 ^ 144 + 1)))) 324 (UInt256.mul (words 10) (UInt256.ofNat (2 ^ 144 + 1)))) at hm360
  rw [hm360]
  have hm396 := PairStoreMerge.three_store_merge
    (StaggerTableMemory.storeDescending memory (StaggerTableLayout.tableWords words) 23 38)
    396 (words 4) (UInt256.mul (words 2) (UInt256.ofNat (2 ^ 144 + 1)))
    (by decide) (hclean 4 (by decide))
    (by simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub] using
      prefix_gap memory words 21 (by decide) hgap)
  change (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord memory 1080 (words 5)) 1062 (words 13)) 1044 (words 6)) 1026 (words 6)) 1008 (words 15)) 990 (words 15)) 972 (words 3)) 954 (words 3)) 936 (words 8)) 918 (words 8)) 900 (words 9)) 882 (words 3)) 864 (words 11)) 846 (words 3)) 828 (words 9)) 810 (words 9)) 792 (words 1)) 774 (words 1)) 756 (words 9)) 738 (words 8)) 720 (words 5)) 702 (words 5)) 684 (words 6)) 666 (words 14)) 648 (words 15)) 630 (words 10)) 612 (words 15)) 594 (words 11)) 576 (words 11)) 558 (words 8)) 540 (words 1)) 522 (words 0)) 504 (words 1)) 486 (words 5)) 468 (words 1)) 450 (words 12)) 432 (words 12)) 414 (words 6)) 396 (words 4)) 378 (words 4)) 360 (UInt256.mul (words 2) (UInt256.ofNat (2 ^ 144 + 1)))) = (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord memory 1080 (words 5)) 1062 (words 13)) 1044 (words 6)) 1026 (words 6)) 1008 (words 15)) 990 (words 15)) 972 (words 3)) 954 (words 3)) 936 (words 8)) 918 (words 8)) 900 (words 9)) 882 (words 3)) 864 (words 11)) 846 (words 3)) 828 (words 9)) 810 (words 9)) 792 (words 1)) 774 (words 1)) 756 (words 9)) 738 (words 8)) 720 (words 5)) 702 (words 5)) 684 (words 6)) 666 (words 14)) 648 (words 15)) 630 (words 10)) 612 (words 15)) 594 (words 11)) 576 (words 11)) 558 (words 8)) 540 (words 1)) 522 (words 0)) 504 (words 1)) 486 (words 5)) 468 (words 1)) 450 (words 12)) 432 (words 12)) 414 (words 6)) 396 (UInt256.mul (words 4) (UInt256.ofNat (2 ^ 144 + 1)))) 360 (UInt256.mul (words 2) (UInt256.ofNat (2 ^ 144 + 1)))) at hm396
  rw [hm396]
  have hm450 := PairStoreMerge.three_store_merge
    (StaggerTableMemory.storeDescending memory (StaggerTableLayout.tableWords words) 26 35)
    450 (words 12) (words 6)
    (by decide) (hclean 12 (by decide))
    (by simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub] using
      prefix_gap memory words 24 (by decide) hgap)
  change (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord memory 1080 (words 5)) 1062 (words 13)) 1044 (words 6)) 1026 (words 6)) 1008 (words 15)) 990 (words 15)) 972 (words 3)) 954 (words 3)) 936 (words 8)) 918 (words 8)) 900 (words 9)) 882 (words 3)) 864 (words 11)) 846 (words 3)) 828 (words 9)) 810 (words 9)) 792 (words 1)) 774 (words 1)) 756 (words 9)) 738 (words 8)) 720 (words 5)) 702 (words 5)) 684 (words 6)) 666 (words 14)) 648 (words 15)) 630 (words 10)) 612 (words 15)) 594 (words 11)) 576 (words 11)) 558 (words 8)) 540 (words 1)) 522 (words 0)) 504 (words 1)) 486 (words 5)) 468 (words 1)) 450 (words 12)) 432 (words 12)) 414 (words 6)) = (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord memory 1080 (words 5)) 1062 (words 13)) 1044 (words 6)) 1026 (words 6)) 1008 (words 15)) 990 (words 15)) 972 (words 3)) 954 (words 3)) 936 (words 8)) 918 (words 8)) 900 (words 9)) 882 (words 3)) 864 (words 11)) 846 (words 3)) 828 (words 9)) 810 (words 9)) 792 (words 1)) 774 (words 1)) 756 (words 9)) 738 (words 8)) 720 (words 5)) 702 (words 5)) 684 (words 6)) 666 (words 14)) 648 (words 15)) 630 (words 10)) 612 (words 15)) 594 (words 11)) 576 (words 11)) 558 (words 8)) 540 (words 1)) 522 (words 0)) 504 (words 1)) 486 (words 5)) 468 (words 1)) 450 (UInt256.mul (words 12) (UInt256.ofNat (2 ^ 144 + 1)))) 414 (words 6)) at hm450
  rw [hm450]
  have hm594 := PairStoreMerge.three_store_merge
    (StaggerTableMemory.storeDescending memory (StaggerTableLayout.tableWords words) 34 27)
    594 (words 11) (words 8)
    (by decide) (hclean 11 (by decide))
    (by simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub] using
      prefix_gap memory words 32 (by decide) hgap)
  change (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord memory 1080 (words 5)) 1062 (words 13)) 1044 (words 6)) 1026 (words 6)) 1008 (words 15)) 990 (words 15)) 972 (words 3)) 954 (words 3)) 936 (words 8)) 918 (words 8)) 900 (words 9)) 882 (words 3)) 864 (words 11)) 846 (words 3)) 828 (words 9)) 810 (words 9)) 792 (words 1)) 774 (words 1)) 756 (words 9)) 738 (words 8)) 720 (words 5)) 702 (words 5)) 684 (words 6)) 666 (words 14)) 648 (words 15)) 630 (words 10)) 612 (words 15)) 594 (words 11)) 576 (words 11)) 558 (words 8)) = (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord memory 1080 (words 5)) 1062 (words 13)) 1044 (words 6)) 1026 (words 6)) 1008 (words 15)) 990 (words 15)) 972 (words 3)) 954 (words 3)) 936 (words 8)) 918 (words 8)) 900 (words 9)) 882 (words 3)) 864 (words 11)) 846 (words 3)) 828 (words 9)) 810 (words 9)) 792 (words 1)) 774 (words 1)) 756 (words 9)) 738 (words 8)) 720 (words 5)) 702 (words 5)) 684 (words 6)) 666 (words 14)) 648 (words 15)) 630 (words 10)) 612 (words 15)) 594 (UInt256.mul (words 11) (UInt256.ofNat (2 ^ 144 + 1)))) 558 (words 8)) at hm594
  rw [hm594]
  have hm720 := PairStoreMerge.three_store_merge
    (StaggerTableMemory.storeDescending memory (StaggerTableLayout.tableWords words) 41 20)
    720 (words 5) (words 6)
    (by decide) (hclean 5 (by decide))
    (by simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub] using
      prefix_gap memory words 39 (by decide) hgap)
  change (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord memory 1080 (words 5)) 1062 (words 13)) 1044 (words 6)) 1026 (words 6)) 1008 (words 15)) 990 (words 15)) 972 (words 3)) 954 (words 3)) 936 (words 8)) 918 (words 8)) 900 (words 9)) 882 (words 3)) 864 (words 11)) 846 (words 3)) 828 (words 9)) 810 (words 9)) 792 (words 1)) 774 (words 1)) 756 (words 9)) 738 (words 8)) 720 (words 5)) 702 (words 5)) 684 (words 6)) = (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord memory 1080 (words 5)) 1062 (words 13)) 1044 (words 6)) 1026 (words 6)) 1008 (words 15)) 990 (words 15)) 972 (words 3)) 954 (words 3)) 936 (words 8)) 918 (words 8)) 900 (words 9)) 882 (words 3)) 864 (words 11)) 846 (words 3)) 828 (words 9)) 810 (words 9)) 792 (words 1)) 774 (words 1)) 756 (words 9)) 738 (words 8)) 720 (UInt256.mul (words 5) (UInt256.ofNat (2 ^ 144 + 1)))) 684 (words 6)) at hm720
  rw [hm720]
  have hm792 := PairStoreMerge.three_store_merge
    (StaggerTableMemory.storeDescending memory (StaggerTableLayout.tableWords words) 45 16)
    792 (words 1) (words 9)
    (by decide) (hclean 1 (by decide))
    (by simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub] using
      prefix_gap memory words 43 (by decide) hgap)
  change (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord memory 1080 (words 5)) 1062 (words 13)) 1044 (words 6)) 1026 (words 6)) 1008 (words 15)) 990 (words 15)) 972 (words 3)) 954 (words 3)) 936 (words 8)) 918 (words 8)) 900 (words 9)) 882 (words 3)) 864 (words 11)) 846 (words 3)) 828 (words 9)) 810 (words 9)) 792 (words 1)) 774 (words 1)) 756 (words 9)) = (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord memory 1080 (words 5)) 1062 (words 13)) 1044 (words 6)) 1026 (words 6)) 1008 (words 15)) 990 (words 15)) 972 (words 3)) 954 (words 3)) 936 (words 8)) 918 (words 8)) 900 (words 9)) 882 (words 3)) 864 (words 11)) 846 (words 3)) 828 (words 9)) 810 (words 9)) 792 (UInt256.mul (words 1) (UInt256.ofNat (2 ^ 144 + 1)))) 756 (words 9)) at hm792
  rw [hm792]
  have hm828 := PairStoreMerge.three_store_merge
    (StaggerTableMemory.storeDescending memory (StaggerTableLayout.tableWords words) 47 14)
    828 (words 9) (UInt256.mul (words 1) (UInt256.ofNat (2 ^ 144 + 1)))
    (by decide) (hclean 9 (by decide))
    (by simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub] using
      prefix_gap memory words 45 (by decide) hgap)
  change (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord memory 1080 (words 5)) 1062 (words 13)) 1044 (words 6)) 1026 (words 6)) 1008 (words 15)) 990 (words 15)) 972 (words 3)) 954 (words 3)) 936 (words 8)) 918 (words 8)) 900 (words 9)) 882 (words 3)) 864 (words 11)) 846 (words 3)) 828 (words 9)) 810 (words 9)) 792 (UInt256.mul (words 1) (UInt256.ofNat (2 ^ 144 + 1)))) = (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord memory 1080 (words 5)) 1062 (words 13)) 1044 (words 6)) 1026 (words 6)) 1008 (words 15)) 990 (words 15)) 972 (words 3)) 954 (words 3)) 936 (words 8)) 918 (words 8)) 900 (words 9)) 882 (words 3)) 864 (words 11)) 846 (words 3)) 828 (UInt256.mul (words 9) (UInt256.ofNat (2 ^ 144 + 1)))) 792 (UInt256.mul (words 1) (UInt256.ofNat (2 ^ 144 + 1)))) at hm828
  rw [hm828]
  have hm936 := PairStoreMerge.three_store_merge
    (StaggerTableMemory.storeDescending memory (StaggerTableLayout.tableWords words) 53 8)
    936 (words 8) (words 9)
    (by decide) (hclean 8 (by decide))
    (by simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub] using
      prefix_gap memory words 51 (by decide) hgap)
  change (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord memory 1080 (words 5)) 1062 (words 13)) 1044 (words 6)) 1026 (words 6)) 1008 (words 15)) 990 (words 15)) 972 (words 3)) 954 (words 3)) 936 (words 8)) 918 (words 8)) 900 (words 9)) = (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord memory 1080 (words 5)) 1062 (words 13)) 1044 (words 6)) 1026 (words 6)) 1008 (words 15)) 990 (words 15)) 972 (words 3)) 954 (words 3)) 936 (UInt256.mul (words 8) (UInt256.ofNat (2 ^ 144 + 1)))) 900 (words 9)) at hm936
  rw [hm936]
  have hm972 := PairStoreMerge.three_store_merge
    (StaggerTableMemory.storeDescending memory (StaggerTableLayout.tableWords words) 55 6)
    972 (words 3) (UInt256.mul (words 8) (UInt256.ofNat (2 ^ 144 + 1)))
    (by decide) (hclean 3 (by decide))
    (by simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub] using
      prefix_gap memory words 53 (by decide) hgap)
  change (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord memory 1080 (words 5)) 1062 (words 13)) 1044 (words 6)) 1026 (words 6)) 1008 (words 15)) 990 (words 15)) 972 (words 3)) 954 (words 3)) 936 (UInt256.mul (words 8) (UInt256.ofNat (2 ^ 144 + 1)))) = (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord memory 1080 (words 5)) 1062 (words 13)) 1044 (words 6)) 1026 (words 6)) 1008 (words 15)) 990 (words 15)) 972 (UInt256.mul (words 3) (UInt256.ofNat (2 ^ 144 + 1)))) 936 (UInt256.mul (words 8) (UInt256.ofNat (2 ^ 144 + 1)))) at hm972
  rw [hm972]
  have hm1008 := PairStoreMerge.three_store_merge
    (StaggerTableMemory.storeDescending memory (StaggerTableLayout.tableWords words) 57 4)
    1008 (words 15) (UInt256.mul (words 3) (UInt256.ofNat (2 ^ 144 + 1)))
    (by decide) (hclean 15 (by decide))
    (by simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub] using
      prefix_gap memory words 55 (by decide) hgap)
  change (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord memory 1080 (words 5)) 1062 (words 13)) 1044 (words 6)) 1026 (words 6)) 1008 (words 15)) 990 (words 15)) 972 (UInt256.mul (words 3) (UInt256.ofNat (2 ^ 144 + 1)))) = (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord memory 1080 (words 5)) 1062 (words 13)) 1044 (words 6)) 1026 (words 6)) 1008 (UInt256.mul (words 15) (UInt256.ofNat (2 ^ 144 + 1)))) 972 (UInt256.mul (words 3) (UInt256.ofNat (2 ^ 144 + 1)))) at hm1008
  rw [hm1008]
  have hm1044 := PairStoreMerge.three_store_merge
    (StaggerTableMemory.storeDescending memory (StaggerTableLayout.tableWords words) 59 2)
    1044 (words 6) (UInt256.mul (words 15) (UInt256.ofNat (2 ^ 144 + 1)))
    (by decide) (hclean 6 (by decide))
    (by simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub] using
      prefix_gap memory words 57 (by decide) hgap)
  change (writeWord (writeWord (writeWord (writeWord (writeWord memory 1080 (words 5)) 1062 (words 13)) 1044 (words 6)) 1026 (words 6)) 1008 (UInt256.mul (words 15) (UInt256.ofNat (2 ^ 144 + 1)))) = (writeWord (writeWord (writeWord (writeWord memory 1080 (words 5)) 1062 (words 13)) 1044 (UInt256.mul (words 6) (UInt256.ofNat (2 ^ 144 + 1)))) 1008 (UInt256.mul (words 15) (UInt256.ofNat (2 ^ 144 + 1)))) at hm1044
  rw [hm1044]
  refine Eq.trans (PairStoreMerge.writeWord_getD_congr _ _ 0 _ q
    (PairStoreMerge.two_store_residual _ 54 36 18 (words 0) (words 4) q rfl rfl
      (hclean 0 (by decide)) (by omega))) ?_
  simp only [Pair13WriterRaw.writerMemory, Pair13WriterRaw.writeChain,
    Pair13WriterRaw.writerWrites, Pair13WriterRaw.dualW, List.foldl_cons, List.foldl_nil, coefficient_eq,
    RawExpressionAC.mul_comm]

#print axioms writerMemory_getD_resultMemoryD
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Pair13Memory
