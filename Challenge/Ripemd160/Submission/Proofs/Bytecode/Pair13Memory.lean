import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairStoreGap
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairStoreMerge
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Pair13WriterRaw
import Challenge.Ripemd160.Submission.Proofs.Bytecode.JD8Merge

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

/-!
# The 48-store writer image, as a SLOT-indexed table

The writer emits 48 stores where the model has 61: the thirteen `lowerPairSlots` are elided and
recovered from the dual lane of the slot above.  With clean words that is invisible, because an
elided slot and its pair hold the same 32-bit field.  With junk it is not: the surviving slot
keeps the load's LOW 144 bits and the elided slot receives its HIGH half, so the two carry the
same schedule word with DIFFERENT junk.

`StaggerTableLayout.tableWords words j = words slots[j]!` is word-indexed and cannot express
that.  `tableJ` is the slot-indexed table the writer actually leaves, and the merge that licenses
it — `JD8Merge.three_store_merge_hi` — needs NO bound on the source word at all: taking the
elided slot's modelled value to be `hi144` of the stored one makes all three side conditions
free.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Pair13Memory
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open PairedScheduleMemory

/-- The table image the 48-store writer leaves, indexed by SLOT.  An elided slot holds the high
half of the value stored one slot above it; every other slot holds what the pool produced. -/
def tableJ (words : Nat → UInt256) (j : Nat) : UInt256 :=
  if j ∈ PairStoreGap.lowerPairSlots then
    JD8Merge.hi144 (Pair13WriterRaw.dualW words StaggerTableLayout.slots[j]!)
  else Pair13WriterRaw.dualW words StaggerTableLayout.slots[j]!

def resultMemoryJ (memory : ByteArray) (words : Nat → UInt256) : ByteArray :=
  StaggerTableMemory.storeDescending memory (tableJ words) 0 61

/-- The thirteen elided slots are adjacent EQUAL pairs (`slots[j] = slots[j+1]`), which is what
makes the elided value the high half of its neighbour's. -/
theorem elide_eq (words : Nat → UInt256) (j : Nat) (hj : j ∈ PairStoreGap.lowerPairSlots) :
    tableJ words j = JD8Merge.hi144 (tableJ words (j + 1)) := by
  simp only [PairStoreGap.lowerPairSlots, List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num [tableJ, PairStoreGap.lowerPairSlots, StaggerTableLayout.slots]

/-- The four exposed gap bytes below a merged store are still zero in the chain above it. -/
theorem prefix_gap (memory : ByteArray) (words : Nat → UInt256)
    (j : Nat) (hj : j ∈ PairStoreGap.lowerPairSlots) (hgap : PairStoreGap.GapClear memory) :
    ∀ i, 18 * (j + 1) - 4 ≤ i → i < 18 * (j + 1) →
      (StaggerTableMemory.storeDescending memory (tableJ words)
        (j + 2) (59 - j))[i]?.getD 0 = 0 := by
  intro i hi0 hi1
  rw [StaggerTableMemory.getD_storeDescending_outside _ _ _ _ _
    (by intro k hk0 hk1; left; omega)]
  have hz := hgap j hj (i - 18 * j) (by omega) (by omega)
  simpa only [Nat.add_sub_of_le (by omega : 18 * j ≤ i)] using hz

/-- **The writer bridge.**  The emitted 48-store chain leaves exactly the slot-indexed table,
under the four-byte exposed-gap invariant and NO bound on any source word. -/
theorem writerMemory_eq_resultMemoryJ (memory : ByteArray) (words : Nat → UInt256)
    (hgap : PairStoreGap.GapClear memory) :
    Pair13WriterRaw.writerMemory memory words = resultMemoryJ memory words := by
  symm
  rw [resultMemoryJ]
  have g8 := prefix_gap memory words 8 (by decide) hgap
  have g10 := prefix_gap memory words 10 (by decide) hgap
  have g13 := prefix_gap memory words 13 (by decide) hgap
  have g17 := prefix_gap memory words 17 (by decide) hgap
  have g21 := prefix_gap memory words 21 (by decide) hgap
  have g24 := prefix_gap memory words 24 (by decide) hgap
  have g32 := prefix_gap memory words 32 (by decide) hgap
  have g39 := prefix_gap memory words 39 (by decide) hgap
  have g45 := prefix_gap memory words 45 (by decide) hgap
  have g51 := prefix_gap memory words 51 (by decide) hgap
  have g53 := prefix_gap memory words 53 (by decide) hgap
  have g55 := prefix_gap memory words 55 (by decide) hgap
  have g57 := prefix_gap memory words 57 (by decide) hgap
  simp only [StaggerTableMemory.storeDescending, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub]
    at g8 g10 g13 g17 g21 g24 g32 g39 g45 g51 g53 g55 g57 ⊢
  simp only [elide_eq words 8 (by decide),
    elide_eq words 10 (by decide),
    elide_eq words 13 (by decide),
    elide_eq words 17 (by decide),
    elide_eq words 21 (by decide),
    elide_eq words 24 (by decide),
    elide_eq words 32 (by decide),
    elide_eq words 39 (by decide),
    elide_eq words 45 (by decide),
    elide_eq words 51 (by decide),
    elide_eq words 53 (by decide),
    elide_eq words 55 (by decide),
    elide_eq words 57 (by decide)]
    at g8 g10 g13 g17 g21 g24 g32 g39 g45 g51 g53 g55 g57 ⊢
  rw [JD8Merge.three_store_merge_hi (a := 162) (ha := by decide) (hgap := g8),
      JD8Merge.three_store_merge_hi (a := 198) (ha := by decide) (hgap := g10),
      JD8Merge.three_store_merge_hi (a := 252) (ha := by decide) (hgap := g13),
      JD8Merge.three_store_merge_hi (a := 324) (ha := by decide) (hgap := g17),
      JD8Merge.three_store_merge_hi (a := 396) (ha := by decide) (hgap := g21),
      JD8Merge.three_store_merge_hi (a := 450) (ha := by decide) (hgap := g24),
      JD8Merge.three_store_merge_hi (a := 594) (ha := by decide) (hgap := g32),
      JD8Merge.three_store_merge_hi (a := 720) (ha := by decide) (hgap := g39),
      JD8Merge.three_store_merge_hi (a := 828) (ha := by decide) (hgap := g45),
      JD8Merge.three_store_merge_hi (a := 936) (ha := by decide) (hgap := g51),
      JD8Merge.three_store_merge_hi (a := 972) (ha := by decide) (hgap := g53),
      JD8Merge.three_store_merge_hi (a := 1008) (ha := by decide) (hgap := g55),
      JD8Merge.three_store_merge_hi (a := 1044) (ha := by decide) (hgap := g57)]
  have e0 : tableJ words 0 = Pair13WriterRaw.dualW words 6 := by
    norm_num [tableJ, PairStoreGap.lowerPairSlots, StaggerTableLayout.slots]
  have e1 : tableJ words 1 = Pair13WriterRaw.dualW words 4 := by
    norm_num [tableJ, PairStoreGap.lowerPairSlots, StaggerTableLayout.slots]
  have e2 : tableJ words 2 = Pair13WriterRaw.dualW words 0 := by
    norm_num [tableJ, PairStoreGap.lowerPairSlots, StaggerTableLayout.slots]
  have e3 : tableJ words 3 = Pair13WriterRaw.dualW words 0 := by
    norm_num [tableJ, PairStoreGap.lowerPairSlots, StaggerTableLayout.slots]
  have e4 : tableJ words 4 = Pair13WriterRaw.dualW words 4 := by
    norm_num [tableJ, PairStoreGap.lowerPairSlots, StaggerTableLayout.slots]
  have e5 : tableJ words 5 = Pair13WriterRaw.dualW words 12 := by
    norm_num [tableJ, PairStoreGap.lowerPairSlots, StaggerTableLayout.slots]
  have e6 : tableJ words 6 = Pair13WriterRaw.dualW words 5 := by
    norm_num [tableJ, PairStoreGap.lowerPairSlots, StaggerTableLayout.slots]
  have e7 : tableJ words 7 = Pair13WriterRaw.dualW words 11 := by
    norm_num [tableJ, PairStoreGap.lowerPairSlots, StaggerTableLayout.slots]
  have e9 : tableJ words 9 = Pair13WriterRaw.dualW words 14 := by
    norm_num [tableJ, PairStoreGap.lowerPairSlots, StaggerTableLayout.slots]
  have e11 : tableJ words 11 = Pair13WriterRaw.dualW words 13 := by
    norm_num [tableJ, PairStoreGap.lowerPairSlots, StaggerTableLayout.slots]
  have e12 : tableJ words 12 = Pair13WriterRaw.dualW words 10 := by
    norm_num [tableJ, PairStoreGap.lowerPairSlots, StaggerTableLayout.slots]
  have e14 : tableJ words 14 = Pair13WriterRaw.dualW words 7 := by
    norm_num [tableJ, PairStoreGap.lowerPairSlots, StaggerTableLayout.slots]
  have e15 : tableJ words 15 = Pair13WriterRaw.dualW words 15 := by
    norm_num [tableJ, PairStoreGap.lowerPairSlots, StaggerTableLayout.slots]
  have e16 : tableJ words 16 = Pair13WriterRaw.dualW words 7 := by
    norm_num [tableJ, PairStoreGap.lowerPairSlots, StaggerTableLayout.slots]
  have e18 : tableJ words 18 = Pair13WriterRaw.dualW words 10 := by
    norm_num [tableJ, PairStoreGap.lowerPairSlots, StaggerTableLayout.slots]
  have e19 : tableJ words 19 = Pair13WriterRaw.dualW words 2 := by
    norm_num [tableJ, PairStoreGap.lowerPairSlots, StaggerTableLayout.slots]
  have e20 : tableJ words 20 = Pair13WriterRaw.dualW words 2 := by
    norm_num [tableJ, PairStoreGap.lowerPairSlots, StaggerTableLayout.slots]
  have e22 : tableJ words 22 = Pair13WriterRaw.dualW words 4 := by
    norm_num [tableJ, PairStoreGap.lowerPairSlots, StaggerTableLayout.slots]
  have e23 : tableJ words 23 = Pair13WriterRaw.dualW words 6 := by
    norm_num [tableJ, PairStoreGap.lowerPairSlots, StaggerTableLayout.slots]
  have e25 : tableJ words 25 = Pair13WriterRaw.dualW words 12 := by
    norm_num [tableJ, PairStoreGap.lowerPairSlots, StaggerTableLayout.slots]
  have e26 : tableJ words 26 = Pair13WriterRaw.dualW words 1 := by
    norm_num [tableJ, PairStoreGap.lowerPairSlots, StaggerTableLayout.slots]
  have e27 : tableJ words 27 = Pair13WriterRaw.dualW words 5 := by
    norm_num [tableJ, PairStoreGap.lowerPairSlots, StaggerTableLayout.slots]
  have e28 : tableJ words 28 = Pair13WriterRaw.dualW words 1 := by
    norm_num [tableJ, PairStoreGap.lowerPairSlots, StaggerTableLayout.slots]
  have e29 : tableJ words 29 = Pair13WriterRaw.dualW words 0 := by
    norm_num [tableJ, PairStoreGap.lowerPairSlots, StaggerTableLayout.slots]
  have e30 : tableJ words 30 = Pair13WriterRaw.dualW words 1 := by
    norm_num [tableJ, PairStoreGap.lowerPairSlots, StaggerTableLayout.slots]
  have e31 : tableJ words 31 = Pair13WriterRaw.dualW words 8 := by
    norm_num [tableJ, PairStoreGap.lowerPairSlots, StaggerTableLayout.slots]
  have e33 : tableJ words 33 = Pair13WriterRaw.dualW words 11 := by
    norm_num [tableJ, PairStoreGap.lowerPairSlots, StaggerTableLayout.slots]
  have e34 : tableJ words 34 = Pair13WriterRaw.dualW words 15 := by
    norm_num [tableJ, PairStoreGap.lowerPairSlots, StaggerTableLayout.slots]
  have e35 : tableJ words 35 = Pair13WriterRaw.dualW words 10 := by
    norm_num [tableJ, PairStoreGap.lowerPairSlots, StaggerTableLayout.slots]
  have e36 : tableJ words 36 = Pair13WriterRaw.dualW words 15 := by
    norm_num [tableJ, PairStoreGap.lowerPairSlots, StaggerTableLayout.slots]
  have e37 : tableJ words 37 = Pair13WriterRaw.dualW words 14 := by
    norm_num [tableJ, PairStoreGap.lowerPairSlots, StaggerTableLayout.slots]
  have e38 : tableJ words 38 = Pair13WriterRaw.dualW words 6 := by
    norm_num [tableJ, PairStoreGap.lowerPairSlots, StaggerTableLayout.slots]
  have e40 : tableJ words 40 = Pair13WriterRaw.dualW words 5 := by
    norm_num [tableJ, PairStoreGap.lowerPairSlots, StaggerTableLayout.slots]
  have e41 : tableJ words 41 = Pair13WriterRaw.dualW words 8 := by
    norm_num [tableJ, PairStoreGap.lowerPairSlots, StaggerTableLayout.slots]
  have e42 : tableJ words 42 = Pair13WriterRaw.dualW words 9 := by
    norm_num [tableJ, PairStoreGap.lowerPairSlots, StaggerTableLayout.slots]
  have e43 : tableJ words 43 = Pair13WriterRaw.dualW words 1 := by
    norm_num [tableJ, PairStoreGap.lowerPairSlots, StaggerTableLayout.slots]
  have e44 : tableJ words 44 = Pair13WriterRaw.dualW words 1 := by
    norm_num [tableJ, PairStoreGap.lowerPairSlots, StaggerTableLayout.slots]
  have e46 : tableJ words 46 = Pair13WriterRaw.dualW words 9 := by
    norm_num [tableJ, PairStoreGap.lowerPairSlots, StaggerTableLayout.slots]
  have e47 : tableJ words 47 = Pair13WriterRaw.dualW words 3 := by
    norm_num [tableJ, PairStoreGap.lowerPairSlots, StaggerTableLayout.slots]
  have e48 : tableJ words 48 = Pair13WriterRaw.dualW words 11 := by
    norm_num [tableJ, PairStoreGap.lowerPairSlots, StaggerTableLayout.slots]
  have e49 : tableJ words 49 = Pair13WriterRaw.dualW words 3 := by
    norm_num [tableJ, PairStoreGap.lowerPairSlots, StaggerTableLayout.slots]
  have e50 : tableJ words 50 = Pair13WriterRaw.dualW words 9 := by
    norm_num [tableJ, PairStoreGap.lowerPairSlots, StaggerTableLayout.slots]
  have e52 : tableJ words 52 = Pair13WriterRaw.dualW words 8 := by
    norm_num [tableJ, PairStoreGap.lowerPairSlots, StaggerTableLayout.slots]
  have e54 : tableJ words 54 = Pair13WriterRaw.dualW words 3 := by
    norm_num [tableJ, PairStoreGap.lowerPairSlots, StaggerTableLayout.slots]
  have e56 : tableJ words 56 = Pair13WriterRaw.dualW words 15 := by
    norm_num [tableJ, PairStoreGap.lowerPairSlots, StaggerTableLayout.slots]
  have e58 : tableJ words 58 = Pair13WriterRaw.dualW words 6 := by
    norm_num [tableJ, PairStoreGap.lowerPairSlots, StaggerTableLayout.slots]
  have e59 : tableJ words 59 = Pair13WriterRaw.dualW words 13 := by
    norm_num [tableJ, PairStoreGap.lowerPairSlots, StaggerTableLayout.slots]
  have e60 : tableJ words 60 = Pair13WriterRaw.dualW words 5 := by
    norm_num [tableJ, PairStoreGap.lowerPairSlots, StaggerTableLayout.slots]
  simp only [e0, e1, e2, e3, e4, e5, e6, e7, e9, e11, e12, e14, e15, e16, e18, e19, e20, e22, e23, e25, e26, e27, e28, e29, e30, e31, e33, e34, e35, e36, e37, e38, e40, e41, e42, e43, e44, e46, e47, e48, e49, e50, e52, e54, e56, e58, e59, e60, Nat.reduceSub,
    Pair13WriterRaw.writerMemory, Pair13WriterRaw.writeChain, Pair13WriterRaw.writerWrites,
    Pair13WriterRaw.sortedWrites, List.foldl_cons, List.foldl_nil]

#print axioms elide_eq
#print axioms writerMemory_eq_resultMemoryJ
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Pair13Memory
