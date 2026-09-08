import Challenge.EvmProof.Bytes
import Challenge.EvmProof.Memory
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedLoadModel
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedGapInvariant

set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 10000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedReadWindow

open EvmSemantics
open Challenge.EvmProof.Bytes

/-- The low half of an EVM word is precisely its last sixteen memory bytes. -/
theorem low_half (memory : ByteArray) (address : Nat) :
    (MachineState.readWord memory address).toNat % 2 ^ 128 =
      EVM.Precompile.bytesToNatPadded memory (address + 16) 16 := by
  rw [readWord_toNat]
  have hs := bytesToNatPadded_add memory address 16 16
  have hb := bytesToNatPadded_lt_pow memory (address + 16) 16
  have hp : (256 : Nat) ^ 16 = 2 ^ 128 := by norm_num
  rw [hp] at hs hb
  rw [hs, Nat.add_mod, Nat.mul_mod_left, Nat.zero_add,
    Nat.mod_eq_of_lt hb]
  exact Nat.mod_eq_of_lt hb

theorem low_half_write_disjoint (memory bytes : ByteArray) (address start : Nat)
    (h : address + 32 ≤ start ∨ start + bytes.size ≤ address + 16) :
    (MachineState.readWord (MachineState.writeBytes memory bytes start) address).toNat
        % 2 ^ 128 = (MachineState.readWord memory address).toNat % 2 ^ 128 := by
  rw [low_half, low_half]
  unfold EVM.Precompile.bytesToNatPadded
  rw [Challenge.EvmProof.Memory.readPadded_writeBytes_disjoint memory bytes
    (address + 16) 16 start (by omega)]

private theorem recompose (x : Nat) :
    x = (x % 2 ^ 128) ||| ((x >>> 128) <<< 128) := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 128
  · have hn : ¬128 ≤ i := by omega
    simp only [Nat.testBit_or, Nat.testBit_mod_two_pow, Nat.testBit_shiftLeft,
      hi, hn, decide_true, decide_false, Bool.true_and, Bool.false_and,
      Bool.or_false]
  · have hn : 128 ≤ i := by omega
    simp only [Nat.testBit_or, Nat.testBit_mod_two_pow, Nat.testBit_shiftLeft,
      Nat.testBit_shiftRight, hi, hn, decide_false, decide_true, Bool.false_and,
      Bool.true_and, Bool.false_or]
    congr 1
    omega

/-- Concrete sixteen-byte suffix facts suffice for both packed read shapes. -/
theorem spreadReads_of_suffixes (memory : ByteArray) (words : Nat → UInt32)
    (hl : ∀ i, i < 16 → EVM.Precompile.bytesToNatPadded memory (16 * i + 16) 16
      = (words i).toNat)
    (hr : ∀ i, i < 16 → EVM.Precompile.bytesToNatPadded memory (16 * i + 24) 16
      = (words i).toNat <<< 64) : PackedLoadModel.SpreadReads memory words := by
  constructor
  · intro i hi
    refine ⟨(MachineState.readWord memory (16 * i)).toNat >>> 128, ?_⟩
    have h := recompose (MachineState.readWord memory (16 * i)).toNat
    rw [low_half, hl i hi] at h
    exact h
  · intro i hi
    refine ⟨(MachineState.readWord memory (16 * i + 8)).toNat >>> 128, ?_⟩
    have h := recompose (MachineState.readWord memory (16 * i + 8)).toNat
    rw [low_half, show 16 * i + 8 + 16 = 16 * i + 24 by omega, hr i hi] at h
    exact h

/-- Scratch and H writes start above every low-half read, including the
eight-byte gap used by the last right load. This carries established suffix
facts across those writes; it does not assert that arbitrary memory is spread. -/
theorem spreadReads_after_high_write (memory bytes : ByteArray)
    (words : Nat → UInt32) (start : Nat) (hs : 280 ≤ start)
    (hl : ∀ i, i < 16 → EVM.Precompile.bytesToNatPadded memory (16 * i + 16) 16
      = (words i).toNat)
    (hr : ∀ i, i < 16 → EVM.Precompile.bytesToNatPadded memory (16 * i + 24) 16
      = (words i).toNat <<< 64) :
    PackedLoadModel.SpreadReads (MachineState.writeBytes memory bytes start) words := by
  apply spreadReads_of_suffixes
  · intro i hi
    unfold EVM.Precompile.bytesToNatPadded
    rw [Challenge.EvmProof.Memory.readPadded_writeBytes_disjoint memory bytes
      (16 * i + 16) 16 start (Or.inl (by omega))]
    exact hl i hi
  · intro i hi
    unfold EVM.Precompile.bytesToNatPadded
    rw [Challenge.EvmProof.Memory.readPadded_writeBytes_disjoint memory bytes
      (16 * i + 24) 16 start (Or.inl (by omega))]
    exact hr i hi

/-- Earlier descending stores may overlap a word's high half, but cannot
touch the sixteen-byte suffix used by its left packed lane. -/
theorem spread_earlier_preserves_low_half (words : Nat → UInt256)
    (n i : Nat) (hni : n ≤ i) (memory : ByteArray) :
    (MachineState.readWord (PackedGapInvariant.spreadWords words n memory)
      (16 * i)).toNat % 2 ^ 128 =
      (MachineState.readWord memory (16 * i)).toNat % 2 ^ 128 := by
  induction n generalizing memory with
  | zero => rfl
  | succ n ih =>
    rw [PackedGapInvariant.spreadWords, ih (by omega)]
    unfold PackedGapInvariant.storeWord
    apply low_half_write_disjoint
    right
    have hs : (Data.Bytes.natToBytesPadded (words n).toNat 32).size = 32 := by
      simp [Data.Bytes.natToBytesPadded, ByteArray.size]
    rw [hs]
    omega

/-- The actual descending MSTORE sequence establishes every left suffix.
Unlike a whole-word equality this remains true under the overlapping stores. -/
theorem spread_left_low_half (words : Nat → UInt256) (n i : Nat)
    (hi : i < n) (memory : ByteArray) :
    (MachineState.readWord (PackedGapInvariant.spreadWords words n memory)
      (16 * i)).toNat % 2 ^ 128 = (words i).toNat % 2 ^ 128 := by
  induction n generalizing memory with
  | zero => omega
  | succ n ih =>
    rw [PackedGapInvariant.spreadWords]
    by_cases heq : i = n
    · subst i
      rw [spread_earlier_preserves_low_half words n n (Nat.le_refl n)]
      unfold PackedGapInvariant.storeWord
      rw [Challenge.EvmProof.Memory.readWord_writeWord]
    · exact ih (by omega) _

theorem gap_read_zero (memory : ByteArray) (h : PackedGapInvariant.GapZero memory) :
    EVM.Precompile.bytesToNatPadded memory 272 8 = 0 := by
  unfold EVM.Precompile.bytesToNatPadded
  rw [Challenge.EvmProof.Memory.readPadded_congr memory ByteArray.empty 272 8
    (by intro i hi; rw [h (272 + i) (by omega) (by omega)]; rfl)]
  rw [← bytesNat_toList, readPadded_toList, ByteArray.toList_empty]
  rfl

/-- Adjacent small left suffixes force the right suffixes. Only the final
eight bytes need the separate gap invariant; no arbitrary-memory assumption. -/
theorem right_suffixes_of_left (memory : ByteArray) (words : Nat → UInt32)
    (hl : ∀ i, i < 16 → EVM.Precompile.bytesToNatPadded memory (16 * i + 16) 16
      = (words i).toNat)
    (hgap : PackedGapInvariant.GapZero memory) (i : Nat) (hi : i < 16) :
    EVM.Precompile.bytesToNatPadded memory (16 * i + 24) 16 =
      (words i).toNat <<< 64 := by
  have hsplit := bytesToNatPadded_add memory (16 * i + 16) 8 8
  have hw := (words i).toNat_lt
  norm_num only [Nat.reduceAdd, Nat.reducePow] at hsplit
  rw [hl i hi] at hsplit
  have hoff : 16 * i + 16 + 8 = 16 * i + 24 := by omega
  rw [hoff] at hsplit
  have hlow : EVM.Precompile.bytesToNatPadded memory (16 * i + 24) 8 =
      (words i).toNat := by omega
  have hnext : EVM.Precompile.bytesToNatPadded memory (16 * i + 32) 8 = 0 := by
    by_cases hn : i + 1 < 16
    · have hs := bytesToNatPadded_add memory (16 * (i + 1) + 16) 8 8
      have hb := (words (i + 1)).toNat_lt
      norm_num only [Nat.reduceAdd, Nat.reducePow] at hs
      rw [hl (i + 1) hn] at hs
      have ha : 16 * (i + 1) + 16 = 16 * i + 32 := by omega
      rw [ha] at hs
      omega
    · have he : i = 15 := by omega
      subst i
      exact gap_read_zero memory hgap
  have hout := bytesToNatPadded_add memory (16 * i + 24) 8 8
  norm_num only [Nat.reduceAdd, Nat.reducePow] at hout
  rw [hlow, show 16 * i + 24 + 8 = 16 * i + 32 by omega, hnext] at hout
  simpa [Nat.shiftLeft_eq] using hout

/-- Concrete descending word stores establish both packed read families.
The remaining caller obligation is the initial zero gap and the values placed
in these stores, not an assumed post-spread memory layout. -/
theorem spreadWords_reads (memory : ByteArray) (words : Nat → UInt256)
    (values : Nat → UInt32) (hgap : PackedGapInvariant.GapZero memory)
    (hv : ∀ i, i < 16 → (words i).toNat = (values i).toNat) :
    PackedLoadModel.SpreadReads (PackedGapInvariant.spreadWords words 16 memory)
      values := by
  have hl : ∀ i, i < 16 → EVM.Precompile.bytesToNatPadded
      (PackedGapInvariant.spreadWords words 16 memory) (16 * i + 16) 16
        = (values i).toNat := by
    intro i hi
    rw [← low_half, spread_left_low_half words 16 i hi, hv i hi]
    apply Nat.mod_eq_of_lt
    have hb := (values i).toNat_lt
    omega
  apply spreadReads_of_suffixes _ values hl
  exact right_suffixes_of_left _ values hl
    (PackedGapInvariant.spreadWords_gap words 16 (Nat.le_refl 16) memory hgap)

/-- Optional admission-friendly initialization: an explicit zero MSTORE
establishes the gap in arbitrary memory. This is not asserted to occur in
the current runtime; a candidate adding it still needs trace/oracle checks. -/
theorem clear_gap_store (memory : ByteArray) :
    PackedGapInvariant.GapZero
      (MachineState.writeBytes memory (Data.Bytes.natToBytesPadded 0 32) 272) := by
  intro i hi hj
  rw [MachineState.writeBytes_getElem?_getD,
    YulEvmCompiler.BytesLemmas.natToBytesPadded_size, if_pos (by omega),
    YulEvmCompiler.BytesLemmas.natToBytesPadded_getElem?_getD 0 32 (i - 272)
      (by omega)]
  simp

/-- The concrete spread's paired loads feed exactly the requested message lanes;
no post-layout premise is left for the round-template caller. -/
theorem loadPair_after_spread (memory : ByteArray) (words : Nat → UInt256)
    (values : Nat → UInt32) (hgap : PackedGapInvariant.GapZero memory)
    (hv : ∀ i, i < 16 → (words i).toNat = (values i).toNat)
    (i j : Nat) (hi : i < 16) (hj : j < 16) :
    let loaded := PackedLoadModel.loadPair
      (PackedGapInvariant.spreadWords words 16 memory) i j
    PackedLaneMask.lane0N loaded.toNat = (values i).toNat ∧
    PackedLaneMask.lane1N loaded.toNat = (values j).toNat ∧
    loaded.toNat % 2 ^ 64 < 2 ^ 32 := by
  exact PackedLoadModel.loadPair_spec _ values
    (spreadWords_reads memory words values hgap hv) i j hi hj

#print axioms loadPair_after_spread
#print axioms clear_gap_store
#print axioms spreadWords_reads
#print axioms right_suffixes_of_left
#print axioms gap_read_zero
#print axioms spread_left_low_half
#print axioms spread_earlier_preserves_low_half
#print axioms spreadReads_after_high_write
#print axioms low_half_write_disjoint
#print axioms spreadReads_of_suffixes

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedReadWindow
