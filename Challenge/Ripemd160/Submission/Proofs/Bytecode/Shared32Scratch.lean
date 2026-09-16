import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairStoreGap
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Pair13Endian
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Pair13PoolRaw
import Challenge.Ripemd160.Submission.Proofs.Bytecode.JD8Pool
import Challenge.Ripemd160.Submission.Proofs.Bytecode.JD8Merge

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Shared32Scratch
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open PairedScheduleMemory

def highWord : UInt256 := UInt256.ofNat (2 ^ 231 + 2 ^ 40)

def sparseMemory (memory : ByteArray) : ByteArray :=
  MachineState.writeBytes
    (MachineState.writeBytes memory (ByteArray.mk #[128]) 99)
    (ByteArray.mk #[1]) 122

theorem highWord_bytes : Data.Bytes.natToBytesPadded highWord.toNat 32 =
    ByteArray.mk #[0, 0, 0, 128, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0] := by
  apply ByteArray.ext_getElem
  · rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]; rfl
  · intro i hA hB
    have hi : i < 32 := hB
    rw [← Memory.getD0_eq_getElem _ _ hA, ← Memory.getD0_eq_getElem _ _ hB,
      YulEvmCompiler.BytesLemmas.natToBytesPadded_getElem?_getD _ _ _ hi]
    interval_cases i <;> norm_num [highWord, Word.word_toNat_ofNat] <;> rfl

/-- The sparse stores equal the upper endian scratch word on fresh scratch bytes. -/
theorem sparse_eq_writeWord (memory : ByteArray) (hsize : 128 ≤ memory.size)
    (hzero : ∀ a, 96 ≤ a → a < 128 → memory[a]?.getD 0 = 0) :
    sparseMemory memory = writeWord memory 96 highWord := by
  apply ByteArray.ext_getElem
  · simp only [sparseMemory, MachineState.writeBytes_size, writeWord, highWord_bytes]
    have h1 : (ByteArray.mk #[1]) ≠ ByteArray.empty := by decide
    have h128 : (ByteArray.mk #[128]) ≠ ByteArray.empty := by decide
    try simp only [if_neg h1, if_neg h128]
    have h32 : (Data.Bytes.natToBytesPadded highWord.toNat 32) ≠ ByteArray.empty := by
      intro h
      have := congrArg ByteArray.size h
      rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size] at this
      contradiction
    rw [highWord_bytes] at h32
    try simp only [if_neg h32]
    change max (max memory.size 100) 123 = max memory.size 128
    omega
  · intro a hA hB
    rw [← Memory.getD0_eq_getElem _ _ hA, ← Memory.getD0_eq_getElem _ _ hB]
    simp only [sparseMemory, writeWord, highWord_bytes,
      MachineState.writeBytes_getElem?_getD]
    change (if 122 ≤ a ∧ a < 123 then (ByteArray.mk #[1])[a - 122]?.getD 0
      else if 99 ≤ a ∧ a < 100 then (ByteArray.mk #[128])[a - 99]?.getD 0
      else memory[a]?.getD 0) =
      if 96 ≤ a ∧ a < 128 then _ else memory[a]?.getD 0
    by_cases h60 : 96 ≤ a
    · by_cases h92 : a < 128
      · have hz := hzero a h60 h92
        interval_cases a <;> simp_all <;> rfl
      · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]

def copiedMemory (input : ByteArray) : ByteArray :=
  MachineState.writeBytes ByteArray.empty input 1120

theorem copiedMemory_size (input : ByteArray) (hn : 0 < input.size) :
    (copiedMemory input).size = 1120 + input.size := by
  have hne : input ≠ ByteArray.empty := by intro h; subst input; exact Nat.not_lt_zero _ hn
  simp [copiedMemory, MachineState.writeBytes_size, hne]

theorem copiedMemory_zero (input : ByteArray) (a : Nat) (ha : a < 1120) :
    (copiedMemory input)[a]?.getD 0 = 0 := by
  simp [copiedMemory, MachineState.writeBytes_getElem?_getD, show ¬1120 ≤ a by omega]

theorem copiedMemory_sparse (input : ByteArray) (hn : 0 < input.size) :
    sparseMemory (copiedMemory input) = writeWord (copiedMemory input) 96 highWord :=
  sparse_eq_writeWord _ (by rw [copiedMemory_size input hn]; omega)
    (fun a _ h => copiedMemory_zero input a (by omega))

theorem copiedMemory_gapClear (input : ByteArray) :
    PairStoreGap.GapClear (copiedMemory input) := by
  intro j hj k hk0 hk1
  have hb := PairStoreGap.lowerPairSlots_bounds j hj
  exact copiedMemory_zero input _ (by omega)

theorem scratch_read_prefix (memory : ByteArray) (low high high' : UInt256)
    (a : Nat) (ha : a + 32 ≤ 60) :
    MachineState.readWord (StaggerScratch.scratchMemory memory low high) a =
      MachineState.readWord (StaggerScratch.scratchMemory memory low high') a := by
  apply Word.word_ext
  simp only [Bytes.readWord_toNat]
  apply StaggerTableMemory.bytesToNatPadded_congrOffset
  intro j hj
  simp only [StaggerScratch.scratchMemory, writeWord,
    MachineState.writeBytes_getElem?_getD,
    YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  by_cases hw : 28 ≤ a + j ∧ a + j < 28 + 32
  · rw [if_pos hw, if_pos hw]
  · rw [if_neg hw, if_neg hw, if_neg (by omega), if_neg (by omega)]

/-- The eight lower schedule words do not see the upper scratch word at all, whatever it is. -/
theorem pool_lower_high_irrelevant (memory : ByteArray) (p i : Nat) (high : UInt256)
    (hi : i < 8) :
    StaggerScratch.poolWordD
      (StaggerScratch.scratchMemory memory
        (PairedScheduleData.reversedWord (MachineState.readWord memory p)) high) i =
    StaggerScratch.poolWordD
      (StaggerScratch.scratchMemory memory
        (PairedScheduleData.reversedWord (MachineState.readWord memory p))
        (PairedScheduleData.reversedWord (MachineState.readWord memory (p + 32)))) i := by
  by_cases hd : i ≤ 2
  · simp only [StaggerScratch.poolWordD, if_pos hd]
    exact scratch_read_prefix _ _ _ _ _ (by omega)
  · simp only [StaggerScratch.poolWordD, if_neg hd]
    rw [StaggerScratch.poolWord_eq _ _ _ _ (by omega),
      StaggerScratch.poolWord_eq _ _ _ _ (by omega), if_pos hi, if_pos hi]

theorem pool_lower (memory : ByteArray) (p i : Nat) (high : UInt256)
    (hi : i < 8) (hlow : (MachineState.readWord memory 0).toNat % 2 ^ 144 < 2 ^ 32) :
    (StaggerScratch.poolWordD
      (StaggerScratch.scratchMemory memory
        (PairedScheduleData.reversedWord (MachineState.readWord memory p)) high) i).toNat
        % 2 ^ 144
      = (StaggerScratch.dirtyWord memory p i).toNat % 2 ^ 144 := by
  rw [pool_lower_high_irrelevant memory p i high hi]
  exact StaggerScratch.poolWordD_eq_dirty memory p i (by omega) hlow

theorem pool_upper (memory : ByteArray) (low : UInt256) (i : Nat)
    (hi0 : 8 ≤ i) (hi1 : i < 16) :
    StaggerScratch.poolWordD (StaggerScratch.scratchMemory memory low highWord) i =
      UInt256.ofNat (if i = 8 then 128 else if i = 14 then 256 else 0) := by
  rw [StaggerScratch.poolWordD, if_neg (by omega),
    StaggerScratch.poolWord_eq _ _ _ _ hi1, if_neg (by omega)]
  interval_cases i <;> rfl

/-! ## The S51 fan image

`Pair13Endian.template` leaves `Pair13Endian.scratch3 memory low high`
(`96 ← high`, `46 ← low`, `28 ← low`), and the first two MCOPYs of
`Pair13PoolRaw.template` then duplicate `[96,112) → [78,94)` and `[112,128) → [130,146)`.
The result carries every four-byte schedule field twice, eighteen bytes apart, which is what
lets one masked MLOAD return the `2 ^ 144 + 1` broadcast without a multiply. -/

def fanMemory (memory : ByteArray) (low high : UInt256) : ByteArray :=
  Pair13PoolRaw.copied (Pair13Endian.scratch3 memory low high)

/-- The schedule field the S48 pool would have produced for source `i`. -/
def fanWord (low high : UInt256) (i : Nat) : UInt256 :=
  Word.mask32 (UInt256.shiftRight (if i < 8 then low else high)
    (UInt256.ofNat (32 * (7 - i % 8))))

/-- The value the pool leaves on the stack, as a function of the schedule fields: the
`2 ^ 144 + 1` broadcast for the seven words this artifact still masks, the field itself (which
IS the raw load) for the nine it does not.  Mirrors `Pair13WriterRaw.dualW`, which this module
cannot import. -/
def dualOf (words : Nat → UInt256) (i : Nat) : UInt256 :=
  if i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 11 then
    UInt256.mul Pair13PoolRaw.coefficient (words i) else words i

private theorem mask32_toNat_mod (x : UInt256) : (Word.mask32 x).toNat = x.toNat % 2 ^ 32 := by
  rw [Word.mask32_toNat, show (0xffffffff : Nat) = 2 ^ 32 - 1 by norm_num,
    Nat.and_two_pow_sub_one_eq_mod]

theorem fanWord_lt (low high : UInt256) (i : Nat) : (fanWord low high i).toNat < 2 ^ 32 := by
  rw [fanWord, mask32_toNat_mod]
  exact Nat.mod_lt _ (by norm_num)

private theorem writeWord_getD (memory : ByteArray) (address : Nat) (value : UInt256) (a : Nat) :
    (writeWord memory address value)[a]?.getD 0 =
      if address ≤ a ∧ a < address + 32 then
        (Data.Bytes.natToBytesPadded value.toNat 32)[a - address]?.getD 0
      else memory[a]?.getD 0 := by
  rw [writeWord, MachineState.writeBytes_getElem?_getD,
    YulEvmCompiler.BytesLemmas.natToBytesPadded_size]

private theorem copied_getD (m : ByteArray) (a : Nat) :
    (Pair13PoolRaw.copied m)[a]?.getD 0 =
      if 130 ≤ a ∧ a < 146 then m[a - 18]?.getD 0
      else if 78 ≤ a ∧ a < 94 then m[a + 18]?.getD 0
      else m[a]?.getD 0 := by
  have hone : ∀ b : Nat, (Pair13PoolRaw.copiedOnce m)[b]?.getD 0 =
      if 78 ≤ b ∧ b < 94 then m[b + 18]?.getD 0 else m[b]?.getD 0 := by
    intro b
    rw [Pair13PoolRaw.copiedOnce, MachineState.writeBytes_getElem?_getD,
      Memory.readPadded_size]
    by_cases hb : 78 ≤ b ∧ b < 78 + 16
    · rw [if_pos hb, if_pos (by omega), Memory.readPadded_getElem?_getD,
        if_pos (by omega : b - 78 < 16), show 96 + (b - 78) = b + 18 by omega]
    · rw [if_neg hb, if_neg (by omega)]
  rw [Pair13PoolRaw.copied, MachineState.writeBytes_getElem?_getD, Memory.readPadded_size]
  by_cases ha : 130 ≤ a ∧ a < 130 + 16
  · rw [if_pos ha, if_pos (by omega), Memory.readPadded_getElem?_getD,
      if_pos (by omega : a - 130 < 16), show 112 + (a - 130) = a - 18 by omega, hone,
      if_neg (by omega)]
  · rw [if_neg ha, if_neg (by omega), hone]

private theorem scratch3_getD (memory : ByteArray) (low high : UInt256) (a : Nat) :
    (Pair13Endian.scratch3 memory low high)[a]?.getD 0 =
      if 28 ≤ a ∧ a < 60 then (Data.Bytes.natToBytesPadded low.toNat 32)[a - 28]?.getD 0
      else if 60 ≤ a ∧ a < 78 then (Data.Bytes.natToBytesPadded low.toNat 32)[a - 46]?.getD 0
      else if 96 ≤ a ∧ a < 128 then (Data.Bytes.natToBytesPadded high.toNat 32)[a - 96]?.getD 0
      else memory[a]?.getD 0 := by
  rw [Pair13Endian.scratch3, writeWord_getD, writeWord_getD, writeWord_getD]
  by_cases h1 : 28 ≤ a ∧ a < 28 + 32
  · rw [if_pos h1, if_pos (by omega : 28 ≤ a ∧ a < 60)]
  · rw [if_neg h1, if_neg (by omega : ¬ (28 ≤ a ∧ a < 60))]
    by_cases h2 : 46 ≤ a ∧ a < 46 + 32
    · rw [if_pos h2, if_pos (by omega : 60 ≤ a ∧ a < 78)]
    · rw [if_neg h2, if_neg (by omega : ¬ (60 ≤ a ∧ a < 78))]

/-- Above the copied block the fan image is the incoming memory verbatim. -/
theorem fan_getD_high (memory : ByteArray) (low high : UInt256) (a : Nat) (ha : 146 ≤ a) :
    (fanMemory memory low high)[a]?.getD 0 = memory[a]?.getD 0 := by
  rw [fanMemory, copied_getD, if_neg (by omega), if_neg (by omega), scratch3_getD,
    if_neg (by omega), if_neg (by omega), if_neg (by omega)]

/-- Below the endian scratch the fan image agrees with the S48 scratch image. -/
theorem fan_prefix (memory : ByteArray) (low high : UInt256) (a n : Nat) (h : a + n ≤ 60) :
    Precompile.bytesToNatPadded (fanMemory memory low high) a n =
      Precompile.bytesToNatPadded (StaggerScratch.scratchMemory memory low high) a n := by
  apply StaggerTableMemory.bytesToNatPadded_congrOffset
  intro i hi
  rw [fanMemory, copied_getD, if_neg (by omega), if_neg (by omega), scratch3_getD,
    if_neg (by omega : ¬ (60 ≤ a + i ∧ a + i < 78)),
    if_neg (by omega : ¬ (96 ≤ a + i ∧ a + i < 128)),
    StaggerScratch.scratchMemory, writeWord_getD, writeWord_getD,
    if_neg (by omega : ¬ (60 ≤ a + i ∧ a + i < 60 + 32))]

/-- Below the endian scratch the fan image is the incoming memory. -/
theorem fan_prefix_memory (memory : ByteArray) (low high : UInt256) (a n : Nat) (h : a + n ≤ 28) :
    Precompile.bytesToNatPadded (fanMemory memory low high) a n =
      Precompile.bytesToNatPadded memory a n := by
  apply StaggerTableMemory.bytesToNatPadded_congrOffset
  intro i hi
  rw [fanMemory, copied_getD, if_neg (by omega), if_neg (by omega), scratch3_getD,
    if_neg (by omega), if_neg (by omega), if_neg (by omega)]

theorem fan_read_low (memory : ByteArray) (low high : UInt256) :
    MachineState.readWord (fanMemory memory low high) 28 = low := by
  rw [fanMemory, Pair13PoolRaw.copied,
    Memory.readWord_writeBytes_disjoint _ _ _ _ (Or.inl (by omega)),
    Pair13PoolRaw.copiedOnce,
    Memory.readWord_writeBytes_disjoint _ _ _ _ (Or.inl (by omega)),
    Pair13Endian.scratch3, read_writeWord]

theorem fan_read_high (memory : ByteArray) (low high : UInt256) :
    MachineState.readWord (fanMemory memory low high) 96 = high := by
  rw [fanMemory, Pair13PoolRaw.copied,
    Memory.readWord_writeBytes_disjoint _ _ _ _ (Or.inl (by omega)),
    Pair13PoolRaw.copiedOnce,
    Memory.readWord_writeBytes_disjoint _ _ _ _
      (Or.inr (by rw [Memory.readPadded_size]; omega)),
    Pair13Endian.scratch3,
    read_writeWord_disjoint _ _ _ _ (Or.inr (by omega)),
    read_writeWord_disjoint _ _ _ _ (Or.inr (by omega)), read_writeWord]

/-- The eighteen-byte duplication the two MCOPYs and the double low store create. -/
theorem fan_dup (memory : ByteArray) (low high : UInt256) (x : Nat)
    (hx : (42 ≤ x ∧ x < 60) ∨ (78 ≤ x ∧ x < 94) ∨ (112 ≤ x ∧ x < 128)) :
    (fanMemory memory low high)[x]?.getD 0 = (fanMemory memory low high)[x + 18]?.getD 0 := by
  rcases hx with h | h | h
  · rw [fanMemory, copied_getD, if_neg (by omega), if_neg (by omega),
      copied_getD, if_neg (by omega), if_neg (by omega),
      scratch3_getD, if_pos (by omega), scratch3_getD,
      if_neg (by omega), if_pos (by omega), show x + 18 - 46 = x - 28 by omega]
  · rw [fanMemory, copied_getD, if_neg (by omega), if_pos (by omega),
      copied_getD, if_neg (by omega), if_neg (by omega)]
  · rw [fanMemory, copied_getD, if_neg (by omega), if_neg (by omega),
      copied_getD, if_pos (by omega), show x + 18 - 18 = x by omega]

theorem fan_window (memory : ByteArray) (low high : UInt256) (a : Nat)
    (ha : ∀ j, j < 4 → (42 ≤ a + j ∧ a + j < 60) ∨ (78 ≤ a + j ∧ a + j < 94) ∨
      (112 ≤ a + j ∧ a + j < 128)) :
    Precompile.bytesToNatPadded (fanMemory memory low high) (a + 18) 4 =
      Precompile.bytesToNatPadded (fanMemory memory low high) a 4 := by
  symm
  refine Pair13PoolRaw.window_congr _ a (a + 18) 4 (fun j hj => ?_)
  rw [fan_dup memory low high (a + j) (ha j hj), show a + j + 18 = a + 18 + j by omega]

/-- One masked pool load, read back through the anchor word it came from. -/
private theorem fan_chunk (memory : ByteArray) (low high v : UInt256) (base j : Nat)
    (hb : 28 ≤ base) (hj : j < 8)
    (hbase : MachineState.readWord (fanMemory memory low high) base = v) :
    Precompile.bytesToNatPadded (fanMemory memory low high) (base + 4 * j) 4 =
      (Word.mask32 (UInt256.shiftRight v (UInt256.ofNat (32 * (7 - j))))).toNat := by
  have h := Pair13PoolRaw.lane_lo (fanMemory memory low high) (base + 4 * j - 28)
  rw [show base + 4 * j - 28 + 28 = base + 4 * j by omega] at h
  have hm := PairTableScratch.mask32_window (fanMemory memory low high) base j hb hj
  rw [hbase] at hm
  rw [← h, ← mask32_toNat_mod, hm]

theorem fan_low_chunk (memory : ByteArray) (low high : UInt256) (j a : Nat)
    (hj : j < 8) (ha : a = 28 + 4 * j) :
    Precompile.bytesToNatPadded (fanMemory memory low high) a 4 = (fanWord low high j).toNat := by
  subst ha
  rw [fan_chunk memory low high low 28 j (by omega) hj (fan_read_low memory low high),
    fanWord, if_pos hj, Nat.mod_eq_of_lt hj]

theorem fan_high_chunk (memory : ByteArray) (low high : UInt256) (j a k : Nat)
    (hj : j < 8) (ha : a = 96 + 4 * j) (hk : k = j + 8) :
    Precompile.bytesToNatPadded (fanMemory memory low high) a 4 = (fanWord low high k).toNat := by
  subst ha
  subst hk
  rw [fan_chunk memory low high high 96 j (by omega) hj (fan_read_high memory low high),
    fanWord, if_neg (by omega), show (j + 8) % 8 = j by omega]

/-- The zero prefix `[0,28)` survives the fan, which is what makes word 3's upper lane zero. -/
theorem fan_zero (memory : ByteArray) (low high : UInt256)
    (hlow : (MachineState.readWord memory 0).toNat % 2 ^ 144 < 2 ^ 32) :
    Precompile.bytesToNatPadded (fanMemory memory low high) 22 4 = 0 := by
  rw [fan_prefix_memory memory low high 22 4 (by omega)]
  have h6 := StaggerScratch.low_zero memory hlow 22 (by omega) (by omega)
  have hsplit := Bytes.bytesToNatPadded_add memory 22 4 2
  rw [show (4 : Nat) + 2 = 28 - 22 by norm_num] at hsplit
  rw [h6] at hsplit
  simp only [show (256 : Nat) ^ 2 = 65536 by norm_num] at hsplit
  omega

theorem fan_lanes (memory : ByteArray) (low high : UInt256) (i : Nat)
    (hi0 : 4 ≤ i) (hi1 : i < 16) :
    Precompile.bytesToNatPadded (fanMemory memory low high) (Pair13PoolRaw.poolAddr i + 28) 4 =
        (fanWord low high i).toNat ∧
      Precompile.bytesToNatPadded (fanMemory memory low high) (Pair13PoolRaw.poolAddr i + 10) 4 =
        (fanWord low high i).toNat := by
  have W : ∀ a : Nat, (∀ j, j < 4 → (42 ≤ a + j ∧ a + j < 60) ∨ (78 ≤ a + j ∧ a + j < 94) ∨
      (112 ≤ a + j ∧ a + j < 128)) →
      Precompile.bytesToNatPadded (fanMemory memory low high) (a + 18) 4 =
        Precompile.bytesToNatPadded (fanMemory memory low high) a 4 :=
    fan_window memory low high
  interval_cases i
  -- i = 4 :  low lane 62, high lane 44
  · have hd := fan_low_chunk memory low high 4 44 (by omega) (by omega)
    refine ⟨?_, hd⟩
    rw [show Pair13PoolRaw.poolAddr 4 + 28 = 44 + 18 from by norm_num [Pair13PoolRaw.poolAddr],
      W 44 (by intro j hj; omega)]
    exact hd
  -- i = 5 :  low lane 66, high lane 48
  · have hd := fan_low_chunk memory low high 5 48 (by omega) (by omega)
    refine ⟨?_, hd⟩
    rw [show Pair13PoolRaw.poolAddr 5 + 28 = 48 + 18 from by norm_num [Pair13PoolRaw.poolAddr],
      W 48 (by intro j hj; omega)]
    exact hd
  -- i = 6 :  low lane 70, high lane 52
  · have hd := fan_low_chunk memory low high 6 52 (by omega) (by omega)
    refine ⟨?_, hd⟩
    rw [show Pair13PoolRaw.poolAddr 6 + 28 = 52 + 18 from by norm_num [Pair13PoolRaw.poolAddr],
      W 52 (by intro j hj; omega)]
    exact hd
  -- i = 7 :  low lane 74, high lane 56
  · have hd := fan_low_chunk memory low high 7 56 (by omega) (by omega)
    refine ⟨?_, hd⟩
    rw [show Pair13PoolRaw.poolAddr 7 + 28 = 56 + 18 from by norm_num [Pair13PoolRaw.poolAddr],
      W 56 (by intro j hj; omega)]
    exact hd
  -- i = 8 :  low lane 96, high lane 78
  · have hd := fan_high_chunk memory low high 0 96 8 (by omega) (by omega) (by omega)
    refine ⟨hd, ?_⟩
    rw [show Pair13PoolRaw.poolAddr 8 + 10 = 78 from by norm_num [Pair13PoolRaw.poolAddr],
      ← W 78 (by intro j hj; omega), show (78 : Nat) + 18 = 96 from by norm_num]
    exact hd
  -- i = 9 :  low lane 100, high lane 82
  · have hd := fan_high_chunk memory low high 1 100 9 (by omega) (by omega) (by omega)
    refine ⟨hd, ?_⟩
    rw [show Pair13PoolRaw.poolAddr 9 + 10 = 82 from by norm_num [Pair13PoolRaw.poolAddr],
      ← W 82 (by intro j hj; omega), show (82 : Nat) + 18 = 100 from by norm_num]
    exact hd
  -- i = 10 :  low lane 104, high lane 86
  · have hd := fan_high_chunk memory low high 2 104 10 (by omega) (by omega) (by omega)
    refine ⟨hd, ?_⟩
    rw [show Pair13PoolRaw.poolAddr 10 + 10 = 86 from by norm_num [Pair13PoolRaw.poolAddr],
      ← W 86 (by intro j hj; omega), show (86 : Nat) + 18 = 104 from by norm_num]
    exact hd
  -- i = 11 :  low lane 108, high lane 90
  · have hd := fan_high_chunk memory low high 3 108 11 (by omega) (by omega) (by omega)
    refine ⟨hd, ?_⟩
    rw [show Pair13PoolRaw.poolAddr 11 + 10 = 90 from by norm_num [Pair13PoolRaw.poolAddr],
      ← W 90 (by intro j hj; omega), show (90 : Nat) + 18 = 108 from by norm_num]
    exact hd
  -- i = 12 :  low lane 130, high lane 112
  · have hd := fan_high_chunk memory low high 4 112 12 (by omega) (by omega) (by omega)
    refine ⟨?_, hd⟩
    rw [show Pair13PoolRaw.poolAddr 12 + 28 = 112 + 18 from by norm_num [Pair13PoolRaw.poolAddr],
      W 112 (by intro j hj; omega)]
    exact hd
  -- i = 13 :  low lane 134, high lane 116
  · have hd := fan_high_chunk memory low high 5 116 13 (by omega) (by omega) (by omega)
    refine ⟨?_, hd⟩
    rw [show Pair13PoolRaw.poolAddr 13 + 28 = 116 + 18 from by norm_num [Pair13PoolRaw.poolAddr],
      W 116 (by intro j hj; omega)]
    exact hd
  -- i = 14 :  low lane 138, high lane 120
  · have hd := fan_high_chunk memory low high 6 120 14 (by omega) (by omega) (by omega)
    refine ⟨?_, hd⟩
    rw [show Pair13PoolRaw.poolAddr 14 + 28 = 120 + 18 from by norm_num [Pair13PoolRaw.poolAddr],
      W 120 (by intro j hj; omega)]
    exact hd
  -- i = 15 :  low lane 142, high lane 124
  · have hd := fan_high_chunk memory low high 7 124 15 (by omega) (by omega) (by omega)
    refine ⟨?_, hd⟩
    rw [show Pair13PoolRaw.poolAddr 15 + 28 = 124 + 18 from by norm_num [Pair13PoolRaw.poolAddr],
      W 124 (by intro j hj; omega)]
    exact hd

theorem fanMemory_size (memory : ByteArray) (low high : UInt256) :
    (fanMemory memory low high).size = max memory.size 146 := by
  have h16 : ¬ ((MachineState.readPadded
      (Pair13PoolRaw.copiedOnce (Pair13Endian.scratch3 memory low high)) 112 16).size = 0) := by
    rw [Memory.readPadded_size]; decide
  have h16' : ¬ ((MachineState.readPadded
      (Pair13Endian.scratch3 memory low high) 96 16).size = 0) := by
    rw [Memory.readPadded_size]; decide
  rw [fanMemory, Pair13PoolRaw.copied, MachineState.writeBytes_size, if_neg h16,
    Pair13PoolRaw.copiedOnce, MachineState.writeBytes_size, if_neg h16',
    Memory.readPadded_size, Memory.readPadded_size,
    Pair13Endian.scratch3, writeWord_size, writeWord_size, writeWord_size]
  omega

/-- Every byte the fan touches lies below the table, so the table erases the whole image. -/
theorem erase_fan (memory : ByteArray) (words : Nat → UInt256) (low high : UInt256) :
    StaggerTableMemory.storeDescending (fanMemory memory low high) words 0 61 =
      StaggerTableMemory.storeDescending memory words 0 61 := by
  apply ByteArray.ext_getElem
  · rw [StaggerTableMemory.storeDescending_size _ _ _ _ (by omega),
      StaggerTableMemory.storeDescending_size _ _ _ _ (by omega), fanMemory_size]
    omega
  · intro address hA hB
    rw [← Memory.getD0_eq_getElem _ _ hA, ← Memory.getD0_eq_getElem _ _ hB]
    by_cases hin : address < 1112
    · exact StaggerTableMemory.getD_storeDescending_inside _ _ _ _ _ _
        (by omega) (by omega) (by simpa using hin)
    · rw [StaggerTableMemory.getD_table_outside _ _ _ (by omega),
        StaggerTableMemory.getD_table_outside _ _ _ (by omega)]
      exact fan_getD_high memory low high address (by omega)

theorem fanMemory_gapClear (memory : ByteArray) (low high : UInt256)
    (hg : PairStoreGap.GapClear memory) :
    PairStoreGap.GapClear (fanMemory memory low high) := by
  intro j hj k hk0 hk1
  have hb := PairStoreGap.lowerPairSlots_bounds j hj
  rw [fan_getD_high memory low high (18 * j + k) (by omega)]
  exact hg j hj k hk0 hk1


/-! ## The JD6 pool: seven words masked, nine raw -/

/-- The schedule field each source contributes, as the writer sees it: the clean chunk for the
seven words this artifact still masks, and the raw thirty-two byte load for the nine it does
not.  `Pair13WriterRaw.dualW` applied to this is exactly what the pool leaves on the stack. -/
def wordsJ (memory : ByteArray) (low high : UInt256) (i : Nat) : UInt256 :=
  if i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 11 then fanWord low high i
  else Pair13PoolRaw.poolWord (fanMemory memory low high) i

theorem fan_poolWordJ (memory : ByteArray) (low high : UInt256) (i : Nat) (hi : i < 16) :
    Pair13PoolRaw.poolWord (fanMemory memory low high) i
      = dualOf (wordsJ memory low high) i := by
  by_cases hm : i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 11
  · rw [dualOf, if_pos hm, wordsJ, if_pos hm]
    obtain ⟨hlo, hhi⟩ := fan_lanes memory low high i (by omega) hi
    exact Pair13PoolRaw.poolWord_dual _ i hm _ (fanWord_lt low high i) hlo hhi
  · rw [dualOf, if_neg hm, wordsJ, if_neg hm]

/-- The six bytes the fan never writes survive it. -/
theorem fan_poolClear (memory : ByteArray) (low high : UInt256)
    (h : PairStoreGap.PoolClear memory) :
    PairStoreGap.PoolClear (fanMemory memory low high) := by
  refine PairStoreGap.poolClear_congr memory _ (fun a hA => ?_) h
  rw [fanMemory, copied_getD, if_neg (by omega), if_neg (by omega), scratch3_getD,
    if_neg (by omega), if_neg (by omega), if_neg (by omega)]

theorem copiedMemory_poolClear (input : ByteArray) :
    PairStoreGap.PoolClear (copiedMemory input) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    exact JD8Pool.window2_of_bytes _ _ (copiedMemory_zero input _ (by omega))
      (copiedMemory_zero input _ (by omega))

/-- **The junk bound, per unmasked word.**  Each one's fourteen-byte window crosses one of the
three fan gaps, so `PoolClear` puts a zero two-byte window inside it. -/
theorem fan_jl_bound (memory : ByteArray) (low high : UInt256)
    (h : PairStoreGap.PoolClear (fanMemory memory low high)) (i : Nat)
    (hd : i = 3 ∨ i = 10 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15) :
    JD8Pool.jlOf (fanMemory memory low high) i < 2 ^ 112 - 4 := by
  obtain ⟨h26, h94, h128⟩ := h
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl
  · exact JD8Pool.jlOf_bound _ 3 0 (by omega) (by simpa [Pair13PoolRaw.poolAddr] using h26)
  · exact JD8Pool.jlOf_bound _ 10 4 (by omega) (by simpa [Pair13PoolRaw.poolAddr] using h94)
  · exact JD8Pool.jlOf_bound _ 12 12 (by omega) (by simpa [Pair13PoolRaw.poolAddr] using h128)
  · exact JD8Pool.jlOf_bound _ 13 8 (by omega) (by simpa [Pair13PoolRaw.poolAddr] using h128)
  · exact JD8Pool.jlOf_bound _ 14 4 (by omega) (by simpa [Pair13PoolRaw.poolAddr] using h128)
  · exact JD8Pool.jlOf_bound _ 15 0 (by omega) (by simpa [Pair13PoolRaw.poolAddr] using h128)

#print axioms fan_poolWordJ
#print axioms fan_poolClear
#print axioms fan_jl_bound


/-! ## What each slot actually holds: the field, plus a bounded junk window -/

/-- Two bytes anywhere in the fan's zero prefix `[14,28)` are zero. -/
theorem fan_prefix_zero2 (memory : ByteArray) (low high : UInt256)
    (hlow : (MachineState.readWord memory 0).toNat % 2 ^ 144 < 2 ^ 32)
    (a : Nat) (ha0 : 14 ≤ a) (ha1 : a + 2 ≤ 28) :
    Precompile.bytesToNatPadded (fanMemory memory low high) a 2 = 0 := by
  rw [fan_prefix_memory memory low high a 2 (by omega)]
  have h := StaggerScratch.low_zero memory hlow a ha0 (by omega)
  have hs := Bytes.bytesToNatPadded_add memory a 2 (26 - a)
  rw [show 2 + (26 - a) = 28 - a by omega, h] at hs
  obtain ⟨hXc, -⟩ := Nat.add_eq_zero_iff.mp hs.symm
  rcases Nat.mul_eq_zero.mp hXc with h' | h'
  · exact h'
  · simp at h'

/-- Word 0's junk window lies wholly inside the zero prefix. -/
theorem fan_zero_word0 (memory : ByteArray) (low high : UInt256)
    (hlow : (MachineState.readWord memory 0).toNat % 2 ^ 144 < 2 ^ 32) :
    JD8Pool.jlOf (fanMemory memory low high) 0 = 0 := by
  have h := StaggerScratch.low_zero memory hlow 14 (by omega) (by omega)
  rw [JD8Pool.jlOf, show Pair13PoolRaw.poolAddr 0 + 14 = 14 from rfl,
    fan_prefix_memory memory low high 14 14 (by omega)]
  simpa using h

/-- The lower lane the fan presents for word `k` is the schedule field itself. -/
theorem fan_loLane (memory : ByteArray) (low high : UInt256) (k : Nat) (hk : k < 16) :
    JD8Pool.loLane (fanMemory memory low high) k = (fanWord low high k).toNat := by
  rw [JD8Pool.loLane]
  by_cases h4 : 4 ≤ k
  · exact (fan_lanes memory low high k h4 hk).1
  · have hk3 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases hk3 with rfl | rfl | rfl | rfl
    · exact fan_low_chunk memory low high 0 28 (by decide) rfl
    · exact fan_low_chunk memory low high 1 32 (by decide) rfl
    · exact fan_low_chunk memory low high 2 36 (by decide) rfl
    · exact fan_low_chunk memory low high 3 40 (by decide) rfl

/-- Word 3's rebuilt broadcast leaves its low 144 bits exactly the raw load's. -/
theorem three_lo144 (memory : ByteArray) :
    (Pair13PoolRaw.poolWord memory 3).toNat % 2 ^ 144
      = (Pair13PoolRaw.rawLoad memory 3).toNat % 2 ^ 144 := by
  rw [Pair13PoolRaw.poolWord_three_raw, Word.word_toNat_lor, JD8Pool.shl144_toNat,
    JD8Pool.lor_mod_two_pow]
  have h1 : (Pair13PoolRaw.rawLoad memory 3).toNat % 2 ^ 112 * 2 ^ 144 % 2 ^ 144 = 0 :=
    Nat.mul_mod_left _ _
  rw [h1, Nat.zero_or]

/-- What a slot holding an UNMASKED word receives: the field plus its fourteen junk bytes. -/
theorem dualOf_lo144 (memory : ByteArray) (low high : UInt256) (k : Nat) (hk : k < 16)
    (hm : ¬ (k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 11)) :
    (dualOf (wordsJ memory low high) k).toNat % 2 ^ 144
      = JD8Pool.loLane (fanMemory memory low high) k
        + JD8Pool.jlOf (fanMemory memory low high) k * 2 ^ 32 := by
  rw [dualOf, if_neg hm, wordsJ, if_neg hm]
  have hval : (Pair13PoolRaw.poolWord (fanMemory memory low high) k).toNat % 2 ^ 144
      = (Pair13PoolRaw.rawLoad (fanMemory memory low high) k).toNat % 2 ^ 144 := by
    by_cases h3 : k = 3
    · subst h3; exact three_lo144 _
    · by_cases hs : k = 0 ∨ k = 1 ∨ k = 2
      · rw [Pair13PoolRaw.poolWord_low _ k hs]
      · rw [Pair13PoolRaw.poolWord_raw _ k (by omega)]
  rw [hval, JD8Pool.rawLoad_split]
  have hl := JD8Pool.loLane_lt (fanMemory memory low high) k
  have hj := JD8Pool.jlOf_lt (fanMemory memory low high) k
  have hb : JD8Pool.jlOf (fanMemory memory low high) k * 2 ^ 32
      ≤ (2 ^ 112 - 1) * 2 ^ 32 := Nat.mul_le_mul_right _ (by omega)
  omega

/-- What a slot holding a MASKED word receives: the field, and nothing else. -/
theorem dualOf_lo144_masked (memory : ByteArray) (low high : UInt256) (k : Nat)
    (hm : k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 11) :
    (dualOf (wordsJ memory low high) k).toNat % 2 ^ 144 = (fanWord low high k).toNat := by
  rw [dualOf, if_pos hm, wordsJ, if_pos hm,
    Pair13PoolRaw.mul_coefficient_toNat _ (fanWord_lt low high k)]
  have := fanWord_lt low high k
  omega

/-- The LOW 32 bits of whatever a slot holding word `k` receives are the schedule field. -/
theorem dualOf_low32 (memory : ByteArray) (low high : UInt256) (k : Nat) (hk : k < 16) :
    (dualOf (wordsJ memory low high) k).toNat % 2 ^ 32 = (fanWord low high k).toNat := by
  have h144 : (2:Nat) ^ 144 = 2 ^ 32 * 2 ^ 112 := by rw [← Nat.pow_add]
  have hmod : (dualOf (wordsJ memory low high) k).toNat % 2 ^ 32
      = ((dualOf (wordsJ memory low high) k).toNat % 2 ^ 144) % 2 ^ 32 := by
    rw [h144, Nat.mod_mul_right_mod]
  rw [hmod]
  by_cases hm : k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 11
  · rw [dualOf_lo144_masked memory low high k hm]
    have := fanWord_lt low high k
    omega
  · rw [dualOf_lo144 memory low high k hk hm, fan_loLane memory low high k hk]
    have := fanWord_lt low high k
    omega

/-- The junk budget, per word.  Zero for the seven the artifact still masks and for word 0;
below the carry threshold for the rest, by a zero two-byte window inside each junk window. -/
theorem dualOf_lo_bound (memory : ByteArray) (low high : UInt256)
    (hlow : (MachineState.readWord memory 0).toNat % 2 ^ 144 < 2 ^ 32)
    (hpc : PairStoreGap.PoolClear (fanMemory memory low high)) (k : Nat) (hk : k < 16) :
    ((dualOf (wordsJ memory low high) k).toNat % 2 ^ 144) / 2 ^ 32 < 2 ^ 112 - 4 := by
  by_cases hm : k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 11
  · rw [dualOf_lo144_masked memory low high k hm]
    have := fanWord_lt low high k
    omega
  · rw [dualOf_lo144 memory low high k hk hm]
    have hl := JD8Pool.loLane_lt (fanMemory memory low high) k
    have hjb : JD8Pool.jlOf (fanMemory memory low high) k < 2 ^ 112 - 4 := by
      have hk0 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 10 ∨ k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15 := by
        omega
      rcases hk0 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [fan_zero_word0 memory low high hlow]; norm_num
      · exact JD8Pool.jlOf_bound _ 1 0 (by omega)
          (fan_prefix_zero2 memory low high hlow 18 (by omega) (by omega))
      · exact JD8Pool.jlOf_bound _ 2 0 (by omega)
          (fan_prefix_zero2 memory low high hlow 22 (by omega) (by omega))
      · exact fan_jl_bound memory low high hpc 3 (by tauto)
      · exact fan_jl_bound memory low high hpc 10 (by tauto)
      · exact fan_jl_bound memory low high hpc 12 (by tauto)
      · exact fan_jl_bound memory low high hpc 13 (by tauto)
      · exact fan_jl_bound memory low high hpc 14 (by tauto)
      · exact fan_jl_bound memory low high hpc 15 (by tauto)
    omega

/-- A word the artifact still masks (or word 0) reaches its slot with NO junk at all. -/
theorem dualOf_lo_zero (memory : ByteArray) (low high : UInt256)
    (hlow : (MachineState.readWord memory 0).toNat % 2 ^ 144 < 2 ^ 32) (k : Nat) (hk : k < 16)
    (hc : k = 0 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 11) :
    ((dualOf (wordsJ memory low high) k).toNat % 2 ^ 144) / 2 ^ 32 = 0 := by
  by_cases hm : k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 11
  · rw [dualOf_lo144_masked memory low high k hm]
    have := fanWord_lt low high k
    omega
  · have hz : k = 0 := by omega
    subst hz
    rw [dualOf_lo144 memory low high 0 (by omega) hm, fan_zero_word0 memory low high hlow]
    have hl := JD8Pool.loLane_lt (fanMemory memory low high) 0
    omega

#print axioms fan_loLane
#print axioms dualOf_lo144
#print axioms dualOf_low32
#print axioms dualOf_lo_bound
#print axioms dualOf_lo_zero

/-! ## The ELIDED half: what the merged store leaves one slot down -/

private theorem dual_div144 (w : Nat) (hw : w < 2 ^ 32) :
    (2 ^ 144 * w + w) / 2 ^ 144 = w := by
  have h : 2 ^ 144 * w + w = w + w * 2 ^ 144 := by ring
  rw [h, Nat.add_mul_div_right _ _ (Nat.two_pow_pos 144), Nat.div_eq_of_lt (by omega),
    Nat.zero_add]


/-- The upper lane the fan presents for word `k` (4 <= k) is the schedule field again --
that duplication is what lets one masked load carry the broadcast. -/
theorem fan_hiLane (memory : ByteArray) (low high : UInt256) (k : Nat)
    (hk0 : 4 ≤ k) (hk1 : k < 16) :
    JD8Pool.hiLane (fanMemory memory low high) k = (fanWord low high k).toNat := by
  rw [JD8Pool.hiLane]
  exact (fan_lanes memory low high k hk0 hk1).2

theorem fan_hiLane_three (memory : ByteArray) (low high : UInt256)
    (hlow : (MachineState.readWord memory 0).toNat % 2 ^ 144 < 2 ^ 32) :
    JD8Pool.hiLane (fanMemory memory low high) 3 = 0 := by
  rw [JD8Pool.hiLane, show Pair13PoolRaw.poolAddr 3 + 10 = 22 from rfl]
  exact fan_zero memory low high hlow

/-- An elided slot receives the HIGH half of the merged store, and its low 32 bits are still
the schedule field. -/
theorem dualOf_hi_low32 (memory : ByteArray) (low high : UInt256)
    (hlow : (MachineState.readWord memory 0).toNat % 2 ^ 144 < 2 ^ 32) (k : Nat)
    (hk0 : 3 ≤ k) (hk1 : k < 16) :
    (JD8Merge.hi144 (dualOf (wordsJ memory low high) k)).toNat % 2 ^ 32
      = (fanWord low high k).toNat := by
  rw [JD8Merge.hi144_toNat]
  by_cases hm : k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 11
  · rw [dualOf, if_pos hm, wordsJ, if_pos hm,
      Pair13PoolRaw.mul_coefficient_toNat _ (fanWord_lt low high k),
      dual_div144 _ (fanWord_lt low high k)]
    exact Nat.mod_eq_of_lt (fanWord_lt low high k)
  · rw [dualOf, if_neg hm, wordsJ, if_neg hm]
    by_cases h3 : k = 3
    · subst h3
      rw [JD8Pool.three_hi_low32 _ (fan_hiLane_three memory low high hlow),
        fan_loLane memory low high 3 (by omega)]
    · rw [JD8Pool.raw_hi _ k (Pair13PoolRaw.poolWord_raw _ k (by omega)),
        fan_hiLane memory low high k (by omega) hk1]
      have := fanWord_lt low high k
      have hjr := JD8Pool.jrOf_lt (fanMemory memory low high) k
      omega

/-- The elided half's junk is at most the ten bytes above the upper lane -- far below the
carry threshold, and free: `hi144` of anything is below `2 ^ 112`. -/
theorem dualOf_hi_bound (memory : ByteArray) (low high : UInt256) (k : Nat) :
    ((JD8Merge.hi144 (dualOf (wordsJ memory low high) k)).toNat % 2 ^ 144) / 2 ^ 32
      < 2 ^ 112 - 4 := by
  have h := JD8Merge.hi144_lt (dualOf (wordsJ memory low high) k)
  omega

theorem dualOf_hi_zero (memory : ByteArray) (low high : UInt256) (k : Nat)
    (hm : k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 11) :
    ((JD8Merge.hi144 (dualOf (wordsJ memory low high) k)).toNat % 2 ^ 144) / 2 ^ 32 = 0 := by
  rw [JD8Merge.hi144_toNat, dualOf, if_pos hm, wordsJ, if_pos hm,
    Pair13PoolRaw.mul_coefficient_toNat _ (fanWord_lt low high k),
    dual_div144 _ (fanWord_lt low high k)]
  have := fanWord_lt low high k
  omega

#print axioms dualOf_hi_low32
#print axioms dualOf_hi_bound
#print axioms dualOf_hi_zero

#print axioms sparse_eq_writeWord
#print axioms copiedMemory_sparse
#print axioms copiedMemory_gapClear
#print axioms pool_lower
#print axioms pool_upper
#print axioms erase_fan
#print axioms fanMemory_gapClear
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Shared32Scratch
