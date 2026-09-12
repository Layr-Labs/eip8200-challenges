import Challenge.Ripemd160.Submission.Proofs.Bytecode.VerifierData


set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

/-!
# Verifier correctness: the accumulator decides the input

`verifyAcc input n = 0` exactly when `input` equals the `n`-byte patterned
prefix `patternedInput.extract 0 n`.  For `n ≥ 32` every compare offset leaves
room for a full word, so `readWord` on the extracted prefix agrees with
`readWord` on the full vector.  For `n < 32` a single word compare against
`expectedShort n` decides the whole input.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.VerifierLogic

open EvmSemantics EvmSemantics.EVM
open PatternedInputData PatternedWordData PatternedWordLogic
open KnownInputLogic VerifierData

/-- Byte `r` of the expected word at an arbitrary offset. -/
theorem byteAt_expectedWordAtOffset (off r : Nat) (hr : r < 32) :
    UInt256.byteAt (UInt256.ofNat r) (expectedWordAtOffset off) =
      UInt256.ofNat (paddedByte (off + r)).toNat := by
  rw [← readWord_patterned_offset off,
    Challenge.EvmProof.Bytes.byteAt_readWord patternedInput off r hr,
    byteFrom_patterned]

/-- Every compare offset leaves room for a full word. -/
theorem compareOffsets_bound (n off : Nat) (hn32 : 32 ≤ n)
    (hoff : off ∈ compareOffsets n) : off + 32 ≤ n := by
  unfold compareOffsets at hoff
  simp only [List.mem_append, List.mem_map, List.mem_range,
    List.mem_ite_nil_right, List.mem_singleton] at hoff
  rcases hoff with ⟨j, hj, rfl⟩ | ⟨hmod, rfl⟩
  · omega
  · omega

/-- `readWord` on the `n`-byte prefix equals `readWord` on the full vector
when the whole word lies inside the prefix. -/
theorem readWord_extract_prefix (off n : Nat) (h : off + 32 ≤ n) :
    MachineState.readWord (patternedInput.extract 0 n) off =
      MachineState.readWord patternedInput off := by
  apply Challenge.EvmProof.Word.word_ext
  rw [Challenge.EvmProof.Bytes.readWord_toNat,
    Challenge.EvmProof.Bytes.readWord_toNat]
  unfold EvmSemantics.EVM.Precompile.bytesToNatPadded
    EvmSemantics.Data.Bytes.bytesToBigEndianNat
  congr 1
  apply ByteArray.ext_getElem
  · simp [MachineState.readPadded]
  · intro i hi _
    rw [Memory.readPadded_getElem?_getD, Memory.readPadded_getElem?_getD]
    simp only [if_pos (by omega : i < 32)]
    rw [ByteArray.getElem?_eq_getElem, ByteArray.getElem_extract]
    · rfl
    · omega
    · omega

/-- Every byte `j < n` is covered by some compare offset. -/
theorem covered (n j : Nat) (hj : j < n) (hn32 : 32 ≤ n) :
    ∃ off, off ∈ compareOffsets n ∧ ∃ r, r < 32 ∧ off + r = j := by
  by_cases htail : j / 32 < n / 32
  · exact ⟨32 * (j / 32), by
      unfold compareOffsets
      simp only [List.mem_append, List.mem_map, List.mem_range]
      left; exact ⟨j / 32, htail, rfl⟩,
      j % 32, Nat.mod_lt _ (by omega), by omega⟩
  · have hmod : n % 32 ≠ 0 := by
      by_contra h
      omega
    refine ⟨n - 32, ?_, j - (n - 32), by omega, by omega⟩
    unfold compareOffsets
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton]
    right
    exact ⟨hmod, rfl⟩

/-- `verifyAcc input n = 0` forces `input = patternedInput.extract 0 n`
(`n ≥ 32`). -/
theorem eq_extract_of_verifyAcc (input : ByteArray) (n : Nat)
    (hsize : input.size = n) (hn32 : 32 ≤ n)
    (hacc : verifyAcc input n = 0) :
    input = patternedInput.extract 0 n := by
  have hall := (verifyAcc_zero_iff_offsets input n hn32).1 hacc
  apply ByteArray.ext_getElem
  · rw [hsize]
    simp [patternedInput_size]
  · intro j hj hjtarget
    have hjn : j < n := by simpa [hsize] using hj
    obtain ⟨off, hoff, r, hr, hdecomp⟩ := covered n j hjn hn32
    have hb := congrArg (UInt256.byteAt (UInt256.ofNat r)) (hall off hoff)
    rw [Challenge.EvmProof.Bytes.byteAt_readWord input off r hr,
      byteAt_expectedWordAtOffset off r hr, hdecomp] at hb
    have hbyte : YulSemantics.EVM.byteFrom input.toList j = paddedByte j := by
      apply UInt8.ext
      have hv := congrArg UInt256.toNat hb
      rw [Challenge.EvmProof.Word.word_toNat_ofNat,
        Nat.mod_eq_of_lt (Nat.lt_trans
          (YulSemantics.EVM.byteFrom input.toList j).toNat_lt (by norm_num)),
        Challenge.EvmProof.Word.word_toNat_ofNat,
        Nat.mod_eq_of_lt (Nat.lt_trans (paddedByte j).toNat_lt (by norm_num))] at hv
      exact hv
    have hdata : j < input.data.size := hj
    rw [YulEvmCompiler.ByteArray.toList_eq_data] at hbyte
    unfold YulSemantics.EVM.byteFrom at hbyte
    rw [List.getD_eq_getElem?_getD, Array.getElem?_toList,
      Array.getElem?_eq_getElem hdata] at hbyte
    simp only [Option.getD_some, paddedByte, if_pos (by omega : j < 1000)] at hbyte
    rw [ByteArray.getElem_extract j hjtarget (by omega)]
    rw [patternedInput_getElem j (by omega)]
    exact hbyte

/-- The reverse direction (`n ≥ 32`). -/
theorem verifyAcc_of_extract (input : ByteArray) (n : Nat)
    (hsize : input.size = n) (hn32 : 32 ≤ n)
    (heq : input = patternedInput.extract 0 n) :
    verifyAcc input n = 0 := by
  rw [verifyAcc_zero_iff_offsets input n hn32]
  intro off hoff
  have hbound := compareOffsets_bound n off hn32 hoff
  subst heq
  rw [readWord_extract_prefix off n hbound, readWord_patterned_offset]

/-- The two directions together (`n ≥ 32`). -/
theorem verifyAcc_zero_iff_eq (input : ByteArray) (n : Nat)
    (hsize : input.size = n) (hn32 : 32 ≤ n) :
    verifyAcc input n = 0 ↔ input = patternedInput.extract 0 n :=
  ⟨eq_extract_of_verifyAcc input n hsize hn32,
   verifyAcc_of_extract input n hsize hn32⟩

/-- `verifyAcc input n = 0` for `n < 32` forces `input = extract 0 n`.
Proved per concrete size (`1`, `31`) where `expectedShort` is a literal. -/
theorem eq_extract_of_verifyAcc_short (input : ByteArray) (n : Nat)
    (hsize : input.size = n) (hn : n = 1 ∨ n = 31)
    (hacc : verifyAcc input n = 0) :
    input = patternedInput.extract 0 n := by
  have hall := (verifyAcc_zero_iff input n).1 hacc
  have hmem : (0, expectedShort n) ∈ comparePairs n := by
    rcases hn with rfl | rfl <;> decide
  have hword := hall (0, expectedShort n) hmem
  apply ByteArray.ext_getElem
  · rw [hsize]
    rcases hn with rfl | rfl <;> simp [patternedInput_size]
  · intro j hj hjtarget
    have hjn : j < n := by simpa [hsize] using hj
    have hb := congrArg (UInt256.byteAt (UInt256.ofNat j)) hword
    rw [Challenge.EvmProof.Bytes.byteAt_readWord input 0 j (by omega)] at hb
    -- byteAt j (expectedShort n) = paddedByte j for j < n (concrete n)
    have hexp : UInt256.byteAt (UInt256.ofNat j) (expectedShort n) =
        UInt256.ofNat (paddedByte j).toNat := by
      rcases hn with rfl | rfl
      · interval_cases j <;> decide
      · interval_cases j <;> decide
    rw [hexp] at hb
    have hbyte : YulSemantics.EVM.byteFrom input.toList j = paddedByte j := by
      apply UInt8.ext
      have hv := congrArg UInt256.toNat hb
      rw [Challenge.EvmProof.Word.word_toNat_ofNat,
        Nat.mod_eq_of_lt (Nat.lt_trans
          (YulSemantics.EVM.byteFrom input.toList j).toNat_lt (by norm_num)),
        Challenge.EvmProof.Word.word_toNat_ofNat,
        Nat.mod_eq_of_lt (Nat.lt_trans (paddedByte j).toNat_lt (by norm_num))] at hv
      exact hv
    have hdata : j < input.data.size := hj
    rw [YulEvmCompiler.ByteArray.toList_eq_data] at hbyte
    unfold YulSemantics.EVM.byteFrom at hbyte
    rw [List.getD_eq_getElem?_getD, Array.getElem?_toList,
      Array.getElem?_eq_getElem hdata] at hbyte
    simp only [Option.getD_some, paddedByte, if_pos (by omega : j < 1000)] at hbyte
    rw [ByteArray.getElem_extract j hjtarget (by omega)]
    rw [patternedInput_getElem j (by omega)]
    exact hbyte

/-- The reverse direction (`n < 32`). -/
theorem verifyAcc_of_extract_short (input : ByteArray) (n : Nat)
    (hsize : input.size = n) (hn : n = 1 ∨ n = 31)
    (heq : input = patternedInput.extract 0 n) :
    verifyAcc input n = 0 := by
  rw [verifyAcc_zero_iff]
  intro p hp
  rcases hn with rfl | rfl
  · have hmem : p = (0, expectedShort 1) := by
      have : comparePairs 1 = [(0, expectedShort 1)] := rfl
      rw [this] at hp
      exact List.mem_singleton.1 hp
    subst hmem
    subst heq
    -- readWord (extract 0 1) 0 = expectedShort 1
    apply Challenge.EvmProof.Word.word_ext
    rw [Challenge.EvmProof.Bytes.readWord_toNat]
    unfold expectedShort expectedShortNat
    rw [Challenge.EvmProof.Word.word_toNat_ofNat]
    apply Nat.mod_eq_of_lt
    -- bytesToNatPadded (extract 0 1) 0 32 = expectedShortNat 1
    have : EvmSemantics.EVM.Precompile.bytesToNatPadded
        (patternedInput.extract 0 1) 0 32 = expectedShortNat 1 := by
      unfold EvmSemantics.EVM.Precompile.bytesToNatPadded
        EvmSemantics.Data.Bytes.bytesToBigEndianNat
      decide
    rw [this]
    unfold expectedShortNat
    decide
  · have hmem : p = (0, expectedShort 31) := by
      have : comparePairs 31 = [(0, expectedShort 31)] := rfl
      rw [this] at hp
      exact List.mem_singleton.1 hp
    subst hmem
    subst heq
    apply Challenge.EvmProof.Word.word_ext
    rw [Challenge.EvmProof.Bytes.readWord_toNat]
    unfold expectedShort expectedShortNat
    rw [Challenge.EvmProof.Word.word_toNat_ofNat]
    apply Nat.mod_eq_of_lt
    have : EvmSemantics.EVM.Precompile.bytesToNatPadded
        (patternedInput.extract 0 31) 0 32 = expectedShortNat 31 := by
      unfold EvmSemantics.EVM.Precompile.bytesToNatPadded
        EvmSemantics.Data.Bytes.bytesToBigEndianNat
      decide
    rw [this]
    unfold expectedShortNat
    decide

/-- The two directions together (`n < 32`). -/
theorem verifyAcc_zero_iff_eq_short (input : ByteArray) (n : Nat)
    (hsize : input.size = n) (hn : n = 1 ∨ n = 31) :
    verifyAcc input n = 0 ↔ input = patternedInput.extract 0 n :=
  ⟨eq_extract_of_verifyAcc_short input n hsize hn,
   verifyAcc_of_extract_short input n hsize hn⟩
end Challenge.Ripemd160.Submission.Proofs.Bytecode.VerifierLogic
