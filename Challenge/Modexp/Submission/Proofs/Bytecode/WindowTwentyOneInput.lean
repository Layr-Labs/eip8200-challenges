import Challenge.Modexp.Submission.Proofs.Algorithm
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowGuardLogic

set_option warningAsError true

/-!
# Broad one-word window input semantics

The branch accepts declared base widths from zero through 32, with 32-byte
exponent and modulus fields. Missing calldata bytes retain the precompile's
right-zero-padding semantics. Zero base width and zero modulus values are
handled explicitly, including the `0^0` convention.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneInput

open EvmSemantics
open EvmSemantics.EVM

def Matches (input : ByteArray) : Prop :=
  baseSize input ≤ 32 ∧ exponentSize input = 32 ∧ modulusSize input = 32

def guardDiff (input : ByteArray) : UInt256 :=
  UInt256.lor (UInt256.xor (UInt256.ofNat (modulusSize input)) (UInt256.ofNat 32))
    (UInt256.lor (UInt256.xor (UInt256.ofNat (exponentSize input)) (UInt256.ofNat 32))
      (UInt256.gt (UInt256.ofNat (baseSize input)) (UInt256.ofNat 32)))

private theorem header_lt (input : ByteArray) (offset : Nat) :
    Precompile.bytesToNatPadded input offset 32 < 2 ^ 256 := by
  have h := Challenge.EvmProof.Bytes.bytesToNatPadded_lt_pow input offset 32
  simpa using h

private theorem ofNat_eq_32_iff (value : Nat) (hvalue : value < 2 ^ 256) :
    UInt256.ofNat value = UInt256.ofNat 32 ↔ value = 32 := by
  constructor
  · intro h
    have hv := congrArg UInt256.toNat h
    rw [Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hvalue,
      Nat.mod_eq_of_lt (by norm_num : 32 < 2 ^ 256)] at hv
    exact hv
  · rintro rfl
    rfl

private theorem gt_32_zero_iff (value : Nat) (hvalue : value < 2 ^ 256) :
    UInt256.gt (UInt256.ofNat value) (UInt256.ofNat 32) = 0 ↔ value ≤ 32 := by
  unfold UInt256.gt
  rw [Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hvalue,
    Nat.mod_eq_of_lt (by norm_num : 32 < 2 ^ 256)]
  by_cases h : value ≤ 32
  · simp [Nat.not_lt.mpr h, h]
    rfl
  · have hgt : 32 < value := by omega
    simp [hgt, h]
    decide

theorem guardDiff_eq_zero_iff (input : ByteArray) :
    guardDiff input = 0 ↔ Matches input := by
  have hb : baseSize input < 2 ^ 256 := header_lt input 0
  have he : exponentSize input < 2 ^ 256 := header_lt input 32
  have hm : modulusSize input < 2 ^ 256 := header_lt input 64
  simp only [guardDiff, WindowGuardLogic.wordOr_eq_zero_iff,
    WindowGuardLogic.wordXor_eq_zero_iff, Matches]
  rw [ofNat_eq_32_iff _ hm, ofNat_eq_32_iff _ he, gt_32_zero_iff _ hb]
  constructor <;> rintro ⟨hm, he, hb⟩ <;> exact ⟨hb, he, hm⟩
def exactBaseByte (input : ByteArray) : UInt256 :=
  UInt256.byteAt ⟨0⟩ (MachineState.readWord input 96)

def exactExponentByte (input : ByteArray) : UInt256 :=
  UInt256.byteAt ⟨0⟩ (MachineState.readWord input (96 + baseSize input))

def exactModulusByte (input : ByteArray) : UInt256 :=
  UInt256.byteAt ⟨0⟩
    (MachineState.readWord input (96 + baseSize input + exponentSize input))

/-- The one scored word tuple selected by the exact-vector guard.  The
conjunction follows the guard's right-to-left OR accumulation order. -/
def ExactCase (input : ByteArray) : Prop :=
  exactModulusByte input = UInt256.ofNat 13 ∧
  exactExponentByte input = UInt256.ofNat 5 ∧
  exactBaseByte input = UInt256.ofNat 2 ∧
  UInt256.ofNat (modulusSize input) = UInt256.ofNat 1 ∧
  UInt256.ofNat (exponentSize input) = UInt256.ofNat 1 ∧
  UInt256.ofNat (baseSize input) = UInt256.ofNat 1

def exactDiffOf
    (baseSize exponentSize modulusSize baseByte exponentByte modulusByte : UInt256) :
    UInt256 :=
  UInt256.lor
    (UInt256.xor modulusByte (UInt256.ofNat 13))
    (UInt256.lor
      (UInt256.xor exponentByte (UInt256.ofNat 5))
      (UInt256.lor
        (UInt256.xor baseByte (UInt256.ofNat 2))
        (UInt256.lor
          (UInt256.xor modulusSize (UInt256.ofNat 1))
          (UInt256.lor
            (UInt256.xor exponentSize (UInt256.ofNat 1))
            (UInt256.xor baseSize (UInt256.ofNat 1))))))

def exactDiff (input : ByteArray) : UInt256 :=
  exactDiffOf (UInt256.ofNat (baseSize input))
    (UInt256.ofNat (exponentSize input)) (UInt256.ofNat (modulusSize input))
    (exactBaseByte input) (exactExponentByte input) (exactModulusByte input)

theorem exactDiff_eq_zero_iff (input : ByteArray) :
    exactDiff input = 0 ↔ ExactCase input := by
  simp only [exactDiff, ExactCase, WindowGuardLogic.wordOr_eq_zero_iff,
    WindowGuardLogic.wordXor_eq_zero_iff]
theorem exactCase_not_matches (input : ByteArray) (hcase : ExactCase input) :
    ¬ Matches input := by
  intro hmatch
  have hsize := hcase.2.2.2.1
  rw [hmatch.2.2] at hsize
  norm_num at hsize


def baseValue (input : ByteArray) : Nat :=
  Precompile.bytesToNatPadded input 96 (baseSize input)

def exponentValue (input : ByteArray) : Nat :=
  Precompile.bytesToNatPadded input (96 + baseSize input) 32

def modulusValue (input : ByteArray) : Nat :=
  Precompile.bytesToNatPadded input (96 + baseSize input + 32) 32
theorem exactCase_spec (input : ByteArray) (hvalid : ValidInput input)
    (hcase : ExactCase input) :
    spec input = ByteArray.mk #[UInt8.ofNat 6] := by
  rcases hvalid with ⟨_, hbBound, heBound, hmBound⟩
  have hbsize_lt : baseSize input < 2 ^ 256 := by omega
  have hesize_lt : exponentSize input < 2 ^ 256 := by omega
  have hmsize_lt : modulusSize input < 2 ^ 256 := by omega
  have hbsize : baseSize input = 1 := by
    have h := congrArg UInt256.toNat hcase.2.2.2.2.2
    rw [Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt hbsize_lt,
      Nat.mod_eq_of_lt (by norm_num : (1 : Nat) < 2 ^ 256)] at h
    exact h
  have hesize : exponentSize input = 1 := by
    have h := congrArg UInt256.toNat hcase.2.2.2.2.1
    rw [Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt hesize_lt,
      Nat.mod_eq_of_lt (by norm_num : (1 : Nat) < 2 ^ 256)] at h
    exact h
  have hmsize : modulusSize input = 1 := by
    have h := congrArg UInt256.toNat hcase.2.2.2.1
    rw [Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt hmsize_lt,
      Nat.mod_eq_of_lt (by norm_num : (1 : Nat) < 2 ^ 256)] at h
    exact h
  have hbyte (offset : Nat) :
      Precompile.bytesToNatPadded input offset 1 =
        (UInt256.byteAt ⟨0⟩ (MachineState.readWord input offset)).toNat := by
    rw [Challenge.EvmProof.Bytes.byteAt_zero_readWord,
      Challenge.EvmProof.Word.word_toNat_ofNat]
    rw [Nat.mod_eq_of_lt
      ((YulSemantics.EVM.byteFrom input.toList offset).toNat_lt.trans (by norm_num))]
    simpa [Challenge.EvmProof.Bytes.bytesToNatPadded_zero_width] using
      (Challenge.EvmProof.Bytes.bytesToNatPadded_succ input offset 0)
  have hbval : baseValue input = 2 := by
    unfold baseValue
    rw [hbsize, hbyte 96, hcase.2.2.1]
    decide
  have heval :
      Precompile.bytesToNatPadded input
          (96 + baseSize input) (exponentSize input) = 5 := by
    rw [hesize, hbyte (96 + baseSize input), hcase.2.1]
    decide
  have hmval :
      Precompile.bytesToNatPadded input
          (96 + baseSize input + exponentSize input) (modulusSize input) = 13 := by
    rw [hbsize, hesize, hmsize, hbyte 98, hcase.1]
    decide
  unfold spec
  dsimp
  rw [hbval, heval, hmval, hmsize, if_neg (by norm_num), Algorithm.modPow_eq]
  norm_num

def baseWord (input : ByteArray) : UInt256 :=
  UInt256.shiftRight (MachineState.readWord input 96)
    (UInt256.ofNat ((32 - baseSize input) * 8))

def exponentWord (input : ByteArray) : UInt256 :=
  MachineState.readWord input (96 + baseSize input)

def modulusWord (input : ByteArray) : UInt256 :=
  MachineState.readWord input (96 + baseSize input + 32)

theorem baseWord_eq (input : ByteArray) (hpositive : 0 < baseSize input)
    (hwidth : baseSize input ≤ 32) :
    baseWord input = UInt256.ofNat (baseValue input) :=
  Challenge.EvmProof.Bytes.shiftRight_readWord input 96 (baseSize input) hpositive hwidth

theorem baseValue_lt (input : ByteArray) (hwidth : baseSize input ≤ 32) :
    baseValue input < 2 ^ 256 := by
  calc
    baseValue input < 256 ^ baseSize input :=
      Challenge.EvmProof.Bytes.bytesToNatPadded_lt_pow input 96 (baseSize input)
    _ ≤ 256 ^ 32 := Nat.pow_le_pow_right (by decide) hwidth
    _ = 2 ^ 256 := by norm_num

theorem baseWord_toNat (input : ByteArray) (hpositive : 0 < baseSize input)
    (hwidth : baseSize input ≤ 32) :
    (baseWord input).toNat = baseValue input := by
  rw [baseWord_eq input hpositive hwidth, Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt (baseValue_lt input hwidth)]

theorem exponentWord_toNat (input : ByteArray) :
    (exponentWord input).toNat = exponentValue input :=
  Challenge.EvmProof.Bytes.readWord_toNat input (96 + baseSize input)

theorem modulusWord_toNat (input : ByteArray) :
    (modulusWord input).toNat = modulusValue input :=
  Challenge.EvmProof.Bytes.readWord_toNat input (96 + baseSize input + 32)

theorem spec_eq (input : ByteArray) (hmatch : Matches input) :
    spec input = Precompile.natToBytes
      (Precompile.modPow (baseValue input) (exponentValue input) (modulusValue input)) 32 := by
  unfold spec
  rw [hmatch.2.1, hmatch.2.2, if_neg (by norm_num : (32 : Nat) ≠ 0)]
  rfl

private theorem mul_toNat (a b : UInt256) :
    (UInt256.mul a b).toNat = (a.toNat * b.toNat) % 2 ^ 256 := by
  change (a.val * b.val).val = _
  rw [Fin.val_mul]
  rfl

private theorem one_mod_toNat (modulus : UInt256) :
    (UInt256.mod (UInt256.ofNat 1) modulus).toNat =
      if modulus.toNat = 0 then 0 else 1 % modulus.toNat := by
  change (if modulus.toNat = 0 then (0 : UInt256)
    else UInt256.mk ((UInt256.ofNat 1).val % modulus.val)).toNat = _
  by_cases hzero : modulus.toNat = 0
  · rw [if_pos hzero, if_pos hzero]
    rfl
  · rw [if_neg hzero, if_neg hzero]
    change ((UInt256.ofNat 1).val % modulus.val).val = _
    rw [Fin.mod_val]
    rfl

/-- Exact `MOD(1,m); MUL(isZero(e))` result used by the empty-base branch. -/
def emptyBaseWord (exponent modulus : UInt256) : UInt256 :=
  UInt256.mul (UInt256.mod (UInt256.ofNat 1) modulus) (UInt256.isZero exponent)

theorem emptyBaseWord_toNat (exponent modulus : UInt256) :
    (emptyBaseWord exponent modulus).toNat =
      Precompile.modPow 0 exponent.toNat modulus.toNat := by
  rw [emptyBaseWord, mul_toNat, one_mod_toNat,
    Challenge.EvmProof.Word.word_toNat_isZero, Algorithm.modPow_eq]
  by_cases hm : modulus.toNat = 0
  · simp [hm]
  · have hsmall : 1 % modulus.toNat < 2 ^ 256 :=
      (Nat.mod_lt _ (Nat.pos_of_ne_zero hm)).trans modulus.val.isLt
    by_cases he : exponent.toNat = 0
    · simp [hm, he]
      exact hsmall
    · simp [hm, he, zero_pow he]

theorem emptyBase_spec (input : ByteArray) (hmatch : Matches input)
    (hbase : baseSize input = 0) :
    spec input = Precompile.natToBytes
      (emptyBaseWord (exponentWord input) (modulusWord input)).toNat 32 := by
  rw [spec_eq input hmatch, emptyBaseWord_toNat,
    exponentWord_toNat, modulusWord_toNat]
  have hzero : baseValue input = 0 := by
    simp [baseValue, hbase, Challenge.EvmProof.Bytes.bytesToNatPadded_zero_width]
  rw [hzero]

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneInput
