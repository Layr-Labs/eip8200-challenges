import Challenge.Modexp.Submission.Proofs.Bytecode.WordExit
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
/-!
# Correctness of the one-word MODEXP arithmetic

The bytecode uses a branchless square-and-multiply update.  These lemmas
bridge its `UInt256` bitwise expression to ordinary modular arithmetic and
then to the padded EIP-198 exponent parser.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WordCorrect

open EvmSemantics
open EvmSemantics.EVM
open Word
open WordExit

theorem land_toNat (a b : UInt256) :
    (UInt256.land a b).toNat = (a.toNat &&& b.toNat) := by
  cases a with | mk a =>
  cases b with | mk b =>
  simp only [UInt256.land, UInt256.toNat]
  unfold Fin.land
  simp only
  exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt Nat.and_le_left a.isLt)

theorem xor_toNat (a b : UInt256) :
    (UInt256.xor a b).toNat = (a.toNat ^^^ b.toNat) := by
  cases a with | mk a =>
  cases b with | mk b =>
  simp only [UInt256.xor, UInt256.toNat]
  unfold Fin.xor
  simp only
  exact Nat.mod_eq_of_lt (Nat.xor_lt_two_pow a.isLt b.isLt)

theorem ofNat_toNat (a : UInt256) : UInt256.ofNat a.toNat = a := by
  apply Challenge.EvmProof.Word.word_ext
  rw [Challenge.EvmProof.Word.word_toNat_ofNat]
  exact Nat.mod_eq_of_lt a.val.isLt

theorem select_zero (x y : UInt256) :
    UInt256.xor x (UInt256.land (UInt256.xor x y)
      (UInt256.ofNat 0 - UInt256.ofNat 0)) = x := by
  apply Challenge.EvmProof.Word.word_ext
  rw [xor_toNat, land_toNat, xor_toNat]
  have hmask : UInt256.ofNat 0 - UInt256.ofNat 0 = UInt256.ofNat 0 := by
    decide
  rw [hmask, Challenge.EvmProof.Word.word_toNat_ofNat]
  norm_num

theorem select_one (x y : UInt256) :
    UInt256.xor x (UInt256.land (UInt256.xor x y)
      (UInt256.ofNat 0 - UInt256.ofNat 1)) = y := by
  apply Challenge.EvmProof.Word.word_ext
  rw [xor_toNat, land_toNat, xor_toNat]
  have hmask : UInt256.ofNat 0 - UInt256.ofNat 1 =
      UInt256.ofNat (2 ^ 256 - 1) := by decide
  rw [hmask, Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : 2 ^ 256 - 1 < 2 ^ 256),
    Nat.and_two_pow_sub_one_eq_mod]
  have hxor : (x.toNat ^^^ y.toNat) % 2 ^ 256 = x.toNat ^^^ y.toNat :=
    Nat.mod_eq_of_lt (Nat.xor_lt_two_pow x.val.isLt y.val.isLt)
  rw [hxor, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]

def exponentBitNat (byte : UInt256) (j : Nat) : Nat :=
  (byte.toNat >>> (7 - j)) % 2

theorem exponentBit_eq (byte : UInt256) (j : Nat) (hj : j < 8) :
    exponentBit byte j = UInt256.ofNat (exponentBitNat byte j) := by
  have hshift := Challenge.EvmProof.Word.shiftRight_ofNat
    (value := byte.toNat) (shift := 7 - j) byte.val.isLt (by omega)
  have hword := ofNat_toNat byte
  calc
    exponentBit byte j = UInt256.land
        (UInt256.ofNat (byte.toNat >>> (7 - j))) (UInt256.ofNat 1) := by
      unfold exponentBit
      rw [show UInt256.shiftRight byte (UInt256.ofNat (7 - j)) =
          UInt256.ofNat (byte.toNat >>> (7 - j)) by
        calc
          UInt256.shiftRight byte (UInt256.ofNat (7 - j)) =
              UInt256.shiftRight (UInt256.ofNat byte.toNat)
                (UInt256.ofNat (7 - j)) := by rw [hword]
          _ = UInt256.ofNat (byte.toNat >>> (7 - j)) := hshift]
    _ = UInt256.ofNat (exponentBitNat byte j) := by
      apply Challenge.EvmProof.Word.word_ext
      unfold exponentBitNat
      rw [land_toNat, Challenge.EvmProof.Word.word_toNat_ofNat,
        Challenge.EvmProof.Word.word_toNat_ofNat,
        Challenge.EvmProof.Word.word_toNat_ofNat]
      have hsrmod : (byte.toNat >>> (7 - j)) % 2 ^ 256 =
          byte.toNat >>> (7 - j) := Nat.mod_eq_of_lt
            (Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) byte.val.isLt)
      have h1mod : 1 % 2 ^ 256 = 1 :=
        Nat.mod_eq_of_lt (by norm_num)
      simp only [hsrmod, h1mod]
      change ((byte.toNat >>> (7 - j)) &&& 1) =
        ((byte.toNat >>> (7 - j)) % 2) % 2 ^ 256
      rw [show (1 : Nat) = 2 ^ 1 - 1 by norm_num,
        Nat.and_two_pow_sub_one_eq_mod,
        Nat.mod_eq_of_lt
          (by omega : (byte.toNat >>> (7 - j)) % 2 < 2 ^ 256)]

theorem exponentBitNat_zero_or_one (byte : UInt256) (j : Nat) :
    exponentBitNat byte j = 0 ∨ exponentBitNat byte j = 1 := by
  unfold exponentBitNat
  omega

theorem mulMod_toNat (a b : UInt256) (modulus : Nat)
    (hmodpos : 0 < modulus) (hmodlt : modulus < 2 ^ 256) :
    (UInt256.mulMod a b (UInt256.ofNat modulus)).toNat =
      (a.toNat * b.toNat) % modulus := by
  unfold UInt256.mulMod
  have hmword : (UInt256.ofNat modulus).val.val ≠ 0 := by
    change (UInt256.ofNat modulus).toNat ≠ 0
    rw [Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt hmodlt]
    omega
  rw [if_neg hmword, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt hmodlt,
    Nat.mod_eq_of_lt ((Nat.mod_lt _ hmodpos).trans hmodlt)]

theorem mulMod_ofNat (a b modulus : Nat)
    (hmodpos : 0 < modulus) (hmodlt : modulus < 2 ^ 256)
    (ha : a < 2 ^ 256) (hb : b < 2 ^ 256) :
    UInt256.mulMod (UInt256.ofNat a) (UInt256.ofNat b)
        (UInt256.ofNat modulus) =
      UInt256.ofNat ((a * b) % modulus) := by
  apply Challenge.EvmProof.Word.word_ext
  rw [mulMod_toNat _ _ modulus hmodpos hmodlt,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb,
    Nat.mod_eq_of_lt ((Nat.mod_lt _ hmodpos).trans hmodlt)]

theorem mod_ofNat (value modulus : Nat) (hmodpos : 0 < modulus)
    (hmodlt : modulus < 2 ^ 256) (hvalue : value < 2 ^ 256) :
    UInt256.ofNat value % UInt256.ofNat modulus =
      UInt256.ofNat (value % modulus) := by
  change UInt256.mod (UInt256.ofNat value) (UInt256.ofNat modulus) = _
  unfold UInt256.mod
  have hmword : (UInt256.ofNat modulus).val.val ≠ 0 := by
    change (UInt256.ofNat modulus).toNat ≠ 0
    rw [Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt hmodlt]
    omega
  rw [if_neg hmword]
  apply Challenge.EvmProof.Word.word_ext
  change ((UInt256.ofNat value).val % (UInt256.ofNat modulus).val).val = _
  rw [Fin.val_mod]
  change (UInt256.ofNat value).toNat % (UInt256.ofNat modulus).toNat = _
  rw [Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt hvalue, Nat.mod_eq_of_lt hmodlt,
    Nat.mod_eq_of_lt ((Nat.mod_lt _ hmodpos).trans hmodlt)]

def baseNat (input : ByteArray) : Nat :=
  Precompile.bytesToNatPadded input 96 (baseSize input)

def exponentNat (input : ByteArray) : Nat :=
  Precompile.bytesToNatPadded input (expOffset input) (exponentSize input)

def wordBase (input : ByteArray) : UInt256 :=
  baseAfter input (baseSize input)

def wordInitialAcc (input : ByteArray) : UInt256 :=
  UInt256.ofNat 1 % UInt256.ofNat (modulusValue input)

/-- The one-word route finishes only with an empty exponent: the result is `1 % modulus`. -/
def wordResult (input : ByteArray) : UInt256 :=
  wordInitialAcc input

theorem wordBase_correct (input : ByteArray) (hvalid : ValidInput input)
    (hmodpos : 0 < modulusValue input) (hmodlt : modulusValue input < 2 ^ 256) :
    wordBase input = UInt256.ofNat (baseNat input % modulusValue input) := by
  rcases hvalid with ⟨_, hb, he, hm⟩
  exact baseAfter_correct input (baseSize input) hmodpos hmodlt hb (by rfl)

theorem wordInitialAcc_correct (input : ByteArray)
    (hmodpos : 0 < modulusValue input) (hmodlt : modulusValue input < 2 ^ 256) :
    wordInitialAcc input = UInt256.ofNat (1 % modulusValue input) := by
  exact mod_ofNat 1 (modulusValue input) hmodpos hmodlt (by norm_num)

theorem residue_power_eq_modPow (base exponent modulus count : Nat)
    (hmodpos : 0 < modulus) :
    (((1 % modulus) ^ (256 ^ count)) *
        ((base % modulus) ^ exponent)) % modulus =
      Precompile.modPow base exponent modulus := by
  rw [Algorithm.modPow_eq, if_neg (Nat.ne_of_gt hmodpos)]
  by_cases hm1 : modulus = 1
  · subst modulus
    simp [Nat.mod_one]
  · have hone : 1 < modulus := by omega
    rw [Nat.mod_eq_of_lt hone]
    simp only [one_pow, one_mul]
    exact (Nat.pow_mod base exponent modulus).symm

theorem wordResult_correct (input : ByteArray) (he : exponentSize input = 0)
    (hmodpos : 0 < modulusValue input) (hmodlt : modulusValue input < 2 ^ 256) :
    wordResult input = UInt256.ofNat
      (Precompile.modPow (baseNat input) (exponentNat input)
        (modulusValue input)) := by
  rw [wordResult, wordInitialAcc_correct input hmodpos hmodlt, exponentNat, he,
    Challenge.EvmProof.Bytes.bytesToNatPadded_zero_width]
  apply congrArg UInt256.ofNat
  rw [← residue_power_eq_modPow (baseNat input) 0 (modulusValue input) 0 hmodpos]
  simp

theorem outputShift_eq (input : ByteArray) (hword : modulusSize input ≤ 32) :
    outputShift input = UInt256.ofNat ((32 - modulusSize input) * 8) := by
  have hsub := Challenge.EvmProof.Word.ofNat_sub_ofNat hword
    (by norm_num : 32 < 2 ^ 256)
  unfold outputShift
  rw [show (32 : UInt256) = UInt256.ofNat 32 by decide, hsub,
    Challenge.EvmProof.Word.shiftLeft_ofNat] <;>
    norm_num [Nat.shiftLeft_eq] <;> omega

theorem outputWord_toNat (input : ByteArray) (n : Nat)
    (hmsize : 0 < modulusSize input) (hword : modulusSize input ≤ 32)
    (hn : n < 256 ^ modulusSize input) :
    (outputWord input (UInt256.ofNat n)).toNat =
      n * 256 ^ (32 - modulusSize input) := by
  have hfactor : 0 < 256 ^ (32 - modulusSize input) := pow_pos (by norm_num) _
  have hmul := Nat.mul_lt_mul_of_pos_right hn hfactor
  have hbound : n * 256 ^ (32 - modulusSize input) < 2 ^ 256 := by
    rw [show (2 : Nat) ^ 256 = 256 ^ 32 by norm_num]
    calc
      n * 256 ^ (32 - modulusSize input) <
          256 ^ (modulusSize input) * 256 ^ (32 - modulusSize input) := hmul
      _ = 256 ^ 32 := by rw [← Nat.pow_add]; congr 1; omega
  have hn256 : n < 2 ^ 256 := by
    calc
      n < 256 ^ (modulusSize input) := hn
      _ ≤ 256 ^ 32 := pow_le_pow_right₀ (by omega) hword
      _ = 2 ^ 256 := by norm_num
  unfold outputWord
  rw [outputShift_eq input hword,
    Challenge.EvmProof.Word.shiftLeft_ofNat hn256 (by omega) (by
      simpa [show (2 : Nat) ^ ((32 - modulusSize input) * 8) =
          256 ^ (32 - modulusSize input) by
        rw [show (256 : Nat) = 2 ^ 8 by norm_num, ← Nat.pow_mul]
        congr 1
        omega] using hbound),
    Challenge.EvmProof.Word.word_toNat_ofNat]
  rw [show (2 : Nat) ^ ((32 - modulusSize input) * 8) =
      256 ^ (32 - modulusSize input) by
    rw [show (256 : Nat) = 2 ^ 8 by norm_num, ← Nat.pow_mul]
    congr 1
    omega,
    Nat.mod_eq_of_lt hbound]

theorem shifted_div (n width k : Nat) (hwidth : width ≤ 32) (hk : k < width) :
    n * 256 ^ (32 - width) / 256 ^ (32 - 1 - k) =
      n / 256 ^ (width - 1 - k) := by
  have hexponent : 32 - 1 - k = (32 - width) + (width - 1 - k) := by
    omega
  rw [hexponent, Nat.pow_add, Nat.mul_comm (256 ^ (32 - width))]
  exact Nat.mul_div_mul_right n (256 ^ (width - 1 - k))
    (pow_pos (by norm_num) _)

theorem outputMemory_readPadded (input : ByteArray) (n : Nat)
    (hmsize : 0 < modulusSize input) (hword : modulusSize input ≤ 32)
    (hn : n < 256 ^ modulusSize input) :
    MachineState.readPadded (outputMemory input (UInt256.ofNat n)) 0
        (modulusSize input) =
      Precompile.natToBytes n (modulusSize input) := by
  apply ByteArray.ext_getElem
  · rw [Challenge.EvmProof.Memory.readPadded_size]
    rw [Precompile.natToBytes,
      YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  · intro k hleft hright
    have hk : k < modulusSize input := by
      simpa [Precompile.natToBytes,
        YulEvmCompiler.BytesLemmas.natToBytesPadded_size] using hright
    rw [← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hleft,
      ← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hright,
      Challenge.EvmProof.Memory.readPadded_getElem?_getD,
      if_pos hk]
    unfold outputMemory
    rw [MachineState.writeBytes_getElem?_getD, if_pos (by
      constructor
      · omega
      · simp [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
        omega)]
    rw [show 0 + k - 0 = k by omega,
      YulEvmCompiler.BytesLemmas.natToBytesPadded_getElem?_getD _ 32 k
        (by omega),
      Precompile.natToBytes,
      YulEvmCompiler.BytesLemmas.natToBytesPadded_getElem?_getD _
        (modulusSize input) k hk,
      outputWord_toNat input n hmsize hword hn,
      shifted_div n (modulusSize input) k hword hk]

theorem wordFinalState_result (input : ByteArray) (_hvalid : ValidInput input)
    (he : exponentSize input = 0) (hmsize : 0 < modulusSize input) (hword : modulusSize input ≤ 32)
    (hmodpos : 0 < modulusValue input) :
    (wordFinalState input (wordResult input) (wordBase input)).toResult =
      .returned (spec input) := by
  have hmodWidth : modulusValue input < 256 ^ modulusSize input :=
    Challenge.EvmProof.Bytes.bytesToNatPadded_lt_pow input
      (modulusOffset input) (modulusSize input)
  have hmodlt : modulusValue input < 2 ^ 256 := by
    calc
      modulusValue input < 256 ^ modulusSize input := hmodWidth
      _ ≤ 256 ^ 32 := pow_le_pow_right₀ (by omega) hword
      _ = 2 ^ 256 := by norm_num
  let result := Precompile.modPow (baseNat input) (exponentNat input)
    (modulusValue input)
  have hresult : result < 256 ^ modulusSize input :=
    (Algorithm.modPow_lt hmodpos).trans hmodWidth
  rw [show wordResult input = UInt256.ofNat result by
    exact wordResult_correct input he hmodpos hmodlt]
  change ExecutionResult.returned
      (MachineState.readPadded (outputMemory input (UInt256.ofNat result))
        0 (modulusSize input)) = ExecutionResult.returned (spec input)
  rw [outputMemory_readPadded input result hmsize hword hresult]
  congr 1
  simp [spec, Nat.ne_of_gt hmsize, result, baseNat, exponentNat,
    modulusValue, modulusOffset, expOffset, Nat.add_assoc]

end Challenge.Modexp.Submission.Proofs.Bytecode.WordCorrect
