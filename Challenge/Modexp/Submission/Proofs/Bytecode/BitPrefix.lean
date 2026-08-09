import Challenge.Modexp.Submission.Proofs.Bytecode.Word
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
/-!
# Bit- and byte-level exponent arithmetic shared by the big path

The multi-limb (`modexpBig`) proof reuses a family of purely arithmetic
definitions and lemmas that the *previous*, bit-serial one-word path happened
to carry in its `WordCorrect` module.  The current one-word path is a 4-bit
windowed rewrite and no longer defines any of them, so they live here instead.

Nothing in this module mentions the one-word path's bytecode.  Every
declaration is carried over **verbatim** from the corresponding declaration in
`Challenge/Modexp/Reference/Proofs/Bytecode/WordCorrect.lean` (and, for
`exponentBit` and `byteWord_eq`, from `Reference/Proofs/Bytecode/Word.lean`),
where each is already proved against the same specification.  Keeping them
byte-identical to the reference means the carry-over is checkable by diff.

Source lines in the reference, in the order they appear below:
`WordCorrect` 39, `Word` 254, `Word` 332, `WordCorrect` 68, 71, 106, 223, 227,
231, 242, 279, 282, 304, 307, 351, 411, 414, 437.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.BitPrefix

open EvmSemantics
open EvmSemantics.EVM
open Word

theorem ofNat_toNat (a : UInt256) : UInt256.ofNat a.toNat = a := by
  apply Challenge.EvmProof.Word.word_ext
  rw [Challenge.EvmProof.Word.word_toNat_ofNat]
  exact Nat.mod_eq_of_lt a.val.isLt

def exponentBit (byte : UInt256) (j : Nat) : UInt256 :=
  UInt256.land
    (UInt256.shiftRight byte (UInt256.ofNat (7 - j))) (UInt256.ofNat 1)

theorem byteWord_eq (input : ByteArray) (offset : Nat)
    (hoffset : offset < 2 ^ 256) :
    byteWord input offset = UInt256.ofNat
      (YulSemantics.EVM.byteFrom input.toList offset).toNat := by
  unfold byteWord Accessors.calldataByteValue
  rw [Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt hoffset]
  change UInt256.byteAt ⟨0⟩ (MachineState.readWord input offset) = _
  exact Challenge.EvmProof.Bytes.byteAt_zero_readWord input offset

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

def bitPrefix (byte : UInt256) : Nat → Nat
  | 0 => 0
  | j + 1 => 2 * bitPrefix byte j + exponentBitNat byte j

theorem bitPrefix_ofNat_eight (n : Nat) (hn : n < 256) :
    bitPrefix (UInt256.ofNat n) 8 = n := by
  interval_cases n <;> decide

theorem bitPrefix_eight (byte : UInt256) (hbyte : byte.toNat < 256) :
    bitPrefix byte 8 = byte.toNat := by
  calc
    bitPrefix byte 8 = bitPrefix (UInt256.ofNat byte.toNat) 8 := by
      rw [ofNat_toNat]
    _ = byte.toNat := bitPrefix_ofNat_eight byte.toNat hbyte

theorem left_mod_mul (a b modulus : Nat) :
    ((a % modulus) * b) % modulus = (a * b) % modulus := by
  rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]

def exponentByte (input : ByteArray) (i : Nat) : UInt256 :=
  byteWord input (expOffset input + i)

theorem exponentByte_toNat (input : ByteArray) (i : Nat)
    (hvalid : ValidInput input) (hi : i < exponentSize input) :
    (exponentByte input i).toNat =
      (YulSemantics.EVM.byteFrom input.toList (expOffset input + i)).toNat := by
  rcases hvalid with ⟨_, hb, he, hm⟩
  have hoff : expOffset input + i < 2 ^ 256 := by
    simp only [expOffset]
    omega
  have h := congrArg UInt256.toNat
    (byteWord_eq input (expOffset input + i) hoff)
  rw [Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt
      ((YulSemantics.EVM.byteFrom input.toList (expOffset input + i)).toNat_lt.trans
        (by norm_num))] at h
  exact h

def natExpStep (modulus : Nat) (byte : UInt256) (acc base : Nat) : Nat :=
  (acc ^ 256 * base ^ byte.toNat) % modulus

def natExpAfter (input : ByteArray) (modulus base : Nat) :
    Nat → Nat → Nat
  | 0, acc => acc
  | i + 1, acc => natExpStep modulus (exponentByte input i)
      (natExpAfter input modulus base i acc) base

theorem natExpAfter_eq (input : ByteArray) (modulus base acc count : Nat)
    (hvalid : ValidInput input) (hcount : count ≤ exponentSize input)
    (hacc : acc < modulus) :
    natExpAfter input modulus base count acc =
      (acc ^ (256 ^ count) *
        base ^ (Precompile.bytesToNatPadded input (expOffset input) count)) %
        modulus := by
  induction count with
  | zero =>
      simp [natExpAfter, Challenge.EvmProof.Bytes.bytesToNatPadded_zero_width,
        Nat.mod_eq_of_lt hacc]
  | succ count ih =>
      rw [natExpAfter, natExpStep, ih (by omega),
        Challenge.EvmProof.Bytes.bytesToNatPadded_succ,
        exponentByte_toNat]
      · let a := acc ^ (256 ^ count)
        let b := base ^
          (Precompile.bytesToNatPadded input (expOffset input) count)
        let digit :=
          (YulSemantics.EVM.byteFrom input.toList (expOffset input + count)).toNat
        calc
          (((a * b) % modulus) ^ 256 * base ^ digit) % modulus =
              ((((a * b) % modulus) ^ 256 % modulus) * base ^ digit) %
                modulus := (left_mod_mul _ _ _).symm
          _ = (((a * b) ^ 256 % modulus) * base ^ digit) % modulus := by
            rw [← Nat.pow_mod]
          _ = ((a * b) ^ 256 * base ^ digit) % modulus :=
            left_mod_mul _ _ _
          _ = (acc ^ (256 ^ (count + 1)) *
                base ^
                  (Precompile.bytesToNatPadded input (expOffset input) count *
                    256 + digit)) % modulus := by
            congr 1
            simp only [a, b, Nat.pow_succ, Nat.pow_mul, Nat.pow_add]
            ring
      · exact hvalid
      · omega

def baseNat (input : ByteArray) : Nat :=
  Precompile.bytesToNatPadded input 96 (baseSize input)

def exponentNat (input : ByteArray) : Nat :=
  Precompile.bytesToNatPadded input (expOffset input) (exponentSize input)

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

end Challenge.Modexp.Submission.Proofs.Bytecode.BitPrefix
