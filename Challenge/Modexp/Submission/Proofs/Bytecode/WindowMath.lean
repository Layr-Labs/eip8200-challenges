import Challenge.Modexp.Spec
import Challenge.EvmProof.Bytes
import Mathlib.Tactic.Ring

set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/-!
# Four-bit window arithmetic

Artifact-independent semantics for one exponent byte and for a prefix of
bytes.  The execution proof only has to show that its table lookup implements
`nibbleStep`; this module then supplies the MODEXP exponent invariant.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowMath

open EvmSemantics
open EvmSemantics.EVM

theorem mulMod_toNat (left right modulus : UInt256)
    (hmodulus : 0 < modulus.toNat) :
    (UInt256.mulMod left right modulus).toNat =
      (left.toNat * right.toNat) % modulus.toNat := by
  unfold UInt256.mulMod
  have hval : modulus.val.val ≠ 0 := Nat.ne_of_gt hmodulus
  rw [if_neg hval]
  rw [Challenge.EvmProof.Word.word_toNat_ofNat]
  apply Nat.mod_eq_of_lt
  exact (Nat.mod_lt _ hmodulus).trans modulus.val.isLt

private theorem left_mod_mul (a b modulus : Nat) :
    ((a % modulus) * b) % modulus = (a * b) % modulus := by
  rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]

private theorem mul_mod_reduced (a b modulus : Nat) :
    ((a % modulus) * (b % modulus)) % modulus =
      (a * b) % modulus :=
  (Nat.mul_mod a b modulus).symm

private theorem right_mod_mul (a b modulus : Nat) :
    (a * (b % modulus)) % modulus = (a * b) % modulus := by
  rw [Nat.mul_comm a, left_mod_mul, Nat.mul_comm b]

def squareAfter (modulus : Nat) : Nat → Nat → Nat
  | 0, acc => acc
  | count + 1, acc =>
      let previous := squareAfter modulus count acc
      (previous * previous) % modulus

def squareWordAfter (modulus : UInt256) : Nat → UInt256 → UInt256
  | 0, acc => acc
  | count + 1, acc =>
      let previous := squareWordAfter modulus count acc
      UInt256.mulMod previous previous modulus

theorem squareWordAfter_toNat (modulus acc : UInt256) (count : Nat)
    (hmodulus : 0 < modulus.toNat) :
    (squareWordAfter modulus count acc).toNat =
      squareAfter modulus.toNat count acc.toNat := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [squareWordAfter, squareAfter,
        mulMod_toNat _ _ _ hmodulus, ih]

theorem squareAfter_succ_eq (modulus acc count : Nat) :
    squareAfter modulus (count + 1) acc =
      acc ^ (2 ^ (count + 1)) % modulus := by
  induction count with
  | zero => simp [squareAfter, pow_two]
  | succ count ih =>
      rw [squareAfter, ih, mul_mod_reduced]
      congr 1
      calc
        acc ^ (2 ^ (count + 1)) * acc ^ (2 ^ (count + 1)) =
            (acc ^ (2 ^ (count + 1))) ^ 2 := (pow_two _).symm
        _ = acc ^ (2 ^ (count + 1) * 2) := by rw [← Nat.pow_mul]
        _ = acc ^ (2 ^ (count + 1 + 1)) := by
          congr 1

theorem squareWordFour_toNat (modulus acc : UInt256)
    (hmodulus : 0 < modulus.toNat) :
    (squareWordAfter modulus 4 acc).toNat =
      acc.toNat ^ 16 % modulus.toNat := by
  rw [squareWordAfter_toNat modulus acc 4 hmodulus,
    show 4 = 3 + 1 by omega, squareAfter_succ_eq]
  norm_num

/-- Exact table word shape: slots zero and one are stored unreduced; every
later slot is the preceding word multiplied by the base modulo `modulus`. -/
def tableWord (base modulus : UInt256) : Nat → UInt256
  | 0 => UInt256.ofNat 1
  | index + 1 =>
      if index = 0 then base
      else UInt256.mulMod (tableWord base modulus index) base modulus

theorem tableWord_mod (base modulus : UInt256) (index : Nat)
    (hmodulus : 0 < modulus.toNat) :
    (tableWord base modulus index).toNat % modulus.toNat =
      base.toNat ^ index % modulus.toNat := by
  induction index with
  | zero => simp [tableWord]
  | succ index ih =>
      by_cases hzero : index = 0
      · subst index
        simp [tableWord]
      · rw [tableWord, if_neg hzero, mulMod_toNat _ _ _ hmodulus,
          Nat.mod_mod]
        calc
          (tableWord base modulus index).toNat * base.toNat %
                modulus.toNat =
              (((tableWord base modulus index).toNat % modulus.toNat) *
                base.toNat) % modulus.toNat :=
            (left_mod_mul (tableWord base modulus index).toNat base.toNat
              modulus.toNat).symm
          _ = ((base.toNat ^ index % modulus.toNat) * base.toNat) %
                modulus.toNat := by rw [ih]
          _ = (base.toNat ^ index * base.toNat) % modulus.toNat :=
            left_mod_mul (base.toNat ^ index) base.toNat modulus.toNat
          _ = base.toNat ^ (index + 1) % modulus.toNat := by
            rw [Nat.pow_succ]

def nibbleStep (modulus base acc nibble : Nat) : Nat :=
  (acc ^ 16 * base ^ nibble) % modulus

def nibbleWordStep (modulus base acc : UInt256) (nibble : Nat) : UInt256 :=
  UInt256.mulMod (squareWordAfter modulus 4 acc)
    (tableWord base modulus nibble) modulus

theorem nibbleWordStep_toNat (modulus base acc : UInt256) (nibble : Nat)
    (hmodulus : 0 < modulus.toNat) :
    (nibbleWordStep modulus base acc nibble).toNat =
      nibbleStep modulus.toNat base.toNat acc.toNat nibble := by
  rw [nibbleWordStep, mulMod_toNat _ _ _ hmodulus,
    squareWordFour_toNat modulus acc hmodulus]
  unfold nibbleStep
  calc
    (acc.toNat ^ 16 % modulus.toNat) *
          (tableWord base modulus nibble).toNat % modulus.toNat =
        ((acc.toNat ^ 16 % modulus.toNat) *
          ((tableWord base modulus nibble).toNat % modulus.toNat)) %
            modulus.toNat :=
      (right_mod_mul (acc.toNat ^ 16 % modulus.toNat)
        (tableWord base modulus nibble).toNat modulus.toNat).symm
    _ = ((acc.toNat ^ 16 % modulus.toNat) *
          (base.toNat ^ nibble % modulus.toNat)) % modulus.toNat := by
      rw [tableWord_mod base modulus nibble hmodulus]
    _ = (acc.toNat ^ 16 * base.toNat ^ nibble) % modulus.toNat :=
      mul_mod_reduced (acc.toNat ^ 16) (base.toNat ^ nibble) modulus.toNat

def byteStep (modulus base acc byte : Nat) : Nat :=
  nibbleStep modulus base
    (nibbleStep modulus base acc (byte / 16)) (byte % 16)

def byteWordStep (modulus base acc : UInt256) (byte : Nat) : UInt256 :=
  nibbleWordStep modulus base
    (nibbleWordStep modulus base acc (byte / 16)) (byte % 16)

theorem byteWordStep_toNat (modulus base acc : UInt256) (byte : Nat)
    (hmodulus : 0 < modulus.toNat) :
    (byteWordStep modulus base acc byte).toNat =
      byteStep modulus.toNat base.toNat acc.toNat byte := by
  rw [byteWordStep, nibbleWordStep_toNat _ _ _ _ hmodulus,
    nibbleWordStep_toNat _ _ _ _ hmodulus]
  rfl

def exponentByte (input : ByteArray) (offset index : Nat) : Nat :=
  (YulSemantics.EVM.byteFrom input.toList (offset + index)).toNat

def afterBytes (input : ByteArray) (offset modulus base : Nat) :
    Nat → Nat → Nat
  | 0, acc => acc
  | count + 1, acc => byteStep modulus base
      (afterBytes input offset modulus base count acc)
      (exponentByte input offset count)

theorem afterBytes_add (input : ByteArray)
    (offset modulus base left right acc : Nat) :
    afterBytes input offset modulus base (left + right) acc =
      afterBytes input (offset + left) modulus base right
        (afterBytes input offset modulus base left acc) := by
  induction right with
  | zero => rfl
  | succ right ih =>
      rw [Nat.add_succ, afterBytes, ih, afterBytes]
      have hbyte : exponentByte input offset (left + right) =
          exponentByte input (offset + left) right := by
        unfold exponentByte
        congr 2
        omega
      rw [hbyte]

def chunkWordStep (modulus base acc word : UInt256) : UInt256 :=
  let after0 := byteWordStep modulus base acc
    (UInt256.byteAt (UInt256.ofNat 0) word).toNat
  let after1 := byteWordStep modulus base after0
    (UInt256.byteAt (UInt256.ofNat 1) word).toNat
  let after2 := byteWordStep modulus base after1
    (UInt256.byteAt (UInt256.ofNat 2) word).toNat
  byteWordStep modulus base after2
    (UInt256.byteAt (UInt256.ofNat 3) word).toNat

theorem chunkWordStep_toNat (modulus base acc word : UInt256)
    (hmodulus : 0 < modulus.toNat) :
    (chunkWordStep modulus base acc word).toNat =
      byteStep modulus.toNat base.toNat
        (byteStep modulus.toNat base.toNat
          (byteStep modulus.toNat base.toNat
            (byteStep modulus.toNat base.toNat acc.toNat
              (UInt256.byteAt (UInt256.ofNat 0) word).toNat)
            (UInt256.byteAt (UInt256.ofNat 1) word).toNat)
          (UInt256.byteAt (UInt256.ofNat 2) word).toNat)
        (UInt256.byteAt (UInt256.ofNat 3) word).toNat := by
  unfold chunkWordStep
  rw [byteWordStep_toNat _ _ _ _ hmodulus,
    byteWordStep_toNat _ _ _ _ hmodulus,
    byteWordStep_toNat _ _ _ _ hmodulus,
    byteWordStep_toNat _ _ _ _ hmodulus]

private theorem byteAtRead_toNat (input : ByteArray) (offset index : Nat)
    (hindex : index < 32) :
    (UInt256.byteAt (UInt256.ofNat index)
      (MachineState.readWord input offset)).toNat =
        exponentByte input offset index := by
  have h := congrArg UInt256.toNat
    (Challenge.EvmProof.Bytes.byteAt_readWord input offset index hindex)
  rw [Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt
      ((YulSemantics.EVM.byteFrom input.toList (offset + index)).toNat_lt.trans
        (by norm_num))] at h
  exact h

theorem chunkReadWord_toNat (input : ByteArray) (offset : Nat)
    (modulus base acc : UInt256) (hmodulus : 0 < modulus.toNat) :
    (chunkWordStep modulus base acc (MachineState.readWord input offset)).toNat =
      afterBytes input offset modulus.toNat base.toNat 4 acc.toNat := by
  rw [chunkWordStep_toNat modulus base acc _ hmodulus,
    byteAtRead_toNat input offset 0 (by norm_num),
    byteAtRead_toNat input offset 1 (by norm_num),
    byteAtRead_toNat input offset 2 (by norm_num),
    byteAtRead_toNat input offset 3 (by norm_num)]
  rfl

/-- Word-level loop model used by the concrete bytecode: one calldata word is
loaded for every four processed exponent bytes. -/
def afterChunksWord (input : ByteArray) (offset : Nat)
    (modulus base : UInt256) : Nat → UInt256 → UInt256
  | 0, acc => acc
  | count + 1, acc =>
      chunkWordStep modulus base (afterChunksWord input offset modulus base
        count acc) (MachineState.readWord input (offset + 4 * count))

theorem afterChunksWord_toNat (input : ByteArray) (offset : Nat)
    (modulus base acc : UInt256) (count : Nat)
    (hmodulus : 0 < modulus.toNat) :
    (afterChunksWord input offset modulus base count acc).toNat =
      afterBytes input offset modulus.toNat base.toNat (4 * count) acc.toNat := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [afterChunksWord,
        chunkReadWord_toNat input (offset + 4 * count) modulus base _ hmodulus,
        ih]
      rw [show 4 * (count + 1) = 4 * count + 4 by omega,
        afterBytes_add input offset modulus.toNat base.toNat (4 * count) 4
          acc.toNat]

/-- Two four-bit steps are one base-256 Horner step. -/
theorem byteStep_eq (modulus base acc byte : Nat) :
    byteStep modulus base acc byte =
      (acc ^ 256 * base ^ byte) % modulus := by
  unfold byteStep nibbleStep
  let high := byte / 16
  let low := byte % 16
  let inner := acc ^ 16 * base ^ high
  calc
    (((inner % modulus) ^ 16 * base ^ low) % modulus) =
        ((((inner % modulus) ^ 16 % modulus) * base ^ low) % modulus) :=
      (left_mod_mul ((inner % modulus) ^ 16) (base ^ low) modulus).symm
    _ = (((inner ^ 16 % modulus) * base ^ low) % modulus) := by
      rw [← Nat.pow_mod]
    _ = ((inner ^ 16 * base ^ low) % modulus) :=
      left_mod_mul (inner ^ 16) (base ^ low) modulus
    _ = (acc ^ 256 * base ^ byte) % modulus := by
      congr 1
      dsimp [inner, high, low]
      rw [Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul,
        show 16 * 16 = 256 by norm_num, Nat.mul_assoc, ← Nat.pow_add]
      congr 2
      rw [Nat.mul_comm (byte / 16) 16]
      exact Nat.div_add_mod byte 16

theorem byteStep_lt (modulus base acc byte : Nat) (hmodulus : 0 < modulus) :
    byteStep modulus base acc byte < modulus := by
  unfold byteStep nibbleStep
  exact Nat.mod_lt _ hmodulus

theorem afterBytes_lt (input : ByteArray) (offset modulus base acc count : Nat)
    (hmodulus : 0 < modulus) (hacc : acc < modulus) :
    afterBytes input offset modulus base count acc < modulus := by
  induction count with
  | zero => exact hacc
  | succ count ih =>
      rw [afterBytes]
      exact byteStep_lt modulus base _ _ hmodulus

/-- A processed byte prefix is the corresponding base-256 exponent prefix. -/
theorem afterBytes_eq (input : ByteArray) (offset modulus base acc count : Nat)
    (hacc : acc < modulus) :
    afterBytes input offset modulus base count acc =
      (acc ^ (256 ^ count) *
        base ^ (Precompile.bytesToNatPadded input offset count)) % modulus := by
  induction count with
  | zero =>
      simp [afterBytes, Challenge.EvmProof.Bytes.bytesToNatPadded_zero_width,
        Nat.mod_eq_of_lt hacc]
  | succ count ih =>
      rw [afterBytes, byteStep_eq, ih,
        Challenge.EvmProof.Bytes.bytesToNatPadded_succ]
      let a := acc ^ (256 ^ count)
      let b := base ^ (Precompile.bytesToNatPadded input offset count)
      let digit := exponentByte input offset count
      change ((((a * b) % modulus) ^ 256 * base ^ digit) % modulus) = _
      calc
        (((a * b) % modulus) ^ 256 * base ^ digit) % modulus =
            ((((a * b) % modulus) ^ 256 % modulus) * base ^ digit) %
              modulus :=
          (left_mod_mul (((a * b) % modulus) ^ 256)
            (base ^ digit) modulus).symm
        _ = (((a * b) ^ 256 % modulus) * base ^ digit) % modulus := by
          rw [← Nat.pow_mod]
        _ = ((a * b) ^ 256 * base ^ digit) % modulus :=
          left_mod_mul ((a * b) ^ 256) (base ^ digit) modulus
        _ = (acc ^ (256 ^ (count + 1)) *
              base ^
                (Precompile.bytesToNatPadded input offset count * 256 +
                  digit)) % modulus := by
          congr 1
          simp only [a, b, Nat.pow_succ, Nat.pow_mul, Nat.pow_add]
          ring

/-- Starting from the reduced multiplicative identity yields ordinary modular
exponentiation by the processed byte prefix. -/
theorem afterBytes_one (input : ByteArray) (offset modulus base count : Nat)
    (hmodulus : 0 < modulus) :
    afterBytes input offset modulus base count (1 % modulus) =
      base ^ (Precompile.bytesToNatPadded input offset count) % modulus := by
  rw [afterBytes_eq input offset modulus base (1 % modulus) count
    (Nat.mod_lt _ hmodulus)]
  by_cases hone : modulus = 1
  · subst modulus
    calc
      (1 % 1) ^ (256 ^ count) *
            base ^ (Precompile.bytesToNatPadded input offset count) % 1 = 0 :=
        Nat.mod_one _
      _ = base ^ (Precompile.bytesToNatPadded input offset count) % 1 :=
        (Nat.mod_one _).symm
  · have hidentity : 1 % modulus = 1 := Nat.mod_eq_of_lt (by omega)
    rw [hidentity]
    simp

/-- Processing at least one byte makes the literal EVM accumulator `1`
equivalent to the mathematically reduced identity `1 % modulus`. -/
theorem afterBytes_literal_one (input : ByteArray)
    (offset modulus base count : Nat) :
    afterBytes input offset modulus base (count + 1) 1 =
      afterBytes input offset modulus base (count + 1) (1 % modulus) := by
  by_cases hzero : modulus = 0
  · subst modulus
    simp
  by_cases hone : modulus = 1
  · subst modulus
    rw [afterBytes, afterBytes]
    unfold byteStep nibbleStep
    rw [Nat.mod_one, Nat.mod_one]
  have hlt : 1 < modulus := by omega
  rw [Nat.mod_eq_of_lt hlt]

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowMath
