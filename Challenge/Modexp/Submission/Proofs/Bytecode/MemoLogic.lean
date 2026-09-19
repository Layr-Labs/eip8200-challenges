import Challenge.Modexp.Submission.Proofs.Algorithm
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowGuardLogic

set_option warningAsError true

/-!
# Recognition logic of the fixed-vector block

The block at the legacy trampoline runs two tests on calldata.  The first
leaves `1 - bsize` and branches away unless it is zero; the second builds one
accumulator as the bitwise OR of three differences and branches away unless it
is zero.  This module states both words exactly as the machine builds them and
proves they vanish together exactly when the four calldata conditions hold.
Nothing here mentions the artifact.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.MemoLogic

open EvmSemantics
open EvmSemantics.EVM

/-- `0x2003ffff80`: the low 28 bytes of a declared modulus size of 32 followed
by the four operand bytes `03 ff ff 80`, read as one word at offset 68. -/
def tailConst : Nat := 137506062208

/-- The set of calldata the block recognises. -/
def Matches (input : ByteArray) : Prop :=
  baseSize input = 1 ∧ exponentSize input = 2 ∧
    MachineState.readWord input 68 = UInt256.ofNat tailConst ∧
    MachineState.readWord input 100 = 0

/-- The first test: `PUSH5 K PUSH1 68 CALLDATALOAD SUB` leaves `word68 - K`.
The most selective comparison runs first so that every other input leaves
after one test. -/
def widthGuard (input : ByteArray) : UInt256 :=
  MachineState.readWord input 68 - UInt256.ofNat tailConst

/-- The second test, in the order the block builds it: `SUB` yields top minus
second and `OR` yields top or second, so the nesting below is literal. -/
def tailGuard (input : ByteArray) : UInt256 :=
  UInt256.lor (MachineState.readWord input 100)
    (UInt256.lor (UInt256.ofNat 2 - UInt256.ofNat (exponentSize input))
      (UInt256.ofNat 1 - UInt256.ofNat (baseSize input)))

theorem toNat_inj (x y : UInt256) (h : x.toNat = y.toNat) : x = y := by
  obtain ⟨v⟩ := x
  obtain ⟨w⟩ := y
  simp only [UInt256.toNat] at h
  exact congrArg UInt256.mk (Fin.ext h)

theorem sub_eq_zero_iff (a b : UInt256) : a - b = 0 ↔ a = b := by
  have ha : a.toNat < 2 ^ 256 := a.val.isLt
  have hb : b.toNat < 2 ^ 256 := b.val.isLt
  have hzero : (0 : UInt256).toNat = 0 := by decide
  constructor
  · intro h
    have hv : (2 ^ 256 + a.toNat - b.toNat) % 2 ^ 256 = 0 := by
      rw [← Challenge.EvmProof.Word.word_toNat_sub, h, hzero]
    obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero hv
    have hk1 : k = 1 := by
      rcases Nat.lt_or_ge k 2 with h2 | h2
      · omega
      · exfalso
        have hmul : 2 ^ 256 * 2 ≤ 2 ^ 256 * k := Nat.mul_le_mul_left _ h2
        omega
    exact toNat_inj a b (by omega)
  · intro h
    subst h
    refine toNat_inj _ _ ?_
    rw [Challenge.EvmProof.Word.word_toNat_sub, hzero]
    have hid : 2 ^ 256 + a.toNat - a.toNat = 2 ^ 256 := by omega
    rw [hid, Nat.mod_self]

theorem header_lt (input : ByteArray) (offset : Nat) :
    Precompile.bytesToNatPadded input offset 32 < 2 ^ 256 := by
  have h := Challenge.EvmProof.Bytes.bytesToNatPadded_lt_pow input offset 32
  simpa using h

theorem ofNat_eq_iff (target value : Nat) (hvalue : value < 2 ^ 256)
    (htarget : target < 2 ^ 256) :
    UInt256.ofNat target = UInt256.ofNat value ↔ value = target := by
  constructor
  · intro h
    have hv := congrArg UInt256.toNat h
    rw [Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hvalue,
      Nat.mod_eq_of_lt htarget] at hv
    omega
  · rintro rfl
    rfl

theorem widthGuard_eq_zero_iff (input : ByteArray) :
    widthGuard input = 0 ↔ MachineState.readWord input 68 = UInt256.ofNat tailConst := by
  simp only [widthGuard, sub_eq_zero_iff]

theorem tailGuard_eq_zero_iff (input : ByteArray) :
    tailGuard input = 0 ↔
      baseSize input = 1 ∧ exponentSize input = 2 ∧
        MachineState.readWord input 100 = 0 := by
  have hb : baseSize input < 2 ^ 256 := header_lt input 0
  have he : exponentSize input < 2 ^ 256 := header_lt input 32
  simp only [tailGuard, WindowGuardLogic.wordOr_eq_zero_iff, sub_eq_zero_iff]
  rw [ofNat_eq_iff 2 _ he (by norm_num), ofNat_eq_iff 1 _ hb (by norm_num)]
  constructor
  · rintro ⟨hw100, he', hb'⟩; exact ⟨hb', he', hw100⟩
  · rintro ⟨hb', he', hw100⟩; exact ⟨hw100, he', hb'⟩

theorem matches_iff (input : ByteArray) :
    Matches input ↔ widthGuard input = 0 ∧ tailGuard input = 0 := by
  rw [widthGuard_eq_zero_iff, tailGuard_eq_zero_iff]
  constructor
  · rintro ⟨hb, he, hw68, hw100⟩; exact ⟨hw68, hb, he, hw100⟩
  · rintro ⟨hw68, hb, he, hw100⟩; exact ⟨hb, he, hw68, hw100⟩

end Challenge.Modexp.Submission.Proofs.Bytecode.MemoLogic
