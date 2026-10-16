import Challenge.Modexp.Submission.Proofs.Fast.Model
import Challenge.EvmProof.Bytes
set_option warningAsError true
set_option maxHeartbeats 1000000
set_option exponentiation.threshold 4096

namespace HistoricalSearch.CRTInputMemory
open EvmSemantics
open Challenge.EvmProof.Bytes
open Challenge.Modexp.Submission.Proofs
open Fast

/-- A possibly unaligned word inside a big-endian byte block is the indicated
256-bit window of the whole block. This includes zero-padded memory reads. -/
theorem readWord_window (mem : ByteArray) (ptr lead suffix : Nat) :
    (MachineState.readWord mem (ptr + lead)).toNat =
      EVM.Precompile.bytesToNatPadded mem ptr (lead + 32 + suffix) /
        256^suffix % 2^256 := by
  have ht := bytesToNatPadded_lt_pow mem (ptr + lead + 32) suffix
  have hm := bytesToNatPadded_lt_pow mem (ptr + lead) 32
  rw [show lead + 32 + suffix = lead + (32 + suffix) by omega,
    bytesToNatPadded_add, bytesToNatPadded_add, Nat.pow_add]
  have he (a b c p q : Nat) : a*(p*q)+(b*q+c) = c+q*(a*p+b) := by ring
  rw [he, Nat.add_mul_div_left _ _ (Nat.pow_pos (by decide)),
    Nat.div_eq_of_lt (by simpa [Nat.add_assoc] using ht), Nat.zero_add]
  rw [show (256:Nat)^32 = 2^256 by norm_num,
    Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt (by simpa using hm)]
  exact readWord_toNat mem (ptr + lead)

/-- The existing aligned-word representation also specifies the entire byte
block, allowing new internal limb widths without strengthening the caller. -/
theorem fullBytes_of_fastRepresents {mem : ByteArray} {ptr count A : Nat}
    (hrep : Model.FastRepresents mem ptr count A) :
    EVM.Precompile.bytesToNatPadded mem ptr (32*count) = A := by
  let X := EVM.Precompile.bytesToNatPadded mem ptr (32*count)
  have hp (k : Nat) : (256:Nat)^(32*k) = Limbs.radix^k := by
    rw [Nat.pow_mul]
    rfl
  have hX : X < Limbs.radix^count := by
    have h := bytesToNatPadded_lt_pow mem ptr (32*count)
    rwa [hp] at h
  have hr : Model.FastRepresents mem ptr count X := by
    apply Model.fastRepresents_of_limbs hX
    intro k hk
    have h := readWord_window mem ptr (32*(count-1-k)) (32*k)
    have hs : 32*(count-1-k)+32+32*k = 32*count := by omega
    rw [hs, hp] at h
    exact h
  exact Model.fastRepresents_value_unique hr hrep

/-- Masking a smaller digit after an EVM-word window does not discard any bit
used by that digit. The width/shift bound rules out crossing-window bugs. -/
theorem window_digit (X shift width : Nat) (h : shift+width ≤ 256) :
    (X % 2^256 / 2^shift) % 2^width = X/2^shift % 2^width := by
  have hs : shift ≤ 256 := by omega
  rw [show (2:Nat)^256 = 2^shift * 2^(256-shift) by
    rw [← Nat.pow_add, Nat.add_sub_of_le hs], Nat.mod_mul_right_div_self]
  apply Nat.mod_mod_of_dvd
  exact Nat.pow_dvd_pow 2 (by omega)

theorem unaligned_digit {mem : ByteArray} {ptr count A lead suffix shift width : Nat}
    (hrep : Model.FastRepresents mem ptr count A)
    (hbytes : lead+32+suffix = 32*count)
    (hbits : shift+width ≤ 256) :
    ((MachineState.readWord mem (ptr+lead)).toNat / 2^shift) % 2^width =
      A / 2^(8*suffix+shift) % 2^width := by
  rw [readWord_window, hbytes, fullBytes_of_fastRepresents hrep, window_digit _ _ _ hbits]
  rw [Nat.div_div_eq_div_mul]
  congr 2
  rw [show (256:Nat) = 2^8 by norm_num, ← Nat.pow_mul, ← Nat.pow_add]

def loadOffset (i : Nat) : Nat := 224 - (244*i)/8
def loadShift (i : Nat) : Nat := (244*i)%8

/-- All eight low mixed-radix digits loaded by the frozen244-bit adapter. -/
theorem input244 {mem : ByteArray} {ptr A : Nat}
    (hrep : Model.FastRepresents mem ptr 8 A) (i : Nat) (hi : i < 8) :
    ((MachineState.readWord mem (ptr + loadOffset i)).toNat / 2^(loadShift i)) % 2^244 =
      A / 2^(244*i) % 2^244 := by
  have hbytes : loadOffset i + 32 + (224-loadOffset i) = 32*8 := by
    unfold loadOffset
    omega
  have hbits : loadShift i + 244 ≤ 256 := by
    unfold loadShift
    omega
  have hindex : 8*(224-loadOffset i)+loadShift i = 244*i := by
    unfold loadOffset loadShift
    omega
  simpa only [hindex] using
    (unaligned_digit (lead := loadOffset i) (suffix := 224-loadOffset i)
      (shift := loadShift i) (width := 244) hrep hbytes hbits)

/-- The ninth digit contains the remaining96 high bits; it needs no mask. -/
theorem inputTop {mem : ByteArray} {ptr A : Nat}
    (hrep : Model.FastRepresents mem ptr 8 A) :
    (MachineState.readWord mem ptr).toNat / 2^160 = A/2^1952 := by
  have hw := Model.readWord_of_fastRepresents hrep (j := 0) (by decide)
  have hA : A < (2:Nat)^2048 := by simpa [Limbs.radix, ← Nat.pow_mul] using hrep.1
  have hdiv : A/2^1792 < (2:Nat)^256 := by
    apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos 1792)).2
    simpa [← Nat.pow_add] using hA
  have hw' : (MachineState.readWord mem ptr).toNat = A/2^1792 := by
    change (MachineState.readWord mem ptr).toNat = A/2^1792%2^256 at hw
    rwa [Nat.mod_eq_of_lt hdiv] at hw
  rw [hw', Nat.div_div_eq_div_mul, ← Nat.pow_add]

def inputDigitWord (mem : ByteArray) (ptr i : Nat) : UInt256 :=
  UInt256.land
    (UInt256.shiftRight (MachineState.readWord mem (ptr+loadOffset i))
      (UInt256.ofNat (loadShift i)))
    (UInt256.ofNat (2^244-1))

/-- Meaning of the adapter's actual SHR/AND expression, with EVM word
truncation and the potentially unaligned MLOAD included. -/
theorem inputDigitWord_toNat {mem : ByteArray} {ptr A : Nat}
    (hrep : Model.FastRepresents mem ptr 8 A) (i : Nat) (hi : i < 8) :
    (inputDigitWord mem ptr i).toNat = A/2^(244*i)%2^244 := by
  have hs : loadShift i < 256 := by unfold loadShift; omega
  unfold inputDigitWord
  rw [Challenge.EvmProof.Word.word_toNat_land,
    Challenge.EvmProof.Word.shiftRight_toNat _ hs,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt (by norm_num : (2:Nat)^244-1 < 2^256),
    Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]
  exact input244 hrep i hi

theorem inputTopWord_toNat {mem : ByteArray} {ptr A : Nat}
    (hrep : Model.FastRepresents mem ptr 8 A) :
    (UInt256.shiftRight (MachineState.readWord mem ptr) (UInt256.ofNat 160)).toNat =
      A/2^1952 := by
  rw [Challenge.EvmProof.Word.shiftRight_toNat _ (by decide : 160 < 256),
    Nat.shiftRight_eq_div_pow]
  exact inputTop hrep

#print axioms readWord_window
#print axioms fullBytes_of_fastRepresents
#print axioms window_digit
#print axioms unaligned_digit
#print axioms input244
#print axioms inputTop
#print axioms inputDigitWord_toNat
#print axioms inputTopWord_toNat
end HistoricalSearch.CRTInputMemory
