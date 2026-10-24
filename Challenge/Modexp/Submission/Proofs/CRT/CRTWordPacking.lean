import Challenge.Modexp.Submission.Proofs.CRT.CRTPacking
import Challenge.Modexp.Submission.Proofs.CRT.CRTWordBridge
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 4096

namespace HistoricalSearch.CRTWordPacking
open EvmSemantics
open Challenge.EvmProof.Word
open Challenge.Modexp.Submission.Proofs
open HistoricalSearch.MixedMontgomery HistoricalSearch.CRTPacking

def value (d : Nat → UInt256) : Nat := weighted (2^244) 9 (fun i => (d i).toNat) / 2^96

def outputWord (d : Nat → UInt256) (j : Nat) : UInt256 :=
  UInt256.lor (UInt256.shiftRight (d j) (UInt256.ofNat (96+12*j)))
    (UInt256.shiftLeft (d (j+1)) (UInt256.ofNat (148-12*j)))

def retainedWord (d : Nat → UInt256) (j : Nat) : UInt256 :=
  UInt256.land
    (UInt256.lor (UInt256.shiftRight (d j) (UInt256.ofNat 96))
      (UInt256.shiftLeft (d (j+1)) (UInt256.ofNat 148)))
    (UInt256.ofNat (2^244-1))

theorem outputWord_toNat (d : Nat → UInt256) (j : Nat) (hj : j < 8)
    (hd : ∀ i < 9, (d i).toNat < 2^244) :
    (outputWord d j).toNat = value d / 2^(256*j) % 2^256 := by
  unfold outputWord value
  rw [word_toNat_lor, shiftRight_toNat _ (by omega : 96+12*j < 256),
    HistoricalSearch.CRTWordBridge.shiftLeft_toNat _ _ (by omega : 148-12*j < 256)]
  exact output_word (fun i => (d i).toNat) j hj hd

theorem retainedWord_toNat (d : Nat → UInt256) (j : Nat) (hj : j < 8)
    (hd : ∀ i < 9, (d i).toNat < 2^244) :
    (retainedWord d j).toNat = value d / 2^(244*j) % 2^244 := by
  have hlo : (d j).toNat >>> 96 < 2^244 := by
    rw [Nat.shiftRight_eq_div_pow]
    exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (hd j (by omega))
  unfold retainedWord value
  rw [word_toNat_land, word_toNat_ofNat,
    Nat.mod_eq_of_lt (by norm_num : (2:Nat)^244-1 < 2^256),
    Nat.and_two_pow_sub_one_eq_mod, word_toNat_lor,
    shiftRight_toNat _ (by decide : 96 < 256),
    HistoricalSearch.CRTWordBridge.shiftLeft_toNat _ _ (by decide : 148 < 256),
    Nat.or_mod_two_pow, Nat.mod_eq_of_lt hlo,
    Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by decide : 244 ≤ 256))]
  exact retained_digit (fun i => (d i).toNat) j hj hd

theorem retainedTop_toNat (d : Nat → UInt256)
    (hd : ∀ i < 9, (d i).toNat < 2^244) :
    (UInt256.shiftRight (d 8) (UInt256.ofNat 96)).toNat = value d / 2^1952 := by
  rw [shiftRight_toNat _ (by decide : 96 < 256), Nat.shiftRight_eq_div_pow]
  exact retained_top (fun i => (d i).toNat) hd

theorem overflow_toNat (d : Nat → UInt256)
    (hd : ∀ i < 9, (d i).toNat < 2^244) :
    (UInt256.shiftRight (d 8) (UInt256.ofNat 192)).toNat = value d / 2^2048 := by
  rw [shiftRight_toNat _ (by decide : 192 < 256), Nat.shiftRight_eq_div_pow]
  exact quotient_overflow (fun i => (d i).toNat) hd

/-- The ordinary output words establish exactly the old tail's representation
of the low2048 bits. Overflow is reported separately, as in the old interface. -/
theorem output_represents (d : Nat → UInt256) (mem : ByteArray)
    (hd : ∀ i < 9, (d i).toNat < 2^244)
    (hm : ∀ j < 8, MachineState.readWord mem (2112+32*(7-j)) = outputWord d j) :
    Fast.Model.FastRepresents mem 2112 8 (value d % 2^2048) := by
  apply Fast.Model.fastRepresents_of_limbs
  · change value d % 2^2048 < 2^2048
    exact Nat.mod_lt _ (Nat.two_pow_pos 2048)
  · intro k hk
    rw [hm k hk, outputWord_toNat d k hk hd]
    have he : Limbs.radix^k = (2:Nat)^(256*k) := by rw [Limbs.radix, ← Nat.pow_mul]
    rw [he]
    exact (mod_window (value d) 2048 (256*k) 256 (by omega)).symm

#print axioms outputWord_toNat
#print axioms retainedWord_toNat
#print axioms retainedTop_toNat
#print axioms overflow_toNat
#print axioms output_represents
end HistoricalSearch.CRTWordPacking
