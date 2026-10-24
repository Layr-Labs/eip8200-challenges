import Challenge.Modexp.Submission.Proofs.CRT.CRTPacking
import Challenge.Modexp.Submission.Proofs.CRT.CRTWordBridge
import Challenge.Modexp.Submission.Proofs.Cycle.ControlArithmetic
set_option warningAsError true
set_option maxHeartbeats 3000000
set_option exponentiation.threshold 4096
namespace CycleSubmission.Packing
open EvmSemantics
open Challenge.EvmProof.Word
open Challenge.Modexp.Submission.Proofs
open HistoricalSearch.MixedMontgomery HistoricalSearch.CRTPacking
open CycleSubmission.ControlArithmetic (value)

theorem two_digit_window (d : Nat → Nat) (i s k w : Nat)
    (hi : i < 8) (hsk : s+k = 240) (hkw : k ≤ w) (hroom : w ≤ 240+k)
    (hd : ∀ j < 9, d j < 2^240) :
    (d i >>> s) ||| ((d (i+1) <<< k) % 2^w) =
      weighted (2^240) 9 d / 2^(240*i+s) % 2^w := by
  have ht := weighted_two (2^240) 9 i d (Nat.two_pow_pos 240) (by omega) hd
  have hp := repackOr (2^240) s k w (d i) (d (i+1))
    (weighted (2^240) (9-i-2) (fun j => d (i+2+j)))
    (by rw [← Nat.pow_add, hsk])
    (by rw [← Nat.pow_add]; exact Nat.pow_dvd_pow 2 hroom)
    (hd i (by omega)) hkw
  rw [← ht] at hp
  rw [Nat.div_div_eq_div_mul, ← Nat.pow_mul, ← Nat.pow_add] at hp
  exact hp

def lowPart (a : Nat → UInt256) (j : Nat) : UInt256 :=
  if j = 0 then a 0 else UInt256.shiftRight (a j) (UInt256.ofNat (16*j))
def outputWord (a : Nat → UInt256) (j : Nat) : UInt256 :=
  UInt256.lor (UInt256.shiftLeft (a (j+1)) (UInt256.ofNat (240-16*j))) (lowPart a j)

theorem lowPart_toNat (a : Nat → UInt256) (j : Nat) (hj : j < 8) :
    (lowPart a j).toNat = (a j).toNat >>> (16*j) := by
  by_cases he : j = 0
  · subst j; simp [lowPart]
  · rw [lowPart, if_neg he, shiftRight_toNat _ (by omega : 16*j < 256)]

theorem outputWord_toNat (a : Nat → UInt256) (j : Nat) (hj : j < 8)
    (ha : ∀ i < 9, (a i).toNat < 2^240) :
    (outputWord a j).toNat = value a / 2^(256*j) % 2^256 := by
  rw [outputWord, word_toNat_lor, lowPart_toNat a j hj,
    HistoricalSearch.CRTWordBridge.shiftLeft_toNat _ _ (by omega : 240-16*j < 256), Nat.or_comm]
  have h := two_digit_window (fun i => (a i).toNat) j (16*j) (240-16*j) 256
    hj (by omega) (by omega) (by omega) ha
  rw [show 240*j+16*j = 256*j by omega] at h
  exact h

theorem output_represents (a : Nat → UInt256) (mem : ByteArray)
    (ha : ∀ i < 9, (a i).toNat < 2^240) (hv : value a < 2^2048)
    (hm : ∀ j < 8, MachineState.readWord mem (2112+32*(7-j)) = outputWord a j) :
    Fast.Model.FastRepresents mem 2112 8 (value a) := by
  apply Fast.Model.fastRepresents_of_limbs hv
  intro k hk
  rw [hm k hk, outputWord_toNat a k hk ha]
  rw [Limbs.radix, ← Nat.pow_mul]

end CycleSubmission.Packing
