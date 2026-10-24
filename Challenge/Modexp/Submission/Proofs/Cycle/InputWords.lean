import Challenge.Modexp.Submission.Proofs.CRT.CRTInputMemory
import Challenge.Modexp.Submission.Proofs.Cycle.WordArithmetic
import Challenge.Modexp.Submission.Proofs.CRT.CRTWordBridge
set_option warningAsError true
set_option maxHeartbeats 3000000
set_option exponentiation.threshold 4096
namespace CycleSubmission.InputWords
open EvmSemantics
open Challenge.EvmProof.Word
open HistoricalSearch.CRTInputMemory HistoricalSearch.WordCancellation
open HistoricalSearch.MixedMontgomery
open Challenge.Modexp.Submission.Proofs

def low (mem : ByteArray) (ptr i : Nat) : UInt256 :=
  UInt256.land (UInt256.ofNat (2^240-1))
    (MachineState.readWord mem (ptr+(224-30*i)))
def top (mem : ByteArray) (ptr : Nat) : UInt256 :=
  UInt256.shiftRight (MachineState.readWord mem ptr) (UInt256.ofNat 128)

theorem low_value {mem : ByteArray} {ptr A : Nat}
    (h : Fast.Model.FastRepresents mem ptr 8 A) (i : Nat) (hi : i < 8) :
    (low mem ptr i).toNat = A/2^(240*i)%2^240 := by
  unfold low
  rw [land_comm]
  change ((MachineState.readWord mem (ptr+(224-30*i))) &&& UInt256.ofNat (2^240-1)).toNat = _
  rw [mask_toNat _ 240 (by decide)]
  have hu := unaligned_digit (lead := 224-30*i) (suffix := 30*i)
    (shift := 0) (width := 240) h (by omega) (by decide)
  simpa only [Nat.pow_zero, Nat.div_one, Nat.add_zero,
    show 8*(30*i)=240*i by omega] using hu

theorem top_value {mem : ByteArray} {ptr A : Nat}
    (h : Fast.Model.FastRepresents mem ptr 8 A) :
    (top mem ptr).toNat = A/2^1920 := by
  have hw := Fast.Model.readWord_of_fastRepresents h (j := 0) (by decide)
  have hA : A < 2^2048 := h.1
  have hd : A/2^1792 < 2^256 := by
    apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).mpr
    simpa only [← Nat.pow_add] using hA
  change (MachineState.readWord mem ptr).toNat = A/2^1792%2^256 at hw
  rw [Nat.mod_eq_of_lt hd] at hw
  rw [top, shiftRight_toNat _ (by decide : 128 < 256), Nat.shiftRight_eq_div_pow,
    hw, Nat.div_div_eq_div_mul, ← Nat.pow_add]

theorem digit_decomposition (B X count : Nat) (_hB : 0 < B) :
    weighted B count (fun i => X/B^i%B) + B^count*(X/B^count) = X := by
  induction count with
  | zero => simp [weighted]
  | succ count ih =>
    have h := congrArg (fun z => B^count*z) (Nat.mod_add_div (X/B^count) B)
    rw [Nat.div_div_eq_div_mul, ← Nat.pow_succ] at h
    simp only [weighted, Finset.sum_range_succ, Nat.pow_succ] at ih h ⊢
    nlinarith

theorem reconstruct (B X count : Nat) (hB : 0 < B) (hX : X < B^count) :
    weighted B count (fun i => X/B^i%B) = X := by
  have h := digit_decomposition B X count hB
  simpa only [Nat.div_eq_of_lt hX, Nat.mul_zero, Nat.add_zero] using h

def scaledLow (mem : ByteArray) (ptr i : Nat) : UInt256 :=
  UInt256.land (UInt256.ofNat (2^240-1))
    (if i = 0 then UInt256.shiftLeft (MachineState.readWord mem (ptr+224)) (UInt256.ofNat 112)
     else MachineState.readWord mem (ptr+(238-30*i)))

def scaledTop (mem : ByteArray) (ptr : Nat) : UInt256 :=
  UInt256.shiftRight (MachineState.readWord mem ptr) (UInt256.ofNat 16)

theorem scaled_div (A k : Nat) (hk : 112 ≤ k) :
    A*2^112/2^k = A/2^(k-112) := by
  rw [show (2:Nat)^k = 2^112*2^(k-112) by
    rw [← Nat.pow_add, Nat.add_sub_of_le hk]]
  rw [← Nat.div_div_eq_div_mul, Nat.mul_div_cancel _ (Nat.two_pow_pos _)]

theorem scaled_low_value {mem : ByteArray} {ptr A : Nat}
    (h : Fast.Model.FastRepresents mem ptr 8 A) (i : Nat) (hi : i < 8) :
    (scaledLow mem ptr i).toNat = (A*2^112)/2^(240*i)%2^240 := by
  unfold scaledLow
  rw [land_comm]
  by_cases hz : i = 0
  · subst i
    simp only [Nat.mul_zero, Nat.pow_zero, Nat.div_one]
    change ((UInt256.shiftLeft (MachineState.readWord mem (ptr+224)) (UInt256.ofNat 112))
      &&& UInt256.ofNat (2^240-1)).toNat = _
    rw [mask_toNat _ 240 (by decide), HistoricalSearch.CRTWordBridge.shiftLeft_toNat _ 112 (by decide),
      Nat.shiftLeft_eq, Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by decide : 240 ≤ 256))]
    have hw := Fast.Model.readWord_of_fastRepresents h (j := 7) (by decide)
    norm_num only [Nat.reduceSub, Nat.reduceMul, Nat.pow_zero, Nat.div_one] at hw
    change (MachineState.readWord mem (ptr+224)).toNat = A%2^256 at hw
    rw [hw, Nat.mul_mod, Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by decide : 240 ≤ 256)),
      ← Nat.mul_mod]
  · rw [if_neg hz]
    change ((MachineState.readWord mem (ptr+(238-30*i))) &&& UInt256.ofNat (2^240-1)).toNat = _
    rw [mask_toNat _ 240 (by decide), scaled_div A (240*i) (by omega)]
    have hu := unaligned_digit (lead := 238-30*i) (suffix := 30*i-14)
      (shift := 0) (width := 240) h (by omega) (by decide)
    simpa only [Nat.pow_zero, Nat.div_one, Nat.add_zero,
      show 8*(30*i-14)=240*i-112 by omega] using hu

theorem scaled_top_value {mem : ByteArray} {ptr A : Nat}
    (h : Fast.Model.FastRepresents mem ptr 8 A) :
    (scaledTop mem ptr).toNat = (A*2^112)/2^1920 := by
  have hw := Fast.Model.readWord_of_fastRepresents h (j := 0) (by decide)
  have hA : A < 2^2048 := h.1
  have hd : A/2^1792 < 2^256 := by
    apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).mpr
    simpa only [← Nat.pow_add] using hA
  change (MachineState.readWord mem ptr).toNat = A/2^1792%2^256 at hw
  rw [Nat.mod_eq_of_lt hd] at hw
  rw [scaledTop, shiftRight_toNat _ (by decide : 16 < 256), Nat.shiftRight_eq_div_pow,
    hw, Nat.div_div_eq_div_mul, ← Nat.pow_add, scaled_div A 1920 (by decide)]

def ordinary (mem : ByteArray) (ptr i : Nat) : UInt256 :=
  if i < 8 then low mem ptr i else top mem ptr
def scaled (mem : ByteArray) (ptr i : Nat) : UInt256 :=
  if i < 8 then scaledLow mem ptr i else scaledTop mem ptr

theorem top_mod (X : Nat) (hX : X < 2^2160) :
    X/2^1920 = X/2^1920%2^240 := by
  symm
  apply Nat.mod_eq_of_lt
  apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).mpr
  simpa only [← Nat.pow_add] using hX

theorem represented (words : Nat → UInt256) (X : Nat) (hX : X < 2^2160)
    (hwords : ∀ i < 9, (words i).toNat = X/2^(240*i)%2^240) :
    (∀ i < 9, (words i).toNat < 2^240) ∧
    weighted (2^240) 9 (fun i => (words i).toNat) = X := by
  refine ⟨?_, ?_⟩
  · intro i hi
    rw [hwords i hi]
    exact Nat.mod_lt _ (Nat.two_pow_pos _)
  · have he : weighted (2^240) 9 (fun i => (words i).toNat) =
        weighted (2^240) 9 (fun i => X/(2^240)^i%2^240) := by
      apply Finset.sum_congr rfl
      intro i hi
      dsimp only
      rw [hwords i (Finset.mem_range.mp hi), ← Nat.pow_mul]
    rw [he]
    apply reconstruct _ _ _ (Nat.two_pow_pos _)
    simpa only [← Nat.pow_mul] using hX

theorem ordinary_represents {mem : ByteArray} {ptr A : Nat}
    (h : Fast.Model.FastRepresents mem ptr 8 A) :
    (∀ i < 9, (ordinary mem ptr i).toNat < 2^240) ∧
    weighted (2^240) 9 (fun i => (ordinary mem ptr i).toNat) = A := by
  have hA : A < 2^2048 := h.1
  have hR : A < 2^2160 := hA.trans_le (Nat.pow_le_pow_right (by decide) (by decide))
  apply represented _ _ hR
  intro i hi
  by_cases hlo : i < 8
  · rw [ordinary, if_pos hlo]
    exact low_value h i hlo
  · have he : i = 8 := by omega
    subst i
    rw [ordinary, if_neg (by decide), top_value h]
    exact top_mod A hR

theorem scaled_represents {mem : ByteArray} {ptr A : Nat}
    (h : Fast.Model.FastRepresents mem ptr 8 A) :
    (∀ i < 9, (scaled mem ptr i).toNat < 2^240) ∧
    weighted (2^240) 9 (fun i => (scaled mem ptr i).toNat) = A*2^112 := by
  have hA : A < 2^2048 := h.1
  have hR : A*2^112 < 2^2160 := by
    have h := Nat.mul_lt_mul_of_pos_right hA (Nat.two_pow_pos 112)
    simpa only [← Nat.pow_add] using h
  apply represented _ _ hR
  intro i hi
  by_cases hlo : i < 8
  · rw [scaled, if_pos hlo]
    exact scaled_low_value h i hlo
  · have he : i = 8 := by omega
    subst i
    rw [scaled, if_neg (by decide), scaled_top_value h]
    exact top_mod (A*2^112) hR

end CycleSubmission.InputWords
