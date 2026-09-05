import Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundState
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RotationFold
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackCompression
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DenseScheduleWord
import Mathlib.Tactic.Ring

set_option warningAsError true

/-!
# Q4M semantic bridge: machine-shaped rounds equal `ScratchLow.rawRound`

`qRound` mirrors the stepper output of the quad templates.  With the wrapper
multiplier `rotM r = (2^32 + 1) <<< r` it equals the pinned raw round model
for every round group `j < 5` and rotation `r ≤ 32`, on arbitrary 256-bit
working and message words.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundModel

open EvmSemantics
open Challenge.EvmProof.Word
open Challenge.Ripemd160.Submission.Proofs.Bytecode.Compression
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTemplate
open Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundState
open Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundTemplate

/-- The rotation multiplier pushed by the wrappers. -/
def rotM (r : Nat) : UInt256 := UInt256.ofNat ((2 ^ 32 + 1) <<< r)

private theorem mul_toNat (a b : UInt256) :
    (a * b).toNat = (a.toNat * b.toNat) % 2 ^ 256 := by
  change (a.val * b.val).val = _
  rw [Fin.val_mul]
  rfl

private theorem shiftLeft_toNat (v : UInt256) (n : Nat) (hn : n < 256) :
    (UInt256.shiftLeft v (UInt256.ofNat n)).toNat =
      (v.toNat <<< n) % 2 ^ 256 := by
  unfold UInt256.shiftLeft
  have hshift : (UInt256.ofNat n).toNat = n := by
    rw [word_toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  rw [if_neg (by omega), hshift, word_toNat_ofNat]
  rw [show UInt256.size = 2 ^ 256 by rfl, Nat.mod_mod]

private theorem pow_le_pow32 (r : Nat) (hr : r ≤ 32) : 2 ^ r ≤ 2 ^ 32 :=
  Nat.pow_le_pow_right (by norm_num) hr

theorem rotM_toNat (r : Nat) (hr : r ≤ 32) :
    (rotM r).toNat = (2 ^ 32 + 1) * 2 ^ r := by
  unfold rotM
  rw [word_toNat_ofNat, Nat.shiftLeft_eq]
  apply Nat.mod_eq_of_lt
  have h := pow_le_pow32 r hr
  calc
    (2 ^ 32 + 1) * 2 ^ r ≤ (2 ^ 32 + 1) * 2 ^ 32 := Nat.mul_le_mul_left _ h
    _ < 2 ^ 256 := by norm_num

/-- `q ||| q <<< 32` as a natural number, for a 32-bit `q`. -/
private theorem or_shift_toNat (q : UInt256) (hq : q.toNat < 2 ^ 32) :
    (q ||| UInt256.shiftLeft q (UInt256.ofNat 32)).toNat = q.toNat * (2 ^ 32 + 1) := by
  show (UInt256.lor q (UInt256.shiftLeft q (UInt256.ofNat 32))).toNat = q.toNat * (2 ^ 32 + 1)
  rw [word_toNat_lor, shiftLeft_toNat q 32 (by norm_num)]
  have hl : q.toNat <<< 32 < 2 ^ 256 := by
    rw [Nat.shiftLeft_eq]
    calc
      q.toNat * 2 ^ 32 < 2 ^ 32 * 2 ^ 32 := Nat.mul_lt_mul_of_pos_right hq (by norm_num)
      _ < 2 ^ 256 := by norm_num
  rw [Nat.mod_eq_of_lt hl, Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt hq, Nat.shiftLeft_eq]
  ring

/-- Multiplying a 32-bit `q` by `rotM r` is the shifted OR fold. -/
private theorem mul_rotM_eq (q : UInt256) (r : Nat) (hq : q.toNat < 2 ^ 32) (hr : r ≤ 32) :
    q * rotM r =
      UInt256.shiftLeft (q ||| UInt256.shiftLeft q (UInt256.ofNat 32)) (UInt256.ofNat r) := by
  apply word_ext
  have hpow := pow_le_pow32 r hr
  have hprod : q.toNat * ((2 ^ 32 + 1) * 2 ^ r) < 2 ^ 256 := by
    calc
      q.toNat * ((2 ^ 32 + 1) * 2 ^ r) ≤ 2 ^ 32 * ((2 ^ 32 + 1) * 2 ^ 32) :=
        Nat.mul_le_mul (Nat.le_of_lt hq) (Nat.mul_le_mul_left _ hpow)
      _ < 2 ^ 256 := by norm_num
  rw [mul_toNat, rotM_toNat r hr, shiftLeft_toNat _ r (by omega), or_shift_toNat q hq,
    Nat.shiftLeft_eq, Nat.mod_eq_of_lt hprod]
  have h2 : q.toNat * (2 ^ 32 + 1) * 2 ^ r < 2 ^ 256 := by
    rw [Nat.mul_assoc]
    exact hprod
  rw [Nat.mod_eq_of_lt h2]
  ring

/-- `(v <<< r) >>> 32 = v >>> (32 - r)` for `v < 2^65`, `r ≤ 32`. -/
private theorem shiftLeft_shiftRight_eq (v : UInt256) (r : Nat)
    (hv : v.toNat < 2 ^ 65) (hr : r ≤ 32) :
    UInt256.shiftRight (UInt256.shiftLeft v (UInt256.ofNat r)) (UInt256.ofNat 32) =
      UInt256.shiftRight v (UInt256.ofNat (32 - r)) := by
  apply word_ext
  have hpow := pow_le_pow32 r hr
  rw [shiftRight_toNat (UInt256.shiftLeft v (UInt256.ofNat r)) (shift := 32) (by norm_num),
    shiftRight_toNat v (shift := 32 - r) (by omega),
    shiftLeft_toNat v r (by omega), Nat.shiftLeft_eq]
  have hlt : v.toNat * 2 ^ r < 2 ^ 256 := by
    calc
      v.toNat * 2 ^ r ≤ 2 ^ 65 * 2 ^ 32 := Nat.mul_le_mul (Nat.le_of_lt hv) hpow
      _ < 2 ^ 256 := by norm_num
  rw [Nat.mod_eq_of_lt hlt, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
  have h32 : (2 : Nat) ^ 32 = 2 ^ (32 - r) * 2 ^ r := by
    rw [← Nat.pow_add]
    congr 1
    omega
  rw [h32, Nat.mul_div_mul_right _ _ (Nat.two_pow_pos r)]

/-- The multiplier rotation of a 32-bit word is the raw inline rotate. -/
theorem rawRot_mulShift (q : UInt256) (r : Nat) (hq : q.toNat < 2 ^ 32) (hr : r ≤ 32) :
    UInt256.shiftRight (q * rotM r) (UInt256.ofNat 32) = StackRound.stackRawRot q r := by
  have hv : (q ||| UInt256.shiftLeft q (UInt256.ofNat 32)).toNat < 2 ^ 65 := by
    rw [or_shift_toNat q hq]
    calc
      q.toNat * (2 ^ 32 + 1) < 2 ^ 32 * (2 ^ 32 + 1) :=
        Nat.mul_lt_mul_of_pos_right hq (by norm_num)
      _ ≤ 2 ^ 65 := by norm_num
  rw [mul_rotM_eq q r hq hr, shiftLeft_shiftRight_eq _ r hv hr]
  exact RotationFold.rawRot_or_fold q r hq hr

theorem land_mask_eq_mask32 (z : UInt256) : UInt256.land mask z = mask32 z := by
  unfold mask32
  exact Challenge.Ripemd160.Submission.Proofs.Bytecode.Word.land_comm _ _

private theorem mask32_toNat_lt (z : UInt256) : (mask32 z).toNat < 2 ^ 32 := by
  rw [mask32_toNat, show (4294967295 : Nat) = 2 ^ 32 - 1 by norm_num,
    Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_lt _ (by norm_num)

/-- Reordered masked sum with a constant. -/
private theorem mask_sum_reorder (k a f w : UInt256) :
    mask32 (k + (a + (f + w))) = mask32 (((f + a) + w) + k) := by
  apply word_ext
  simp only [mask32_toNat, word_toNat_add]
  rw [show (4294967295 : Nat) = 2 ^ 32 - 1 by norm_num]
  simp only [Nat.and_two_pow_sub_one_eq_mod]
  omega

/-- Reordered masked sum without a constant (`K = 0`). -/
private theorem mask_sum_reorder0 (a f w : UInt256) :
    mask32 (a + (f + w)) = mask32 (((f + a) + w) + 0) := by
  apply word_ext
  simp only [mask32_toNat, word_toNat_add]
  rw [show (4294967295 : Nat) = 2 ^ 32 - 1 by norm_num]
  simp only [Nat.and_two_pow_sub_one_eq_mod]
  have h0 : (0 : UInt256).toNat = 0 := rfl
  rw [h0]
  omega

/-- Reordered masked sum absorbing an inner mask on the Boolean term. -/
private theorem mask_sum_absorb (k a f w : UInt256) :
    mask32 (k + (a + (f + w))) = mask32 (((mask32 f + a) + w) + k) := by
  apply word_ext
  simp only [mask32_toNat, word_toNat_add]
  rw [show (4294967295 : Nat) = 2 ^ 32 - 1 by norm_num]
  simp only [Nat.and_two_pow_sub_one_eq_mod]
  omega

/-- The masked machine sum equals the pinned `stackSum` for each group. -/
theorem qSum_eq_stackSum (j : Nat) (hj : j < 5) (b c d a word constant : UInt256)
    (hzero : j = 0 → constant = 0) :
    UInt256.land mask (qSum j (qf j b c d) a word constant) =
      StackRound.stackSum (StackRound.stackF j b c d) a word constant := by
  rw [land_mask_eq_mask32]
  unfold StackRound.stackSum
  interval_cases j
  · have hc := hzero rfl
    subst hc
    exact mask_sum_reorder0 a (StackRound.stackF 0 b c d) word
  · exact mask_sum_reorder constant a (StackRound.stackF 1 b c d) word
  · change mask32 (constant + (a + (qf 2 b c d + word))) =
      mask32 (((mask32 (qf 2 b c d) + a) + word) + constant)
    exact mask_sum_absorb constant a (qf 2 b c d) word
  · exact mask_sum_reorder constant a (StackRound.stackF 3 b c d) word
  · change mask32 (constant + (a + (qf 4 b c d + word))) =
      mask32 (((mask32 (qf 4 b c d) + a) + word) + constant)
    exact mask_sum_absorb constant a (qf 4 b c d) word

/-- One machine-shaped round equals one raw round. -/
theorem qRound_eq_rawRound (x : EvmWorking) (j : Nat) (word : UInt256) (r : Nat)
    (constant : UInt256) (hj : j < 5) (hr : r ≤ 32) (hzero : j = 0 → constant = 0) :
    qRound x j word (rotM r) constant = ScratchLow.rawRound x j word r constant := by
  have hsum := qSum_eq_stackSum j hj x.b x.c x.d x.a word constant hzero
  have hq : (StackRound.stackSum (StackRound.stackF j x.b x.c x.d) x.a word constant).toNat
      < 2 ^ 32 := by
    unfold StackRound.stackSum
    exact mask32_toNat_lt _
  have hrot := rawRot_mulShift
    (StackRound.stackSum (StackRound.stackF j x.b x.c x.d) x.a word constant) r hq hr
  simp only [qRound, ScratchLow.rawRound, EvmWorking.mk.injEq, true_and, and_true]
  rw [hsum, hrot, land_mask_eq_mask32, word_add_comm]
  exact ⟨rfl, rfl⟩

/-- Four machine rounds equal four raw rounds. -/
theorem quadWorking_eq_rawRounds (s : EvmSemantics.EVM.State) (x : EvmWorking) (j : Nat)
    (p0 p1 p2 p3 : UInt256) (r0 r1 r2 r3 : Nat) (constant : UInt256)
    (hj : j < 5) (hr0 : r0 ≤ 32) (hr1 : r1 ≤ 32) (hr2 : r2 ≤ 32) (hr3 : r3 ≤ 32)
    (hzero : j = 0 → constant = 0) :
    quadWorking s x j p0 p1 p2 p3 (rotM r0) (rotM r1) (rotM r2) (rotM r3) constant =
      ScratchLow.rawRound
        (ScratchLow.rawRound
          (ScratchLow.rawRound
            (ScratchLow.rawRound x j (MachineState.readWord s.memory p0.toNat) r0 constant)
            j (MachineState.readWord s.memory p1.toNat) r1 constant)
          j (MachineState.readWord s.memory p2.toNat) r2 constant)
        j (MachineState.readWord s.memory p3.toNat) r3 constant := by
  unfold quadWorking
  rw [qRound_eq_rawRound x j _ r0 constant hj hr0 hzero,
    qRound_eq_rawRound _ j _ r1 constant hj hr1 hzero,
    qRound_eq_rawRound _ j _ r2 constant hj hr2 hzero,
    qRound_eq_rawRound _ j _ r3 constant hj hr3 hzero]

/-- Replacing message words by low-32-equal words leaves four raw rounds unchanged. -/
theorem fourRawRound_eq_of_toUInt32_eq (x : EvmWorking) (j : Nat)
    (w0 w0' w1 w1' w2 w2' w3 w3' : UInt256) (r0 r1 r2 r3 : Nat) (constant : UInt256)
    (h0 : toUInt32 w0 = toUInt32 w0') (h1 : toUInt32 w1 = toUInt32 w1')
    (h2 : toUInt32 w2 = toUInt32 w2') (h3 : toUInt32 w3 = toUInt32 w3') :
    ScratchLow.rawRound (ScratchLow.rawRound (ScratchLow.rawRound
      (ScratchLow.rawRound x j w0 r0 constant) j w1 r1 constant) j w2 r2 constant)
      j w3 r3 constant =
    ScratchLow.rawRound (ScratchLow.rawRound (ScratchLow.rawRound
      (ScratchLow.rawRound x j w0' r0 constant) j w1' r1 constant) j w2' r2 constant)
      j w3' r3 constant := by
  rw [DenseScheduleWord.rawRound_eq_of_toUInt32_eq x j w0 w0' r0 constant h0,
    DenseScheduleWord.rawRound_eq_of_toUInt32_eq _ j w1 w1' r1 constant h1,
    DenseScheduleWord.rawRound_eq_of_toUInt32_eq _ j w2 w2' r2 constant h2,
    DenseScheduleWord.rawRound_eq_of_toUInt32_eq _ j w3 w3' r3 constant h3]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundModel
