import Challenge.EvmProof.Bytes
import Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputData
import Batteries.Data.Nat.Bitwise.Lemmas
import Mathlib.Data.Nat.ModEq

set_option warningAsError true
set_option maxHeartbeats 2000000

/-!
# Low-64 anchor

Universal invariant, not a new recognizer case.  If two 32-byte windows eight
bytes apart are the same word `r`, then

  `r = q8 * B^3 + b24 = b24 * B + t8`

with `B = 2^64`, `q8, t8 < B` and `b24 < B^3`.  Reducing modulo `B - 1` gives
`q8 ≡ t8`, so either `q8 = t8` or one of the two all-ones edges
(`q8 = B - 1`, `t8 = 0` or the reverse).  The on-chain screen

  `SHL 192 (0x6161616161616161 XOR r) = 0`

is exactly `r % B = 0x6161616161616161`, which is neither edge.  Therefore
`q8 = t8` and `r` is that block repeated four times, i.e. `KnownInputData.fullWord`.
Padding is part of `readWord`, so no input-length hypothesis is used.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Low64Anchor

open EvmSemantics EvmSemantics.EVM Challenge.EvmProof

abbrev low64 : Nat := 7016996765293437281

abbrev B : Nat := 2 ^ 64

theorem low64_lt : low64 < B := by decide

theorem low64_ne_zero : low64 ≠ 0 := by decide

theorem low64_ne_allOnes : low64 ≠ B - 1 := by decide

theorem fullWord_repeat :
    KnownInputData.fullWord.toNat = low64 * (1 + B + B ^ 2 + B ^ 3) := by
  decide

private theorem word_toNat_xor (a b : UInt256) :
    (UInt256.xor a b).toNat = a.toNat ^^^ b.toNat := by
  change (a.val ^^^ b.val).val = _
  rw [Fin.xor_val]
  apply Nat.mod_eq_of_lt
  exact Nat.lt_of_lt_of_le (Nat.xor_lt_two_pow a.val.isLt b.val.isLt) (by rfl)

/-- `SHL 192 (low64 XOR r) = 0` keeps only the low 64 bits, so they equal `low64`. -/
theorem low64_of_shl (r : UInt256)
    (h : UInt256.shiftLeft (UInt256.xor (UInt256.ofNat low64) r) (UInt256.ofNat 192) = 0) :
    r.toNat % B = low64 := by
  have hshiftNat : (UInt256.ofNat 192).toNat = 192 := by
    rw [Word.word_toNat_ofNat]
    exact Nat.mod_eq_of_lt (by decide)
  rw [UInt256.shiftLeft, hshiftNat, if_neg (by decide : ¬192 ≥ 256)] at h
  have hnat := congrArg UInt256.toNat h
  have hzero : (UInt256.ofNat 0).toNat = 0 := by
    rw [Word.word_toNat_ofNat]
    exact Nat.zero_mod _
  rw [show (0 : UInt256) = UInt256.ofNat 0 from rfl, hzero, Word.word_toNat_ofNat,
    UInt256.size] at hnat
  have hmod : ((UInt256.xor (UInt256.ofNat low64) r).toNat <<< 192) % 2 ^ 256 = 0 := by
    simpa [Nat.mod_mod] using hnat
  rw [Nat.shiftLeft_eq, show 2 ^ 256 = 2 ^ 64 * 2 ^ 192 by rw [← Nat.pow_add],
    Nat.mul_mod_mul_right] at hmod
  have hxor0 : (UInt256.xor (UInt256.ofNat low64) r).toNat % B = 0 := by
    rcases Nat.mul_eq_zero.mp hmod with h0 | h0
    · simpa [B] using h0
    · exact absurd h0 (by decide)
  rw [word_toNat_xor, Word.word_toNat_ofNat] at hxor0
  have hlow256 : low64 % 2 ^ 256 = low64 :=
    Nat.mod_eq_of_lt (low64_lt.trans (by decide : B < 2 ^ 256))
  rw [hlow256, Nat.xor_mod_two_pow, Nat.mod_eq_of_lt low64_lt] at hxor0
  exact (Nat.xor_eq_zero_iff.mp hxor0).symm

/-- Equal windows eight bytes apart, with a non-edge low limb, are that limb repeated. -/
theorem overlap_repeat (input : ByteArray) (off : Nat)
    (heq : MachineState.readWord input off = MachineState.readWord input (off + 8))
    (hlow : (MachineState.readWord input off).toNat % B ≠ 0)
    (hhi : (MachineState.readWord input off).toNat % B ≠ B - 1) :
    (MachineState.readWord input off).toNat =
      ((MachineState.readWord input off).toNat % B) * (1 + B + B ^ 2 + B ^ 3) := by
  let r := MachineState.readWord input off
  let q8 := Precompile.bytesToNatPadded input off 8
  let b24 := Precompile.bytesToNatPadded input (off + 8) 24
  let t8 := Precompile.bytesToNatPadded input (off + 32) 8
  have hr : r.toNat = Precompile.bytesToNatPadded input off 32 :=
    Bytes.readWord_toNat input off
  have hs : (MachineState.readWord input (off + 8)).toNat =
      Precompile.bytesToNatPadded input (off + 8) 32 :=
    Bytes.readWord_toNat input (off + 8)
  have heqNat : r.toNat = (MachineState.readWord input (off + 8)).toNat := by
    simpa [r] using congrArg UInt256.toNat heq
  have h24 : 256 ^ 24 = B ^ 3 := by decide
  have h8 : 256 ^ 8 = B := by decide
  have hsplit1 : r.toNat = q8 * B ^ 3 + b24 := by
    rw [hr, show (32 : Nat) = 8 + 24 by decide, Bytes.bytesToNatPadded_add, h24]
  have htail : off + 8 + 24 = off + 32 := by omega
  have hsplit2 : r.toNat = b24 * B + t8 := by
    rw [heqNat, hs, show (32 : Nat) = 24 + 8 by decide, Bytes.bytesToNatPadded_add, htail, h8]
  have hq8 : q8 < B := by
    simpa [q8, h8] using Bytes.bytesToNatPadded_lt_pow input off 8
  have ht8 : t8 < B := by
    simpa [t8, h8] using Bytes.bytesToNatPadded_lt_pow input (off + 32) 8
  have ht8eq : t8 = r.toNat % B := by
    rw [hsplit2, Nat.add_mod, Nat.mul_mod, Nat.mod_self, Nat.mul_zero, Nat.zero_mod,
      Nat.zero_add, Nat.mod_mod, Nat.mod_eq_of_lt ht8]
  have hBpos : 0 < B := by decide
  have hBm1 : 0 < B - 1 := by decide
  have hB1 : B % (B - 1) = 1 := by decide
  have hB3 : B ^ 3 % (B - 1) = 1 := by decide
  have hcong : q8 ≡ t8 [MOD (B - 1)] := by
    have heqLimbs : q8 * B ^ 3 + b24 = b24 * B + t8 := by rw [← hsplit1, hsplit2]
    have honeLt : 1 < B - 1 := by decide
    have hpow : B ^ 3 ≡ 1 [MOD (B - 1)] := by
      rw [Nat.ModEq, hB3, Nat.mod_eq_of_lt honeLt]
    have hone : B ≡ 1 [MOD (B - 1)] := by
      rw [Nat.ModEq, hB1, Nat.mod_eq_of_lt honeLt]
    have hL : q8 * B ^ 3 + b24 ≡ q8 + b24 [MOD (B - 1)] := by
      simpa [Nat.mul_one] using (hpow.mul_left q8).add (Nat.ModEq.refl b24)
    have hR : b24 * B + t8 ≡ b24 + t8 [MOD (B - 1)] := by
      simpa [Nat.mul_one] using (hone.mul_left b24).add (Nat.ModEq.refl t8)
    have hboth : q8 + b24 ≡ t8 + b24 [MOD (B - 1)] := by
      have hjoin : q8 * B ^ 3 + b24 ≡ b24 * B + t8 [MOD (B - 1)] := by rw [heqLimbs]
      have := hL.symm.trans (hjoin.trans hR)
      simpa [Nat.add_comm b24 t8] using this
    exact Nat.ModEq.add_right_cancel' b24 hboth
  have hq_cases : q8 = t8 ∨ (q8 = B - 1 ∧ t8 = 0) ∨ (q8 = 0 ∧ t8 = B - 1) := by
    rw [Nat.ModEq] at hcong
    have hqle : q8 ≤ B - 1 := by omega
    have htle : t8 ≤ B - 1 := by omega
    by_cases hq : q8 = B - 1 <;> by_cases ht : t8 = B - 1
    · exact Or.inl (hq.trans ht.symm)
    · have htlt : t8 < B - 1 := by omega
      rw [hq, Nat.mod_self, Nat.mod_eq_of_lt htlt] at hcong
      exact Or.inr (Or.inl ⟨hq, hcong.symm⟩)
    · have hqlt : q8 < B - 1 := by omega
      rw [ht, Nat.mod_self, Nat.mod_eq_of_lt hqlt] at hcong
      exact Or.inr (Or.inr ⟨hcong, ht⟩)
    · have hqlt : q8 < B - 1 := by omega
      have htlt : t8 < B - 1 := by omega
      rw [Nat.mod_eq_of_lt hqlt, Nat.mod_eq_of_lt htlt] at hcong
      exact Or.inl hcong
  have ht8ne0 : t8 ≠ 0 := by simpa [ht8eq, r] using hlow
  have ht8ne1 : t8 ≠ B - 1 := by simpa [ht8eq, r] using hhi
  have hqeq : q8 = t8 := by
    rcases hq_cases with h | h | h
    · exact h
    · exact absurd h.2 ht8ne0
    · exact absurd h.2 ht8ne1
  have hfactor : B ^ 3 - 1 = (B - 1) * (B ^ 2 + B + 1) := by decide
  have hlePow : 1 ≤ B ^ 3 := by decide
  have hcancel : b24 = t8 * (B ^ 2 + B + 1) := by
    have heqLimbs : t8 * B ^ 3 + b24 = b24 * B + t8 := by
      rw [hqeq] at hsplit1
      rw [← hsplit1, hsplit2]
    have hBsplit : B = (B - 1) + 1 := Nat.sub_add_cancel (Nat.le_of_lt hBpos)
    have hdistB : b24 * B = b24 * (B - 1) + b24 := by
      conv_lhs => rw [hBsplit]
      rw [Nat.mul_add, Nat.mul_one]
    have hsum : t8 * B ^ 3 = b24 * (B - 1) + t8 := by
      have h' : t8 * B ^ 3 + b24 = b24 * (B - 1) + t8 + b24 := by
        rw [heqLimbs, hdistB, Nat.add_right_comm]
      exact Nat.add_right_cancel h'
    have hle : t8 ≤ t8 * B ^ 3 := by
      simpa [Nat.mul_one] using Nat.mul_le_mul_left t8 hlePow
    have hsub : t8 * B ^ 3 - t8 = b24 * (B - 1) :=
      (Nat.sub_eq_iff_eq_add hle).2 hsum
    have hgeom : t8 * (B ^ 3 - 1) = t8 * B ^ 3 - t8 := by
      have hsucc : (B ^ 3 - 1) + 1 = B ^ 3 := Nat.sub_add_cancel hlePow
      have hgeomLe : t8 ≤ t8 * B ^ 3 := hle
      apply Eq.symm
      apply (Nat.sub_eq_iff_eq_add hgeomLe).2
      calc
        t8 * B ^ 3 = t8 * ((B ^ 3 - 1) + 1) := by rw [hsucc]
        _ = t8 * (B ^ 3 - 1) + t8 * 1 := by rw [Nat.mul_add]
        _ = t8 * (B ^ 3 - 1) + t8 := by rw [Nat.mul_one]
    have hmul : (B - 1) * b24 = (B - 1) * (t8 * (B ^ 2 + B + 1)) := by
      rw [Nat.mul_comm (B - 1) b24, ← hsub, ← hgeom, hfactor, ← Nat.mul_assoc,
        Nat.mul_comm t8 (B - 1), Nat.mul_assoc]
    exact Nat.mul_left_cancel hBm1 hmul
  have hpoly : (B ^ 2 + B + 1) * B + 1 = 1 + B + B ^ 2 + B ^ 3 := by
    calc
      (B ^ 2 + B + 1) * B + 1 = B ^ 2 * B + B * B + 1 * B + 1 := by
        rw [Nat.add_mul, Nat.add_mul, Nat.add_assoc, Nat.add_assoc, Nat.one_mul]
      _ = B ^ 3 + B ^ 2 + B + 1 := by
        rw [show B ^ 2 * B = B ^ 3 from (Nat.pow_succ B 2).symm,
          show B * B = B ^ 2 from (Nat.pow_two B).symm, Nat.one_mul]
      _ = 1 + B + B ^ 2 + B ^ 3 := by ac_rfl
  have hrform : r.toNat = t8 * (1 + B + B ^ 2 + B ^ 3) := by
    rw [hsplit2, hcancel, Nat.mul_assoc]
    conv_lhs =>
      arg 2
      rw [← Nat.mul_one t8]
    rw [← Nat.mul_add, hpoly]
  simpa [r, ht8eq] using hrform

/-- Screened 8-byte overlap at the inherited anchor forces the repeated-`a` word. -/
theorem low64_anchor (input : ByteArray)
    (h960 : MachineState.readWord input 960 = MachineState.readWord input 0)
    (h968 : MachineState.readWord input 968 = MachineState.readWord input 0)
    (hlow : UInt256.shiftLeft
        (UInt256.xor (UInt256.ofNat 7016996765293437281)
          (MachineState.readWord input 0))
        (UInt256.ofNat 192) = 0) :
    MachineState.readWord input 0 = KnownInputData.fullWord := by
  have hmod : (MachineState.readWord input 0).toNat % B = low64 :=
    low64_of_shl _ hlow
  have hover : MachineState.readWord input 960 =
      MachineState.readWord input (960 + 8) := by
    rw [h960, h968]
  have hne0 : (MachineState.readWord input 960).toNat % B ≠ 0 := by
    rw [h960, hmod]
    exact low64_ne_zero
  have hne1 : (MachineState.readWord input 960).toNat % B ≠ B - 1 := by
    rw [h960, hmod]
    exact low64_ne_allOnes
  have hrep := overlap_repeat input 960 hover hne0 hne1
  apply Word.word_ext
  rw [← h960, hrep, h960, hmod, ← fullWord_repeat]

#print axioms low64_of_shl
#print axioms overlap_repeat
#print axioms low64_anchor

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Low64Anchor
