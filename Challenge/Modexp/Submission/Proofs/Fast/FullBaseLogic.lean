import Challenge.Modexp.Submission.Proofs.Fast.Setup
import Challenge.Modexp.Submission.Proofs.Fast.R1
set_option warningAsError true
/-!
# Mathematical interface for the full-width-base branch

This module isolates the data-independent facts used by the appended branch.
It deliberately contains no control-flow proof: the located execution is kept
in `FullBasePaths`, while the eventual driver theorem can consume the small
memory and range lemmas below.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.FullBase

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs

/-- The exact semantic predicate tested by the branch. -/
def Matches (memory : ByteArray) (n bsize : Nat) : Prop :=
  bsize = 32 * n ∧ R1.TopBitSet memory

/-! The top-bit predicate for the copied full-width base. -/
def BaseTopBitSet (memory : ByteArray) : Prop :=
  2 ^ 255 ≤ (MachineState.readWord memory 1024).toNat


instance (memory : ByteArray) (n bsize : Nat) : Decidable (Matches memory n bsize) := by
  unfold Matches
  infer_instance

/-- Memory after copying the complete `n`-word base from calldata to `ACC`. -/
def copyBaseMem (memory input : ByteArray) (n : Nat) : ByteArray :=
  MachineState.writeBytes memory (MachineState.readPadded input 96 (32 * n)) 1024

/-- A word wholly inside a copied region is the corresponding source word.
This is the calldata-to-memory analogue of `Csub.readWord_mcopy`. -/
theorem readPadded_copyFrom (memory source : ByteArray) (src dst sz i : Nat)
    (h : 32 * i + 32 ≤ sz) :
    MachineState.readPadded (MachineState.writeBytes memory
        (MachineState.readPadded source src sz) dst) (dst + 32 * i) 32 =
      MachineState.readPadded source (src + 32 * i) 32 := by
  apply ByteArray.ext_getElem
  · simp
  · intro k hk1 hk2
    have hk : k < 32 := by simpa using hk1
    rw [← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hk1,
      ← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hk2,
      Challenge.EvmProof.Memory.readPadded_getElem?_getD,
      Challenge.EvmProof.Memory.readPadded_getElem?_getD, if_pos hk, if_pos hk,
      MachineState.writeBytes_getElem?_getD,
      Challenge.EvmProof.Memory.readPadded_size,
      if_pos (show dst ≤ dst + 32 * i + k ∧ dst + 32 * i + k < dst + sz from
        ⟨by omega, by omega⟩),
      show dst + 32 * i + k - dst = 32 * i + k from by omega,
      Challenge.EvmProof.Memory.readPadded_getElem?_getD,
      if_pos (show 32 * i + k < sz from by omega)]
    simp only [Nat.add_assoc]

theorem readWord_copyFrom (memory source : ByteArray) (src dst sz i : Nat)
    (h : 32 * i + 32 ≤ sz) :
    MachineState.readWord (MachineState.writeBytes memory
        (MachineState.readPadded source src sz) dst) (dst + 32 * i) =
      MachineState.readWord source (src + 32 * i) := by
  unfold MachineState.readWord
  rw [readPadded_copyFrom memory source src dst sz i h]

/-- The copied block represents the calldata base as an `n`-word integer. -/
theorem copyBaseMem_represents (memory input : ByteArray) (n : Nat) :
    Model.FastRepresents (copyBaseMem memory input n) 1024 n
      (Precompile.bytesToNatPadded input 96 (32 * n)) := by
  have hsource := Setup.fastRepresents_bytes input 96 n
  apply Model.fastRepresents_of_limbs hsource.1
  intro k hk
  unfold copyBaseMem
  rw [readWord_copyFrom memory input 96 1024 (32 * n) (n - 1 - k) (by omega)]
  exact Model.readLimb_of_fastRepresents hsource hk

/-- The copy leaves a represented block outside `ACC` unchanged. -/
theorem copyBaseMem_preserves (memory input : ByteArray) (n ptr count value : Nat)
    (hdisjoint : 1024 + 32 * n ≤ ptr ∨ ptr + 32 * count ≤ 1024)
    (hrep : Model.FastRepresents memory ptr count value) :
    Model.FastRepresents (copyBaseMem memory input n) ptr count value := by
  unfold copyBaseMem
  apply Model.fastRepresents_writeBytes_disjoint memory _ 1024 ptr count value
  · rw [Challenge.EvmProof.Memory.readPadded_size]
    exact hdisjoint
  · exact hrep

/-- A disjoint word is unchanged by the calldata copy. -/
theorem copyBaseMem_readWord_disjoint (memory input : ByteArray) (n addr : Nat)
    (hdisjoint : addr + 32 ≤ 1024 ∨ 1024 + 32 * n ≤ addr) :
    MachineState.readWord (copyBaseMem memory input n) addr =
      MachineState.readWord memory addr := by
  unfold copyBaseMem
  apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
  simpa only [Challenge.EvmProof.Memory.readPadded_size] using hdisjoint

/-- All words above the ACC block, including configuration words, survive. -/
theorem copyBaseMem_readWord_high (memory input : ByteArray) (n addr : Nat)
    (hn32 : n ≤ 32) (haddr : 2048 ≤ addr) :
    MachineState.readWord (copyBaseMem memory input n) addr =
      MachineState.readWord memory addr :=
  copyBaseMem_readWord_disjoint memory input n addr (Or.inr (by omega))

private theorem activeWordsAfter_eq_of_end_le (curr offset size : Nat)
    (hend : offset + size ≤ curr * 32) :
    MachineState.activeWordsAfter curr offset size = curr := by
  unfold MachineState.activeWordsAfter
  split
  · rfl
  · dsimp only
    apply Nat.max_eq_left
    have hq : (offset + size - 1) / 32 < curr :=
      (Nat.div_lt_iff_lt_mul (by omega)).2 (by omega)
    omega

/-- The ACC copy stays inside the already allocated fast-path memory. -/
theorem copyBase_activeWords (s : State) (n : Nat)
    (hn32 : n ≤ 32) (hactive : 298 ≤ s.activeWords.toNat) :
    s.activeWordsAfterUInt256 1024 (32 * n) = s.activeWords := by
  unfold State.activeWordsAfterUInt256
  rw [activeWordsAfter_eq_of_end_le]
  · exact (Challenge.EvmProof.Word.word_eq_ofNat_toNat _).symm
  · omega

/-- In particular, the modulus block survives the calldata copy. -/
theorem copyBaseMem_modulus {memory input : ByteArray} {n mm : Nat}
    (hn32 : n ≤ 32) (hmod : Model.FastRepresents memory 0 n mm) :
    Model.FastRepresents (copyBaseMem memory input n) 0 n mm :=
  copyBaseMem_preserves memory input n 0 n mm (Or.inr (by omega)) hmod

/-- A full-width calldata value fits below the Montgomery radix. -/
theorem baseValue_lt_radix (input : ByteArray) (n : Nat) :
    Precompile.bytesToNatPadded input 96 (32 * n) < Limbs.radix ^ n := by
  have h := Limbs.byteValue_fits_limbs input 96 (32 * n)
  have hcount : Limbs.limbCount (32 * n) = n := by
    unfold Limbs.limbCount
    omega
  rwa [hcount] at h

/-- Under the top-bit guard, the copied value meets `ADDMOD`/`CSUB`'s
single-subtraction bound. -/
theorem baseValue_lt_two_mul {memory input : ByteArray} {n mm : Nat}
    (hn : 1 ≤ n) (hodd : mm % 2 = 1)
    (hmod : Model.FastRepresents memory 0 n mm) (htop : R1.TopBitSet memory) :
    Precompile.bytesToNatPadded input 96 (32 * n) < 2 * mm :=
  (baseValue_lt_radix input n).trans
    (R1.radix_pow_lt_two_mul hn hodd hmod htop)

/-! A clear top bit makes the copied base strictly smaller than the guarded
modulus, so the modular reduction is an identity. -/
theorem baseValue_lt_modulus_of_not_top
    {memory input : ByteArray} {n mm : Nat}
    (hn : 1 ≤ n) (hmod : Model.FastRepresents memory 0 n mm)
    (hmodTop : R1.TopBitSet memory)
    (hbase : Model.FastRepresents (copyBaseMem memory input n) 1024 n
      (Precompile.bytesToNatPadded input 96 (32 * n)))
    (hbaseTop : ¬ BaseTopBitSet (copyBaseMem memory input n)) :
    Precompile.bytesToNatPadded input 96 (32 * n) < mm := by
  let base := Precompile.bytesToNatPadded input 96 (32 * n)
  have hbaseBound : base < Limbs.radix ^ n := by
    simpa [base] using baseValue_lt_radix input n
  have hpow : 0 < Limbs.radix ^ (n - 1) := pow_pos Limbs.radix_pos _
  have hquotLt : base / Limbs.radix ^ (n - 1) < Limbs.radix := by
    rw [Nat.div_lt_iff_lt_mul hpow]
    calc
      base < Limbs.radix ^ n := hbaseBound
      _ = Limbs.radix * Limbs.radix ^ (n - 1) := by
        rw [← pow_succ']
        congr 1
        omega
  have hlimb : (MachineState.readWord
      (copyBaseMem memory input n) 1024).toNat =
      base / Limbs.radix ^ (n - 1) % Limbs.radix := by
    simpa [base] using
      Model.readWord_of_fastRepresents hbase (j := 0) (by omega)
  have hwordLt : (MachineState.readWord
      (copyBaseMem memory input n) 1024).toNat < 2 ^ 255 :=
    Nat.lt_of_not_ge (by simpa [BaseTopBitSet] using hbaseTop)
  have hquot : base / Limbs.radix ^ (n - 1) < 2 ^ 255 := by
    rw [Nat.mod_eq_of_lt hquotLt] at hlimb
    exact hlimb ▸ hwordLt
  have hbaseHalf : base < 2 ^ 255 * Limbs.radix ^ (n - 1) :=
    (Nat.div_lt_iff_lt_mul hpow).mp hquot
  have hmodLimb : (MachineState.readWord memory 0).toNat =
      mm / Limbs.radix ^ (n - 1) % Limbs.radix := by
    simpa using Model.readWord_of_fastRepresents hmod (j := 0) (by omega)
  have hmodGe : 2 ^ 255 ≤ mm / Limbs.radix ^ (n - 1) :=
    le_trans (hmodLimb ▸ hmodTop) (Nat.mod_le _ _)
  have hmul : 2 ^ 255 * Limbs.radix ^ (n - 1) ≤ mm :=
    le_trans (Nat.mul_le_mul_right _ hmodGe) (Nat.div_mul_le_self _ _)
  exact hbaseHalf.trans_le hmul

end Challenge.Modexp.Submission.Proofs.Fast.FullBase

