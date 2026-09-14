import Challenge.Modexp.Submission.Proofs.Fast.EarlyCsubModel
import Challenge.Modexp.Submission.Proofs.Fast.Exp

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000

/-!
Pure memory semantics for a caller which retains its canonical accumulator at
2112. This module contains no located instruction or artifact certificate.
The strict high-limb arm leaves memory untouched. The other arm reuses the
existing complete subtraction semantics with destination 2112.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.RetainedTNormalizer

open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs

def Skip (memory : ByteArray) : Prop :=
  (MachineState.readWord memory 2112).toNat <
    (MachineState.readWord memory 0).toNat

instance (memory : ByteArray) : Decidable (Skip memory) :=
  inferInstanceAs (Decidable (_ < _))

def resultMemory (memory : ByteArray) (n : Nat) : ByteArray :=
  if Skip memory then memory else Csub.subResultMemory memory n 2112

theorem skip_iff_early (memory : ByteArray)
    (htn : (MachineState.readWord memory 2080).toNat = 0) :
    Skip memory ↔ EarlyCsub.Skip memory := by
  rw [EarlyCsub.skip_iff]
  exact ⟨fun h => ⟨htn, h⟩, fun h => h.2⟩

theorem result_of_skip (memory : ByteArray) (n : Nat) (h : Skip memory) :
    resultMemory memory n = memory := by
  simp only [resultMemory, if_pos h]

theorem result_of_not_skip (memory : ByteArray) (n : Nat) (h : ¬ Skip memory) :
    resultMemory memory n = Csub.subResultMemory memory n 2112 := by
  simp only [resultMemory, if_neg h]

/-- The caller supplies the zero high carry; a high-limb comparison alone
does not establish this premise. -/
theorem result_correct (memory : ByteArray) (n tlow modulus : Nat)
    (hn : 2 ≤ n) (hn8 : n ≤ 8)
    (ht : Model.FastRepresents memory 2112 n tlow)
    (hm : Model.FastRepresents memory 0 n modulus)
    (htn : (MachineState.readWord memory 2080).toNat = 0)
    (hmpos : 0 < modulus) (hbound : tlow < 2 * modulus) :
    Model.FastRepresents (resultMemory memory n) 2112 n
      (tlow % modulus) := by
  unfold resultMemory
  split
  · rename_i hskip
    have hlt : tlow < modulus := EarlyCsub.high_limb_lt (by omega) ht hm hskip
    simpa only [Nat.mod_eq_of_lt hlt] using ht
  · simpa only [Nat.zero_mul, Nat.zero_add] using
      Csub.csub_sub_correct memory n tlow modulus 0 2112 hn hn8 ht hm htn
        (by decide) hmpos (by simpa only [Nat.zero_mul, Nat.zero_add] using hbound)

/-- Only the subtraction scratch and retained accumulator can change. -/
theorem preserves_region (memory : ByteArray) (n ptr count value : Nat)
    (hn : 2 ≤ n)
    (hsub : ptr + 32 * count ≤ 1792 ∨ 1792 + 32 * n ≤ ptr)
    (hdst : 2112 + 32 * n ≤ ptr ∨ ptr + 32 * count ≤ 2112)
    (hrep : Model.FastRepresents memory ptr count value) :
    Model.FastRepresents (resultMemory memory n) ptr count value := by
  unfold resultMemory
  split
  · exact hrep
  · exact Csub.csub_sub_preserves_region memory n 2112 ptr count value
      hn hsub hdst hrep

theorem readWord_outside (memory : ByteArray) (n address : Nat)
    (hn : 1 ≤ n)
    (hsub : address + 32 ≤ 1792 ∨ 1792 + 32 * n ≤ address)
    (hdst : address + 32 ≤ 2112 ∨ 2112 + 32 * n ≤ address) :
    MachineState.readWord (resultMemory memory n) address =
      MachineState.readWord memory address := by
  unfold resultMemory
  split
  · rfl
  · unfold Csub.subResultMemory
    rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint]
    · exact Csub.csStep_readWord_disjoint memory n address hn hsub n le_rfl
    · rw [Challenge.EvmProof.Memory.readPadded_size]
      exact hdst

theorem preserves_tn (memory : ByteArray) (n : Nat)
    (hn : 2 ≤ n) (hn8 : n ≤ 8) :
    MachineState.readWord (resultMemory memory n) 2080 =
      MachineState.readWord memory 2080 := by
  exact readWord_outside memory n 2080 (by omega) (Or.inr (by omega))
    (Or.inl (by omega))

theorem preserves_tn_zero (memory : ByteArray) (n : Nat)
    (hn : 2 ≤ n) (hn8 : n ≤ 8)
    (htn : (MachineState.readWord memory 2080).toNat = 0) :
    (MachineState.readWord (resultMemory memory n) 2080).toNat = 0 := by
  rw [preserves_tn memory n hn hn8]
  exact htn

theorem preserves_high (memory : ByteArray) (n address : Nat)
    (hn : 2 ≤ n) (hn8 : n ≤ 8) (haddress : 2368 ≤ address) :
    MachineState.readWord (resultMemory memory n) address =
      MachineState.readWord memory address := by
  exact readWord_outside memory n address (by omega) (Or.inr (by omega))
    (Or.inr (by omega))

theorem preserves_modulus (memory : ByteArray) (n modulus : Nat)
    (hn : 2 ≤ n) (hn8 : n ≤ 8)
    (hm : Model.FastRepresents memory 0 n modulus) :
    Model.FastRepresents (resultMemory memory n) 0 n modulus := by
  exact preserves_region memory n 0 n modulus hn (Or.inl (by omega))
    (Or.inr (by omega)) hm

theorem preserves_low_block (memory : ByteArray) (n ptr count value : Nat)
    (hn : 2 ≤ n) (hend : ptr + 32 * count ≤ 1792)
    (hrep : Model.FastRepresents memory ptr count value) :
    Model.FastRepresents (resultMemory memory n) ptr count value := by
  exact preserves_region memory n ptr count value hn (Or.inl hend)
    (Or.inr (by omega)) hrep

theorem preserves_frame (memory : ByteArray) (n bsize inverse : Nat)
    (hn : 2 ≤ n) (hn8 : n ≤ 8) (hf : Exp.Frame memory n bsize inverse) :
    Exp.Frame (resultMemory memory n) n bsize inverse := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [preserves_high memory n 2688 hn hn8 (by decide)]
    exact hf.s32
  · rw [preserves_high memory n 2720 hn hn8 (by decide)]
    exact hf.minvW
  · rw [preserves_high memory n 2752 hn hn8 (by decide)]
    exact hf.ml
  · rw [preserves_high memory n 2784 hn hn8 (by decide)]
    exact hf.tl
  · rw [preserves_high memory n 2816 hn hn8 (by decide)]
    exact hf.eoff

#print axioms result_correct
#print axioms preserves_tn_zero
#print axioms preserves_modulus
#print axioms preserves_high
#print axioms preserves_frame

end Challenge.Modexp.Submission.Proofs.Fast.RetainedTNormalizer
