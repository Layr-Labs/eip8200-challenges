import Challenge.Modexp.Submission.Proofs.Fast.EarlyCsubModel
import Challenge.Modexp.Submission.Proofs.Fast.RetainedTNormalizer
import Challenge.Modexp.Submission.Proofs.Fast.FullBaseLogic
import Challenge.Modexp.Submission.Proofs.Fast.Exp

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.ShiftProducerCanonical
open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Fast

/-! Memory-only semantics of the retained-accumulator producer. The raw base is
placed at 2112, the leading-limb guard reduces it in place (`RetainedTNormalizer`),
and the reduced value is copied from 2112 to ACC before scale.
These facts do not certify the artifact locations or complete input theorem. -/

/-! The phase-9 image no longer zeroes `TN` (2080) on the hit path — the first
`CSUB` entry owns that store now (instruction 3311, pc 4129) — so the hit model is
the raw copy alone, and the zero is threaded as a hypothesis where the csub's
`TN` precondition needs it. -/
def hitMemory (mem input : ByteArray) (n : Nat) : ByteArray :=
  MachineState.writeBytes mem (MachineState.readPadded input 96 (32*n)) 2112

def reducedMemory (mem input : ByteArray) (n : Nat) : ByteArray :=
  RetainedTNormalizer.resultMemory (hitMemory mem input n) n

def canonicalMemory (mem input : ByteArray) (n : Nat) : ByteArray :=
  Exp.mcopyMem (reducedMemory mem input n) 256 2112 (32*n)

theorem hit_t (mem input : ByteArray) (n : Nat) :
    Model.FastRepresents (hitMemory mem input n) 2112 n
      (Precompile.bytesToNatPadded input 96 (32*n)) := by
  unfold hitMemory
  have hsource := Setup.fastRepresents_bytes input 96 n
  apply Model.fastRepresents_of_limbs hsource.1
  intro k hk
  rw [FullBase.readWord_copyFrom _ input 96 2112 (32*n) (n-1-k) (by omega)]
  exact Model.readLimb_of_fastRepresents hsource hk

theorem hit_modulus (mem input : ByteArray) (n mm : Nat) (hn32 : n ≤ 8)
    (hmod : Model.FastRepresents mem 0 n mm) :
    Model.FastRepresents (hitMemory mem input n) 0 n mm := by
  unfold hitMemory
  apply Model.fastRepresents_writeBytes_disjoint
  · rw [Challenge.EvmProof.Memory.readPadded_size]; omega
  · exact hmod

theorem hit_high_zero_of (mem input : ByteArray) (n : Nat)
    (htn0 : MachineState.readWord mem 2080 = UInt256.ofNat 0) :
    (MachineState.readWord (hitMemory mem input n) 2080).toNat = 0 := by
  rw [show (hitMemory mem input n) = MachineState.writeBytes mem
      (MachineState.readPadded input 96 (32*n)) 2112 from rfl]
  rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint _ _ _ _
    (by rw [Challenge.EvmProof.Memory.readPadded_size]; omega)]
  rw [htn0]; decide

theorem reduced_base (mem input : ByteArray) (n mm : Nat)
    (hn : 2 ≤ n) (hn32 : n ≤ 8) (hm : 0 < mm) (hodd : mm % 2 = 1)
    (hmod : Model.FastRepresents mem 0 n mm) (htop : R1.TopBitSet mem)
    (htn0 : MachineState.readWord mem 2080 = UInt256.ofNat 0) :
    Model.FastRepresents (reducedMemory mem input n) 2112 n
      (Precompile.bytesToNatPadded input 96 (32*n) % mm) := by
  have hb : Precompile.bytesToNatPadded input 96 (32*n) < 2 * mm :=
    FullBase.baseValue_lt_two_mul (by omega) hodd hmod htop (input := input)
  exact RetainedTNormalizer.result_correct (hitMemory mem input n) n
    (Precompile.bytesToNatPadded input 96 (32*n)) mm hn hn32
    (hit_t mem input n) (hit_modulus mem input n mm hn32 hmod)
    (hit_high_zero_of mem input n htn0) hm hb

theorem canonical_acc (mem input : ByteArray) (n mm : Nat)
    (hn : 2 ≤ n) (hn32 : n ≤ 8) (hm : 0 < mm) (hodd : mm % 2 = 1)
    (hmod : Model.FastRepresents mem 0 n mm) (htop : R1.TopBitSet mem)
    (htn0 : MachineState.readWord mem 2080 = UInt256.ofNat 0) :
    Model.FastRepresents (canonicalMemory mem input n) 256 n
      (Precompile.bytesToNatPadded input 96 (32*n) % mm) :=
  Exp.fastRepresents_mcopyMem _ 256 2112 n _ (by omega)
    (reduced_base mem input n mm hn hn32 hm hodd hmod htop htn0)

theorem canonical_base (mem input : ByteArray) (n mm : Nat)
    (hn : 2 ≤ n) (hn32 : n ≤ 8) (hm : 0 < mm) (hodd : mm % 2 = 1)
    (hmod : Model.FastRepresents mem 0 n mm) (htop : R1.TopBitSet mem)
    (htn0 : MachineState.readWord mem 2080 = UInt256.ofNat 0) :
    Model.FastRepresents (canonicalMemory mem input n) 2112 n
      (Precompile.bytesToNatPadded input 96 (32*n) % mm) :=
  Exp.fastRepresents_mcopyMem_disjoint _ 256 2112 (32*n) 2112 n _ (Or.inl (by omega))
    (reduced_base mem input n mm hn hn32 hm hodd hmod htop htn0)

theorem canonical_lt (input : ByteArray) (n mm : Nat) (hm : 0 < mm) :
    Precompile.bytesToNatPadded input 96 (32*n) % mm < mm := Nat.mod_lt _ hm

theorem canonical_readWord (mem input : ByteArray) (n addr : Nat)
    (hn : 1 ≤ n) (_hn32 : n ≤ 8)
    (hd : (addr+32 ≤ 256 ∨ 256+32*n ≤ addr) ∧
      (addr+32 ≤ 512 ∨ 512+32*n ≤ addr) ∧
      (addr+32 ≤ 1792 ∨ 1792+32*n ≤ addr) ∧
      (addr+32 ≤ 2080 ∨ 2112+32*n ≤ addr)) :
    MachineState.readWord (canonicalMemory mem input n) addr =
      MachineState.readWord mem addr := by
  unfold canonicalMemory reducedMemory
  rw [Exp.readWord_mcopyMem_disjoint _ 256 2112 (32*n) addr hd.1,
    RetainedTNormalizer.readWord_outside _ n addr hn hd.2.2.1
      (hd.2.2.2.elim (fun h => Or.inl (by omega)) (fun h => Or.inr h))]
  unfold hitMemory
  apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
  rw [Challenge.EvmProof.Memory.readPadded_size]
  omega

theorem canonical_frame (mem input : ByteArray) (n bsize minv : Nat)
    (hn : 2 ≤ n) (hn32 : n ≤ 8) (hf : Exp.Frame mem n bsize minv) :
    Exp.Frame (canonicalMemory mem input n) n bsize minv := by
  have hh (addr : Nat) (ha : 2688 ≤ addr) :=
    canonical_readWord mem input n addr (by omega) hn32
      (show (addr+32 ≤ 256 ∨ 256+32*n ≤ addr) ∧
        (addr+32 ≤ 512 ∨ 512+32*n ≤ addr) ∧
        (addr+32 ≤ 1792 ∨ 1792+32*n ≤ addr) ∧
        (addr+32 ≤ 2080 ∨ 2112+32*n ≤ addr) from by omega)
  exact ⟨by rw [hh 2688 (by omega)]; exact hf.s32,
    by rw [hh 2720 (by omega)]; exact hf.minvW,
    by rw [hh 2752 (by omega)]; exact hf.ml,
    by rw [hh 2784 (by omega)]; exact hf.tl,
    by rw [hh 2816 (by omega)]; exact hf.eoff⟩

/-! The two guards have the same semantic predicate. Every fallback stage
preserves the represented modulus and outer n/bsize, which is sufficient to
propagate MISS to the later guard without tracing each scratch write. -/

theorem topBit_of_same_modulus (a b : ByteArray) (n mm : Nat) (hn : 1 ≤ n)
    (ha : Model.FastRepresents a 0 n mm) (hb : Model.FastRepresents b 0 n mm) :
    R1.TopBitSet a ↔ R1.TopBitSet b := by
  have h1 := Model.readWord_of_fastRepresents (j := 0) ha (by omega)
  have h2 := Model.readWord_of_fastRepresents (j := 0) hb (by omega)
  simp only [Nat.mul_zero, Nat.add_zero, Nat.sub_zero] at h1 h2
  unfold R1.TopBitSet
  rw [h1,h2]

theorem matches_of_same_modulus (a b : ByteArray) (n bsize mm : Nat) (hn : 1 ≤ n)
    (ha : Model.FastRepresents a 0 n mm) (hb : Model.FastRepresents b 0 n mm) :
    FullBase.Matches a n bsize ↔ FullBase.Matches b n bsize := by
  unfold FullBase.Matches
  rw [topBit_of_same_modulus a b n mm hn ha hb]

theorem miss_of_same_modulus (a b : ByteArray) (n bsize mm : Nat) (hn : 1 ≤ n)
    (ha : Model.FastRepresents a 0 n mm) (hb : Model.FastRepresents b 0 n mm)
    (hmiss : ¬ FullBase.Matches a n bsize) : ¬ FullBase.Matches b n bsize :=
  fun h => hmiss ((matches_of_same_modulus a b n bsize mm hn ha hb).mpr h)

#print axioms canonical_acc
#print axioms miss_of_same_modulus
end Challenge.Modexp.Submission.Proofs.Fast.ShiftProducerCanonical
