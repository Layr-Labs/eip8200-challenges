import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedPointers
import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedRowFrames

set_option warningAsError true
set_option maxHeartbeats 1000000

namespace Challenge.Modexp.Submission.Proofs.Fast.TnCacheRowPointers
open EvmSemantics
open Challenge.Modexp.Submission.Proofs.Fast Monpro CiosCached

def pointer (pb n i : Nat) : UInt256 := UInt256.ofNat (ptrAt (pb+32*n-32) i)

theorem pointer_succ (pb n i : Nat) :
    negative32 + pointer pb n i = pointer pb n (i+1) := by
  change UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904 +
    UInt256.ofNat (ptrAt (pb+32*n-32) i) = UInt256.ofNat (ptrAt (pb+32*n-32) (i+1))
  rw [Challenge.EvmProof.Word.ofNat_add_mod, ptrAt_succ]

theorem pointer_value (pb n i : Nat) (hpb : 32 ≤ pb) (hfit : pb+32*n ≤ 2816) (hi : i ≤ n) :
    (pointer pb n i).toNat = pb-32+32*(n-i) :=
  CiosCachedPointers.l1_pointer pb n i hpb hfit hi

theorem pointer_limb (pb n i : Nat) (hpb : 32 ≤ pb) (hfit : pb+32*n ≤ 2816) (hi : i < n) :
    (pointer pb n i).toNat = pb+32*(n-1-i) := by
  rw [pointer_value pb n i hpb hfit (by omega)]
  omega

theorem pointer_condition (pb n i : Nat) (hpb : 32 ≤ pb) (hfit : pb+32*n ≤ 2816)
    (hi : i < n) :
    UInt256.isTrue (UInt256.gt (negative32+pointer pb n i) (UInt256.ofNat (pb-32))) ↔ i+1 < n := by
  rw [pointer_succ]
  exact CiosCachedPointers.l1_condition pb n (i+1) hpb hfit (by omega)

theorem pointer_end (pb n : Nat) (hpb : 32 ≤ pb) (hfit : pb+32*n ≤ 2816) :
    pointer pb n n = UInt256.ofNat (pb-32) := by
  apply Challenge.EvmProof.Word.word_ext
  rw [pointer_value pb n n hpb hfit le_rfl,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  simp

#print axioms pointer_succ
#print axioms pointer_condition
end Challenge.Modexp.Submission.Proofs.Fast.TnCacheRowPointers
