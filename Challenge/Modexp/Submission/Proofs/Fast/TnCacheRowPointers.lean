import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedPointers
import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedRowFrames

set_option warningAsError true
set_option maxHeartbeats 1000000

namespace Challenge.Modexp.Submission.Proofs.Fast.TnCacheRowPointers
open EvmSemantics
open Challenge.Modexp.Submission.Proofs.Fast Monpro CiosCached

def pointer (pb n i : Nat) : UInt256 := UInt256.ofNat (ptrAt (pb+32*n-32) i)

def qptr (n i : Nat) : UInt256 := UInt256.ofNat (2^256 - 32*(n-i))

private theorem two256 : (2:Nat)^256 =
    115792089237316195423570985008687907853269984665640564039457584007913129639936 := by norm_num

theorem qptr_succ (n i : Nat) (_hn : n ≤ 8) (hi : i < n) :
    UInt256.ofNat 32 + qptr n i = qptr n (i+1) := by
  unfold qptr
  rw [Challenge.EvmProof.Word.ofNat_add_mod, two256]
  congr 1
  omega

theorem qptr_end (n : Nat) : qptr n n = UInt256.ofNat 0 := by
  apply Challenge.EvmProof.Word.word_ext
  unfold qptr
  rw [Challenge.EvmProof.Word.word_toNat_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat, two256]
  simp

theorem sub_qptr (c n i : Nat) (hn : n ≤ 8) (hc : c < 2^200) :
    UInt256.ofNat c - qptr n i = UInt256.ofNat (c + 32*(n-i)) := by
  apply Challenge.EvmProof.Word.word_ext
  unfold qptr
  rw [Challenge.EvmProof.Word.word_toNat_sub, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat, two256]
  have hc' : c < 2^256 := lt_trans hc (by norm_num)
  rw [two256] at hc'
  rw [Nat.mod_eq_of_lt hc']
  rcases Nat.eq_zero_or_pos (n-i) with h0 | hpos
  · rw [h0]; omega
  · rw [Nat.mod_eq_of_lt (show 115792089237316195423570985008687907853269984665640564039457584007913129639936 -
      32*(n-i) < 115792089237316195423570985008687907853269984665640564039457584007913129639936 by omega)]
    omega

theorem sub_qptr_toNat (c n i : Nat) (hn : n ≤ 8) (hc : c < 2^200) :
    (UInt256.ofNat c - qptr n i).toNat = c + 32*(n-i) := by
  rw [sub_qptr c n i hn hc, Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt]
  have : (2:Nat)^200 < 2^256 := by norm_num
  omega

theorem qptr_condition (n i : Nat) (hn : n ≤ 8) (hi : i < n) :
    UInt256.isTrue (UInt256.ofNat 32 + qptr n i) ↔ i+1 < n := by
  rw [qptr_succ n i hn hi]
  show (qptr n (i+1)).toNat ≠ 0 ↔ _
  unfold qptr
  rw [Challenge.EvmProof.Word.word_toNat_ofNat, two256]
  rcases Nat.eq_zero_or_pos (n-(i+1)) with h0 | hpos
  · rw [h0]; simp; omega
  · rw [Nat.mod_eq_of_lt (by omega)]; omega

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

end Challenge.Modexp.Submission.Proofs.Fast.TnCacheRowPointers
