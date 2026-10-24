import Challenge.Modexp.Submission.Proofs.CRT.ColumnExpressions
set_option warningAsError true
set_option maxHeartbeats 2000000
namespace HistoricalSearch.CancelledCRT
open EvmSemantics
open Challenge.EvmProof.Word
open HistoricalSearch.CRTColumn HistoricalSearch.ColumnExpressions HistoricalSearch.ProductAccumulate

theorem cancelledResidual (B P I S H : Nat) (_hB : 0 < B) (_hP : 0 < P)
    (hI : (B*I)%P = 1) (hH : H%P=S%P) (hcancel : S%B=0) (hbound : S/B<P) :
    (H*I)%P = S/B := by
  have he : S = B*(S/B) := by have h := Nat.mod_add_div S B; omega
  calc (H*I)%P = ((H%P)*(I%P))%P := Nat.mul_mod _ _ _
    _ = ((S%P)*(I%P))%P := by rw [hH]
    _ = (S*I)%P := (Nat.mul_mod _ _ _).symm
    _ = ((B*I)*(S/B))%P := by nth_rw 1 [he]; congr 1; ac_rfl
    _ = ((S/B)%P)%P := by rw [Nat.mul_mod, hI, Nat.one_mul]
    _ = S/B := by rw [Nat.mod_mod, Nat.mod_eq_of_lt hbound]

def carryWord (H P : UInt256) : UInt256 := UInt256.mulMod H (UInt256.ofNat 128) P

theorem reconstructExpressions (hi : Expr) (C : Nat)
    (hcount : hi.count ≤ 19) (hlit : hi.literalsBounded (residueModulus-1))
    (hC : C ≤ 18*((2^244 : Nat)-1))
    (hS : hi.value ≤ 18*((2^244 : Nat)-1)^2+C)
    (hcancel : hi.value % 2^244 = 0) :
    (carryWord (hi.high (UInt256.ofNat residueModulus)) (UInt256.ofNat residueModulus)).toNat = hi.value/2^244 := by
  have hpv : (UInt256.ofNat residueModulus).toNat = residueModulus := by
    rw [word_toNat_ofNat]; exact Nat.mod_eq_of_lt (by norm_num [residueModulus])
  have hp : 0 < (UInt256.ofNat residueModulus).toNat := by rw [hpv]; norm_num [residueModulus]
  have hh := highInvariant (UInt256.ofNat residueModulus) hpv hi hcount hlit
  have hc := columnCarryBound (2^244) 18 hi.value C (Nat.two_pow_pos _) hC hS
  have hb : hi.value/2^244 < residueModulus := by norm_num [residueModulus] at *; omega
  unfold carryWord
  rw [mulMod_toNat _ _ _ hp, hpv]
  change ((hi.high (UInt256.ofNat residueModulus)).toNat*128)%residueModulus = _
  exact cancelledResidual (2^244) residueModulus 128 hi.value
    (hi.high (UInt256.ofNat residueModulus)).toNat (by positivity) (by norm_num [residueModulus])
    (by norm_num [residueModulus]) hh.2 hcancel hb

#print axioms cancelledResidual
#print axioms reconstructExpressions
end HistoricalSearch.CancelledCRT
