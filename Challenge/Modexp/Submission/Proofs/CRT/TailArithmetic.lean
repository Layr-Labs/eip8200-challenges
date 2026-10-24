import Challenge.Modexp.Submission.Proofs.CRT.GeneratedArithmetic
set_option warningAsError true
set_option maxHeartbeats 2000000

namespace HistoricalSearch.TailArithmetic
open EvmSemantics
open Challenge.EvmProof.Word
open HistoricalSearch.CRTColumn HistoricalSearch.ProductAccumulate
open HistoricalSearch.ColumnExpressions HistoricalSearch.GeneratedArithmetic

theorem mixedProductBound (x y : UInt256) (B F : Nat)
    (hx : x.toNat < B) (hy : y.toNat < F) : x.toNat*y.toNat ≤ (B-1)*(F-1) := by
  exact Nat.mul_le_mul (by omega) (by omega)

/-- The penultimate column only has four products, each containing a short
96-bit top limb. Its outgoing carry is therefore much smaller than the generic bound. -/
theorem col15_sharp (carry : UInt256) (a n q : Nat → UInt256)
    (ha7 : (a 7).toNat < radix) (ha8 : (a 8).toNat < 2^96)
    (hn7 : (n 7).toNat < radix) (hn8 : (n 8).toNat < 2^96)
    (hq7 : (q 7).toNat < radix) (hq8 : (q 8).toNat < 2^96)
    (hc : carry.toNat ≤ 18*(radix-1)) :
    (col15High carry a n q).value / radix ≤ 4*((2^96 : Nat)-1)+18 := by
  have haa := mixedProductBound (a 7) (a 8) radix (2^96) ha7 ha8
  have hnq := mixedProductBound (n 7) (q 8) radix (2^96) hn7 hq8
  have hqn := mixedProductBound (q 7) (n 8) radix (2^96) hq7 hn8
  apply column15CarryBound radix (2^96) carry.toNat _ (Nat.two_pow_pos 244) hc
  simp only [col15High, Expr.value]
  nlinarith

/-- Exact final ordinary MUL/ADD expression from generated column16. The sharp
carry makes the whole sum smaller than beta, so both omitted CRT and omitted
following columns are justified. -/
theorem col16_ordinary (a8 n8 q8 carry : UInt256)
    (ha : a8.toNat < 2^96) (hn : n8.toNat < 2^96) (hq : q8.toNat < 2^96)
    (hc : carry.toNat ≤ 4*((2^96 : Nat)-1)+18) :
    (n8*q8+(a8*a8+carry)).toNat = a8.toNat*a8.toNat+q8.toNat*n8.toNat+carry.toNat ∧
    (n8*q8+(a8*a8+carry)).toNat < radix ∧
    (a8.toNat*a8.toNat+q8.toNat*n8.toNat+carry.toNat)/radix = 0 := by
  have htop := column16Bound a8.toNat q8.toNat n8.toNat carry.toNat ha hq hn hc
  have hword : a8.toNat*a8.toNat+q8.toNat*n8.toNat+carry.toNat < wordRadix :=
    htop.trans (by norm_num [wordRadix])
  have h1 : a8.toNat*a8.toNat < 2^256 := by change _ < wordRadix; omega
  have h2 : n8.toNat*q8.toNat < 2^256 := by change _ < wordRadix; nlinarith
  have h3 : a8.toNat*a8.toNat+carry.toNat < 2^256 := by change _ < wordRadix; omega
  have heq : (n8*q8+(a8*a8+carry)).toNat = a8.toNat*a8.toNat+q8.toNat*n8.toNat+carry.toNat := by
    simp only [word_toNat_add, mul_toNat, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2,
      Nat.mod_eq_of_lt h3]
    have he : n8.toNat*q8.toNat+(a8.toNat*a8.toNat+carry.toNat) =
        a8.toNat*a8.toNat+q8.toNat*n8.toNat+carry.toNat := by ring
    rw [he]
    exact Nat.mod_eq_of_lt hword
  exact ⟨heq, by rw [heq]; exact htop, Nat.div_eq_of_lt htop⟩

#print axioms col15_sharp
#print axioms col16_ordinary

end HistoricalSearch.TailArithmetic
