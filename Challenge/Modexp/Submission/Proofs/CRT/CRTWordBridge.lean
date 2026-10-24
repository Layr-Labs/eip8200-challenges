import Challenge.Modexp.Submission.Proofs.CRT.GenericColumn
import Challenge.Modexp.Submission.Proofs.CRT.CRTExecution
set_option warningAsError true
set_option maxHeartbeats 2000000

namespace HistoricalSearch.CRTWordBridge
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.EvmProof.Word
open HistoricalSearch.CRTColumn HistoricalSearch.GenericColumn HistoricalSearch.CRTExecution
open Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleKernel

theorem mod_toNat (a b : UInt256) (hb : b.toNat ≠ 0) :
    (a % b).toNat = a.toNat % b.toNat := by
  change (UInt256.mod a b).toNat = _
  unfold UInt256.mod UInt256.toNat at *
  rw [if_neg hb]
  rfl

theorem shiftLeft_toNat (a : UInt256) (shift : Nat) (hshift : shift < 256) :
    (UInt256.shiftLeft a (UInt256.ofNat shift)).toNat = (a.toNat <<< shift) % 2^256 := by
  have hs : (UInt256.ofNat shift).toNat = shift := by
    rw [word_toNat_ofNat]
    apply Nat.mod_eq_of_lt
    exact hshift.trans (by norm_num)
  unfold UInt256.shiftLeft
  rw [hs, if_neg (by omega), word_toNat_ofNat]
  change ((a.toNat <<< shift) % 2^256) % 2^256 = _
  exact Nat.mod_mod _ _

/-- The UInt256 expression produced by the concrete EVM macro recovers the
exact mathematical carry. No abstraction of EVM subtraction or shifts remains. -/
theorem carryWord_toNat (W S C H : Nat) (hWpos : 0 < W) (hW : W ≤ 248)
    (hC : C ≤ 18*(2^W-1)) (hS : S ≤ 18*(2^W-1)^2+C)
    (hHbound : H ≤ 19*(residueModulus-1))
    (hH : H % residueModulus = S % residueModulus) :
    (carryWord (UInt256.ofNat H) (UInt256.ofNat (S % wordRadix))
      (UInt256.ofNat residueModulus) (UInt256.ofNat W) (UInt256.ofNat (256-W))).toNat = S/2^W := by
  have hb := widthBounds W S C H hW hC hS hHbound
  have hp : 0 < residueModulus := by norm_num [residueModulus]
  have hpR : residueModulus < wordRadix := by norm_num [residueModulus, wordRadix]
  have hHR : H < wordRadix := by omega
  have hloR : S % wordRadix < wordRadix := Nat.mod_lt _ (by norm_num [wordRadix])
  have hHv : (UInt256.ofNat H).toNat = H := by
    rw [word_toNat_ofNat]
    exact Nat.mod_eq_of_lt hHR
  have hlov : (UInt256.ofNat (S % wordRadix)).toNat = S % wordRadix := by
    rw [word_toNat_ofNat]
    exact Nat.mod_eq_of_lt hloR
  have hPv : (UInt256.ofNat residueModulus).toNat = residueModulus := by
    rw [word_toNat_ofNat]
    exact Nat.mod_eq_of_lt hpR
  have hPn : (UInt256.ofNat residueModulus).toNat ≠ 0 := by rw [hPv]; omega
  have hrem : (UInt256.ofNat (S % wordRadix) % UInt256.ofNat residueModulus).toNat =
      (S % wordRadix) % residueModulus := by rw [mod_toNat _ _ hPn, hlov, hPv]
  have hrl := Nat.mod_lt (S % wordRadix) hp
  have hsub : (UInt256.ofNat residueModulus -
      UInt256.ofNat (S % wordRadix) % UInt256.ofNat residueModulus).toNat =
      residueModulus - (S % wordRadix) % residueModulus := by
    rw [word_toNat_sub_cond, hPv, hrem, if_neg (by omega)]
  have hadd : ((UInt256.ofNat residueModulus -
      UInt256.ofNat (S % wordRadix) % UInt256.ofNat residueModulus) + UInt256.ofNat H).toNat =
      (H+(residueModulus-(S % wordRadix) % residueModulus)) % wordRadix := by
    rw [word_toNat_add, hsub, hHv, Nat.add_comm]
    rfl
  unfold carryWord
  rw [word_toNat_add, shiftRight_toNat _ (by omega : W < 256), hlov,
    shiftLeft_toNat _ (256-W) (by omega), shiftRight_toNat _ (by decide : 5 < 256),
    mod_toNat _ _ hPn, hadd, hPv]
  exact wrappedShiftsAtWidth W S C H hW hC hS hHbound hH

theorem carryWord_eq (W S C H : Nat) (hWpos : 0 < W) (hW : W ≤ 248)
    (hC : C ≤ 18*(2^W-1)) (hS : S ≤ 18*(2^W-1)^2+C)
    (hHbound : H ≤ 19*(residueModulus-1))
    (hH : H % residueModulus = S % residueModulus) :
    carryWord (UInt256.ofNat H) (UInt256.ofNat (S % wordRadix))
      (UInt256.ofNat residueModulus) (UInt256.ofNat W) (UInt256.ofNat (256-W)) =
      UInt256.ofNat (S/2^W) := by
  apply word_ext
  rw [carryWord_toNat W S C H hWpos hW hC hS hHbound hH, word_toNat_ofNat]
  have hb := widthBounds W S C H hW hC hS hHbound
  have hpow : 2^W ≤ (2^248 : Nat) := Nat.pow_le_pow_right (by decide) hW
  have hcarry : S/2^W < 2^256 := by
    have := hb.2.2.2
    norm_num at hpow ⊢
    omega
  exact (Nat.mod_eq_of_lt hcarry).symm

/-- Arithmetic correctness of the exact 22-byte reconstruction macro, for any
starting state/address and any bounded stack frame satisfying the column bounds. -/
theorem runCorrect (s : State) (pc : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1018)
    (W S C H : Nat) (hWpos : 0 < W) (hW : W ≤ 248)
    (hC : C ≤ 18*(2^W-1)) (hS : S ≤ 18*(2^W-1)^2+C)
    (hHbound : H ≤ 19*(residueModulus-1))
    (hH : H % residueModulus = S % residueModulus) :
    runInstructions (program (UInt256.ofNat W) (UInt256.ofNat (256-W)))
      {s with pc := pc, stack := (UInt256.ofNat H :: UInt256.ofNat (S % wordRadix) ::
        UInt256.ofNat residueModulus :: rest)} =
      some {s with pc := advancePC 22 pc, stack := (UInt256.ofNat (S/2^W) :: UInt256.ofNat residueModulus :: rest)} := by
  rw [HistoricalSearch.CRTExecution.run s pc _ _ _ _ _ rest hcap,
    carryWord_eq W S C H hWpos hW hC hS hHbound hH]

#print axioms carryWord_toNat
#print axioms carryWord_eq
#print axioms runCorrect

end HistoricalSearch.CRTWordBridge
