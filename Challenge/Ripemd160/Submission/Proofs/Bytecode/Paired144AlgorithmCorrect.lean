import Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired144Algorithm
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired144WordCrypto
set_option warningAsError true
set_option maxRecDepth 8000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired144Algorithm
open EvmSemantics Paired144Core Paired144WordRound PairedLaneUInt256Bridge
open PairedLaneCryptoBridge (cryptoStep)

theorem rotation_bounds (i : Fin 80) :
    5 ≤ Crypto.Ripemd160.s[i.val]! ∧ Crypto.Ripemd160.s[i.val]! ≤ 15 ∧
    5 ≤ Crypto.Ripemd160.sP[i.val]! ∧ Crypto.Ripemd160.sP[i.val]! ≤ 15 := by
  have h : ∀ j : Fin 80,
      5 ≤ Crypto.Ripemd160.s[j.val]! ∧ Crypto.Ripemd160.s[j.val]! ≤ 15 ∧
      5 ≤ Crypto.Ripemd160.sP[j.val]! ∧ Crypto.Ripemd160.sP[j.val]! ≤ 15 := by decide
  exact h i

theorem index_bounds (i : Fin 80) :
    Crypto.Ripemd160.r[i.val]! <16 ∧ Crypto.Ripemd160.rP[i.val]! <16 := by
  have h : ∀j : Fin 80, Crypto.Ripemd160.r[j.val]! <16 ∧ Crypto.Ripemd160.rP[j.val]! <16 := by decide
  exact h i

theorem step_of_crypto (words : Nat → UInt32) (i : Nat) (hi : i<80)
    (message : UInt256) (l q : CryptoLane)
    (hm : message = packed32 (words Crypto.Ripemd160.r[i]!) (words Crypto.Ripemd160.rP[i]!)) :
    step i message (packCrypto l q) =
      packCrypto
        (cryptoStep (i/16) Crypto.Ripemd160.s[i]! (words Crypto.Ripemd160.r[i]!) Crypto.Ripemd160.K[i/16]! l)
        (cryptoStep (4-i/16) Crypto.Ripemd160.sP[i]! (words Crypto.Ripemd160.rP[i]!) Crypto.Ripemd160.KP[i/16]! q) := by
  obtain ⟨hl0,hl,hr0,hr⟩ := rotation_bounds ⟨i,hi⟩
  subst message
  have base := Paired144WordCrypto.wordStep_of_crypto (i/16)
    Crypto.Ripemd160.s[i]! Crypto.Ripemd160.sP[i]! hl0 hl hr0 hr
    (words Crypto.Ripemd160.r[i]!) (words Crypto.Ripemd160.rP[i]!)
    Crypto.Ripemd160.K[i/16]! Crypto.Ripemd160.KP[i/16]! l q
  by_cases hg : i/16=2
  · simp only [step,hg,if_pos,physicalKey]
    obtain ⟨hb,hc,hd⟩ := Paired144WordGroupTwo.packCrypto_supported l q
    rw [Paired144WordGroupTwo.rawWordStep2_eq _ _ _ (key i) (packCrypto l q) hb hc hd]
    simpa only [hg,key,packed32] using base
  · simpa only [step,hg,if_false,key,packed32] using base

theorem fold_crypto (message : Nat → UInt256) (words : Nat → UInt32)
    (count : Nat) (hcount : count≤80) (l q : CryptoLane)
    (hm : MessageReady message words count) :
    fold message count (packCrypto l q) = packCrypto (leftFold words count l) (rightFold words count q) := by
  induction count with
  | zero => rfl
  | succ i ih =>
    have ht : MessageReady message words i := fun j hj => hm j (by omega)
    rw [fold, ih (by omega) ht]
    exact step_of_crypto words i (by omega) (message i) _ _ (hm i (by omega))

#print axioms rotation_bounds
#print axioms step_of_crypto
#print axioms fold_crypto
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired144Algorithm
