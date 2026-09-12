import Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired80WordMessage
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired80WordGroupTwoHoist
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedCompressionBridge

set_option warningAsError true
set_option maxRecDepth 8000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired80Algorithm
open EvmSemantics PairedLaneUInt256Bridge Paired80Core Paired80WordRound
open Paired80WordGroupTwoHoist
open Paired80CryptoBridge (CryptoLane cryptoStep)

def packed32 (lo hi : UInt32) : UInt256 := word (pack lo.toBitVec hi.toBitVec)

def key (i : Nat) : UInt256 :=
  packed32 Crypto.Ripemd160.K[i / 16]! Crypto.Ripemd160.KP[i / 16]!

def physicalKey (i : Nat) : UInt256 := if i / 16 = 2 then adjustedK (key i) else key i

/-- Each physical group2 step uses the cached adjusted constant; the canonical
state omits that cache because physical round boundaries own its lifetime. -/
def step (i : Nat) (message : UInt256) (q : WordLane) : WordLane :=
  if i / 16 = 2 then
    rawWordStep2 Crypto.Ripemd160.s[i]! Crypto.Ripemd160.sP[i]! message (physicalKey i) q
  else wordStep (i / 16) Crypto.Ripemd160.s[i]! Crypto.Ripemd160.sP[i]! message (key i) q

def fold (message : Nat → UInt256) : Nat → WordLane → WordLane
  | 0, q => q
  | i + 1, q => step i (message i) (fold message i q)

def leftFold (words : Nat → UInt32) : Nat → CryptoLane → CryptoLane
  | 0, q => q
  | i + 1, q => cryptoStep (i / 16) Crypto.Ripemd160.s[i]!
      (words Crypto.Ripemd160.r[i]!) Crypto.Ripemd160.K[i / 16]! (leftFold words i q)

def rightFold (words : Nat → UInt32) : Nat → CryptoLane → CryptoLane
  | 0, q => q
  | i + 1, q => cryptoStep (4 - i / 16) Crypto.Ripemd160.sP[i]!
      (words Crypto.Ripemd160.rP[i]!) Crypto.Ripemd160.KP[i / 16]! (rightFold words i q)

theorem rotation_bounds (i : Fin 80) :
    0 < Crypto.Ripemd160.s[i.val]! ∧ Crypto.Ripemd160.s[i.val]! < 17 ∧
    0 < Crypto.Ripemd160.sP[i.val]! ∧ Crypto.Ripemd160.sP[i.val]! < 17 := by
  have h : ∀ j : Fin 80,
      0 < Crypto.Ripemd160.s[j.val]! ∧ Crypto.Ripemd160.s[j.val]! < 17 ∧
      0 < Crypto.Ripemd160.sP[j.val]! ∧ Crypto.Ripemd160.sP[j.val]! < 17 := by decide
  exact h i

theorem index_bounds (i : Fin 80) :
    Crypto.Ripemd160.r[i.val]! < 16 ∧ Crypto.Ripemd160.rP[i.val]! < 16 := by
  have h : ∀ j : Fin 80,
      Crypto.Ripemd160.r[j.val]! < 16 ∧ Crypto.Ripemd160.rP[j.val]! < 16 := by decide
  exact h i

def MessageReady (message : Nat → UInt256) (words : Nat → UInt32) (count : Nat) : Prop :=
  ∀ i < count, Paired80Message.Eq112 (bits (message i))
    (pack (words Crypto.Ripemd160.r[i]!).toBitVec (words Crypto.Ripemd160.rP[i]!).toBitVec)

theorem step_of_crypto (words : Nat → UInt32) (i : Nat) (hi : i < 80)
    (message : UInt256) (l q : CryptoLane)
    (hm : Paired80Message.Eq112 (bits message)
      (pack (words Crypto.Ripemd160.r[i]!).toBitVec (words Crypto.Ripemd160.rP[i]!).toBitVec)) :
    step i message (packCrypto l q) =
      packCrypto
        (cryptoStep (i / 16) Crypto.Ripemd160.s[i]!
          (words Crypto.Ripemd160.r[i]!) Crypto.Ripemd160.K[i / 16]! l)
        (cryptoStep (4 - i / 16) Crypto.Ripemd160.sP[i]!
          (words Crypto.Ripemd160.rP[i]!) Crypto.Ripemd160.KP[i / 16]! q) := by
  obtain ⟨hl0, hl, hr0, hr⟩ := rotation_bounds ⟨i, hi⟩
  have base := Paired80WordMessage.wordStep_of_crypto_message (i / 16)
    Crypto.Ripemd160.s[i]! Crypto.Ripemd160.sP[i]! hl0 hl hr0 hr
    (words Crypto.Ripemd160.r[i]!) (words Crypto.Ripemd160.rP[i]!)
    Crypto.Ripemd160.K[i / 16]! Crypto.Ripemd160.KP[i / 16]! l q message hm
  by_cases hg : i / 16 = 2
  · simp only [step, hg, if_pos, physicalKey]
    rw [rawWordStep2_eq_of_supported _ _ message (key i) (packCrypto l q)
      (packCrypto_supported l q).1 (packCrypto_supported l q).2.1 (packCrypto_supported l q).2.2]
    simpa only [hg, key, packed32] using base
  · simpa only [step, hg, if_false, key, packed32] using base

theorem fold_crypto (message : Nat → UInt256) (words : Nat → UInt32)
    (count : Nat) (hcount : count ≤ 80) (l q : CryptoLane)
    (hm : MessageReady message words count) :
    fold message count (packCrypto l q) = packCrypto (leftFold words count l) (rightFold words count q) := by
  induction count with
  | zero => rfl
  | succ i ih =>
    have ht : MessageReady message words i := fun j hj => hm j (by omega)
    rw [fold, ih (by omega) ht]
    exact step_of_crypto words i (by omega) (message i) _ _ (hm i (by omega))

#print axioms rotation_bounds
#print axioms index_bounds
#print axioms step_of_crypto
#print axioms fold_crypto
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired80Algorithm
