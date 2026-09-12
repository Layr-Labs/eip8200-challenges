import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerWord
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired80Algorithm
set_option warningAsError true
set_option maxRecDepth 10000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerAlgorithm
open EvmSemantics PairedLaneUInt256Bridge Paired144Core Paired144WordRound
open Paired80Algorithm (leftFold rightFold)
open Paired80CryptoBridge (cryptoStep)

def packed32 (lo hi : UInt32) : UInt256 := word (pack lo.toBitVec hi.toBitVec)

theorem rotation_bounds (i : Fin 80) :
    5 ≤ Crypto.Ripemd160.s[i.val]! ∧ Crypto.Ripemd160.s[i.val]! ≤ 15 ∧
    5 ≤ Crypto.Ripemd160.sP[i.val]! ∧ Crypto.Ripemd160.sP[i.val]! ≤ 15 := by
  have h : ∀ j : Fin 80, 5 ≤ Crypto.Ripemd160.s[j.val]! ∧ Crypto.Ripemd160.s[j.val]! ≤ 15 ∧
    5 ≤ Crypto.Ripemd160.sP[j.val]! ∧ Crypto.Ripemd160.sP[j.val]! ≤ 15 := by decide
  exact h i

def mode (i : Nat) : Nat :=
  if i < 13 then 0 else if i < 16 then 5 else
  if i < 29 then 1 else if i < 32 then 6 else
  if i < 45 then 2 else if i < 48 then 7 else
  if i < 61 then 3 else if i < 64 then 8 else 4

def key (i : Nat) : UInt256 :=
  packed32 Crypto.Ripemd160.K[i / 16]! Crypto.Ripemd160.KP[(i + 3) / 16]!
def physicalKey (i : Nat) : UInt256 := StaggerWord.key (mode i) (key i)
def step (i : Nat) (message : UInt256) (q : WordLane) : WordLane :=
  StaggerWord.step (mode i) Crypto.Ripemd160.s[i]! Crypto.Ripemd160.sP[i + 3]!
    message (physicalKey i) q

def stepFinal (i : Nat) (message : UInt256) (q : WordLane) : WordLane :=
  StaggerWord.stepFinal (mode i) Crypto.Ripemd160.s[i]! Crypto.Ripemd160.sP[i + 3]!
    message (physicalKey i) q

theorem stepFinal_left_of_crypto (words : Nat → UInt32) (i : Nat) (hi : i < 77)
    (message : UInt256) (l q : CryptoLane)
    (hm : bits message =
      (pack (words Crypto.Ripemd160.r[i]!).toBitVec (words Crypto.Ripemd160.rP[i + 3]!).toBitVec)) :
    Paired80Compression.unpackLeft (stepFinal i message (packCrypto l q)) =
      cryptoStep (i / 16) Crypto.Ripemd160.s[i]!
        (words Crypto.Ripemd160.r[i]!) Crypto.Ripemd160.K[i / 16]! l := by
  unfold stepFinal
  rw [StaggerWord.unpackLeft_stepFinal]
  change Paired80Compression.unpackLeft (step i message (packCrypto l q)) = _
  rw [step_of_crypto words i hi message l q hm, Paired80Compression.unpackLeft_packCrypto]

theorem stepFinal_right_of_crypto (words : Nat → UInt32) (i : Nat) (hi : i < 77)
    (message : UInt256) (l q : CryptoLane)
    (hm : bits message =
      (pack (words Crypto.Ripemd160.r[i]!).toBitVec (words Crypto.Ripemd160.rP[i + 3]!).toBitVec)) :
    StaggerWord.unpackRightLane (stepFinal i message (packCrypto l q)) =
      cryptoStep (4 - (i + 3) / 16) Crypto.Ripemd160.sP[i + 3]!
        (words Crypto.Ripemd160.rP[i + 3]!) Crypto.Ripemd160.KP[(i + 3) / 16]! q := by
  unfold stepFinal
  rw [StaggerWord.unpackRightLane_stepFinal]
  change StaggerWord.unpackRightLane (step i message (packCrypto l q)) = _
  rw [step_of_crypto words i hi message l q hm, StaggerWord.unpackRightLane_packCrypto]

def fold (message : Nat → UInt256) : Nat → WordLane → WordLane
  | 0, q => q
  | i + 1, q => step i (message i) (fold message i q)

theorem mode_valid (i : Fin 77) : mode i.val < 9 ∧
    StaggerBoolean.leftGroup (mode i.val) = i.val / 16 ∧
    StaggerBoolean.rightGroup (mode i.val) = 4 - (i.val + 3) / 16 := by
  have h : ∀ j : Fin 77, mode j.val < 9 ∧
      StaggerBoolean.leftGroup (mode j.val) = j.val / 16 ∧
      StaggerBoolean.rightGroup (mode j.val) = 4 - (j.val + 3) / 16 := by decide
  exact h i

def MessageReady (message : Nat → UInt256) (words : Nat → UInt32) (count : Nat) : Prop :=
  ∀ i < count, bits (message i) =
    (pack (words Crypto.Ripemd160.r[i]!).toBitVec (words Crypto.Ripemd160.rP[i + 3]!).toBitVec)

theorem step_of_crypto (words : Nat → UInt32) (i : Nat) (hi : i < 77)
    (message : UInt256) (l q : CryptoLane)
    (hm : bits message =
      (pack (words Crypto.Ripemd160.r[i]!).toBitVec (words Crypto.Ripemd160.rP[i + 3]!).toBitVec)) :
    step i message (packCrypto l q) =
      packCrypto
        (cryptoStep (i / 16) Crypto.Ripemd160.s[i]!
          (words Crypto.Ripemd160.r[i]!) Crypto.Ripemd160.K[i / 16]! l)
        (cryptoStep (4 - (i + 3) / 16) Crypto.Ripemd160.sP[i + 3]!
          (words Crypto.Ripemd160.rP[i + 3]!) Crypto.Ripemd160.KP[(i + 3) / 16]! q) := by
  obtain ⟨hl0, hl, _, _⟩ := rotation_bounds ⟨i, by omega⟩
  obtain ⟨_, _, hr0, hr⟩ := rotation_bounds ⟨i + 3, by omega⟩
  obtain ⟨hmode, hleft, hright⟩ := mode_valid ⟨i, hi⟩
  have h := StaggerWord.step_of_crypto (mode i) _ _ hmode hl0 hl hr0 hr
    (words Crypto.Ripemd160.r[i]!) (words Crypto.Ripemd160.rP[i + 3]!)
    Crypto.Ripemd160.K[i / 16]! Crypto.Ripemd160.KP[(i + 3) / 16]! l q message hm
  simpa only [step, physicalKey, key, packed32, hleft, hright] using h

theorem fold_crypto (message : Nat → UInt256) (words : Nat → UInt32)
    (count : Nat) (hcount : count ≤ 77) (l q : CryptoLane)
    (hm : MessageReady message words count) :
    fold message count (packCrypto l (rightFold words 3 q)) =
      packCrypto (leftFold words count l) (rightFold words (count + 3) q) := by
  induction count with
  | zero => rfl
  | succ i ih =>
    have ht : MessageReady message words i := fun j hj => hm j (by omega)
    rw [fold, ih (by omega) ht]
    exact step_of_crypto words i (by omega) (message i) _ _ (hm i (by omega))

#print axioms mode_valid
#print axioms step_of_crypto
#print axioms fold_crypto
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerAlgorithm
