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

/-- The two schedule words stored without their 32-bit mask. -/
def Dirty (k : Nat) : Prop := k = 1 ∨ k = 2
instance (k : Nat) : Decidable (Dirty k) := inferInstanceAs (Decidable (_ ∨ _))

/-- Dead bits allowed above the lanes of round `i`'s message word: none for a clean word,
up to 64 bits in each half, and at most 32 in the lower half when the round rotates through
`compact` (which never looks above bit 32 of the upper half). -/
def JunkBound (i jl jr : Nat) : Prop :=
  jl < 2 ^ 64 ∧ jr < 2 ^ 64 ∧
    (Paired144WordRound.usesCompact Crypto.Ripemd160.s[i]! Crypto.Ripemd160.sP[i + 3]! →
      jl < 2 ^ 32) ∧
    (¬ Dirty Crypto.Ripemd160.r[i]! → jl = 0) ∧ (¬ Dirty Crypto.Ripemd160.rP[i + 3]! → jr = 0)

def MessageWord (message : UInt256) (words : Nat → UInt32) (i : Nat) : Prop :=
  ∃ jl jr, JunkBound i jl jr ∧ bits message =
    (pack (words Crypto.Ripemd160.r[i]!).toBitVec (words Crypto.Ripemd160.rP[i + 3]!).toBitVec) +
      StaggerRound.junk jl jr

def MessageReady (message : Nat → UInt256) (words : Nat → UInt32) (count : Nat) : Prop :=
  ∀ i < count, MessageWord (message i) words i

theorem step_of_crypto (words : Nat → UInt32) (i : Nat) (hi : i < 77)
    (message : UInt256) (l q : CryptoLane)
    (hm : MessageWord message words i) :
    step i message (packCrypto l q) =
      packCrypto
        (cryptoStep (i / 16) Crypto.Ripemd160.s[i]!
          (words Crypto.Ripemd160.r[i]!) Crypto.Ripemd160.K[i / 16]! l)
        (cryptoStep (4 - (i + 3) / 16) Crypto.Ripemd160.sP[i + 3]!
          (words Crypto.Ripemd160.rP[i + 3]!) Crypto.Ripemd160.KP[(i + 3) / 16]! q) := by
  obtain ⟨hl0, hl, _, _⟩ := rotation_bounds ⟨i, by omega⟩
  obtain ⟨_, _, hr0, hr⟩ := rotation_bounds ⟨i + 3, by omega⟩
  obtain ⟨hmode, hleft, hright⟩ := mode_valid ⟨i, hi⟩
  obtain ⟨jl, jr, ⟨hjl, hjr, hc, -, -⟩, hmsg⟩ := hm
  have h := StaggerWord.step_of_crypto_junk (mode i) _ _ hmode hl0 hl hr0 hr
    (words Crypto.Ripemd160.r[i]!) (words Crypto.Ripemd160.rP[i + 3]!)
    Crypto.Ripemd160.K[i / 16]! Crypto.Ripemd160.KP[(i + 3) / 16]! l q message jl jr hjl hjr hc hmsg
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
