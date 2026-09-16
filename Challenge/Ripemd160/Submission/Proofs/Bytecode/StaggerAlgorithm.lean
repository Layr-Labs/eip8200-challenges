import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerAdaptiveWord
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired80Algorithm
import Challenge.Ripemd160.Submission.Proofs.Bytecode.JD8Congr
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
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
  if StaggerAdaptiveWord.usesAdaptive Crypto.Ripemd160.s[i]! Crypto.Ripemd160.sP[i + 3]! then
    StaggerAdaptiveWord.step (mode i) Crypto.Ripemd160.s[i]! Crypto.Ripemd160.sP[i + 3]!
      message (physicalKey i) q
  else
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

/-- The schedule words stored without their 32-bit mask: words 1 and 2 by the data-block
loader, word 14 by the pad-only block (`n <<< 3`, whose `n / 2 ^ 29 < 2 ^ 35` dead lanes sit
above the low bit length). -/
def Dirty (k : Nat) : Prop := k = 1 ∨ k = 2 ∨ k = 14
instance (k : Nat) : Decidable (Dirty k) := inferInstanceAs (Decidable (_ ∨ _))

/-- The schedule words that can reach a round carrying junk under THIS artifact: 1 and 2 from
the data-block loader, 14 from the pad-only block, and 3, 10, 12, 13, 15 from the six lane masks
it does not emit.  **Words 8 and 11 are deliberately absent.**  Rounds 75 and 76 take the
previous round's UNMASKED C output as their `d` lane, so their `raw` term's low 144 bits are
large rather than below `2 ^ 34`, and the zero at bit 121 that licenses the exception tolerates
addends below `2 ^ 120` only.  Those two rounds read words 8 and 11, so those two stay masked
and their message junk is exactly zero. -/
def JDirty (k : Nat) : Prop :=
  k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 10 ∨ k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15
instance (k : Nat) : Decidable (JDirty k) := inferInstanceAs (Decidable (_ ∨ _))

theorem jdirty_of_dirty {k : Nat} (h : Dirty k) : JDirty k := by
  rcases h with rfl | rfl | rfl <;> simp only [JDirty] <;> tauto

theorem ne15_of_not_jdirty {k : Nat} (h : ¬ JDirty k) : k ≠ 15 := by
  intro hk
  exact h (by rw [hk]; simp only [JDirty]; tauto)

/-- Dead bits allowed above the lanes of round `i`'s message word.  A word this artifact still
masks carries NONE; an unmasked one carries up to the carry threshold `2 ^ 112 - 4`, which is
all `normalize` can absorb (`JD8Congr.normalize_ofNat_junk_jrfree`). -/
def JunkBound (i jl jr : Nat) : Prop :=
  jl < 2 ^ 112 - 4 ∧
    (¬ JDirty Crypto.Ripemd160.r[i]! → jl = 0) ∧
    (¬ JDirty Crypto.Ripemd160.rP[i + 3]! → jr = 0)

theorem adaptive_rounds (i : Fin 77) :
    StaggerAdaptiveWord.usesAdaptive Crypto.Ripemd160.s[i.val]! Crypto.Ripemd160.sP[i.val + 3]! ↔
      i.val ∈ [39, 51, 53, 59] := by
  have h : ∀ j : Fin 77,
      StaggerAdaptiveWord.usesAdaptive Crypto.Ripemd160.s[j.val]! Crypto.Ripemd160.sP[j.val + 3]! ↔
        j.val ∈ [39, 51, 53, 59] := by decide
  exact h i

theorem adaptive_schedule (i : Fin 77)
    (h : StaggerAdaptiveWord.usesAdaptive Crypto.Ripemd160.s[i.val]! Crypto.Ripemd160.sP[i.val + 3]!) :
    ((StaggerAdaptiveWord.gap Crypto.Ripemd160.s[i.val]! Crypto.Ripemd160.sP[i.val + 3]! = 68 ∨
      StaggerAdaptiveWord.gap Crypto.Ripemd160.s[i.val]! Crypto.Ripemd160.sP[i.val + 3]! = 69) ∧
      Crypto.Ripemd160.r[i.val]! ≠ 2 ∧ Crypto.Ripemd160.r[i.val]! ≠ 14) ∨
    (StaggerAdaptiveWord.gap Crypto.Ripemd160.s[i.val]! Crypto.Ripemd160.sP[i.val + 3]! = 87 ∧
      ¬ Dirty Crypto.Ripemd160.r[i.val]!) := by
  have hf : ∀ j : Fin 77,
      StaggerAdaptiveWord.usesAdaptive Crypto.Ripemd160.s[j.val]! Crypto.Ripemd160.sP[j.val + 3]! →
      ((StaggerAdaptiveWord.gap Crypto.Ripemd160.s[j.val]! Crypto.Ripemd160.sP[j.val + 3]! = 68 ∨
        StaggerAdaptiveWord.gap Crypto.Ripemd160.s[j.val]! Crypto.Ripemd160.sP[j.val + 3]! = 69) ∧
        Crypto.Ripemd160.r[j.val]! ≠ 2 ∧ Crypto.Ripemd160.r[j.val]! ≠ 14) ∨
      (StaggerAdaptiveWord.gap Crypto.Ripemd160.s[j.val]! Crypto.Ripemd160.sP[j.val + 3]! = 87 ∧
        ¬ Dirty Crypto.Ripemd160.r[j.val]!) := by decide
  exact hf i h

def MessageWord (message : UInt256) (words : Nat → UInt32) (i : Nat) : Prop :=
  ∃ jl jr, JunkBound i jl jr ∧ bits message =
    (pack (words Crypto.Ripemd160.r[i]!).toBitVec (words Crypto.Ripemd160.rP[i + 3]!).toBitVec) +
      StaggerRound.junk jl jr

def MessageReady (message : Nat → UInt256) (words : Nat → UInt32) (count : Nat) : Prop :=
  ∀ i < count, MessageWord (message i) words i

/-- The round step at the ORIGINAL, narrow junk budget.  Retained because the widened version
below reduces to it with `jl = jr = 0`. -/
theorem step_of_crypto_narrow (words : Nat → UInt32) (i : Nat) (hi : i < 77)
    (message : UInt256) (l q : CryptoLane) (jl jr : Nat)
    (hjl : jl < 2 ^ 64) (hjr : jr < 2 ^ 64)
    (hc : usesCompact Crypto.Ripemd160.s[i]! Crypto.Ripemd160.sP[i + 3]! → jl < 2 ^ 35)
    (hclean : ¬ Dirty Crypto.Ripemd160.r[i]! →
      jl < 2 ^ 23 ∧ (Crypto.Ripemd160.r[i]! ≠ 15 → jl = 0))
    (hn2 : Crypto.Ripemd160.r[i]! ≠ 2 → Crypto.Ripemd160.r[i]! ≠ 14 → jl < 2 ^ 32)
    (hmsg : bits message =
      (pack (words Crypto.Ripemd160.r[i]!).toBitVec
        (words Crypto.Ripemd160.rP[i + 3]!).toBitVec) + StaggerRound.junk jl jr) :
    step i message (packCrypto l q) =
      packCrypto
        (cryptoStep (i / 16) Crypto.Ripemd160.s[i]!
          (words Crypto.Ripemd160.r[i]!) Crypto.Ripemd160.K[i / 16]! l)
        (cryptoStep (4 - (i + 3) / 16) Crypto.Ripemd160.sP[i + 3]!
          (words Crypto.Ripemd160.rP[i + 3]!) Crypto.Ripemd160.KP[(i + 3) / 16]! q) := by
  obtain ⟨hl0, hl, _, _⟩ := rotation_bounds ⟨i, by omega⟩
  obtain ⟨_, _, hr0, hr⟩ := rotation_bounds ⟨i + 3, by omega⟩
  obtain ⟨hmode, hleft, hright⟩ := mode_valid ⟨i, hi⟩
  by_cases ha : StaggerAdaptiveWord.usesAdaptive Crypto.Ripemd160.s[i]! Crypto.Ripemd160.sP[i + 3]!
  · have hg := adaptive_schedule ⟨i, hi⟩ ha
    have hj : (StaggerAdaptiveWord.gap Crypto.Ripemd160.s[i]! Crypto.Ripemd160.sP[i + 3]! = 68 ∨
        StaggerAdaptiveWord.gap Crypto.Ripemd160.s[i]! Crypto.Ripemd160.sP[i + 3]! = 69) ∧ jl < 2 ^ 32 ∨
        StaggerAdaptiveWord.gap Crypto.Ripemd160.s[i]! Crypto.Ripemd160.sP[i + 3]! = 87 ∧ jl < 2 ^ 23 := by
      rcases hg with ⟨hg, hn⟩ | ⟨hg, hn⟩
      · exact Or.inl ⟨hg, hn2 hn.1 hn.2⟩
      · exact Or.inr ⟨hg, (hclean hn).1⟩
    have h := StaggerAdaptiveWord.step_of_crypto (mode i) _ _ hmode ha
      (words Crypto.Ripemd160.r[i]!) (words Crypto.Ripemd160.rP[i + 3]!)
      Crypto.Ripemd160.K[i / 16]! Crypto.Ripemd160.KP[(i + 3) / 16]! l q message jl jr hjr hj hmsg
    simpa only [step, ha, if_pos, physicalKey, key, packed32, hleft, hright] using h
  · have h := StaggerWord.step_of_crypto_junk (mode i) _ _ hmode hl0 hl hr0 hr
      (words Crypto.Ripemd160.r[i]!) (words Crypto.Ripemd160.rP[i + 3]!)
      Crypto.Ripemd160.K[i / 16]! Crypto.Ripemd160.KP[(i + 3) / 16]! l q message jl jr hjl hjr hc hmsg
    simpa only [step, ha, if_neg, ite_false, physicalKey, key, packed32, hleft, hright] using h

/-- Both dispatch branches read the message word only through `normalize`, so a round step is
invariant under any junk `normalize` removes. -/
theorem step_congr (i : Nat) (message message' : UInt256) (q : Paired144WordRound.WordLane)
    (h : normalize (bits (StaggerWord.sum (mode i) q.a q.b q.c q.d message (physicalKey i)))
       = normalize (bits (StaggerWord.sum (mode i) q.a q.b q.c q.d message' (physicalKey i)))) :
    step i message q = step i message' q := by
  unfold step
  split_ifs
  · exact JD8Congr.adaptive_step_of_normalize _ _ _ message message' _ q h
  · exact JD8Congr.staggerWord_step_of_normalize _ _ _ message message' _ q h

/-- **The round step at the JD8 budget.**  `JunkBound` is now the single conjunct
`jl < 2 ^ 112 - 4`; `jr` is unbounded.  The proof reduces the junk case to the clean case
rather than reproving either branch. -/
theorem step_of_crypto (words : Nat → UInt32) (i : Nat) (hi : i < 77)
    (message : UInt256) (l q : CryptoLane)
    (hm : MessageWord message words i) :
    step i message (packCrypto l q) =
      packCrypto
        (cryptoStep (i / 16) Crypto.Ripemd160.s[i]!
          (words Crypto.Ripemd160.r[i]!) Crypto.Ripemd160.K[i / 16]! l)
        (cryptoStep (4 - (i + 3) / 16) Crypto.Ripemd160.sP[i + 3]!
          (words Crypto.Ripemd160.rP[i + 3]!) Crypto.Ripemd160.KP[(i + 3) / 16]! q) := by
  obtain ⟨jl, jr, ⟨hjl, -, -⟩, hmsg⟩ := hm
  have hmode := (mode_valid ⟨i, hi⟩).1
  have hmsg' : bits (word (pack (words Crypto.Ripemd160.r[i]!).toBitVec
        (words Crypto.Ripemd160.rP[i + 3]!).toBitVec))
      = pack (words Crypto.Ripemd160.r[i]!).toBitVec
          (words Crypto.Ripemd160.rP[i + 3]!).toBitVec := bits_word _
  have hnorm : normalize (bits (StaggerWord.sum (mode i)
        (packCrypto l q).a (packCrypto l q).b (packCrypto l q).c (packCrypto l q).d message
        (physicalKey i)))
      = normalize (bits (StaggerWord.sum (mode i)
        (packCrypto l q).a (packCrypto l q).b (packCrypto l q).c (packCrypto l q).d
        (word (pack (words Crypto.Ripemd160.r[i]!).toBitVec
          (words Crypto.Ripemd160.rP[i + 3]!).toBitVec))
        (physicalKey i))) := by
    have h1 := JD8Congr.sum_normalize_wide (mode i) hmode l q
      (words Crypto.Ripemd160.r[i]!) (words Crypto.Ripemd160.rP[i + 3]!)
      Crypto.Ripemd160.K[i / 16]! Crypto.Ripemd160.KP[(i + 3) / 16]! message jl jr hjl hmsg
    have h2 := (StaggerWord.sum_inputs (mode i) hmode l q
      (words Crypto.Ripemd160.r[i]!) (words Crypto.Ripemd160.rP[i + 3]!)
      Crypto.Ripemd160.K[i / 16]! Crypto.Ripemd160.KP[(i + 3) / 16]! _ hmsg').2
    exact h1.trans h2.symm
  refine (step_congr i message _ (packCrypto l q) hnorm).trans ?_
  refine step_of_crypto_narrow words i hi _ l q 0 0 (by norm_num) (by norm_num)
    (fun _ => by norm_num) (fun _ => ⟨by norm_num, fun _ => rfl⟩) (fun _ _ => by norm_num) ?_
  rw [bits_word, JD8Congr.add_junk_zero]

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
#print axioms step_of_crypto_narrow
#print axioms step_of_crypto
#print axioms fold_crypto
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerAlgorithm
