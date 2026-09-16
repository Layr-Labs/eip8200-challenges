import Challenge.EvmProof.Word
import Mathlib.Data.Nat.Bitwise

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedLengthLookup
open EvmSemantics Challenge.EvmProof

def lookupNat (n : Nat) : Nat := (6308489473 >>> (n &&& 24)) &&& 1016

private theorem small_cases : ∀ n : Fin 1024,
    lookupNat n.val = n.val ↔ n.val = 256 ∨ n.val = 376 ∨ n.val = 1000 := by
  decide

theorem lookupNat_eq_iff (n : Nat) :
    lookupNat n = n ↔ n = 256 ∨ n = 376 ∨ n = 1000 := by
  by_cases hn : n < 1024
  · exact small_cases ⟨n, hn⟩
  · have hb : lookupNat n ≤ 1016 := Nat.and_le_right
    constructor
    · intro h; omega
    · intro h; omega

def lookup (x : UInt256) : UInt256 :=
  UInt256.land (UInt256.ofNat 1016)
    (UInt256.shiftRight (UInt256.ofNat 6308489473)
      (UInt256.land (UInt256.ofNat 24) x))

theorem lookup_toNat (x : UInt256) : (lookup x).toNat = lookupNat x.toNat := by
  let index := UInt256.land (UInt256.ofNat 24) x
  have hi : index.toNat = x.toNat &&& 24 := by
    rw [show index = UInt256.land (UInt256.ofNat 24) x by rfl, Word.word_toNat_land]
    change 24 &&& x.toNat = x.toNat &&& 24
    exact Nat.and_comm _ _
  have hs : index.toNat < 256 := by
    rw [hi]
    have h : x.toNat &&& 24 ≤ 24 := Nat.and_le_right
    omega
  have hsr := Word.shiftRight_toNat (UInt256.ofNat 6308489473) hs
  rw [← Word.word_eq_ofNat_toNat index] at hsr
  unfold lookup
  rw [Word.word_toNat_land, hsr]
  change 1016 &&& (6308489473 >>> index.toNat) = lookupNat x.toNat
  rw [hi]
  exact Nat.and_comm _ _

theorem lookup_eq_iff (x : UInt256) :
    lookup x = x ↔ x = UInt256.ofNat 284 ∨ x = UInt256.ofNat 376 ∨ x = UInt256.ofNat 1000 := by
  constructor
  · intro h
    have hn := congrArg UInt256.toNat h
    rw [lookup_toNat, lookupNat_eq_iff] at hn
    rcases hn with h | h | h
    · left; apply Word.word_ext; exact h
    · right; left; apply Word.word_ext; exact h
    · right; right; apply Word.word_ext; exact h
  · rintro (rfl | rfl | rfl) <;> decide

theorem flag (x : UInt256) :
    UInt256.eq x (lookup x) =
      UInt256.lor
        (UInt256.lor (UInt256.eq (UInt256.ofNat 1000) x)
          (UInt256.eq (UInt256.ofNat 376) x))
        (UInt256.eq (UInt256.ofNat 284) x) := by
  by_cases h256 : x = UInt256.ofNat 284
  · subst x; decide
  by_cases h376 : x = UInt256.ofNat 376
  · subst x; decide
  by_cases h1000 : x = UInt256.ofNat 1000
  · subst x; decide
  have hlookup : x.toNat ≠ (lookup x).toNat := by
    intro h
    have he : lookup x = x := Word.word_ext h.symm
    rcases (lookup_eq_iff x).mp he with h | h | h
    · exact h256 h
    · exact h376 h
    · exact h1000 h
  have h256n : 256 ≠ x.toNat := by
    intro h; apply h256; apply Word.word_ext; exact h.symm
  have h376n : 376 ≠ x.toNat := by
    intro h; apply h376; apply Word.word_ext; exact h.symm
  have h1000n : 1000 ≠ x.toNat := by
    intro h; apply h1000; apply Word.word_ext; exact h.symm
  simp only [UInt256.eq, show (UInt256.ofNat 284).toNat = 256 by decide,
    show (UInt256.ofNat 376).toNat = 376 by decide,
    show (UInt256.ofNat 1000).toNat = 1000 by decide,
    if_neg hlookup, if_neg h256n, if_neg h376n, if_neg h1000n]
  decide

#print axioms flag
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedLengthLookup
