import Challenge.Blake2f.ProofSupport.Word
set_option warningAsError true

/-!
# Reusable pure model of BLAKE2f rounds

This module names the eight-quarter-round transition and iteration used by the
pinned crypto specification. Candidate proofs can maintain this model without
depending on the bundled reference's memory layout or control flow.
-/

namespace Challenge.Blake2f.ProofSupport.Algorithm

open EvmSemantics

/-- The four lanes touched by one BLAKE2b quarter-round. Keeping this view
separate from any concrete memory layout makes the arithmetic bridge reusable
by candidate implementations. -/
structure Lanes (α : Type) where
  a : α
  b : α
  c : α
  d : α
  deriving DecidableEq

def Lanes.embed (v : Lanes UInt64) : Lanes UInt256 :=
  ⟨Word.ofUInt64 v.a, Word.ofUInt64 v.b, Word.ofUInt64 v.c,
    Word.ofUInt64 v.d⟩

/-- The masked EVM shift/or idiom used for a 64-bit right rotation. -/
def rotrWord (x : UInt256) (n : Nat) : UInt256 :=
  Word.mask64 (UInt256.shiftRight x (UInt256.ofNat n) |||
    UInt256.shiftLeft x (UInt256.ofNat (64 - n)))

/-- Pure four-lane form of the pinned `Crypto.Blake2f.mixG` arithmetic. -/
def mixLanes64 (v : Lanes UInt64) (x y : UInt64) : Lanes UInt64 :=
  let a := v.a + v.b + x
  let d := Crypto.Blake2f.rotr64 (v.d ^^^ a) 32
  let c := v.c + d
  let b := Crypto.Blake2f.rotr64 (v.b ^^^ c) 24
  let a := a + b + y
  let d := Crypto.Blake2f.rotr64 (d ^^^ a) 16
  let c := c + d
  let b := Crypto.Blake2f.rotr64 (b ^^^ c) 63
  ⟨a, b, c, d⟩

/-- The same quarter-round expressed with the exact 256-bit operations used by
proof-friendly EVM bytecode. -/
def mixLanesEVM (v : Lanes UInt256) (x y : UInt256) : Lanes UInt256 :=
  let a := Word.mask64 (v.a + v.b + x)
  let d := rotrWord (v.d ^^^ a) 32
  let c := Word.mask64 (v.c + d)
  let b := rotrWord (v.b ^^^ c) 24
  let a := Word.mask64 (a + b + y)
  let d := rotrWord (d ^^^ a) 16
  let c := Word.mask64 (c + d)
  let b := rotrWord (b ^^^ c) 63
  ⟨a, b, c, d⟩

@[simp] theorem rotrWord_ofUInt64 (x : UInt64) (n : Nat)
    (hn0 : 0 < n) (hn : n < 64) :
    rotrWord (Word.ofUInt64 x) n =
      Word.ofUInt64 (Crypto.Blake2f.rotr64 x (UInt64.ofNat n)) := by
  exact Word.evm_rotr64 x n hn0 hn

/-- The EVM quarter-round is exactly the 64-bit BLAKE2b quarter-round whenever
its six inputs are embedded algorithm words. -/
theorem mixLanesEVM_embed (v : Lanes UInt64) (x y : UInt64) :
    mixLanesEVM v.embed (Word.ofUInt64 x) (Word.ofUInt64 y) =
      (mixLanes64 v x y).embed := by
  cases v with
  | mk a b c d =>
    simp only [mixLanesEVM, mixLanes64, Lanes.embed, Word.mask64_add3]
    rw [← Word.ofUInt64_xor, rotrWord_ofUInt64 _ 32 (by omega) (by omega)]
    rw [Word.mask64_add]
    rw [← Word.ofUInt64_xor, rotrWord_ofUInt64 _ 24 (by omega) (by omega)]
    rw [Word.mask64_add3]
    rw [← Word.ofUInt64_xor, rotrWord_ofUInt64 _ 16 (by omega) (by omega)]
    rw [Word.mask64_add]
    rw [← Word.ofUInt64_xor, rotrWord_ofUInt64 _ 63 (by omega) (by omega)]
    have h32 : UInt64.ofNat 32 = 32 := by decide
    have h24 : UInt64.ofNat 24 = 24 := by decide
    have h16 : UInt64.ofNat 16 = 16 := by decide
    have h63 : UInt64.ofNat 63 = 63 := by decide
    simp only [h32, h24, h16, h63]

/-- Project four algorithm lanes from an array using the same zero-defaulting
indexing convention as the pinned crypto implementation. -/
def lanesAt (v : Array UInt64) (a b c d : Nat) : Lanes UInt64 :=
  ⟨v[a]!, v[b]!, v[c]!, v[d]!⟩

/-- The pinned array implementation of `mixG`, viewed at its four distinct
in-bounds lanes, is the reusable pure four-lane transition above. -/
theorem lanesAt_crypto_mixG (v : Array UInt64) (a b c d : Nat) (x y : UInt64)
    (ha : a < v.size) (hb : b < v.size) (hc : c < v.size) (hd : d < v.size)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    lanesAt (Crypto.Blake2f.mixG v a b c d x y) a b c d =
      mixLanes64 (lanesAt v a b c d) x y := by
  simp [Crypto.Blake2f.mixG, lanesAt, mixLanes64,
    Array.set!_eq_setIfInBounds, ha, hb, hc, hd,
    hab, hac, had, hbc, hbd, hcd,
    Ne.symm hab, Ne.symm hac, Ne.symm had, Ne.symm hbc, Ne.symm hbd,
    Ne.symm hcd]

/-- One complete BLAKE2b mixing round, including columns then diagonals. -/
def roundStep (message : Array UInt64) (v : Array UInt64) (round : Nat) :
    Array UInt64 :=
  let sigma := Crypto.Blake2f.SIGMA[round % 10]!
  let v := Crypto.Blake2f.mixG v 0 4 8 12 message[sigma[0]!]! message[sigma[1]!]!
  let v := Crypto.Blake2f.mixG v 1 5 9 13 message[sigma[2]!]! message[sigma[3]!]!
  let v := Crypto.Blake2f.mixG v 2 6 10 14 message[sigma[4]!]! message[sigma[5]!]!
  let v := Crypto.Blake2f.mixG v 3 7 11 15 message[sigma[6]!]! message[sigma[7]!]!
  let v := Crypto.Blake2f.mixG v 0 5 10 15 message[sigma[8]!]! message[sigma[9]!]!
  let v := Crypto.Blake2f.mixG v 1 6 11 12 message[sigma[10]!]! message[sigma[11]!]!
  let v := Crypto.Blake2f.mixG v 2 7 8 13 message[sigma[12]!]! message[sigma[13]!]!
  Crypto.Blake2f.mixG v 3 4 9 14 message[sigma[14]!]! message[sigma[15]!]!

/-- Iterate the mathematical round transition in execution order. -/
def rounds (message : Array UInt64) : Nat → Array UInt64 → Array UInt64
  | 0, v => v
  | count + 1, v => roundStep message (rounds message count v) count

@[simp] theorem rounds_zero (message v) : rounds message 0 v = v := rfl

theorem rounds_succ (message v) (count : Nat) :
    rounds message (count + 1) v =
      roundStep message (rounds message count v) count := rfl

end Challenge.Blake2f.ProofSupport.Algorithm
