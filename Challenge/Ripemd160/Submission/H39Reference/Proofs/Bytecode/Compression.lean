import Challenge.Ripemd160.Submission.H39Reference.Proofs.Bytecode.Word
set_option warningAsError true
/-!
# RIPEMD-160 round model

This file separates the mathematical five-register transition from symbolic
execution.  It proves that the exact masked EVM-word expressions used by the
reference `round` helper implement one RIPEMD-160 round for either line.
-/

namespace Challenge.Ripemd160.Submission.H39Reference.Proofs.Bytecode.Compression

open EvmSemantics
open Challenge.EvmProof.Word

/-- The five RIPEMD-160 working registers in `a` through `e` order. -/
structure Working where
  a : UInt32
  b : UInt32
  c : UInt32
  d : UInt32
  e : UInt32
deriving DecidableEq

/-- One mathematical round, parameterized so it serves both parallel lines. -/
def round (x : Working) (j : Nat) (word : UInt32) (rotation : Nat)
    (constant : UInt32) : Working :=
  let t := x.a + Crypto.Ripemd160.f j x.b x.c x.d + word + constant
  let t := Crypto.Ripemd160.rotl32 t rotation + x.e
  { a := x.e
    b := t
    c := x.b
    d := Crypto.Ripemd160.rotl32 x.c 10
    e := x.d }

structure EvmWorking where
  a : UInt256
  b : UInt256
  c : UInt256
  d : UInt256
  e : UInt256
deriving DecidableEq

def embed (x : Working) : EvmWorking :=
  { a := ofUInt32 x.a, b := ofUInt32 x.b, c := ofUInt32 x.c
    d := ofUInt32 x.d, e := ofUInt32 x.e }

/-- Exact EVM expressions in the Yul `round` helper, before memory stores. -/
def evmRound (x : EvmWorking) (j : Nat) (word : UInt256) (rotation : Nat)
    (constant : UInt256) : EvmWorking :=
  let t := mask32 (((x.a + Word.evmF j x.b x.c x.d) + word) + constant)
  let t := mask32 (Word.evmRotl32 t rotation + x.e)
  { a := x.e
    b := t
    c := x.b
    d := Word.evmRotl32 x.c 10
    e := x.d }

/-- One reference EVM round is exactly one specification round. -/
theorem evmRound_embed (x : Working) (j : Nat) (word constant : UInt32)
    (rotation : Nat) (hj : j < 5) (hr0 : 0 < rotation)
    (hr : rotation < 32) :
    evmRound (embed x) j (ofUInt32 word) rotation (ofUInt32 constant) =
      embed (round x j word rotation constant) := by
  unfold evmRound embed round
  simp only [Word.evmF_ofUInt32 j x.b x.c x.d hj,
    mask32_eq_ofUInt32, toUInt32_add, toUInt32_ofUInt32,
    Word.evmRotl32_ofUInt32 _ rotation hr0 hr,
    Word.evmRotl32_ofUInt32 x.c 10 (by decide) (by decide)]

/-- Five-word chaining state, named to make the final cross-permutation
auditable without array-index side conditions. -/
structure HashState where
  h0 : UInt32
  h1 : UInt32
  h2 : UInt32
  h3 : UInt32
  h4 : UInt32
deriving DecidableEq

structure EvmHashState where
  h0 : UInt256
  h1 : UInt256
  h2 : UInt256
  h3 : UInt256
  h4 : UInt256
deriving DecidableEq

def embedHash (h : HashState) : EvmHashState :=
  { h0 := ofUInt32 h.h0, h1 := ofUInt32 h.h1, h2 := ofUInt32 h.h2
    h3 := ofUInt32 h.h3, h4 := ofUInt32 h.h4 }

/-- RIPEMD-160's final cross-combination of the left and right lines. -/
def combine (h : HashState) (left right : Working) : HashState :=
  { h0 := h.h1 + left.c + right.d
    h1 := h.h2 + left.d + right.e
    h2 := h.h3 + left.e + right.a
    h3 := h.h4 + left.a + right.b
    h4 := h.h0 + left.b + right.c }

/-- The exact masked EVM additions used by `compress`'s five final stores. -/
def evmCombine (h : EvmHashState) (left right : EvmWorking) : EvmHashState :=
  { h0 := mask32 (h.h1 + left.c + right.d)
    h1 := mask32 (h.h2 + left.d + right.e)
    h2 := mask32 (h.h3 + left.e + right.a)
    h3 := mask32 (h.h4 + left.a + right.b)
    h4 := mask32 (h.h0 + left.b + right.c) }

/-- The reference's five final EVM stores implement the specified
cross-permutation, including 32-bit modular addition. -/
theorem evmCombine_embed (h : HashState) (left right : Working) :
    evmCombine (embedHash h) (embed left) (embed right) =
      embedHash (combine h left right) := by
  simp [evmCombine, embedHash, embed, combine, mask32_eq_ofUInt32]

end Challenge.Ripemd160.Submission.H39Reference.Proofs.Bytecode.Compression
