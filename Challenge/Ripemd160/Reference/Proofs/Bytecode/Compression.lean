import Challenge.Ripemd160.Reference.Proofs.Bytecode.Word
set_option warningAsError true
/-!
# RIPEMD-160 round model

This file separates the mathematical five-register transition from symbolic
execution.  It proves that the exact masked EVM-word expressions used by the
reference `round` helper implement one RIPEMD-160 round for either line.
-/

namespace Challenge.Ripemd160.Reference.Proofs.Bytecode.Compression

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

end Challenge.Ripemd160.Reference.Proofs.Bytecode.Compression
