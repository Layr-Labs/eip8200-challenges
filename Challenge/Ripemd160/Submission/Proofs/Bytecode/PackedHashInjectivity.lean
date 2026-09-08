import Challenge.Ripemd160.Submission.Proofs.Bytecode.Compression

set_option warningAsError true
set_option autoImplicit false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedHashInjectivity

open Challenge.EvmProof

/-- Decode the five canonical chaining words without inspecting proof witnesses. -/
def decode (h : Compression.EvmHashState) : Compression.HashState :=
  { h0 := Word.toUInt32 h.h0
    h1 := Word.toUInt32 h.h1
    h2 := Word.toUInt32 h.h2
    h3 := Word.toUInt32 h.h3
    h4 := Word.toUInt32 h.h4 }

theorem decode_embed (h : Compression.HashState) :
    decode (Compression.embedHash h) = h := by
  cases h
  simp [decode, Compression.embedHash, Word.toUInt32_ofUInt32]

/-- An incoming memory hash determines a unique mathematical chaining state. -/
theorem embedHash_injective : Function.Injective Compression.embedHash := by
  intro a b hab
  have h := congrArg decode hab
  simpa only [decode_embed] using h

#print axioms embedHash_injective

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedHashInjectivity
