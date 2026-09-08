import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedCompression

set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

/-!
# The output combine: where packing ends

`Compression.combine` cross-permutes the two lines:

    h0 := h.h1 + left.c + right.d
    h1 := h.h2 + left.d + right.e
    h2 := h.h3 + left.e + right.a
    h3 := h.h4 + left.a + right.b
    h4 := h.h0 + left.b + right.c

Every output slot takes its left value from one register and its right value
from a DIFFERENT one — `h0` wants `left.c` and `right.d`.  The two lanes are
never read from the same packed word, so this is the point at which the packed
representation has to be taken apart.  It comes apart in five extractions, not
eighty, which is the whole economic argument for packing.

Each field is emitted as `DUP ra ; DUP rb ; PUSH 0x40 ; SHR ; ADD ; MLOAD hj ;
ADD ; AND maskL`, so `packedCombine` below is written in that shape — a
`shiftRight` by 64 for the right lane and a trailing `mask32` — rather than in
terms of `lane0N` / `lane1N`.  That keeps it transportable to the trace layer
without a second adapter.

## `RegsOk` is NOT a premise here, and that is deliberate

The natural guess is that the extractions need `Clean` registers.  They do not.
The trailing `mask32` truncates to 32 bits by itself, so junk in bits 32..63 of
the left source, and junk above bit 95 of the right source, are both discarded
rather than merely absent.  I could not construct an input that violates a
`RegsOk` premise here and changes the result, so stating one would be an inert
hypothesis of the kind that has already cost this team three defects.

`RegsOk` IS load-bearing one level up: `packedCompress_embed` needs it, because
the eighty-round lift needs it.  It is required for the fold, not for the
combine.

STATUS: WRITTEN, NOT ELABORATED.  No admitted goals and no scaffolding gaps;
the file contains zero occurrences of the placeholder token, so a grep and this
claim agree.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedCombine

open EvmSemantics
open Compression
open Challenge.EvmProof.Word
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedLaneMask
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedStepCorrected
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedCompression

/-! ## 1.  Extraction helpers -/

private theorem lane0_toNat {P : UInt256} {l : UInt32}
    (h : UInt32.ofNat (lane0N P.toNat) = l) : lane0N P.toNat = l.toNat := by
  have hlt : lane0N P.toNat < 2 ^ 32 := windowN_lt _ _
  rw [← h, UInt32.toNat_ofNat', Nat.mod_eq_of_lt hlt]

private theorem lane1_toNat {P : UInt256} {l : UInt32}
    (h : UInt32.ofNat (lane1N P.toNat) = l) : lane1N P.toNat = l.toNat := by
  have hlt : lane1N P.toNat < 2 ^ 32 := windowN_lt _ _
  rw [← h, UInt32.toNat_ofNat', Nat.mod_eq_of_lt hlt]

private theorem mask32_toNat_mod (x : UInt256) :
    (mask32 x).toNat = x.toNat % 2 ^ 32 := by
  rw [mask32_toNat, show (0xffffffff : Nat) = 2 ^ 32 - 1 by norm_num,
    Nat.and_two_pow_sub_one_eq_mod]

/-- The emitted `SHR 64` is exactly lane-1 extraction, once truncated. -/
private theorem shr64_lane1 (Q : UInt256) :
    (UInt256.shiftRight Q (UInt256.ofNat 64)).toNat % 2 ^ 32
      = lane1N Q.toNat := by
  rw [Challenge.EvmProof.Word.shiftRight_toNat _
    (by norm_num : (64 : Nat) < 256)]
  rfl

private theorem add_mod32 (A B : UInt256) :
    (A + B).toNat % 2 ^ 32 = (A.toNat + B.toNat) % 2 ^ 32 := by
  rw [word_toNat_add]
  exact Nat.mod_mod_of_dvd _ (by norm_num : (2 : Nat) ^ 32 ∣ 2 ^ 256)

private theorem add3_mod32 (A B C : UInt256) :
    (A + B + C).toNat % 2 ^ 32
      = (A.toNat + B.toNat + C.toNat) % 2 ^ 32 := by
  rw [add_mod32, Nat.add_mod, add_mod32, ← Nat.add_mod]

/-- One output slot.  `hj` is the incoming hash word, `P` supplies the left
line from lane 0 and `Q` the right line from lane 1. -/
private theorem combine_field (hj : UInt32) (P Q : UInt256) (l m : UInt32)
    (hP : UInt32.ofNat (lane0N P.toNat) = l)
    (hQ : UInt32.ofNat (lane1N Q.toNat) = m) :
    mask32 (ofUInt32 hj + P + UInt256.shiftRight Q (UInt256.ofNat 64))
      = ofUInt32 (hj + l + m) := by
  have hPn : P.toNat % 2 ^ 32 = l.toNat := by
    rw [← lane0_toNat hP, lane0N_eq_mod]
  have hQn : (UInt256.shiftRight Q (UInt256.ofNat 64)).toNat % 2 ^ 32
      = m.toNat := by
    rw [shr64_lane1 Q, lane1_toNat hQ]
  apply word_ext
  rw [ofUInt32_toNat (hj + l + m), mask32_toNat_mod, add3_mod32,
    ofUInt32_toNat hj, UInt32.toNat_add, UInt32.toNat_add]
  omega

/-! ## 2.  The packed combine -/

/-- The five final stores, in the shape the bytecode emits them. -/
def packedCombine (h : EvmHashState) (g : Regs) : EvmHashState :=
  { h0 := mask32 (h.h1 + g.c + UInt256.shiftRight g.d (UInt256.ofNat 64))
    h1 := mask32 (h.h2 + g.d + UInt256.shiftRight g.e (UInt256.ofNat 64))
    h2 := mask32 (h.h3 + g.e + UInt256.shiftRight g.a (UInt256.ofNat 64))
    h3 := mask32 (h.h4 + g.a + UInt256.shiftRight g.b (UInt256.ofNat 64))
    h4 := mask32 (h.h0 + g.b + UInt256.shiftRight g.c (UInt256.ofNat 64)) }

/-- **The packed combine is the specified cross-permutation.**  No `RegsOk`:
the trailing `mask32` discharges the truncation itself. -/
theorem packedCombine_embed (h : HashState) (g : Regs) (yl yr : Working)
    (hrep : RegsRepresents g yl yr) :
    packedCombine (embedHash h) g = embedHash (Compression.combine h yl yr) := by
  obtain ⟨ha, hb, hc, hd, he⟩ := hrep
  have e0 := combine_field h.h1 g.c g.d yl.c yr.d hc.1 hd.2
  have e1 := combine_field h.h2 g.d g.e yl.d yr.e hd.1 he.2
  have e2 := combine_field h.h3 g.e g.a yl.e yr.a he.1 ha.2
  have e3 := combine_field h.h4 g.a g.b yl.a yr.b ha.1 hb.2
  have e4 := combine_field h.h0 g.b g.c yl.b yr.c hb.1 hc.2
  simp only [packedCombine, embedHash, Compression.combine, e0, e1, e2, e3, e4]

/-! ## 3.  The full packed block compression -/

/-- **Eighty rounds plus the combine equal the pinned `compressModel`.**
`RegsOk` appears here and not in the combine because it is the fold's
induction hypothesis.

From here the existing chain finishes the job: `compressModel` is already tied
to the pinned block by `CompressionCorrect.compressModel_eq_compressBlock` and
`StackCompression.compress_eq_specBlock`.  Nothing about padding, absorb, or
the hash specification is restated. -/
theorem packedCompress_embed (word : Nat → UInt32) (X K : Nat → UInt256)
    (hX : ∀ i, i < 80 → WordOk (X i) (word Crypto.Ripemd160.r[i]!)
      (word Crypto.Ripemd160.rP[i]!))
    (hK : ∀ i, i < 80 → ConstOk (K i) Crypto.Ripemd160.K[i / 16]!
      Crypto.Ripemd160.KP[i / 16]!)
    (h : HashState) (g0 : Regs)
    (hrep0 : RegsRepresents g0 (CompressionCorrect.workingOfHash h)
      (CompressionCorrect.workingOfHash h))
    (hregs0 : RegsOk g0) :
    packedCombine (embedHash h) (packedRounds X K 80 g0)
      = embedHash (CompressionCorrect.compressModel word h) := by
  have hlift := packedRounds_represents_80 word X K hX hK g0
    (CompressionCorrect.workingOfHash h) (CompressionCorrect.workingOfHash h)
    hrep0 hregs0
  rw [CompressionCorrect.compressModel]
  exact packedCombine_embed h (packedRounds X K 80 g0) _ _ hlift

#print axioms combine_field
#print axioms packedCombine_embed
#print axioms packedCompress_embed

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedCombine
