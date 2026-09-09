import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedDerivedStartup
import Init.Data.BitVec.Bitblast

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-!
# Lane duplication by multiplication at 128-bit spacing

`PairedLaneProduct` proves that multiplying a 32-lane-normalized word by
`2^32 + 1` copies its low lane.  The startup block spaces its two lanes 128
bits apart, so the same identity is needed for the factor `2^128 + 1`.  The
hypothesis is exactly the normalization fact the startup block already
carries for each of its five memory words: masking with `0xffffffff` is the
identity on them.  Nothing here mentions the artifact.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedSpreadProduct

open EvmSemantics
open Challenge.EvmProof
open PairedDerivedStartup

/-- `2^128 + 1`, pushed once per compression block. -/
def spreadFactor : UInt256 :=
  UInt256.ofNat 0x100000000000000000000000000000001

private def bv (value : UInt256) : BitVec 256 := BitVec.ofFin value.val

private theorem bv_injective : Function.Injective bv := by
  intro a b h
  cases a with
  | mk a =>
    cases b with
    | mk b =>
      cases h
      rfl

private theorem bv_ofNat (value : Nat) : bv (UInt256.ofNat value) = BitVec.ofNat 256 value := rfl

private theorem bv_land (a b : UInt256) : bv (UInt256.land a b) = bv a &&& bv b := by
  apply BitVec.eq_of_toNat_eq
  change (UInt256.land a b).toNat = _
  rw [Challenge.EvmProof.Word.word_toNat_land, BitVec.toNat_and]
  rfl

private theorem bv_lor (a b : UInt256) : bv (UInt256.lor a b) = bv a ||| bv b := by
  apply BitVec.eq_of_toNat_eq
  change (UInt256.lor a b).toNat = _
  rw [Challenge.EvmProof.Word.word_toNat_lor, BitVec.toNat_or]
  rfl

private theorem bv_mul (a b : UInt256) : bv (UInt256.mul a b) = bv a * bv b := by
  apply BitVec.eq_of_toNat_eq
  change (UInt256.mul a b).toNat = _
  rw [BitVec.toNat_mul]
  change (a.val * b.val).val = (a.toNat * b.toNat) % 2 ^ 256
  rw [Fin.val_mul]
  rfl

private theorem bv_shl128 (a : UInt256) :
    bv (UInt256.shiftLeft a (UInt256.ofNat 128)) = bv a <<< 128 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft]
  show (UInt256.shiftLeft a (UInt256.ofNat 128)).toNat = _
  have h128 : (UInt256.ofNat 128).toNat = 128 := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat]
    exact Nat.mod_eq_of_lt (by norm_num)
  unfold UInt256.shiftLeft
  rw [h128, if_neg (by omega), Challenge.EvmProof.Word.word_toNat_ofNat,
    show UInt256.size = 2 ^ 256 by rfl, Nat.mod_mod]
  rfl

private theorem and_exchange (a b c d : BitVec 256) :
    (a &&& b) &&& (c &&& d) = (a &&& c) &&& (b &&& d) := by
  rw [BitVec.and_assoc a b (c &&& d), ← BitVec.and_assoc b c d, BitVec.and_comm b c,
    BitVec.and_assoc c b d, ← BitVec.and_assoc a c (b &&& d)]

private theorem lane_mask_disjoint :
    (BitVec.ofNat 256 0xffffffff <<< 128) &&& BitVec.ofNat 256 0xffffffff = 0#256 := by
  decide

private theorem masked_shift_disjoint (x : BitVec 256) :
    ((x &&& BitVec.ofNat 256 0xffffffff) <<< 128) &&& (x &&& BitVec.ofNat 256 0xffffffff)
      = 0#256 := by
  rw [BitVec.shiftLeft_and_distrib]
  calc
    ((x <<< 128) &&& (BitVec.ofNat 256 0xffffffff <<< 128)) &&&
        (x &&& BitVec.ofNat 256 0xffffffff)
        = ((x <<< 128) &&& x) &&&
          ((BitVec.ofNat 256 0xffffffff <<< 128) &&& BitVec.ofNat 256 0xffffffff) :=
      and_exchange _ _ _ _
    _ = 0#256 := by
      rw [lane_mask_disjoint]
      exact BitVec.and_zero

private theorem factor_copies (x : BitVec 256) :
    BitVec.ofNat 256 0x100000000000000000000000000000001 *
        (x &&& BitVec.ofNat 256 0xffffffff) =
      ((x &&& BitVec.ofNat 256 0xffffffff) <<< 128) ||| (x &&& BitVec.ofNat 256 0xffffffff) := by
  rw [BitVec.mul_comm,
    show BitVec.ofNat 256 0x100000000000000000000000000000001
        = BitVec.twoPow 256 128 + 1#256 by decide,
    BitVec.mul_add, BitVec.mul_twoPow_eq_shiftLeft, BitVec.mul_one]
  exact BitVec.add_eq_or_of_and_eq_zero _ _ (masked_shift_disjoint x)

/-- Multiplying a `0xffffffff`-normalized word by `2^128 + 1` is the same word
copied into bits `[128,160)` and left in bits `[0,32)`. -/
theorem spread_mul (value : UInt256)
    (hmask : UInt256.land lowerWord value = value) :
    UInt256.mul spreadFactor value =
      UInt256.lor (UInt256.shiftLeft value (UInt256.ofNat 128)) value := by
  have hb : bv value = bv value &&& BitVec.ofNat 256 0xffffffff := by
    conv_lhs => rw [← hmask]
    rw [bv_land]
    exact BitVec.and_comm _ _
  apply bv_injective
  rw [bv_mul, bv_lor, bv_shl128,
    show bv spreadFactor = BitVec.ofNat 256 0x100000000000000000000000000000001 from rfl]
  conv_lhs => rw [hb]
  conv_rhs => rw [hb]
  exact factor_copies (bv value)

#print axioms spread_mul

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedSpreadProduct
