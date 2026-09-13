import Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired80ScaledRotate
set_option warningAsError true
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired80Regression
open Paired80Core Paired80Product Paired80ScaledRotate

/-- A concrete carry witness forbids weakening the80-bit separation to64.
The rotation pair11/8 is an actual paired-round rotation pair. -/
theorem spacing64_carry_witness :
    let a := (0xffffffff#32)
    let b := (0xffffff#32)
    let p : BitVec 256 := b.setWidth 192 ++ a.setWidth 64
    let scaled := BitVec.ofNat 256 7 * (a.setWidth 256) + p
    ((scaled * factor) >>> 24).extractLsb' 64 32 ≠ b.rotateLeft 8 := by
  decide

theorem spacing80_same_pair_correct (a b : BitVec 32) :
    high ((scaleLow (pack a b) 3 * factor) >>> 24) = b.rotateLeft 8 := by
  exact high_scaleLow a b 11 8 (by decide) (by decide) (by decide) (by decide)

#print axioms spacing64_carry_witness
#print axioms spacing80_same_pair_correct
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired80Regression
