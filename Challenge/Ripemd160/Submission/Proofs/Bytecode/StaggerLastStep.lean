import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerAlgorithm
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired80Compression
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerLastStep
open EvmSemantics PairedLaneUInt256Bridge Paired80Core Paired80WordRound
open Paired80WordRotate Paired80WordBoolean Paired80Compression

/-- The final paired update retains spacer bits, which are no longer rotated. -/
def step (message : UInt256) (q : WordLane) : WordLane :=
  ⟨q.e, UInt256.add (wordRotate
      (StaggerWord.sum (StaggerAlgorithm.mode 76) q.a q.b q.c q.d message
        (StaggerAlgorithm.physicalKey 76)) Crypto.Ripemd160.s[76]! Crypto.Ripemd160.sP[79]!) q.e,
    q.b, wordShift q.c 22, q.d⟩

theorem low32_pair_mask (q : UInt256) : low32 (UInt256.land q pairWord) = low32 q := by
  apply UInt32.toNat_inj.mp
  change (low (bits (UInt256.land q pairWord))).toNat = (low (bits q)).toNat
  rw [bits_land, pairWord, bits_word, ← normalize_eq_and]
  simp only [normalize, low_pack]

theorem high32_pair_mask (q : UInt256) : high32 (UInt256.land q pairWord) = high32 q := by
  apply UInt32.eq_of_toBitVec_eq
  change (bits (UInt256.shiftRight (UInt256.land q pairWord) (UInt256.ofNat 80))).setWidth 32 =
    (bits (UInt256.shiftRight q (UInt256.ofNat 80))).setWidth 32
  rw [bits_shr _ 80 (by decide), bits_shr _ 80 (by decide),
    BitVec.setWidth_ushiftRight_eq_extractLsb, BitVec.setWidth_ushiftRight_eq_extractLsb,
    bits_land, pairWord, bits_word, ← normalize_eq_and]
  exact high_pack _ _

theorem project_left (message : UInt256) (q : WordLane) :
    unpackLeft (step message q) = unpackLeft (StaggerAlgorithm.step 76 message q) := by
  simp only [step, StaggerAlgorithm.step, StaggerWord.step, StaggerWord.t,
    unpackLeft, low32_pair_mask]

theorem project_right (message : UInt256) (q : WordLane) :
    unpackRight (step message q) = unpackRight (StaggerAlgorithm.step 76 message q) := by
  simp only [step, StaggerAlgorithm.step, StaggerWord.step, StaggerWord.t,
    unpackRight, high32_pair_mask]

#print axioms project_left
#print axioms project_right
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerLastStep
