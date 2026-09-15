import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedRowFrames

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000

namespace Challenge.Modexp.Submission.Proofs.Fast.CiosInverseGuard

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open WindowNibbleKernel WindowTwentyOneBinding



theorem inverse_ne_zero (low inverse : UInt256)
    (hinv : (low.toNat * inverse.toNat + 1) % 2 ^ 256 = 0) :
    inverse ≠ UInt256.ofNat 0 := by
  intro hz
  rw [hz] at hinv
  norm_num [Challenge.EvmProof.Word.word_toNat_ofNat] at hinv

theorem inverse_gt_one (inverse : UInt256)
    (hzero : inverse ≠ UInt256.ofNat 0) (hone : inverse ≠ UInt256.ofNat 1) :
    1 < inverse.toNat := by
  have hz : inverse.toNat ≠ 0 := by
    intro h
    apply hzero
    apply Challenge.EvmProof.Word.word_ext
    simpa [Challenge.EvmProof.Word.word_toNat_ofNat] using h
  have ho : inverse.toNat ≠ 1 := by
    intro h
    apply hone
    apply Challenge.EvmProof.Word.word_ext
    simpa [Challenge.EvmProof.Word.word_toNat_ofNat] using h
  omega






end Challenge.Modexp.Submission.Proofs.Fast.CiosInverseGuard
