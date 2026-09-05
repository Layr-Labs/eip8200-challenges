import Challenge.Modexp.Submission.Proofs.Memo.V3.Data
import Challenge.Modexp.Submission.Proofs.Memo.Cover
import Challenge.Modexp.Submission.Proofs.Algorithm
import Mathlib.Tactic.ReduceModChar

set_option warningAsError true
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000

namespace Challenge.Modexp.Submission.Proofs.Memo.V3.Spec

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp
open Challenge.Modexp.Submission.Proofs.Memo
open Logic Data

theorem checks_ok : Cover.checksOk target checks = true := by
  decide +kernel

theorem sizes {input : ByteArray} (hvalid : ValidInput input) (hm : WordsMatch checks input) :
    baseSize input = 1 ∧ exponentSize input = 1 ∧ modulusSize input = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · show Precompile.bytesToNatPadded input 0 32 = 1
    rw [Cover.header_of_low input target 0 hvalid.2.1 (by decide +kernel)
      (Cover.bytesToNatPadded_eq_of_cover input target checks (0 + 30) 2 hm checks_ok (by decide +kernel))]
    decide +kernel
  · show Precompile.bytesToNatPadded input 32 32 = 1
    rw [Cover.header_of_low input target 32 hvalid.2.2.1 (by decide +kernel)
      (Cover.bytesToNatPadded_eq_of_cover input target checks (32 + 30) 2 hm checks_ok (by decide +kernel))]
    decide +kernel
  · show Precompile.bytesToNatPadded input 64 32 = 0
    rw [Cover.header_of_low input target 64 hvalid.2.2.2 (by decide +kernel)
      (Cover.bytesToNatPadded_eq_of_cover input target checks (64 + 30) 2 hm checks_ok (by decide +kernel))]
    decide +kernel

theorem spec_eq {input : ByteArray} (hvalid : ValidInput input) (hm : WordsMatch checks input) :
    spec input = ByteArray.empty := by
  obtain ⟨hb, he, hmm⟩ := sizes hvalid hm
  simp only [spec, hb, he, hmm]
  rw [if_pos trivial]

end Challenge.Modexp.Submission.Proofs.Memo.V3.Spec
