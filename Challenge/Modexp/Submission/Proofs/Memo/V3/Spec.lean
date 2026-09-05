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

theorem msize_eq {input : ByteArray} (hvalid : ValidInput input) (hm : WordsMatch checks input) :
    modulusSize input = 0 := by
  · show Precompile.bytesToNatPadded input 64 32 = 0
    rw [Cover.header_of_low input target 64 hvalid.2.2.2 (by decide +kernel)
      (Cover.bytesToNatPadded_eq_of_cover input target checks (64 + 30) 2 hm checks_ok (by decide +kernel))]
    decide +kernel

theorem spec_eq {input : ByteArray} (hvalid : ValidInput input) (hm : WordsMatch checks input) :
    spec input = ByteArray.empty := by
  have hmm := msize_eq hvalid hm
  simp only [spec, hmm]
  rw [if_pos trivial]

end Challenge.Modexp.Submission.Proofs.Memo.V3.Spec
