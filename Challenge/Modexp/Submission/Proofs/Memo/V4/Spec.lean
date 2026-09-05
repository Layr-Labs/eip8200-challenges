import Challenge.Modexp.Submission.Proofs.Memo.V4.Data
import Challenge.Modexp.Submission.Proofs.Memo.Cover
import Challenge.Modexp.Submission.Proofs.Algorithm
import Mathlib.Tactic.ReduceModChar

set_option warningAsError true
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000

namespace Challenge.Modexp.Submission.Proofs.Memo.V4.Spec

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp
open Challenge.Modexp.Submission.Proofs.Memo
open Logic Data

theorem checks_ok : Cover.checksOk target checks = true := by
  decide +kernel

theorem sizes {input : ByteArray} (hvalid : ValidInput input) (hm : WordsMatch checks input) :
    baseSize input = 1 ∧ exponentSize input = 1 ∧ modulusSize input = 12 := by
  refine ⟨?_, ?_, ?_⟩
  · show Precompile.bytesToNatPadded input 0 32 = 1
    rw [Cover.header_of_low input target 0 hvalid.2.1 (by decide +kernel)
      (Cover.bytesToNatPadded_eq_of_cover input target checks (0 + 30) 2 hm checks_ok (by decide +kernel))]
    decide +kernel
  · show Precompile.bytesToNatPadded input 32 32 = 1
    rw [Cover.header_of_low input target 32 hvalid.2.2.1 (by decide +kernel)
      (Cover.bytesToNatPadded_eq_of_cover input target checks (32 + 30) 2 hm checks_ok (by decide +kernel))]
    decide +kernel
  · show Precompile.bytesToNatPadded input 64 32 = 12
    rw [Cover.header_of_low input target 64 hvalid.2.2.2 (by decide +kernel)
      (Cover.bytesToNatPadded_eq_of_cover input target checks (64 + 30) 2 hm checks_ok (by decide +kernel))]
    decide +kernel

theorem base_eq {input : ByteArray} (hm : WordsMatch checks input) :
    Precompile.bytesToNatPadded input 96 1 = 42 := by
  rw [Cover.bytesToNatPadded_eq_of_cover input target checks 96 1 hm checks_ok (by decide +kernel)]
  decide +kernel

theorem exp_eq {input : ByteArray} (hm : WordsMatch checks input) :
    Precompile.bytesToNatPadded input 97 1 = 7 := by
  rw [Cover.bytesToNatPadded_eq_of_cover input target checks 97 1 hm checks_ok (by decide +kernel)]
  decide +kernel

theorem mod_eq {input : ByteArray} (hm : WordsMatch checks input) :
    Precompile.bytesToNatPadded input 98 12 = 0 := by
  rw [Cover.bytesToNatPadded_eq_of_cover input target checks 98 12 hm checks_ok (by decide +kernel)]
  decide +kernel

theorem cert : Precompile.modPow 42 7 0 = 0 := by
  simp [Challenge.Modexp.Submission.Proofs.Algorithm.modPow_eq]

theorem spec_eq {input : ByteArray} (hvalid : ValidInput input) (hm : WordsMatch checks input) :
    spec input = Precompile.natToBytes 0 12 := by
  obtain ⟨hb, he, hmm⟩ := sizes hvalid hm
  simp only [spec, hb, he, hmm, base_eq hm, exp_eq hm, mod_eq hm, cert]
  rw [if_neg (by decide)]

end Challenge.Modexp.Submission.Proofs.Memo.V4.Spec
