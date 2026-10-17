import Challenge.Ripemd160.Submission.Proofs.Bytecode.RetainedTerminalMul.RetainedAdapters
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedGuardSpec

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

/-! A semantic adapter, not a new fullguard proof.  This checkout calls the
semantic payload `reference 1000`, not `knownInput i13`; `result_zero_iff` is
its checked guard theorem.  The exact 1000-byte premise must not be dropped. -/
namespace RetainedBridge111
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open Challenge.Ripemd160
open Challenge.Ripemd160.Submission.Proofs.Bytecode
open RetainedIntegration105

theorem reference1000_eq_patterned :
    RecognitionAccumulator.reference 1000 = PatternedInputData.patternedInput := by
  simp [RecognitionAccumulator.reference, ← PatternedInputData.patternedInput_size]

/-- The retained raw accumulator and the existing semantic literal guard have
exactly the same zero predicate, including the zero-padded last word. -/
theorem retained_zero_iff_literal_guard (input : ByteArray)
    (hsize1000 : input.size = 1000) :
    retainedResult input = 0 ↔ DirectLiteralModel.result input 1000 = 0 := by
  rw [retainedResult_zero_iff input hsize1000,
    DirectLiteralModel.result_zero_iff input 1000
      (by unfold RecognitionAccumulator.Allowed; omega) hsize1000]

/-- The missing known-input equivalence: no implicit universal size claim. -/
theorem retained_zero_iff_knownInput (input : ByteArray)
    (hsize1000 : input.size = 1000) :
    retainedResult input = 0 ↔ input = PatternedInputData.patternedInput := by
  rw [retainedResult_zero_iff input hsize1000, reference1000_eq_patterned]

/-- The miss is a content miss in the exact 1000-byte case, not a size miss. -/
theorem retained_nonzero_iff_content_miss (input : ByteArray)
    (hsize1000 : input.size = 1000) :
    retainedResult input ≠ 0 ↔ input ≠ PatternedInputData.patternedInput := by
  exact not_congr (retained_zero_iff_knownInput input hsize1000)

/-- The known-input equality feeds the already checked RIPEMD/spec theorem. -/
theorem retained_zero_spec (input : ByteArray)
    (hsize1000 : input.size = 1000) (hz : retainedResult input = 0) :
    spec input = PatternedDigest.paddedDigest := by
  rw [(retained_zero_iff_knownInput input hsize1000).mp hz]
  exact PatternedGuardSpec.spec_patternedInput_eq

#print axioms retained_zero_iff_literal_guard
#print axioms retained_zero_iff_knownInput
#print axioms retained_nonzero_iff_content_miss
#print axioms retained_zero_spec
end RetainedBridge111
