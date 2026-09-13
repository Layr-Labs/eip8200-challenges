import Challenge.Modexp.ProofSupport.Bytecode
import Challenge.Modexp.Submission.Proofs.Bytecode.WordGas
import Challenge.Modexp.Submission.Proofs.Bytecode.BigDispatch
import Challenge.Modexp.Submission.Proofs.Bytecode.BigCMain
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
/-! # Wide-modulus inputs

Inputs whose modulus is longer than one word are dispatched to the compact
multi-limb fallback, whose correctness is `BigC.bigC_correct`.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.SubmissionCorrect

open EvmSemantics
open EvmSemantics.EVM

/-- Every valid input with a modulus longer than 32 bytes returns the MODEXP
result through the compact fallback. -/
theorem bigHandled (input : ByteArray) (hvalid : ValidInput input)
    (hbig : 32 < modulusSize input)
    (entry : Challenge.EvmProof.GasSteps (initialState submissionBytecode input 0)
      (Main.trampolineState input 655)) :
    ∃ final : State,
      Nonempty (Challenge.EvmProof.GasSteps
        (initialState submissionBytecode input 0) final) ∧
        final.isDone = true ∧ final.toResult = .returned (spec input) := by
  have hpositive : 0 < modulusSize input := by omega
  let pre := (Main.gasSteps_header input hvalid entry).trans
    (BigDispatch.gasSteps_bigEntry input hvalid hpositive hbig)
  obtain ⟨final, ⟨tail⟩, hdone, hres⟩ :=
    BigC.bigC_correct (BigDispatch.bigEntryState input)
      ⟨rfl, rfl, rfl, deployAddress_not_precompile⟩ rfl
      (by simp [BigDispatch.bigEntryState])
      (by simp [BigDispatch.bigEntryState, Main.headerState, initialState]; decide)
      (by simp [BigDispatch.bigEntryState, Main.headerState, initialState])
      hvalid hpositive
  exact ⟨final, ⟨pre.trans tail⟩, hdone, hres⟩

end Challenge.Modexp.Submission.Proofs.Bytecode.SubmissionCorrect
