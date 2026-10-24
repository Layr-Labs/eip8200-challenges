import Challenge.Modexp.Submission.Proofs.CycleGlobal.Binding
import Challenge.Modexp.ProofSupport.Bytecode
import Challenge.Modexp.Submission.Proofs.CycleGlobal.WordGasSteps
import Challenge.Modexp.Submission.Proofs.CycleGlobal.WordCorrect
import Challenge.Modexp.Submission.Proofs.CycleGlobal.WordExpRuns
import Challenge.Modexp.Submission.Proofs.CycleGlobal.BigDispatch
import Challenge.Modexp.Submission.Proofs.CycleGlobal.BigCUMain
import Challenge.Modexp.Submission.Proofs.CycleGlobal.BigCUBlocks
noncomputable section
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
/-! # Wide-modulus inputs

Inputs whose modulus is longer than one word are dispatched to the compact
multi-limb fallback, whose correctness is `BigC.U.bigC_correct`, instantiated with
the submitted artifact's location certificates.
-/

namespace CycleSubmission.Global.SubmissionCorrect
open Challenge.Modexp
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode

open EvmSemantics
open EvmSemantics.EVM

/-- Every valid input with a modulus longer than 32 bytes returns the MODEXP
result through the compact fallback. -/
theorem bigHandled (input : ByteArray) (hvalid : ValidInput input)
    (hbig : 32 < modulusSize input)
    (entry : Challenge.EvmProof.GasSteps (initialState CycleSubmission.Artifact.bytecode input 0)
      (Main.trampolineState input 533)) :
    ∃ final : State,
      Nonempty (Challenge.EvmProof.GasSteps
        (initialState CycleSubmission.Artifact.bytecode input 0) final) ∧
        final.isDone = true ∧ final.toResult = .returned (spec input) := by
  have hpositive : 0 < modulusSize input := by omega
  let pre := (Main.gasSteps_header input hvalid entry).trans
    (BigDispatch.gasSteps_bigEntry input hvalid hpositive hbig)
  have env : WindowTwentyOneBinding.Environment CycleSubmission.Artifact.artifact .Osaka
      (BigDispatch.bigEntryState input) :=
    { sizeBound := by
        change CycleSubmission.Artifact.bytecode.size < 2 ^ 256
        rw [CycleSubmission.Artifact.bytecodeSize]
        decide
      code := rfl
      forkEq := rfl
      running := rfl
      noPrecompile := deployAddress_not_precompile }
  obtain ⟨final, ⟨tail⟩, hdone, hres⟩ :=
    BigC.U.bigC_correct BigC.UBlocks.setupBlocks BigC.UBlocks.expBlocks
      BigC.UBlocks.mulBlocks BigC.UBlocks.unsignedBlocks (BigDispatch.bigEntryState input) env rfl
      (by simp [BigDispatch.bigEntryState])
      (by simp [BigDispatch.bigEntryState, Main.headerState, initialState]; decide)
      (by simp [BigDispatch.bigEntryState, Main.headerState, initialState])
      hvalid hpositive
  exact ⟨final, ⟨pre.trans tail⟩, hdone, hres⟩

end CycleSubmission.Global.SubmissionCorrect
