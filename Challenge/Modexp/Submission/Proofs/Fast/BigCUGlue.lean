import Challenge.Modexp.Submission.Proofs.Fast.WindowCorrect
import Challenge.Modexp.Submission.Proofs.Bytecode.BigCUMain
import Challenge.Modexp.Submission.Proofs.Bytecode.BigCUBlocks

set_option warningAsError true
set_option maxHeartbeats 2000000

/-! The wide-modulus fallback entered directly at pc 236 with the six live words on
the stack is correct: the generic cold path proof instantiated with the submitted
artifact's location certificates. -/

namespace Challenge.Modexp.Submission.Proofs.Fast.BigCUGlue
open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast

theorem bigBailHandled : WindowCorrect.BigBailHandled := by
  intro input hvalid h32 _h256 steps
  have env : WindowTwentyOneBinding.Environment Artifact.submissionArtifact .Osaka
      (Setup.bigBailState (initialState submissionBytecode input 0) input) :=
    { sizeBound := by
        change Challenge.Modexp.submissionBytecode.size < 2 ^ 256
        rw [Challenge.Modexp.submissionBytecode_size]
        decide
      code := rfl
      forkEq := rfl
      running := rfl
      noPrecompile := Challenge.Modexp.deployAddress_not_precompile }
  obtain ⟨final, ⟨tail⟩, hdone, hres⟩ :=
    BigC.U.bigC_correct BigC.UBlocks.setupBlocks BigC.UBlocks.expBlocks
      BigC.UBlocks.mulBlocks BigC.UBlocks.unsignedBlocks _ env rfl
      (by simp [Setup.bigBailState, Setup.outerStack, initialState])
      (by simp [Setup.bigBailState, initialState]; decide)
      rfl hvalid (by show 0 < modulusSize input; omega)
  exact ⟨final, ⟨steps.trans tail⟩, hdone, hres⟩

end Challenge.Modexp.Submission.Proofs.Fast.BigCUGlue
