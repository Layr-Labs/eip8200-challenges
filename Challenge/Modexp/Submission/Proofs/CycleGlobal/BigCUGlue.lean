import Challenge.Modexp.Submission.Proofs.CycleGlobal.WindowCorrect
import Challenge.Modexp.Submission.Proofs.CycleGlobal.BigCUMain
import Challenge.Modexp.Submission.Proofs.CycleGlobal.BigCUBlocks

noncomputable section
set_option warningAsError true
set_option maxHeartbeats 2000000

/-! The wide-modulus fallback entered directly at pc 236 with the six live words on
the stack is correct: the generic cold path proof instantiated with the submitted
artifact's location certificates. -/

namespace CycleSubmission.Global.Fast.BigCUGlue
open Challenge.Modexp
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode
open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast

theorem bigBailHandled : WindowCorrect.BigBailHandled := by
  intro input hvalid h32 _h256 steps
  have env : WindowTwentyOneBinding.Environment CycleSubmission.Artifact.artifact .Osaka
      (Setup.bigBailState (initialState CycleSubmission.Artifact.bytecode input 0) input) :=
    { sizeBound := by
        change CycleSubmission.Artifact.bytecode.size < 2 ^ 256
        rw [CycleSubmission.Artifact.bytecodeSize]
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

end CycleSubmission.Global.Fast.BigCUGlue

