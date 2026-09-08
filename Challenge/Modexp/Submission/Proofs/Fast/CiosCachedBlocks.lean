import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedPrograms
import Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowNineSlice

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 1000000

namespace Challenge.Modexp.Submission.Proofs.Fast.CiosCachedBlocks

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel

open CiosCached WindowNineBinding

def entry : Block Artifact.submissionArtifact .Osaka 4225 entryProgram :=
  WindowNineSlice.block Artifact.allWellFormed 2956 40 4225 entryProgram
    (by decide) (by rfl) (by rfl) (by decide)

def out : Block Artifact.submissionArtifact .Osaka 4277 outProgram :=
  WindowNineSlice.block Artifact.allWellFormed 2996 15 4277 outProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l1Dispatch : Block Artifact.submissionArtifact .Osaka 4298 l1DispatchProgram :=
  WindowNineSlice.block Artifact.allWellFormed 3011 4 4298 l1DispatchProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l1Join : Block Artifact.submissionArtifact .Osaka 4452 joinProgram :=
  WindowNineSlice.block Artifact.allWellFormed 3163 1 4452 joinProgram
    (by decide) (by rfl) (by rfl) (by decide)

def mid : Block Artifact.submissionArtifact .Osaka 4601 midProgram :=
  WindowNineSlice.block Artifact.allWellFormed 3312 50 4601 midProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l2Dispatch : Block Artifact.submissionArtifact .Osaka 4669 l2DispatchProgram :=
  WindowNineSlice.block Artifact.allWellFormed 3362 4 4669 l2DispatchProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l2Join : Block Artifact.submissionArtifact .Osaka 4835 joinProgram :=
  WindowNineSlice.block Artifact.allWellFormed 3522 1 4835 joinProgram
    (by decide) (by rfl) (by rfl) (by decide)

def tailLoop : Block Artifact.submissionArtifact .Osaka 4956 (CiosCached.tailProgram.take 26) :=
  WindowNineSlice.block Artifact.allWellFormed 3640 26 4956 (CiosCached.tailProgram.take 26)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac0 : Block Artifact.submissionArtifact .Osaka 4304 l1Program :=
  WindowNineSlice.block Artifact.allWellFormed 3015 37 4304 l1Program
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac1 : Block Artifact.submissionArtifact .Osaka 4341 l1Program :=
  WindowNineSlice.block Artifact.allWellFormed 3052 37 4341 l1Program
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac2 : Block Artifact.submissionArtifact .Osaka 4378 l1Program :=
  WindowNineSlice.block Artifact.allWellFormed 3089 37 4378 l1Program
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac3 : Block Artifact.submissionArtifact .Osaka 4415 l1Program :=
  WindowNineSlice.block Artifact.allWellFormed 3126 37 4415 l1Program
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac4 : Block Artifact.submissionArtifact .Osaka 4453 l1Program :=
  WindowNineSlice.block Artifact.allWellFormed 3164 37 4453 l1Program
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac5 : Block Artifact.submissionArtifact .Osaka 4490 l1Program :=
  WindowNineSlice.block Artifact.allWellFormed 3201 37 4490 l1Program
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac6 : Block Artifact.submissionArtifact .Osaka 4527 l1Program :=
  WindowNineSlice.block Artifact.allWellFormed 3238 37 4527 l1Program
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac7 : Block Artifact.submissionArtifact .Osaka 4564 l1Program :=
  WindowNineSlice.block Artifact.allWellFormed 3275 37 4564 l1Program
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac0 : Block Artifact.submissionArtifact .Osaka 4675 l2Program :=
  WindowNineSlice.block Artifact.allWellFormed 3366 39 4675 l2Program
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac1 : Block Artifact.submissionArtifact .Osaka 4715 l2Program :=
  WindowNineSlice.block Artifact.allWellFormed 3405 39 4715 l2Program
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac2 : Block Artifact.submissionArtifact .Osaka 4755 l2Program :=
  WindowNineSlice.block Artifact.allWellFormed 3444 39 4755 l2Program
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac3 : Block Artifact.submissionArtifact .Osaka 4795 l2Program :=
  WindowNineSlice.block Artifact.allWellFormed 3483 39 4795 l2Program
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac4 : Block Artifact.submissionArtifact .Osaka 4836 l2Program :=
  WindowNineSlice.block Artifact.allWellFormed 3523 39 4836 l2Program
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac5 : Block Artifact.submissionArtifact .Osaka 4876 l2Program :=
  WindowNineSlice.block Artifact.allWellFormed 3562 39 4876 l2Program
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac6 : Block Artifact.submissionArtifact .Osaka 4916 l2Program :=
  WindowNineSlice.block Artifact.allWellFormed 3601 39 4916 l2Program
    (by decide) (by rfl) (by rfl) (by decide)

def exitBlock : Block Artifact.submissionArtifact .Osaka 4992 (CiosCached.tailProgram.drop 26) :=
  WindowNineSlice.block Artifact.allWellFormed 3666 8 4992 (CiosCached.tailProgram.drop 26)
    (by decide) (by rfl) (by rfl) (by decide)

theorem jumpDest4277 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4277 = true :=
  Artifact.isValidJumpDest_index 2996 (by rfl)

theorem jumpDest4452 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4452 = true :=
  Artifact.isValidJumpDest_index 3163 (by rfl)

theorem jumpDest4835 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4835 = true :=
  Artifact.isValidJumpDest_index 3522 (by rfl)

def environment (s : State)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Environment Artifact.submissionArtifact .Osaka s :=
  ⟨by change Challenge.Modexp.submissionBytecode.size < 2^256; rw [Challenge.Modexp.submissionBytecode_size]; decide,
    hcode, hfork, hrun, hnp⟩

end Challenge.Modexp.Submission.Proofs.Fast.CiosCachedBlocks
