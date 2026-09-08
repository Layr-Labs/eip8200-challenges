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
  WindowNineSlice.block Artifact.allWellFormed 2956 39 4225 entryProgram
    (by decide) (by rfl) (by rfl) (by decide)

def out : Block Artifact.submissionArtifact .Osaka 4339 outProgram :=
  WindowNineSlice.block Artifact.allWellFormed 2995 7 4339 outProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l1Dispatch : Block Artifact.submissionArtifact .Osaka 4348 l1DispatchProgram :=
  WindowNineSlice.block Artifact.allWellFormed 3002 4 4348 l1DispatchProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l1Join : Block Artifact.submissionArtifact .Osaka 4502 joinProgram :=
  WindowNineSlice.block Artifact.allWellFormed 3154 1 4502 joinProgram
    (by decide) (by rfl) (by rfl) (by decide)

def mid : Block Artifact.submissionArtifact .Osaka 4651 midProgram :=
  WindowNineSlice.block Artifact.allWellFormed 3303 44 4651 midProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l2Dispatch : Block Artifact.submissionArtifact .Osaka 4719 l2DispatchProgram :=
  WindowNineSlice.block Artifact.allWellFormed 3347 4 4719 l2DispatchProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l2Join : Block Artifact.submissionArtifact .Osaka 4885 joinProgram :=
  WindowNineSlice.block Artifact.allWellFormed 3507 1 4885 joinProgram
    (by decide) (by rfl) (by rfl) (by decide)

def tailLoop : Block Artifact.submissionArtifact .Osaka 5006 (CiosCached.tailProgram.take 26) :=
  WindowNineSlice.block Artifact.allWellFormed 3625 26 5006 (CiosCached.tailProgram.take 26)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac0 : Block Artifact.submissionArtifact .Osaka 4354 l1Program :=
  WindowNineSlice.block Artifact.allWellFormed 3006 37 4354 l1Program
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac1 : Block Artifact.submissionArtifact .Osaka 4391 l1Program :=
  WindowNineSlice.block Artifact.allWellFormed 3043 37 4391 l1Program
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac2 : Block Artifact.submissionArtifact .Osaka 4428 l1Program :=
  WindowNineSlice.block Artifact.allWellFormed 3080 37 4428 l1Program
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac3 : Block Artifact.submissionArtifact .Osaka 4465 l1Program :=
  WindowNineSlice.block Artifact.allWellFormed 3117 37 4465 l1Program
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac4 : Block Artifact.submissionArtifact .Osaka 4503 l1Program :=
  WindowNineSlice.block Artifact.allWellFormed 3155 37 4503 l1Program
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac5 : Block Artifact.submissionArtifact .Osaka 4540 l1Program :=
  WindowNineSlice.block Artifact.allWellFormed 3192 37 4540 l1Program
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac6 : Block Artifact.submissionArtifact .Osaka 4577 l1Program :=
  WindowNineSlice.block Artifact.allWellFormed 3229 37 4577 l1Program
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac7 : Block Artifact.submissionArtifact .Osaka 4614 l1Program :=
  WindowNineSlice.block Artifact.allWellFormed 3266 37 4614 l1Program
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac0 : Block Artifact.submissionArtifact .Osaka 4725 l2Program :=
  WindowNineSlice.block Artifact.allWellFormed 3351 39 4725 l2Program
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac1 : Block Artifact.submissionArtifact .Osaka 4765 l2Program :=
  WindowNineSlice.block Artifact.allWellFormed 3390 39 4765 l2Program
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac2 : Block Artifact.submissionArtifact .Osaka 4805 l2Program :=
  WindowNineSlice.block Artifact.allWellFormed 3429 39 4805 l2Program
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac3 : Block Artifact.submissionArtifact .Osaka 4845 l2Program :=
  WindowNineSlice.block Artifact.allWellFormed 3468 39 4845 l2Program
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac4 : Block Artifact.submissionArtifact .Osaka 4886 l2Program :=
  WindowNineSlice.block Artifact.allWellFormed 3508 39 4886 l2Program
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac5 : Block Artifact.submissionArtifact .Osaka 4926 l2Program :=
  WindowNineSlice.block Artifact.allWellFormed 3547 39 4926 l2Program
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac6 : Block Artifact.submissionArtifact .Osaka 4966 l2Program :=
  WindowNineSlice.block Artifact.allWellFormed 3586 39 4966 l2Program
    (by decide) (by rfl) (by rfl) (by decide)

def exitBlock : Block Artifact.submissionArtifact .Osaka 5042 (CiosCached.tailProgram.drop 26) :=
  WindowNineSlice.block Artifact.allWellFormed 3651 8 5042 (CiosCached.tailProgram.drop 26)
    (by decide) (by rfl) (by rfl) (by decide)

theorem jumpDest4339 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4339 = true :=
  Artifact.isValidJumpDest_index 2995 (by rfl)

theorem jumpDest4502 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4502 = true :=
  Artifact.isValidJumpDest_index 3154 (by rfl)

theorem jumpDest4885 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4885 = true :=
  Artifact.isValidJumpDest_index 3507 (by rfl)

def environment (s : State)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Environment Artifact.submissionArtifact .Osaka s :=
  ⟨by change Challenge.Modexp.submissionBytecode.size < 2^256; rw [Challenge.Modexp.submissionBytecode_size]; decide,
    hcode, hfork, hrun, hnp⟩

end Challenge.Modexp.Submission.Proofs.Fast.CiosCachedBlocks
