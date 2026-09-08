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

def entry : Block Artifact.submissionArtifact .Osaka 4199 entryProgram :=
  WindowNineSlice.block Artifact.allWellFormed 2930 40 4199 entryProgram
    (by decide) (by rfl) (by rfl) (by decide)

def out : Block Artifact.submissionArtifact .Osaka 4251 outProgram :=
  WindowNineSlice.block Artifact.allWellFormed 2970 10 4251 outProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l1Dispatch : Block Artifact.submissionArtifact .Osaka 4267 l1DispatchProgram :=
  WindowNineSlice.block Artifact.allWellFormed 2980 3 4267 l1DispatchProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l1Join : Block Artifact.submissionArtifact .Osaka 4420 joinProgram :=
  WindowNineSlice.block Artifact.allWellFormed 3131 1 4420 joinProgram
    (by decide) (by rfl) (by rfl) (by decide)

def mid : Block Artifact.submissionArtifact .Osaka 4569 midProgram :=
  WindowNineSlice.block Artifact.allWellFormed 3280 50 4569 midProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l2Dispatch : Block Artifact.submissionArtifact .Osaka 4637 l2DispatchProgram :=
  WindowNineSlice.block Artifact.allWellFormed 3330 3 4637 l2DispatchProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l2Join : Block Artifact.submissionArtifact .Osaka 4802 joinProgram :=
  WindowNineSlice.block Artifact.allWellFormed 3489 1 4802 joinProgram
    (by decide) (by rfl) (by rfl) (by decide)

def tailLoop : Block Artifact.submissionArtifact .Osaka 4923 (CiosCached.tailProgram.take 25) :=
  WindowNineSlice.block Artifact.allWellFormed 3607 25 4923 (CiosCached.tailProgram.take 25)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac0 : Block Artifact.submissionArtifact .Osaka 4272 l1Program :=
  WindowNineSlice.block Artifact.allWellFormed 2983 37 4272 l1Program
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac1 : Block Artifact.submissionArtifact .Osaka 4309 l1Program :=
  WindowNineSlice.block Artifact.allWellFormed 3020 37 4309 l1Program
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac2 : Block Artifact.submissionArtifact .Osaka 4346 l1Program :=
  WindowNineSlice.block Artifact.allWellFormed 3057 37 4346 l1Program
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac3 : Block Artifact.submissionArtifact .Osaka 4383 l1Program :=
  WindowNineSlice.block Artifact.allWellFormed 3094 37 4383 l1Program
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac4 : Block Artifact.submissionArtifact .Osaka 4421 l1Program :=
  WindowNineSlice.block Artifact.allWellFormed 3132 37 4421 l1Program
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac5 : Block Artifact.submissionArtifact .Osaka 4458 l1Program :=
  WindowNineSlice.block Artifact.allWellFormed 3169 37 4458 l1Program
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac6 : Block Artifact.submissionArtifact .Osaka 4495 l1Program :=
  WindowNineSlice.block Artifact.allWellFormed 3206 37 4495 l1Program
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac7 : Block Artifact.submissionArtifact .Osaka 4532 l1Program :=
  WindowNineSlice.block Artifact.allWellFormed 3243 37 4532 l1Program
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac0 : Block Artifact.submissionArtifact .Osaka 4642 l2Program :=
  WindowNineSlice.block Artifact.allWellFormed 3333 39 4642 l2Program
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac1 : Block Artifact.submissionArtifact .Osaka 4682 l2Program :=
  WindowNineSlice.block Artifact.allWellFormed 3372 39 4682 l2Program
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac2 : Block Artifact.submissionArtifact .Osaka 4722 l2Program :=
  WindowNineSlice.block Artifact.allWellFormed 3411 39 4722 l2Program
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac3 : Block Artifact.submissionArtifact .Osaka 4762 l2Program :=
  WindowNineSlice.block Artifact.allWellFormed 3450 39 4762 l2Program
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac4 : Block Artifact.submissionArtifact .Osaka 4803 l2Program :=
  WindowNineSlice.block Artifact.allWellFormed 3490 39 4803 l2Program
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac5 : Block Artifact.submissionArtifact .Osaka 4843 l2Program :=
  WindowNineSlice.block Artifact.allWellFormed 3529 39 4843 l2Program
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac6 : Block Artifact.submissionArtifact .Osaka 4883 l2Program :=
  WindowNineSlice.block Artifact.allWellFormed 3568 39 4883 l2Program
    (by decide) (by rfl) (by rfl) (by decide)

def exitBlock : Block Artifact.submissionArtifact .Osaka 4958 (CiosCached.tailProgram.drop 25) :=
  WindowNineSlice.block Artifact.allWellFormed 3632 8 4958 (CiosCached.tailProgram.drop 25)
    (by decide) (by rfl) (by rfl) (by decide)

theorem jumpDest4277 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4251 = true :=
  Artifact.isValidJumpDest_index 2970 (by rfl)

theorem jumpDest4452 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4420 = true :=
  Artifact.isValidJumpDest_index 3131 (by rfl)

theorem jumpDest4835 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4802 = true :=
  Artifact.isValidJumpDest_index 3489 (by rfl)

def environment (s : State)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Environment Artifact.submissionArtifact .Osaka s :=
  ⟨by change Challenge.Modexp.submissionBytecode.size < 2^256; rw [Challenge.Modexp.submissionBytecode_size]; decide,
    hcode, hfork, hrun, hnp⟩

end Challenge.Modexp.Submission.Proofs.Fast.CiosCachedBlocks
