import Challenge.Modexp.Submission.Proofs.Fast.CarryRowPrograms
import Challenge.Modexp.Submission.Proofs.Fast.CiosReadonlyPrograms
import Challenge.Modexp.Submission.Proofs.Fast.CiosReadonlyExtra
import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedPrograms
import Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneSlice

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 1000000

/-!
# Located blocks of the sqCP1m kernel row (shared by the multiply and the square)

Row head `out` (3996, multiply only), `commonFirst` (3999), the first-loop dispatch
`DUP6 JUMP` (4025); the uniform first-loop blocks live in `KernelChain`; the middle block
with its `JUMPDEST` (4293, the empty-chain entry); the second-loop dispatch `DUP10 JUMP`
(4365) and cells (4367..4581); the tail (4582, ends `DUP3 JUMPI` to the row head `hd`) and
the exit (4608, jumps to the moved CSUB guard 4667).  The kernel `setup` block belongs to
the entry side (`Cios2Dispatch` / `StagedOperandEntry`).
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.CarryRowBlocks

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel

open CiosCached WindowTwentyOneBinding

def out : Block Artifact.submissionArtifact .Osaka 3988 outProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3028 3 3988 outProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l1Dispatch : Block Artifact.submissionArtifact .Osaka 4017 l1DispatchProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3057 2 4017 l1DispatchProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac0 : Block Artifact.submissionArtifact .Osaka 3991 CiosReadonly.commonFirstProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3031 26 3991 CiosReadonly.commonFirstProgram
    (by decide) (by rfl) (by rfl) (by decide)

/-- The middle block with its leading `JUMPDEST` (instruction 3286, pc 4293). -/
def mid : Block Artifact.submissionArtifact .Osaka 4285 CarryRowPrograms.middleBlock :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3276 27 4285 CarryRowPrograms.middleBlock
    (by decide) (by rfl) (by rfl) (by decide)

def l2Dispatch : Block Artifact.submissionArtifact .Osaka 4316 l2DispatchProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3303 2 4316 l2DispatchProgram
    (by decide) (by rfl) (by rfl) (by decide)

/-- The first eight-limb second-loop cell loads its modulus word with `PUSH10 0xc0`. -/
def l2Mac0 : Block Artifact.submissionArtifact .Osaka 4319 (l2Program 10 192 8448 8480) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3306 30 4319 (l2Program 10 192 8448 8480)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac1 : Block Artifact.submissionArtifact .Osaka 4364 (l2Program 1 160 8416 8448) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3336 30 4364 (l2Program 1 160 8416 8448)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac2 : Block Artifact.submissionArtifact .Osaka 4400 (l2Program 1 128 8384 8416) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3366 30 4400 (l2Program 1 128 8384 8416)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac3 : Block Artifact.submissionArtifact .Osaka 4436 (CiosReadonlyExtra.extraProgram 0 8352 8384) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3396 29 4436 (CiosReadonlyExtra.extraProgram 0 8352 8384)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Join : Block Artifact.submissionArtifact .Osaka 4470 joinProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3425 1 4470 joinProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac4 : Block Artifact.submissionArtifact .Osaka 4471 (CiosReadonlyExtra.extraProgram 1 8320 8352) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3426 29 4471 (CiosReadonlyExtra.extraProgram 1 8320 8352)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac5 : Block Artifact.submissionArtifact .Osaka 4505 (CiosReadonlyExtra.extraProgram 2 8288 8320) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3455 29 4505 (CiosReadonlyExtra.extraProgram 2 8288 8320)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac6 : Block Artifact.submissionArtifact .Osaka 4539 (l2Program 0 0 8256 8288) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3484 30 4539 (l2Program 0 0 8256 8288)
    (by decide) (by rfl) (by rfl) (by decide)

def tailLoop : Block Artifact.submissionArtifact .Osaka 4574 CarryRowPrograms.tail :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3514 20 4574 CarryRowPrograms.tail
    (by decide) (by rfl) (by rfl) (by decide)

def exitBlock : Block Artifact.submissionArtifact .Osaka 4610 CiosReadonly.fullExitProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3540 14 4610 CiosReadonly.fullExitProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l2Join8 : Block Artifact.submissionArtifact .Osaka 4318 joinProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3305 1 4318 joinProgram
    (by decide) (by rfl) (by rfl) (by decide)

theorem jumpDestL2Eight : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4318 = true :=
  Artifact.isValidJumpDest_index 3305 (by rfl)

/-- The multiply row head (instruction 3040). -/
theorem jumpDest4595 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3988 = true :=
  Artifact.isValidJumpDest_index 3028 (by rfl)

/-- The four-limb second-loop entry (instruction 3439). -/
theorem jumpDest5112 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4470 = true :=
  Artifact.isValidJumpDest_index 3425 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast.CarryRowBlocks

namespace Challenge.Modexp.Submission.Proofs.Fast.CarryRowBlocks

open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode WindowTwentyOneBinding

def environment (s : State)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Environment Artifact.submissionArtifact .Osaka s :=
  ⟨by change Challenge.Modexp.submissionBytecode.size < 2^256; rw [Challenge.Modexp.submissionBytecode_size]; decide,
    hcode, hfork, hrun, hnp⟩

end Challenge.Modexp.Submission.Proofs.Fast.CarryRowBlocks
