import Challenge.Modexp.Submission.Proofs.Fast.CarryRowPrograms
import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedLast
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

Row head `out` (4266, multiply only), `commonFirst` (4269), the first-loop dispatch
`DUP6 JUMP` (4294); the uniform first-loop blocks live in `KernelChain`; the middle block
with its `JUMPDEST` (4555, the empty-chain entry); the second-loop dispatch `DUP10 JUMP`
(4492) and cells (4504..2336); the tail (4835, ends `DUP3 JUMPI` to the row head `hd`) and
the exit (4861, jumps to the moved CSUB guard 4878).  The kernel `setup` block belongs to
the entry side (`Cios2Dispatch` / `StagedOperandEntry`).
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.CarryRowBlocks

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel

open CiosCached WindowTwentyOneBinding

def out : Block Artifact.submissionArtifact .Osaka 3720 outProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 2772 3 3720 outProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l1Dispatch : Block Artifact.submissionArtifact .Osaka 3747 l1DispatchProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 2799 2 3747 l1DispatchProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac0 : Block Artifact.submissionArtifact .Osaka 3723 CiosReadonly.commonFirstProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 2775 24 3723 CiosReadonly.commonFirstProgram
    (by decide) (by rfl) (by rfl) (by decide)

/-- The middle block with its leading `JUMPDEST` (instruction 3360, pc 4555). -/
def mid : Block Artifact.submissionArtifact .Osaka 4008 CarryRowPrograms.middleBlock :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3018 23 4008 CarryRowPrograms.middleBlock
    (by decide) (by rfl) (by rfl) (by decide)

def l2Dispatch : Block Artifact.submissionArtifact .Osaka 4035 l2DispatchProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3041 2 4035 l2DispatchProgram
    (by decide) (by rfl) (by rfl) (by decide)

/-- The first eight-limb second-loop cell loads its modulus word with `PUSH10 0xc0`. -/
def l2Mac0 : Block Artifact.submissionArtifact .Osaka 4039 (l2Program 10 192 2304 2336) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3045 30 4039 (l2Program 10 192 2304 2336)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac1 : Block Artifact.submissionArtifact .Osaka 4083 (l2Program 1 160 2272 2304) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3075 30 4083 (l2Program 1 160 2272 2304)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac2 : Block Artifact.submissionArtifact .Osaka 4118 (l2Program 1 128 2240 2272) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3105 30 4118 (l2Program 1 128 2240 2272)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac3 : Block Artifact.submissionArtifact .Osaka 4153 (CiosReadonlyExtra.extraProgram 0 2208 2240) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3135 28 4153 (CiosReadonlyExtra.extraProgram 0 2208 2240)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Join : Block Artifact.submissionArtifact .Osaka 4186 joinProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3163 1 4186 joinProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac4 : Block Artifact.submissionArtifact .Osaka 4187 (CiosReadonlyExtra.extraProgram 1 2176 2208) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3164 29 4187 (CiosReadonlyExtra.extraProgram 1 2176 2208)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac5 : Block Artifact.submissionArtifact .Osaka 4220 (CiosReadonlyExtra.extraProgram 2 2144 2176) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3193 29 4220 (CiosReadonlyExtra.extraProgram 2 2144 2176)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac6 : Block Artifact.submissionArtifact .Osaka 4253 (CiosCachedLast.l2LastProgram 0 0 2112 2144) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3222 29 4253 (CiosCachedLast.l2LastProgram 0 0 2112 2144)
    (by decide) (by rfl) (by rfl) (by decide)

def tailLoop : Block Artifact.submissionArtifact .Osaka 4286 CarryRowPrograms.tail :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3251 18 4286 CarryRowPrograms.tail
    (by decide) (by rfl) (by rfl) (by decide)

def exitBlock : Block Artifact.submissionArtifact .Osaka 4319 CiosReadonly.fullExitProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3274 14 4319 CiosReadonly.fullExitProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l2Join8 : Block Artifact.submissionArtifact .Osaka 4038 joinProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3044 1 4038 joinProgram
    (by decide) (by rfl) (by rfl) (by decide)

theorem jumpDestL2Eight : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4038 = true :=
  Artifact.isValidJumpDest_index 3044 (by rfl)

/-- The multiply row head (instruction 3189). -/
theorem jumpDest4595 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3720 = true :=
  Artifact.isValidJumpDest_index 2772 (by rfl)

/-- The four-limb second-loop entry (instruction 3460). -/
theorem jumpDest5112 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4186 = true :=
  Artifact.isValidJumpDest_index 3163 (by rfl)

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
