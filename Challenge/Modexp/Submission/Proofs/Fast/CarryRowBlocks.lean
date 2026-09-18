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

Row head `out` (4261, multiply only), `commonFirst` (4264), the first-loop dispatch
`DUP6 JUMP` (4289); the uniform first-loop blocks live in `KernelChain`; the middle block
with its `JUMPDEST` (4555, the empty-chain entry); the second-loop dispatch `DUP10 JUMP`
(4487) and cells (4504..2336); the tail (4839, ends `DUP3 JUMPI` to the row head `hd`) and
the exit (4861, jumps to the moved CSUB guard 4882).  The kernel `setup` block belongs to
the entry side (`Cios2Dispatch` / `StagedOperandEntry`).
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.CarryRowBlocks

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel

open CiosCached WindowTwentyOneBinding

def out : Block Artifact.submissionArtifact .Osaka 3465 outProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 2752 3 3465 outProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l1Dispatch : Block Artifact.submissionArtifact .Osaka 3492 l1DispatchProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 2779 2 3492 l1DispatchProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac0 : Block Artifact.submissionArtifact .Osaka 3468 CiosReadonly.commonFirstProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 2755 24 3468 CiosReadonly.commonFirstProgram
    (by decide) (by rfl) (by rfl) (by decide)

/-- The middle block with its leading `JUMPDEST`, now in its wide form: the first store
address is a `PUSH4`, which absorbs the two bytes freed by deleting the block's trailing
`DUP10 JUMP`.  The instruction index and count are unchanged (2727, 23) -- only the block's
byte span grows, from [3639,3666) to [3639,3668), so it now ends exactly where the deleted
jump used to land.  `l2Dispatch` is gone with it: pcs 3666/3667 are `MLOAD ADDMOD` now. -/
def mid : Block Artifact.submissionArtifact .Osaka 3753 CarryRowPrograms.middleBlockWide :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 2998 23 3753 CarryRowPrograms.middleBlockWide
    (by decide) (by rfl) (by rfl) (by decide)

/-- The same middle block inside the private four-limb ladder copy at 5283, where it keeps
the narrow `PUSH2` because the copy is a byte copy of base 3528-3665. -/
def midCopy : Block Artifact.submissionArtifact .Osaka 5397 CarryRowPrograms.middleBlock :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 4321 23 5397 CarryRowPrograms.middleBlock
    (by decide) (by rfl) (by rfl) (by decide)

/-- The copy's own tail, `PUSH2 0x0ee8 JUMP`, replacing the shared `DUP10 JUMP`. -/
def l2Exit : Block Artifact.submissionArtifact .Osaka 5424 l2ExitProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 4344 2 5424 l2ExitProgram
    (by decide) (by rfl) (by rfl) (by decide)

/-- The first eight-limb second-loop cell loads its modulus word with `PUSH10 0xc0`. -/
def l2Mac0 : Block Artifact.submissionArtifact .Osaka 3783 (l2Program 10 192 2304 2336) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3022 30 3783 (l2Program 10 192 2304 2336)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac1 : Block Artifact.submissionArtifact .Osaka 3827 (l2Program 1 160 2272 2304) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3052 30 3827 (l2Program 1 160 2272 2304)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac2 : Block Artifact.submissionArtifact .Osaka 3862 (l2Program 1 128 2240 2272) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3082 30 3862 (l2Program 1 128 2240 2272)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac3 : Block Artifact.submissionArtifact .Osaka 3897 (CiosReadonlyExtra.extraProgram 0 2208 2240) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3112 28 3897 (CiosReadonlyExtra.extraProgram 0 2208 2240)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Join : Block Artifact.submissionArtifact .Osaka 3930 joinProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3140 1 3930 joinProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac4 : Block Artifact.submissionArtifact .Osaka 3931 (CiosReadonlyExtra.extraProgram 1 2176 2208) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3141 29 3931 (CiosReadonlyExtra.extraProgram 1 2176 2208)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac5 : Block Artifact.submissionArtifact .Osaka 3964 (CiosReadonlyExtra.extraProgram 2 2144 2176) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3170 29 3964 (CiosReadonlyExtra.extraProgram 2 2144 2176)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac6 : Block Artifact.submissionArtifact .Osaka 3997 (CiosCachedLast.l2LastProgram 0 0 2112 2144) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3199 29 3997 (CiosCachedLast.l2LastProgram 0 0 2112 2144)
    (by decide) (by rfl) (by rfl) (by decide)

def tailLoop : Block Artifact.submissionArtifact .Osaka 4030 CarryRowPrograms.tail :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3228 18 4030 CarryRowPrograms.tail
    (by decide) (by rfl) (by rfl) (by decide)

def exitBlock : Block Artifact.submissionArtifact .Osaka 4063 CiosReadonly.fullExitProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3251 14 4063 CiosReadonly.fullExitProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l2Join8 : Block Artifact.submissionArtifact .Osaka 3782 joinProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3021 1 3782 joinProgram
    (by decide) (by rfl) (by rfl) (by decide)

theorem jumpDestL2Eight : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3782 = true :=
  Artifact.isValidJumpDest_index 3021 (by rfl)

/-- The multiply row head (instruction 3190). -/
theorem jumpDest4595 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3465 = true :=
  Artifact.isValidJumpDest_index 2752 (by rfl)

/-- The four-limb second-loop entry (instruction 3461). -/
theorem jumpDest5112 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3930 = true :=
  Artifact.isValidJumpDest_index 3140 (by rfl)

/-- The private ladder copy's middle-block entry. -/
theorem jumpDestMidCopy : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5397 = true :=
  Artifact.isValidJumpDest_index 4321 (by rfl)

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
