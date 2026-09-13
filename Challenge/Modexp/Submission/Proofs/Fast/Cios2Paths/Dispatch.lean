import Challenge.Modexp.Submission.Proofs.Fast.CiosInverseGuard
import Challenge.Modexp.Submission.Proofs.Fast.Defs
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneSlice
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-!
# The kernel's `mul entry` and shared `common` width guard (sqCP1m)

* `mul entry` (instruction 3189, pc 4018 = 0x0f50): `JUMPDEST; PUSH2 0x0fc5` pushes the
  multiply row head `hd = 4266` and falls through into `common`.
* `common` (instruction 3189, pc 4104 = 0x0f54, also entered directly by the square call
  with `hd = 2464`): `JUMPDEST; PUSH2 0x2480; MLOAD; DUP1; PUSH1 0x80; EQ; SWAP1;
  PUSH2 0x100; EQ; OR; PUSH2 0x0f6c; JUMPI` — widths of four and eight limbs jump to the
  kernel `setup` (pc 4128).
* fallback (instruction 3189, pc 3904): `POP; PUSH2 0x0683; JUMP` drops `hd` and enters the
  generic `MONPRO` at pc 1746.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.Cios2Paths.Dispatch

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open WindowTwentyOneBinding

def mulEntryProgram : List Instr :=
  [.op .JUMPDEST, .push 2 3729]

def commonGuardProgram : List Instr := CiosInverseGuard.guardProgram

def commonFallbackProgram : List Instr :=
  [.op .POP, .push 2 1207, .op .JUMP]

def mulEntry : Block Artifact.submissionArtifact .Osaka 3556 mulEntryProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 2664 2 3556 mulEntryProgram
    (by decide) (by rfl) (by rfl) (by decide)

def commonGuard : Block Artifact.submissionArtifact .Osaka 3560 commonGuardProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 2666 17 3560 commonGuardProgram
    (by decide) (by rfl) (by rfl) (by decide)

def commonFallback : Block Artifact.submissionArtifact .Osaka 3587 commonFallbackProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 2683 3 3587 commonFallbackProgram
    (by decide) (by rfl) (by rfl) (by decide)

end Challenge.Modexp.Submission.Proofs.Fast.Cios2Paths.Dispatch
