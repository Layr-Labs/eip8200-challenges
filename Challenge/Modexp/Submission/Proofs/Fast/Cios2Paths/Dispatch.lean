import Challenge.Modexp.Submission.Proofs.Fast.CiosInverseGuard
import Challenge.Modexp.Submission.Proofs.Fast.Defs
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneSlice
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-!
# The kernel's `mul entry` and shared `common` width guard (sqCP1m)

* `mul entry` (instruction 3190, pc 4013 = 0x0f50): `JUMPDEST; PUSH2 0x0fc5` pushes the
  multiply row head `hd = 4261` and falls through into `common`.
* `common` (instruction 3190, pc 4104 = 0x0f54, also entered directly by the square call
  with `hd = 2464`): `JUMPDEST; PUSH2 0x2480; MLOAD; DUP1; PUSH1 0x80; EQ; SWAP1;
  PUSH2 0x100; EQ; OR; PUSH2 0x0f6c; JUMPI` — widths of four and eight limbs jump to the
  kernel `setup` (pc 4123).
* fallback (instruction 3190, pc 3899): `POP; PUSH2 0x0683; JUMP` drops `hd` and enters the
  generic `MONPRO` at pc 1746.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.Cios2Paths.Dispatch

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open WindowTwentyOneBinding

def mulEntryProgram : List Instr :=
  [.op .JUMPDEST, .push 2 3351]

/-- The thirteen-instruction inverse/width guard is gone: the rewritten entry test decides both
conditions before the fast path is entered, so `common` now falls straight through into `setup`. -/
def commonGuardProgram : List Instr := [.op .JUMPDEST]


def mulEntry : Block Artifact.submissionArtifact .Osaka 3209 mulEntryProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 2385 2 3209 mulEntryProgram
    (by decide) (by rfl) (by rfl) (by decide)

def commonGuard : Block Artifact.submissionArtifact .Osaka 3213 commonGuardProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 2387 1 3213 commonGuardProgram
    (by decide) (by rfl) (by rfl) (by decide)


end Challenge.Modexp.Submission.Proofs.Fast.Cios2Paths.Dispatch
