import Challenge.Modexp.Submission.Proofs.Fast.Defs
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneSlice
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-!
# The kernel's `mul entry` and shared `common` width guard (sqCP1m)

* `mul entry` (instruction 3002, pc 4063 = 0x0f50): `JUMPDEST; PUSH2 0x0fc5` pushes the
  multiply row head `hd = 4178` and falls through into `common`.
* `common` (instruction 3004, pc 4067 = 0x0f54, also entered directly by the square call
  with `hd = 4878`): `JUMPDEST; PUSH2 0x2480; MLOAD; DUP1; PUSH1 0x80; EQ; SWAP1;
  PUSH2 0x100; EQ; OR; PUSH2 0x0f6c; JUMPI` — widths of four and eight limbs jump to the
  kernel `setup` (pc 4091).
* fallback (instruction 3016, pc 3904): `POP; PUSH2 0x0683; JUMP` drops `hd` and enters the
  generic `MONPRO` at pc 1667.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.Cios2Paths.Dispatch

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open WindowTwentyOneBinding

def mulEntryProgram : List Instr :=
  [.op .JUMPDEST, .push 2 4170]

def commonGuardProgram : List Instr :=
  [.op .JUMPDEST,
   .push 2 9344,
   .op .MLOAD,
   .op (.Dup ⟨0, by decide⟩),
   .push 1 128,
   .op .EQ,
   .op (.Swap ⟨0, by decide⟩),
   .push 2 256,
   .op .EQ,
   .op .OR,
   .push 2 4083,
   .op .JUMPI]

def commonFallbackProgram : List Instr :=
  [.op .POP, .push 2 1674, .op .JUMP]

def mulEntry : Block Artifact.submissionArtifact .Osaka 4055 mulEntryProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3113 2 4055 mulEntryProgram
    (by decide) (by rfl) (by rfl) (by decide)

def commonGuard : Block Artifact.submissionArtifact .Osaka 4059 commonGuardProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3115 12 4059 commonGuardProgram
    (by decide) (by rfl) (by rfl) (by decide)

def commonFallback : Block Artifact.submissionArtifact .Osaka 4078 commonFallbackProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3127 3 4078 commonFallbackProgram
    (by decide) (by rfl) (by rfl) (by decide)

end Challenge.Modexp.Submission.Proofs.Fast.Cios2Paths.Dispatch
