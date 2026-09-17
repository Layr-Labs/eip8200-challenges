import Challenge.Modexp.Submission.Proofs.Bytecode.PCFast
import Challenge.Modexp.Submission.Proofs.Fast.R4Math
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneSlice
import Challenge.Modexp.Submission.Proofs.Bytecode.Artifact

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-!
# R4：程序切片与定位证书（机器生成，勿手改；gen/emit.py）
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.R4Blocks

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel WindowTwentyOneBinding

/-- The entry and first diagonal share the scheduled stack window (PC 4784..4813). -/
def prog_prodiag : List Instr :=
  [.op .JUMPDEST, .op (.Dup ⟨7, by decide⟩), .push 0 0, .op .MLOAD,
   .op (.Dup ⟨14, by decide⟩), .op (.Dup ⟨14, by decide⟩), .op (.Dup ⟨12, by decide⟩),
   .push 2 2464, .op .MLOAD, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨0, by decide⟩), .op .ADD,
   .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨0, by decide⟩), .op .MUL,
   .op (.Dup ⟨13, by decide⟩), .op (.Dup ⟨0, by decide⟩), .op (.Swap ⟨3, by decide⟩),
   .op (.Dup ⟨0, by decide⟩), .op .MULMOD, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩),
   .op .GT, .op (.Dup ⟨2, by decide⟩), .op (.Swap ⟨1, by decide⟩), .op .SUB, .op .SUB]

def block_prodiag : Block Artifact.submissionArtifact .Osaka 4508 prog_prodiag :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3597 27 4508 prog_prodiag
    (by decide) (by rfl) (by rfl) (by decide)

/-- pc 4824..4846（idx 3639..3659）。 -/
def prog_r0z1 : List Instr :=
  [.push 2 2432, .op .MLOAD, .op (.Dup ⟨4, by decide⟩), .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨2, by decide⟩), .op .MUL, .op (.Swap ⟨1, by decide⟩), .op (.Dup ⟨5, by decide⟩),
   .op .MULMOD, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .GT, .op .SUB,
   .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op .ADD, .op (.Dup ⟨0, by decide⟩),
   .op (.Swap ⟨3, by decide⟩), .op .GT, .op .SUB, .op .SUB]

def block_r0z1 : Block Artifact.submissionArtifact .Osaka 4537 prog_r0z1 :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3624 21 4537 prog_r0z1
    (by decide) (by rfl) (by rfl) (by decide)

/-- pc 4847..4869（idx 3660..3680）。 -/
def prog_r0z2 : List Instr :=
  [.push 2 2400, .op .MLOAD, .op (.Dup ⟨5, by decide⟩), .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨2, by decide⟩), .op .MUL, .op (.Swap ⟨1, by decide⟩), .op (.Dup ⟨6, by decide⟩),
   .op .MULMOD, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .GT, .op .SUB,
   .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op .ADD, .op (.Dup ⟨0, by decide⟩),
   .op (.Swap ⟨3, by decide⟩), .op .GT, .op .SUB, .op .SUB]

def block_r0z2 : Block Artifact.submissionArtifact .Osaka 4560 prog_r0z2 :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3645 21 4560 prog_r0z2
    (by decide) (by rfl) (by rfl) (by decide)

/-- pc 4870..4892（idx 3681..3701）。 -/
def prog_r0z3 : List Instr :=
  [.push 2 2368, .op .MLOAD, .op (.Dup ⟨6, by decide⟩), .op (.Dup ⟨6, by decide⟩),
   .op (.Dup ⟨2, by decide⟩), .op .MUL, .op (.Swap ⟨1, by decide⟩), .op (.Dup ⟨7, by decide⟩),
   .op .MULMOD, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .GT, .op .SUB,
   .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op .ADD, .op (.Dup ⟨0, by decide⟩),
   .op (.Swap ⟨3, by decide⟩), .op .GT, .op .SUB, .op .SUB]

def block_r0z3 : Block Artifact.submissionArtifact .Osaka 4583 prog_r0z3 :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3666 21 4583 prog_r0z3
    (by decide) (by rfl) (by rfl) (by decide)

/-- pc 4893..4902（idx 3702..3707）。 -/
def prog_r0e : List Instr :=
  [.op (.Swap ⟨4, by decide⟩), .op .POP, .push 0 0, .push 2 4616, .push 2 4856,
   .op .JUMP]

def block_r0e : Block Artifact.submissionArtifact .Osaka 4606 prog_r0e :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3687 6 4606 prog_r0e
    (by decide) (by rfl) (by rfl) (by decide)

/-- pc 5158..5173（idx 3935..3950）。 -/
def prog_redm : List Instr :=
  [.op .JUMPDEST, .op (.Dup ⟨5, by decide⟩), .op (.Dup ⟨13, by decide⟩), .op .MUL,
   .op (.Dup ⟨8, by decide⟩), .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨12, by decide⟩), .op .MULMOD, .op (.Dup ⟨8, by decide⟩), .op .ADDMOD]

def block_redm : Block Artifact.submissionArtifact .Osaka 4856 prog_redm :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3905 11 4856 prog_redm
    (by decide) (by rfl) (by rfl) (by decide)

/-- pc 5174..5201（idx 3951..3978）。 -/
def prog_reds1 : List Instr :=
  [.op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨12, by decide⟩), .op .MUL, .op (.Dup ⟨10, by decide⟩), .op (.Dup ⟨13, by decide⟩),
   .op (.Dup ⟨4, by decide⟩), .op .MULMOD, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .GT,
   .op .SUB, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op .ADD, .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨1, by decide⟩), .op .ADD, .op (.Swap ⟨10, by decide⟩), .op .POP, .op (.Dup ⟨10, by decide⟩),
   .op (.Dup ⟨1, by decide⟩), .op .GT, .op (.Swap ⟨3, by decide⟩), .op .GT, .op .SUB,
   .op .SUB, .op .ADD]

def block_reds1 : Block Artifact.submissionArtifact .Osaka 4867 prog_reds1 :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3916 27 4867 prog_reds1
    (by decide) (by rfl) (by rfl) (by decide)

/-- pc 5202..5229（idx 3979..4006）。 -/
def prog_reds2 : List Instr :=
  [.op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨13, by decide⟩), .op .MUL, .op (.Dup ⟨10, by decide⟩), .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨4, by decide⟩), .op .MULMOD, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .GT,
   .op .SUB, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op .ADD, .op (.Dup ⟨8, by decide⟩),
   .op (.Dup ⟨1, by decide⟩), .op .ADD, .op (.Swap ⟨9, by decide⟩), .op .POP, .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨1, by decide⟩), .op .GT, .op (.Swap ⟨3, by decide⟩), .op .GT, .op .SUB,
   .op .SUB, .op .ADD]

def block_reds2 : Block Artifact.submissionArtifact .Osaka 4894 prog_reds2 :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3943 27 4894 prog_reds2
    (by decide) (by rfl) (by rfl) (by decide)

/-- pc 5230..5257（idx 4007..4034）。 -/
def prog_reds3 : List Instr :=
  [.op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨14, by decide⟩), .op .MUL, .op (.Dup ⟨10, by decide⟩), .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨4, by decide⟩), .op .MULMOD, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .GT,
   .op .SUB, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op .ADD, .op (.Dup ⟨7, by decide⟩),
   .op (.Dup ⟨1, by decide⟩), .op .ADD, .op (.Swap ⟨8, by decide⟩), .op .POP, .op (.Dup ⟨8, by decide⟩),
   .op (.Dup ⟨1, by decide⟩), .op .GT, .op (.Swap ⟨3, by decide⟩), .op .GT, .op .SUB,
   .op .SUB, .op .ADD]

def block_reds3 : Block Artifact.submissionArtifact .Osaka 4921 prog_reds3 :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3970 27 4921 prog_reds3
    (by decide) (by rfl) (by rfl) (by decide)

/-- pc 4948..4959 (idx 3997..4008). -/
def prog_redt : List Instr :=
  [.op (.Dup ⟨8, by decide⟩), .op .ADD, .op (.Swap ⟨3, by decide⟩), .op .POP, .op .POP,
   .op (.Swap ⟨5, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .JUMPDEST, .op .LT,
   .op .ADD, .op (.Swap ⟨4, by decide⟩), .op .JUMP]

def block_redt : Block Artifact.submissionArtifact .Osaka 4948 prog_redt :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3997 12 4948 prog_redt
    (by decide) (by rfl) (by rfl) (by decide)

/-- pc 4903..4912（idx 3708..3713）。 -/
def prog_r1h : List Instr :=
  [.op .JUMPDEST, .push 2 2432, .op .MLOAD, .push 2 2464, .op .MLOAD, .push 0 0]

def block_r1h : Block Artifact.submissionArtifact .Osaka 4616 prog_r1h :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3693 6 4616 prog_r1h
    (by decide) (by rfl) (by rfl) (by decide)

/-- pc 4914..4947（idx 3715..3748）。 -/
def prog_r1d : List Instr :=
  [.op (.Dup ⟨1, by decide⟩), .op .ADD, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .ADD, .op (.Swap ⟨1, by decide⟩), .op (.Dup ⟨8, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨5, by decide⟩), .op .MUL, .op (.Swap ⟨4, by decide⟩), .op .LT, .op (.Swap ⟨2, by decide⟩), .op .MULMOD, .op .SUB, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .LT, .op .SUB, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨6, by decide⟩), .op .ADD, .op (.Swap ⟨5, by decide⟩), .op (.Dup ⟨6, by decide⟩), .op .LT, .op .SUB, .op .SUB]

def block_r1d : Block Artifact.submissionArtifact .Osaka 4627 prog_r1d :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3700 29 4627 prog_r1d
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)

/-- pc 4948..4976（idx 3749..3775）。 -/
def prog_r1c2 : List Instr :=
  [.push 2 2400, .op .MLOAD, .op (.Dup ⟨8, by decide⟩), .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨2, by decide⟩), .op .MUL, .op (.Swap ⟨1, by decide⟩), .op (.Dup ⟨4, by decide⟩),
   .op .MULMOD, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .GT, .op .SUB,
   .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op .ADD, .op (.Dup ⟨6, by decide⟩),
   .op (.Dup ⟨1, by decide⟩), .op .ADD, .op (.Swap ⟨6, by decide⟩), .op (.Dup ⟨7, by decide⟩),
   .op .LT, .op (.Swap ⟨3, by decide⟩), .op .GT, .op .SUB, .op .SUB, .op .ADD]

def block_r1c2 : Block Artifact.submissionArtifact .Osaka 4656 prog_r1c2 :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3729 27 4656 prog_r1c2
    (by decide) (by rfl) (by rfl) (by decide)

/-- pc 4977..5005（idx 3776..3802）。 -/
def prog_r1c3 : List Instr :=
  [.push 2 2368, .op .MLOAD, .op (.Dup ⟨8, by decide⟩), .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨2, by decide⟩), .op .MUL, .op (.Swap ⟨1, by decide⟩), .op (.Dup ⟨4, by decide⟩),
   .op .MULMOD, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .GT, .op .SUB,
   .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op .ADD, .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨1, by decide⟩), .op .ADD, .op (.Swap ⟨5, by decide⟩), .op (.Dup ⟨6, by decide⟩),
   .op .LT, .op (.Swap ⟨3, by decide⟩), .op .GT, .op .SUB, .op .SUB, .op .ADD]

def block_r1c3 : Block Artifact.submissionArtifact .Osaka 4685 prog_r1c3 :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3756 27 4685 prog_r1c3
    (by decide) (by rfl) (by rfl) (by decide)

/-- pc 5006..5019（idx 3803..3812）。 -/
def prog_r1e : List Instr :=
  [.op (.Dup ⟨6, by decide⟩), .op .ADD, .op (.Swap ⟨5, by decide⟩), .op (.Dup ⟨6, by decide⟩), .op .LT,
   .op (.Swap ⟨0, by decide⟩), .op .POP, .push 2 4728, .push 2 4856, .op .JUMP]

def block_r1e : Block Artifact.submissionArtifact .Osaka 4714 prog_r1e :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3783 10 4714 prog_r1e
    (by decide) (by rfl) (by rfl) (by decide)

/-- pc 5020..5029（idx 3813..3818）。 -/
def prog_r2h : List Instr :=
  [.op .JUMPDEST, .push 2 2400, .op .MLOAD, .push 2 2432, .op .MLOAD, .push 0 0]

def block_r2h : Block Artifact.submissionArtifact .Osaka 4728 prog_r2h :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3793 6 4728 prog_r2h
    (by decide) (by rfl) (by rfl) (by decide)

/-- pc 5031..5064（idx 3820..3853）。 -/
def prog_r2d : List Instr :=
  [.op (.Dup ⟨1, by decide⟩), .op .ADD, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .ADD, .op (.Swap ⟨1, by decide⟩), .op (.Dup ⟨8, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨5, by decide⟩), .op .MUL, .op (.Swap ⟨4, by decide⟩), .op .LT, .op (.Swap ⟨2, by decide⟩), .op .MULMOD, .op .SUB, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .LT, .op .SUB, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨5, by decide⟩), .op .ADD, .op (.Swap ⟨4, by decide⟩), .op (.Dup ⟨5, by decide⟩), .op .LT, .op .SUB, .op .SUB]

def block_r2d : Block Artifact.submissionArtifact .Osaka 4739 prog_r2d :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3800 29 4739 prog_r2d
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)

/-- pc 5065..5093（idx 3854..3880）。 -/
def prog_r2c3 : List Instr :=
  [.push 2 2368, .op .MLOAD, .op (.Dup ⟨8, by decide⟩), .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨2, by decide⟩), .op .MUL, .op (.Swap ⟨1, by decide⟩), .op (.Dup ⟨4, by decide⟩),
   .op .MULMOD, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .GT, .op .SUB,
   .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op .ADD, .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨1, by decide⟩), .op .ADD, .op (.Swap ⟨5, by decide⟩), .op (.Dup ⟨6, by decide⟩),
   .op .LT, .op (.Swap ⟨3, by decide⟩), .op .GT, .op .SUB, .op .SUB, .op .ADD]

def block_r2c3 : Block Artifact.submissionArtifact .Osaka 4768 prog_r2c3 :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3829 27 4768 prog_r2c3
    (by decide) (by rfl) (by rfl) (by decide)

/-- pc 5094..5107（idx 3881..3890）。 -/
def prog_r2e : List Instr :=
  [.op (.Dup ⟨6, by decide⟩), .op .ADD, .op (.Swap ⟨5, by decide⟩), .op (.Dup ⟨6, by decide⟩), .op .LT,
   .op (.Swap ⟨0, by decide⟩), .op .POP, .push 2 4811, .push 2 4856, .op .JUMP]

def block_r2e : Block Artifact.submissionArtifact .Osaka 4797 prog_r2e :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3856 10 4797 prog_r2e
    (by decide) (by rfl) (by rfl) (by decide)

/-- pc 5108..5117（idx 3891..3896）。 -/
def prog_r3h : List Instr :=
  [.op .JUMPDEST, .push 2 2368, .op .MLOAD, .push 2 2400, .op .MLOAD, .push 0 0]

def block_r3h : Block Artifact.submissionArtifact .Osaka 4811 prog_r3h :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3866 6 4811 prog_r3h
    (by decide) (by rfl) (by rfl) (by decide)

/-- pc 5119..5149（idx 3898..3928）。 -/
def prog_r3d : List Instr :=
  [.op (.Dup ⟨1, by decide⟩), .op .ADD, .op (.Swap ⟨0, by decide⟩), .op (.Dup ⟨7, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨5, by decide⟩), .op .MUL, .op (.Swap ⟨4, by decide⟩), .op .LT, .op (.Swap ⟨2, by decide⟩), .op .MULMOD, .op .SUB, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .LT, .op .SUB, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op .ADD, .op (.Swap ⟨2, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op .LT, .op .SUB, .op .SUB]

def block_r3d : Block Artifact.submissionArtifact .Osaka 4822 prog_r3d :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3873 26 4822 prog_r3d
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)

/-- pc 5150..5155（idx 3929..3934）。 -/
def prog_r3e : List Instr :=
  [.op (.Dup ⟨5, by decide⟩), .op .ADD, .op (.Swap ⟨4, by decide⟩), .op (.Dup ⟨5, by decide⟩), .op .LT,
   .push 2 4962]

def block_r3e : Block Artifact.submissionArtifact .Osaka 4848 prog_r3e :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3899 6 4848 prog_r3e
    (by decide) (by rfl) (by rfl) (by decide)

/-- pc 4848..4888（idx 3707..3725）。

Rider: the five stores consume the top five stack values in stack order instead of `DUP`ing
them.  The slots the `DUP`s vacated are absorbed into the neighbouring `PUSH` by widening it
and left-padding the immediate with zero bytes, so the pcs and the instruction boundaries are
still preserved, and the pushed values are bit-identical — but the padding now costs nothing,
where a `JUMPDEST` cost 1 gas on every execution.  The five target words `0x820 .. 0x8a0` are
pairwise disjoint and word-aligned, so the reordered writes commute
(`writeBytes_comm_disjoint`), and the highest touched word is unchanged, so the
memory-expansion charge is identical.  The eleven incoming values are dead either way: the
block leaves with stack depth 0 and jumps to `0xfa5`.

Ten instructions are deleted, so every instruction index after 3707 shifts down by 10; the
pcs, and hence every jump destination and every pushed code pointer, are untouched. -/
def prog_exit : List Instr :=
  [.op .JUMPDEST, .push 3 2112, .op .MSTORE,
   .push 3 2144, .op .MSTORE, .push 3 2176, .op .MSTORE,
   .push 3 2208, .op .MSTORE, .push 3 2080, .op .MSTORE,
   .op .POP, .op .POP, .op .POP, .op .POP, .op .POP, .op .POP,
   .push 7 4119, .op .JUMP]

def block_exit : Block Artifact.submissionArtifact .Osaka 4962 prog_exit :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 4011 19 4962 prog_exit
    (by decide) (by rfl) (by rfl) (by decide)

end Challenge.Modexp.Submission.Proofs.Fast.R4Blocks
