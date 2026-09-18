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

def block_prodiag : Block Artifact.submissionArtifact .Osaka 4516 prog_prodiag :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3568 27 4516 prog_prodiag
    (by decide) (by rfl) (by rfl) (by decide)

/-- pc 4824..4846（idx 3639..3659）。 -/
def prog_r0z1 : List Instr :=
  [.push 2 2432, .op .MLOAD, .op (.Dup ⟨4, by decide⟩), .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨2, by decide⟩), .op .MUL, .op (.Swap ⟨1, by decide⟩), .op (.Dup ⟨5, by decide⟩),
   .op .MULMOD, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .GT, .op .SUB,
   .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op .ADD, .op (.Dup ⟨0, by decide⟩),
   .op (.Swap ⟨3, by decide⟩), .op .GT, .op .SUB, .op .SUB]

def block_r0z1 : Block Artifact.submissionArtifact .Osaka 4545 prog_r0z1 :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3595 21 4545 prog_r0z1
    (by decide) (by rfl) (by rfl) (by decide)

/-- pc 4847..4869（idx 3660..3680）。 -/
def prog_r0z2 : List Instr :=
  [.push 2 2400, .op .MLOAD, .op (.Dup ⟨5, by decide⟩), .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨2, by decide⟩), .op .MUL, .op (.Swap ⟨1, by decide⟩), .op (.Dup ⟨6, by decide⟩),
   .op .MULMOD, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .GT, .op .SUB,
   .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op .ADD, .op (.Dup ⟨0, by decide⟩),
   .op (.Swap ⟨3, by decide⟩), .op .GT, .op .SUB, .op .SUB]

def block_r0z2 : Block Artifact.submissionArtifact .Osaka 4568 prog_r0z2 :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3616 21 4568 prog_r0z2
    (by decide) (by rfl) (by rfl) (by decide)

/-- pc 4870..4892（idx 3681..3701）。 -/
def prog_r0z3 : List Instr :=
  [.push 2 2368, .op .MLOAD, .op (.Dup ⟨6, by decide⟩), .op (.Dup ⟨6, by decide⟩),
   .op (.Dup ⟨2, by decide⟩), .op .MUL, .op (.Swap ⟨1, by decide⟩), .op (.Dup ⟨7, by decide⟩),
   .op .MULMOD, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .GT, .op .SUB,
   .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op .ADD, .op (.Dup ⟨0, by decide⟩),
   .op (.Swap ⟨3, by decide⟩), .op .GT, .op .SUB, .op .SUB]

def block_r0z3 : Block Artifact.submissionArtifact .Osaka 4591 prog_r0z3 :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3637 21 4591 prog_r0z3
    (by decide) (by rfl) (by rfl) (by decide)

/-- pc 4893..4902（idx 3702..3707）。 -/
def prog_r0e : List Instr :=
  [.op (.Swap ⟨4, by decide⟩), .op .POP, .push 0 0, .push 2 4624, .push 2 4864,
   .op .JUMP]

def block_r0e : Block Artifact.submissionArtifact .Osaka 4614 prog_r0e :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3658 6 4614 prog_r0e
    (by decide) (by rfl) (by rfl) (by decide)

/-- pc 5158..5173（idx 3935..3950）。 -/
def prog_redm : List Instr :=
  [.op .JUMPDEST, .op (.Dup ⟨5, by decide⟩), .op (.Dup ⟨13, by decide⟩), .op .MUL,
   .op (.Dup ⟨8, by decide⟩), .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨12, by decide⟩), .op .MULMOD, .op (.Dup ⟨8, by decide⟩), .op .ADDMOD]

def block_redm : Block Artifact.submissionArtifact .Osaka 4864 prog_redm :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3876 11 4864 prog_redm
    (by decide) (by rfl) (by rfl) (by decide)

/-- pc 5174..5201（idx 3951..3978）。 -/
def prog_reds1 : List Instr :=
  [.op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨12, by decide⟩), .op .MUL, .op (.Dup ⟨10, by decide⟩), .op (.Dup ⟨13, by decide⟩),
   .op (.Dup ⟨4, by decide⟩), .op .MULMOD, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .GT,
   .op .SUB, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op .ADD, .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨1, by decide⟩), .op .ADD, .op (.Swap ⟨10, by decide⟩), .op .POP, .op (.Dup ⟨10, by decide⟩),
   .op (.Dup ⟨1, by decide⟩), .op .GT, .op (.Swap ⟨3, by decide⟩), .op .GT, .op .SUB,
   .op .SUB, .op .ADD]

def block_reds1 : Block Artifact.submissionArtifact .Osaka 4875 prog_reds1 :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3887 27 4875 prog_reds1
    (by decide) (by rfl) (by rfl) (by decide)

/-- pc 5202..5229（idx 3979..4006）。 -/
def prog_reds2 : List Instr :=
  [.op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨13, by decide⟩), .op .MUL, .op (.Dup ⟨10, by decide⟩), .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨4, by decide⟩), .op .MULMOD, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .GT,
   .op .SUB, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op .ADD, .op (.Dup ⟨8, by decide⟩),
   .op (.Dup ⟨1, by decide⟩), .op .ADD, .op (.Swap ⟨9, by decide⟩), .op .POP, .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨1, by decide⟩), .op .GT, .op (.Swap ⟨3, by decide⟩), .op .GT, .op .SUB,
   .op .SUB, .op .ADD]

def block_reds2 : Block Artifact.submissionArtifact .Osaka 4902 prog_reds2 :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3914 27 4902 prog_reds2
    (by decide) (by rfl) (by rfl) (by decide)

/-- pc 5230..5257（idx 4007..4034）。 -/
def prog_reds3 : List Instr :=
  [.op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨14, by decide⟩), .op .MUL, .op (.Dup ⟨10, by decide⟩), .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨4, by decide⟩), .op .MULMOD, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .GT,
   .op .SUB, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op .ADD, .op (.Dup ⟨7, by decide⟩),
   .op (.Dup ⟨1, by decide⟩), .op .ADD, .op (.Swap ⟨8, by decide⟩), .op .POP, .op (.Dup ⟨8, by decide⟩),
   .op (.Dup ⟨1, by decide⟩), .op .GT, .op (.Swap ⟨3, by decide⟩), .op .GT, .op .SUB,
   .op .SUB, .op .ADD]

def block_reds3 : Block Artifact.submissionArtifact .Osaka 4929 prog_reds3 :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3941 27 4929 prog_reds3
    (by decide) (by rfl) (by rfl) (by decide)

/-- pc 5258..5273（idx 4035..4050）。 -/
def prog_redt : List Instr :=
  [.op (.Dup ⟨8, by decide⟩), .op .ADD, .op (.Swap ⟨3, by decide⟩), .op .POP, .op .POP,
   .op (.Swap ⟨5, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .LT,
   .op .ADD, .op (.Swap ⟨4, by decide⟩), .op .JUMP]

def block_redt : Block Artifact.submissionArtifact .Osaka 4956 prog_redt :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3968 11 4956 prog_redt
    (by decide) (by rfl) (by rfl) (by decide)

/-- pc 4903..4912（idx 3708..3713）。 -/
def prog_r1h : List Instr :=
  [.op .JUMPDEST, .push 2 2432, .op .MLOAD, .push 2 2464, .op .MLOAD, .push 0 0]

def block_r1h : Block Artifact.submissionArtifact .Osaka 4624 prog_r1h :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3664 6 4624 prog_r1h
    (by decide) (by rfl) (by rfl) (by decide)

/-- pc 4914..4947（idx 3715..3748）。 -/
def prog_r1d : List Instr :=
  [.op (.Dup ⟨1, by decide⟩), .op .ADD, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .ADD, .op (.Swap ⟨1, by decide⟩), .op (.Dup ⟨8, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨5, by decide⟩), .op .MUL, .op (.Swap ⟨4, by decide⟩), .op .LT, .op (.Swap ⟨2, by decide⟩), .op .MULMOD, .op .SUB, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .LT, .op .SUB, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨6, by decide⟩), .op .ADD, .op (.Swap ⟨5, by decide⟩), .op (.Dup ⟨6, by decide⟩), .op .LT, .op .SUB, .op .SUB]

def block_r1d : Block Artifact.submissionArtifact .Osaka 4635 prog_r1d :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3671 29 4635 prog_r1d
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)

/-- pc 4948..4976（idx 3749..3775）。 -/
def prog_r1c2 : List Instr :=
  [.push 2 2400, .op .MLOAD, .op (.Dup ⟨8, by decide⟩), .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨2, by decide⟩), .op .MUL, .op (.Swap ⟨1, by decide⟩), .op (.Dup ⟨4, by decide⟩),
   .op .MULMOD, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .GT, .op .SUB,
   .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op .ADD, .op (.Dup ⟨6, by decide⟩),
   .op (.Dup ⟨1, by decide⟩), .op .ADD, .op (.Swap ⟨6, by decide⟩), .op (.Dup ⟨7, by decide⟩),
   .op .LT, .op (.Swap ⟨3, by decide⟩), .op .GT, .op .SUB, .op .SUB, .op .ADD]

def block_r1c2 : Block Artifact.submissionArtifact .Osaka 4664 prog_r1c2 :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3700 27 4664 prog_r1c2
    (by decide) (by rfl) (by rfl) (by decide)

/-- pc 4977..5005（idx 3776..3802）。 -/
def prog_r1c3 : List Instr :=
  [.push 2 2368, .op .MLOAD, .op (.Dup ⟨8, by decide⟩), .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨2, by decide⟩), .op .MUL, .op (.Swap ⟨1, by decide⟩), .op (.Dup ⟨4, by decide⟩),
   .op .MULMOD, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .GT, .op .SUB,
   .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op .ADD, .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨1, by decide⟩), .op .ADD, .op (.Swap ⟨5, by decide⟩), .op (.Dup ⟨6, by decide⟩),
   .op .LT, .op (.Swap ⟨3, by decide⟩), .op .GT, .op .SUB, .op .SUB, .op .ADD]

def block_r1c3 : Block Artifact.submissionArtifact .Osaka 4693 prog_r1c3 :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3727 27 4693 prog_r1c3
    (by decide) (by rfl) (by rfl) (by decide)

/-- pc 5006..5019（idx 3803..3812）。 -/
def prog_r1e : List Instr :=
  [.op (.Dup ⟨6, by decide⟩), .op .ADD, .op (.Swap ⟨5, by decide⟩), .op (.Dup ⟨6, by decide⟩), .op .LT,
   .op (.Swap ⟨0, by decide⟩), .op .POP, .push 2 4736, .push 2 4864, .op .JUMP]

def block_r1e : Block Artifact.submissionArtifact .Osaka 4722 prog_r1e :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3754 10 4722 prog_r1e
    (by decide) (by rfl) (by rfl) (by decide)

/-- pc 5020..5029（idx 3813..3818）。 -/
def prog_r2h : List Instr :=
  [.op .JUMPDEST, .push 2 2400, .op .MLOAD, .push 2 2432, .op .MLOAD, .push 0 0]

def block_r2h : Block Artifact.submissionArtifact .Osaka 4736 prog_r2h :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3764 6 4736 prog_r2h
    (by decide) (by rfl) (by rfl) (by decide)

/-- pc 5031..5064（idx 3820..3853）。 -/
def prog_r2d : List Instr :=
  [.op (.Dup ⟨1, by decide⟩), .op .ADD, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .ADD, .op (.Swap ⟨1, by decide⟩), .op (.Dup ⟨8, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨5, by decide⟩), .op .MUL, .op (.Swap ⟨4, by decide⟩), .op .LT, .op (.Swap ⟨2, by decide⟩), .op .MULMOD, .op .SUB, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .LT, .op .SUB, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨5, by decide⟩), .op .ADD, .op (.Swap ⟨4, by decide⟩), .op (.Dup ⟨5, by decide⟩), .op .LT, .op .SUB, .op .SUB]

def block_r2d : Block Artifact.submissionArtifact .Osaka 4747 prog_r2d :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3771 29 4747 prog_r2d
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)

/-- pc 5065..5093（idx 3854..3880）。 -/
def prog_r2c3 : List Instr :=
  [.push 2 2368, .op .MLOAD, .op (.Dup ⟨8, by decide⟩), .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨2, by decide⟩), .op .MUL, .op (.Swap ⟨1, by decide⟩), .op (.Dup ⟨4, by decide⟩),
   .op .MULMOD, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .GT, .op .SUB,
   .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op .ADD, .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨1, by decide⟩), .op .ADD, .op (.Swap ⟨5, by decide⟩), .op (.Dup ⟨6, by decide⟩),
   .op .LT, .op (.Swap ⟨3, by decide⟩), .op .GT, .op .SUB, .op .SUB, .op .ADD]

def block_r2c3 : Block Artifact.submissionArtifact .Osaka 4776 prog_r2c3 :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3800 27 4776 prog_r2c3
    (by decide) (by rfl) (by rfl) (by decide)

/-- pc 5094..5107（idx 3881..3890）。 -/
def prog_r2e : List Instr :=
  [.op (.Dup ⟨6, by decide⟩), .op .ADD, .op (.Swap ⟨5, by decide⟩), .op (.Dup ⟨6, by decide⟩), .op .LT,
   .op (.Swap ⟨0, by decide⟩), .op .POP, .push 2 4819, .push 2 4864, .op .JUMP]

def block_r2e : Block Artifact.submissionArtifact .Osaka 4805 prog_r2e :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3827 10 4805 prog_r2e
    (by decide) (by rfl) (by rfl) (by decide)

/-- pc 5108..5117（idx 3891..3896）。 -/
def prog_r3h : List Instr :=
  [.op .JUMPDEST, .push 2 2368, .op .MLOAD, .push 2 2400, .op .MLOAD, .push 0 0]

def block_r3h : Block Artifact.submissionArtifact .Osaka 4819 prog_r3h :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3837 6 4819 prog_r3h
    (by decide) (by rfl) (by rfl) (by decide)

/-- pc 5119..5149（idx 3898..3928）。 -/
def prog_r3d : List Instr :=
  [.op (.Dup ⟨1, by decide⟩), .op .ADD, .op (.Swap ⟨0, by decide⟩), .op (.Dup ⟨7, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨5, by decide⟩), .op .MUL, .op (.Swap ⟨4, by decide⟩), .op .LT, .op (.Swap ⟨2, by decide⟩), .op .MULMOD, .op .SUB, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .LT, .op .SUB, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op .ADD, .op (.Swap ⟨2, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op .LT, .op .SUB, .op .SUB]

def block_r3d : Block Artifact.submissionArtifact .Osaka 4830 prog_r3d :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3844 26 4830 prog_r3d
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)

/-- pc 5150..5155（idx 3929..3934）。 -/
def prog_r3e : List Instr :=
  [.op (.Dup ⟨5, by decide⟩), .op .ADD, .op (.Swap ⟨4, by decide⟩), .op (.Dup ⟨5, by decide⟩), .op .LT,
   .push 2 4970]

def block_r3e : Block Artifact.submissionArtifact .Osaka 4856 prog_r3e :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3870 6 4856 prog_r3e
    (by decide) (by rfl) (by rfl) (by decide)

/-- pc 4848..4888（idx 3707..3725）。

Rider: the five stores consume the top five stack values in stack order instead of `DUP`ing
them.  The slots the `DUP`s vacated are absorbed into the neighbouring `PUSH` by widening it
and left-padding the immediate with zero bytes, so the pcs and the instruction boundaries are
still preserved, and the pushed values are bit-identical — but the padding now costs nothing,
where a `JUMPDEST` cost 1 gas on every execution.  The five target words `0x820 .. 0x8a0` are
pairwise disjoint and word-aligned, so the reordered writes commute
(`writeBytes_comm_disjoint`), and the highest touched word is unchanged, so the
memory-expansion charge is identical.

E11 (the reassembly): the carry `t4` must reach both the frame cell (the lazy CSUB gate
reads the cell, E9) and the scratch word (the mid-exponent reader at 4437 keeps its `MLOAD`).
`SWAP13` installs `t4` into the cell (absolute stack position 15; the evicted cell value
comes up in its place and is dropped by the first `POP`), `DUP14 PUSH2 0x820 MSTORE` parks a
copy in memory, and the seven `POP`s drop the dead window and the row's operands.  The block
leaves with the retained frame and jumps to `sq_exit`. -/
def prog_exit : List Instr :=
  [.op .JUMPDEST, .push 3 2112, .op .MSTORE,
   .push 3 2144, .op .MSTORE, .push 3 2176, .op .MSTORE,
   .push 3 2208, .op .MSTORE,
   .op (.Swap ⟨12, by decide⟩), .op (.Dup ⟨13, by decide⟩), .push 2 2080, .op .MSTORE,
   .op .POP, .op .POP, .op .POP, .op .POP, .op .POP, .op .POP, .op .POP,
   .push 7 4128, .op .JUMP]

def block_exit : Block Artifact.submissionArtifact .Osaka 4970 prog_exit :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3982 22 4970 prog_exit
    (by decide) (by rfl) (by rfl) (by decide)

end Challenge.Modexp.Submission.Proofs.Fast.R4Blocks
