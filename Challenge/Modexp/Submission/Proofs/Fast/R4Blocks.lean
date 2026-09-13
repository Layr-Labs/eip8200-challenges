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

/-- pc 4792..4799（idx 3609..3616）。 -/
def prog_pro : List Instr :=
  [.op .JUMPDEST, .op (.Dup ⟨7, by decide⟩), .push 0 0, .op .MLOAD, .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨14, by decide⟩), .op (.Dup ⟨12, by decide⟩), .op (.Dup ⟨10, by decide⟩)]

def block_pro : Block Artifact.submissionArtifact .Osaka 4776 prog_pro :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3589 8 4776 prog_pro
    (by decide) (by rfl) (by rfl) (by decide)

/-- pc 4800..4823（idx 3617..3638）。 -/
def prog_r0d : List Instr :=
  [.push 2 2464, .op .MLOAD, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .ADD,
   .op (.Swap ⟨0, by decide⟩), .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .MUL,
   .op (.Swap ⟨0, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨0, by decide⟩), .op .MULMOD, .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨2, by decide⟩), .op .GT, .op .SUB, .op (.Dup ⟨1, by decide⟩), .op .ADD,
   .push 0 0, .op .SUB]

def block_r0d : Block Artifact.submissionArtifact .Osaka 4784 prog_r0d :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3597 22 4784 prog_r0d
    (by decide) (by rfl) (by rfl) (by decide)

/-- pc 4824..4846（idx 3639..3659）。 -/
def prog_r0z1 : List Instr :=
  [.push 2 2432, .op .MLOAD, .op (.Dup ⟨4, by decide⟩), .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨2, by decide⟩), .op .MUL, .op (.Swap ⟨1, by decide⟩), .op (.Dup ⟨5, by decide⟩),
   .op .MULMOD, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .GT, .op .SUB,
   .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op .ADD, .op (.Dup ⟨0, by decide⟩),
   .op (.Swap ⟨3, by decide⟩), .op .GT, .op .SUB, .op .SUB]

def block_r0z1 : Block Artifact.submissionArtifact .Osaka 4808 prog_r0z1 :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3619 21 4808 prog_r0z1
    (by decide) (by rfl) (by rfl) (by decide)

/-- pc 4847..4869（idx 3660..3680）。 -/
def prog_r0z2 : List Instr :=
  [.push 2 2400, .op .MLOAD, .op (.Dup ⟨5, by decide⟩), .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨2, by decide⟩), .op .MUL, .op (.Swap ⟨1, by decide⟩), .op (.Dup ⟨6, by decide⟩),
   .op .MULMOD, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .GT, .op .SUB,
   .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op .ADD, .op (.Dup ⟨0, by decide⟩),
   .op (.Swap ⟨3, by decide⟩), .op .GT, .op .SUB, .op .SUB]

def block_r0z2 : Block Artifact.submissionArtifact .Osaka 4831 prog_r0z2 :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3640 21 4831 prog_r0z2
    (by decide) (by rfl) (by rfl) (by decide)

/-- pc 4870..4892（idx 3681..3701）。 -/
def prog_r0z3 : List Instr :=
  [.push 2 2368, .op .MLOAD, .op (.Dup ⟨6, by decide⟩), .op (.Dup ⟨6, by decide⟩),
   .op (.Dup ⟨2, by decide⟩), .op .MUL, .op (.Swap ⟨1, by decide⟩), .op (.Dup ⟨7, by decide⟩),
   .op .MULMOD, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .GT, .op .SUB,
   .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op .ADD, .op (.Dup ⟨0, by decide⟩),
   .op (.Swap ⟨3, by decide⟩), .op .GT, .op .SUB, .op .SUB]

def block_r0z3 : Block Artifact.submissionArtifact .Osaka 4854 prog_r0z3 :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3661 21 4854 prog_r0z3
    (by decide) (by rfl) (by rfl) (by decide)

/-- pc 4893..4902（idx 3702..3707）。 -/
def prog_r0e : List Instr :=
  [.op (.Swap ⟨4, by decide⟩), .op .POP, .push 0 0, .push 2 4887, .push 2 5142, .op .JUMP]

def block_r0e : Block Artifact.submissionArtifact .Osaka 4877 prog_r0e :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3682 6 4877 prog_r0e
    (by decide) (by rfl) (by rfl) (by decide)

/-- pc 5158..5173（idx 3935..3950）。 -/
def prog_redm : List Instr :=
  [.op .JUMPDEST, .op (.Dup ⟨5, by decide⟩), .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨14, by decide⟩), .op .MUL, .op (.Swap ⟨0, by decide⟩), .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨2, by decide⟩), .op (.Dup ⟨12, by decide⟩), .op .MULMOD,
   .op (.Dup ⟨1, by decide⟩), .op .ADD, .op (.Dup ⟨0, by decide⟩), .op (.Swap ⟨1, by decide⟩),
   .op .GT, .op .ADD]

def block_redm : Block Artifact.submissionArtifact .Osaka 5142 prog_redm :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3915 16 5142 prog_redm
    (by decide) (by rfl) (by rfl) (by decide)

/-- pc 5174..5201（idx 3951..3978）。 -/
def prog_reds1 : List Instr :=
  [.op (.Dup ⟨11, by decide⟩), .op (.Dup ⟨10, by decide⟩), .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨2, by decide⟩), .op .MUL, .op (.Swap ⟨1, by decide⟩), .op (.Dup ⟨4, by decide⟩),
   .op .MULMOD, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .GT, .op .SUB,
   .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op .ADD, .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨1, by decide⟩), .op .ADD, .op (.Swap ⟨10, by decide⟩), .op .POP,
   .op (.Dup ⟨10, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .GT, .op (.Swap ⟨3, by decide⟩),
   .op .GT, .op .SUB, .op .SUB, .op .ADD]

def block_reds1 : Block Artifact.submissionArtifact .Osaka 5158 prog_reds1 :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3931 28 5158 prog_reds1
    (by decide) (by rfl) (by rfl) (by decide)

/-- pc 5202..5229（idx 3979..4006）。 -/
def prog_reds2 : List Instr :=
  [.op (.Dup ⟨12, by decide⟩), .op (.Dup ⟨10, by decide⟩), .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨2, by decide⟩), .op .MUL, .op (.Swap ⟨1, by decide⟩), .op (.Dup ⟨4, by decide⟩),
   .op .MULMOD, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .GT, .op .SUB,
   .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op .ADD, .op (.Dup ⟨8, by decide⟩),
   .op (.Dup ⟨1, by decide⟩), .op .ADD, .op (.Swap ⟨9, by decide⟩), .op .POP,
   .op (.Dup ⟨9, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .GT, .op (.Swap ⟨3, by decide⟩),
   .op .GT, .op .SUB, .op .SUB, .op .ADD]

def block_reds2 : Block Artifact.submissionArtifact .Osaka 5186 prog_reds2 :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3959 28 5186 prog_reds2
    (by decide) (by rfl) (by rfl) (by decide)

/-- pc 5230..5257（idx 4007..4034）。 -/
def prog_reds3 : List Instr :=
  [.op (.Dup ⟨13, by decide⟩), .op (.Dup ⟨10, by decide⟩), .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨2, by decide⟩), .op .MUL, .op (.Swap ⟨1, by decide⟩), .op (.Dup ⟨4, by decide⟩),
   .op .MULMOD, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .GT, .op .SUB,
   .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op .ADD, .op (.Dup ⟨7, by decide⟩),
   .op (.Dup ⟨1, by decide⟩), .op .ADD, .op (.Swap ⟨8, by decide⟩), .op .POP,
   .op (.Dup ⟨8, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .GT, .op (.Swap ⟨3, by decide⟩),
   .op .GT, .op .SUB, .op .SUB, .op .ADD]

def block_reds3 : Block Artifact.submissionArtifact .Osaka 5214 prog_reds3 :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3987 28 5214 prog_reds3
    (by decide) (by rfl) (by rfl) (by decide)

/-- pc 5258..5273（idx 4035..4050）。 -/
def prog_redt : List Instr :=
  [.op (.Dup ⟨8, by decide⟩), .op .ADD, .op (.Swap ⟨3, by decide⟩), .op .POP,
   .op (.Dup ⟨7, by decide⟩), .op (.Dup ⟨4, by decide⟩), .op .LT, .op (.Swap ⟨0, by decide⟩),
   .op .POP, .op (.Dup ⟨2, by decide⟩), .op .ADD, .op (.Swap ⟨6, by decide⟩), .op .POP,
   .op (.Swap ⟨0, by decide⟩), .op .POP, .op .JUMP]

def block_redt : Block Artifact.submissionArtifact .Osaka 5242 prog_redt :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 4015 16 5242 prog_redt
    (by decide) (by rfl) (by rfl) (by decide)

/-- pc 4903..4912（idx 3708..3713）。 -/
def prog_r1h : List Instr :=
  [.op .JUMPDEST, .push 2 2432, .op .MLOAD, .push 2 2464, .op .MLOAD, .push 0 0]

def block_r1h : Block Artifact.submissionArtifact .Osaka 4887 prog_r1h :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3688 6 4887 prog_r1h
    (by decide) (by rfl) (by rfl) (by decide)

/-- pc 4914..4947（idx 3715..3748）。 -/
def prog_r1d : List Instr :=
  [.op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .MUL, .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨2, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op .ADD, .op .ADD,
   .op (.Swap ⟨1, by decide⟩), .op (.Dup ⟨8, by decide⟩), .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨2, by decide⟩), .op .MUL, .op (.Swap ⟨1, by decide⟩), .op (.Dup ⟨0, by decide⟩),
   .op .MULMOD, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .GT, .op .SUB,
   .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op .ADD, .op (.Dup ⟨7, by decide⟩),
   .op (.Dup ⟨1, by decide⟩), .op .ADD, .op (.Swap ⟨7, by decide⟩), .op (.Dup ⟨8, by decide⟩),
   .op .LT, .op (.Swap ⟨3, by decide⟩), .op .GT, .op .SUB, .op .SUB, .op .ADD]

def block_r1d : Block Artifact.submissionArtifact .Osaka 4898 prog_r1d :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3695 34 4898 prog_r1d
    (by decide) (by rfl) (by rfl) (by decide)

/-- pc 4948..4976（idx 3749..3775）。 -/
def prog_r1c2 : List Instr :=
  [.push 2 2400, .op .MLOAD, .op (.Dup ⟨8, by decide⟩), .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨2, by decide⟩), .op .MUL, .op (.Swap ⟨1, by decide⟩), .op (.Dup ⟨4, by decide⟩),
   .op .MULMOD, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .GT, .op .SUB,
   .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op .ADD, .op (.Dup ⟨6, by decide⟩),
   .op (.Dup ⟨1, by decide⟩), .op .ADD, .op (.Swap ⟨6, by decide⟩), .op (.Dup ⟨7, by decide⟩),
   .op .LT, .op (.Swap ⟨3, by decide⟩), .op .GT, .op .SUB, .op .SUB, .op .ADD]

def block_r1c2 : Block Artifact.submissionArtifact .Osaka 4932 prog_r1c2 :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3729 27 4932 prog_r1c2
    (by decide) (by rfl) (by rfl) (by decide)

/-- pc 4977..5005（idx 3776..3802）。 -/
def prog_r1c3 : List Instr :=
  [.push 2 2368, .op .MLOAD, .op (.Dup ⟨8, by decide⟩), .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨2, by decide⟩), .op .MUL, .op (.Swap ⟨1, by decide⟩), .op (.Dup ⟨4, by decide⟩),
   .op .MULMOD, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .GT, .op .SUB,
   .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op .ADD, .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨1, by decide⟩), .op .ADD, .op (.Swap ⟨5, by decide⟩), .op (.Dup ⟨6, by decide⟩),
   .op .LT, .op (.Swap ⟨3, by decide⟩), .op .GT, .op .SUB, .op .SUB, .op .ADD]

def block_r1c3 : Block Artifact.submissionArtifact .Osaka 4961 prog_r1c3 :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3756 27 4961 prog_r1c3
    (by decide) (by rfl) (by rfl) (by decide)

/-- pc 5006..5019（idx 3803..3812）。 -/
def prog_r1e : List Instr :=
  [.op (.Dup ⟨6, by decide⟩), .op .ADD, .op (.Swap ⟨5, by decide⟩), .op (.Dup ⟨6, by decide⟩),
   .op .LT, .op (.Swap ⟨0, by decide⟩), .op .POP, .push 2 5004, .push 2 5142, .op .JUMP]

def block_r1e : Block Artifact.submissionArtifact .Osaka 4990 prog_r1e :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3783 10 4990 prog_r1e
    (by decide) (by rfl) (by rfl) (by decide)

/-- pc 5020..5029（idx 3813..3818）。 -/
def prog_r2h : List Instr :=
  [.op .JUMPDEST, .push 2 2400, .op .MLOAD, .push 2 2432, .op .MLOAD, .push 0 0]

def block_r2h : Block Artifact.submissionArtifact .Osaka 5004 prog_r2h :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3793 6 5004 prog_r2h
    (by decide) (by rfl) (by rfl) (by decide)

/-- pc 5031..5064（idx 3820..3853）。 -/
def prog_r2d : List Instr :=
  [.op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .MUL, .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨2, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op .ADD, .op .ADD,
   .op (.Swap ⟨1, by decide⟩), .op (.Dup ⟨8, by decide⟩), .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨2, by decide⟩), .op .MUL, .op (.Swap ⟨1, by decide⟩), .op (.Dup ⟨0, by decide⟩),
   .op .MULMOD, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .GT, .op .SUB,
   .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op .ADD, .op (.Dup ⟨6, by decide⟩),
   .op (.Dup ⟨1, by decide⟩), .op .ADD, .op (.Swap ⟨6, by decide⟩), .op (.Dup ⟨7, by decide⟩),
   .op .LT, .op (.Swap ⟨3, by decide⟩), .op .GT, .op .SUB, .op .SUB, .op .ADD]

def block_r2d : Block Artifact.submissionArtifact .Osaka 5015 prog_r2d :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3800 34 5015 prog_r2d
    (by decide) (by rfl) (by rfl) (by decide)

/-- pc 5065..5093（idx 3854..3880）。 -/
def prog_r2c3 : List Instr :=
  [.push 2 2368, .op .MLOAD, .op (.Dup ⟨8, by decide⟩), .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨2, by decide⟩), .op .MUL, .op (.Swap ⟨1, by decide⟩), .op (.Dup ⟨4, by decide⟩),
   .op .MULMOD, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .GT, .op .SUB,
   .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op .ADD, .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨1, by decide⟩), .op .ADD, .op (.Swap ⟨5, by decide⟩), .op (.Dup ⟨6, by decide⟩),
   .op .LT, .op (.Swap ⟨3, by decide⟩), .op .GT, .op .SUB, .op .SUB, .op .ADD]

def block_r2c3 : Block Artifact.submissionArtifact .Osaka 5049 prog_r2c3 :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3834 27 5049 prog_r2c3
    (by decide) (by rfl) (by rfl) (by decide)

/-- pc 5094..5107（idx 3881..3890）。 -/
def prog_r2e : List Instr :=
  [.op (.Dup ⟨6, by decide⟩), .op .ADD, .op (.Swap ⟨5, by decide⟩), .op (.Dup ⟨6, by decide⟩),
   .op .LT, .op (.Swap ⟨0, by decide⟩), .op .POP, .push 2 5092, .push 2 5142, .op .JUMP]

def block_r2e : Block Artifact.submissionArtifact .Osaka 5078 prog_r2e :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3861 10 5078 prog_r2e
    (by decide) (by rfl) (by rfl) (by decide)

/-- pc 5108..5117（idx 3891..3896）。 -/
def prog_r3h : List Instr :=
  [.op .JUMPDEST, .push 2 2368, .op .MLOAD, .push 2 2400, .op .MLOAD, .push 0 0]

def block_r3h : Block Artifact.submissionArtifact .Osaka 5092 prog_r3h :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3871 6 5092 prog_r3h
    (by decide) (by rfl) (by rfl) (by decide)

/-- pc 5119..5149（idx 3898..3928）。 -/
def prog_r3d : List Instr :=
  [.op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .MUL, .op (.Swap ⟨0, by decide⟩),
   .op .POP, .op (.Swap ⟨0, by decide⟩), .op (.Dup ⟨7, by decide⟩), .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨2, by decide⟩), .op .MUL, .op (.Swap ⟨1, by decide⟩), .op (.Dup ⟨0, by decide⟩),
   .op .MULMOD, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .GT, .op .SUB,
   .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op .ADD, .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨1, by decide⟩), .op .ADD, .op (.Swap ⟨4, by decide⟩), .op (.Dup ⟨5, by decide⟩),
   .op .LT, .op (.Swap ⟨3, by decide⟩), .op .GT, .op .SUB, .op .SUB, .op .ADD]

def block_r3d : Block Artifact.submissionArtifact .Osaka 5103 prog_r3d :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3878 31 5103 prog_r3d
    (by decide) (by rfl) (by rfl) (by decide)

/-- pc 5150..5155（idx 3929..3934）。 -/
def prog_r3e : List Instr :=
  [.op (.Dup ⟨5, by decide⟩), .op .ADD, .op (.Swap ⟨4, by decide⟩), .op (.Dup ⟨5, by decide⟩),
   .op .LT, .push 2 5258]

def block_r3e : Block Artifact.submissionArtifact .Osaka 5134 prog_r3e :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3909 6 5134 prog_r3e
    (by decide) (by rfl) (by rfl) (by decide)

/-- pc 5274..5314（idx 4051..4079）。 -/
def prog_exit : List Instr :=
  [.op .JUMPDEST, .op (.Dup ⟨3, by decide⟩), .push 2 2208, .op .MSTORE,
   .op (.Dup ⟨2, by decide⟩), .push 2 2176, .op .MSTORE, .op (.Dup ⟨1, by decide⟩),
   .push 2 2144, .op .MSTORE, .op (.Dup ⟨0, by decide⟩), .push 2 2112, .op .MSTORE,
   .op (.Dup ⟨4, by decide⟩), .push 2 2080, .op .MSTORE, .op .POP, .op .POP, .op .POP,
   .op .POP, .op .POP, .op .POP, .op .POP, .op .POP, .op .POP, .op .POP, .op .POP,
   .push 2 4363, .op .JUMP]

def block_exit : Block Artifact.submissionArtifact .Osaka 5258 prog_exit :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 4031 29 5258 prog_exit
    (by decide) (by rfl) (by rfl) (by decide)

end Challenge.Modexp.Submission.Proofs.Fast.R4Blocks
