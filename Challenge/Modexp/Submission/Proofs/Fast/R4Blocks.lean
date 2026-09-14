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

def block_prodiag : Block Artifact.submissionArtifact .Osaka 4784 prog_prodiag :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3608 27 4784 prog_prodiag
    (by decide) (by rfl) (by rfl) (by decide)

/-- pc 4824..4846（idx 3639..3659）。 -/
def prog_r0z1 : List Instr :=
  [.push 2 2432, .op .MLOAD, .op (.Dup ⟨4, by decide⟩), .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨2, by decide⟩), .op .MUL, .op (.Swap ⟨1, by decide⟩), .op (.Dup ⟨5, by decide⟩),
   .op .MULMOD, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .GT, .op .SUB,
   .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op .ADD, .op (.Dup ⟨0, by decide⟩),
   .op (.Swap ⟨3, by decide⟩), .op .GT, .op .SUB, .op .SUB]

def block_r0z1 : Block Artifact.submissionArtifact .Osaka 4813 prog_r0z1 :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3635 21 4813 prog_r0z1
    (by decide) (by rfl) (by rfl) (by decide)

/-- pc 4847..4869（idx 3660..3680）。 -/
def prog_r0z2 : List Instr :=
  [.push 2 2400, .op .MLOAD, .op (.Dup ⟨5, by decide⟩), .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨2, by decide⟩), .op .MUL, .op (.Swap ⟨1, by decide⟩), .op (.Dup ⟨6, by decide⟩),
   .op .MULMOD, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .GT, .op .SUB,
   .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op .ADD, .op (.Dup ⟨0, by decide⟩),
   .op (.Swap ⟨3, by decide⟩), .op .GT, .op .SUB, .op .SUB]

def block_r0z2 : Block Artifact.submissionArtifact .Osaka 4836 prog_r0z2 :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3656 21 4836 prog_r0z2
    (by decide) (by rfl) (by rfl) (by decide)

/-- pc 4870..4892（idx 3681..3701）。 -/
def prog_r0z3 : List Instr :=
  [.push 2 2368, .op .MLOAD, .op (.Dup ⟨6, by decide⟩), .op (.Dup ⟨6, by decide⟩),
   .op (.Dup ⟨2, by decide⟩), .op .MUL, .op (.Swap ⟨1, by decide⟩), .op (.Dup ⟨7, by decide⟩),
   .op .MULMOD, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .GT, .op .SUB,
   .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op .ADD, .op (.Dup ⟨0, by decide⟩),
   .op (.Swap ⟨3, by decide⟩), .op .GT, .op .SUB, .op .SUB]

def block_r0z3 : Block Artifact.submissionArtifact .Osaka 4859 prog_r0z3 :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3677 21 4859 prog_r0z3
    (by decide) (by rfl) (by rfl) (by decide)

/-- pc 4893..4902（idx 3702..3707）。 -/
def prog_r0e : List Instr :=
  [.op (.Swap ⟨4, by decide⟩), .op .POP, .push 0 0, .push 2 4892, .push 2 5135,
   .op .JUMP]

def block_r0e : Block Artifact.submissionArtifact .Osaka 4882 prog_r0e :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3698 6 4882 prog_r0e
    (by decide) (by rfl) (by rfl) (by decide)

/-- pc 5158..5173（idx 3935..3950）。 -/
def prog_redm : List Instr :=
  [.op .JUMPDEST, .op (.Dup ⟨5, by decide⟩), .op (.Dup ⟨13, by decide⟩), .op .MUL,
   .op (.Dup ⟨8, by decide⟩), .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨12, by decide⟩), .op .MULMOD, .op (.Dup ⟨8, by decide⟩), .op .ADDMOD]

def block_redm : Block Artifact.submissionArtifact .Osaka 5135 prog_redm :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3919 11 5135 prog_redm
    (by decide) (by rfl) (by rfl) (by decide)

/-- pc 5174..5201（idx 3951..3978）。 -/
def prog_reds1 : List Instr :=
  [.op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨12, by decide⟩), .op .MUL, .op (.Dup ⟨10, by decide⟩), .op (.Dup ⟨13, by decide⟩),
   .op (.Dup ⟨4, by decide⟩), .op .MULMOD, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .GT,
   .op .SUB, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op .ADD, .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨1, by decide⟩), .op .ADD, .op (.Swap ⟨10, by decide⟩), .op .POP, .op (.Dup ⟨10, by decide⟩),
   .op (.Dup ⟨1, by decide⟩), .op .GT, .op (.Swap ⟨3, by decide⟩), .op .GT, .op .SUB,
   .op .SUB, .op .ADD]

def block_reds1 : Block Artifact.submissionArtifact .Osaka 5146 prog_reds1 :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3930 27 5146 prog_reds1
    (by decide) (by rfl) (by rfl) (by decide)

/-- pc 5202..5229（idx 3979..4006）。 -/
def prog_reds2 : List Instr :=
  [.op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨13, by decide⟩), .op .MUL, .op (.Dup ⟨10, by decide⟩), .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨4, by decide⟩), .op .MULMOD, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .GT,
   .op .SUB, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op .ADD, .op (.Dup ⟨8, by decide⟩),
   .op (.Dup ⟨1, by decide⟩), .op .ADD, .op (.Swap ⟨9, by decide⟩), .op .POP, .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨1, by decide⟩), .op .GT, .op (.Swap ⟨3, by decide⟩), .op .GT, .op .SUB,
   .op .SUB, .op .ADD]

def block_reds2 : Block Artifact.submissionArtifact .Osaka 5173 prog_reds2 :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3957 27 5173 prog_reds2
    (by decide) (by rfl) (by rfl) (by decide)

/-- pc 5230..5257（idx 4007..4034）。 -/
def prog_reds3 : List Instr :=
  [.op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨14, by decide⟩), .op .MUL, .op (.Dup ⟨10, by decide⟩), .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨4, by decide⟩), .op .MULMOD, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .GT,
   .op .SUB, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op .ADD, .op (.Dup ⟨7, by decide⟩),
   .op (.Dup ⟨1, by decide⟩), .op .ADD, .op (.Swap ⟨8, by decide⟩), .op .POP, .op (.Dup ⟨8, by decide⟩),
   .op (.Dup ⟨1, by decide⟩), .op .GT, .op (.Swap ⟨3, by decide⟩), .op .GT, .op .SUB,
   .op .SUB, .op .ADD]

def block_reds3 : Block Artifact.submissionArtifact .Osaka 5200 prog_reds3 :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3984 27 5200 prog_reds3
    (by decide) (by rfl) (by rfl) (by decide)

/-- pc 5258..5273（idx 4035..4050）。 -/
def prog_redt : List Instr :=
  [.op (.Dup ⟨8, by decide⟩), .op .ADD, .op (.Swap ⟨3, by decide⟩), .op .POP, .op .POP,
   .op (.Dup ⟨2, by decide⟩), .op (.Dup ⟨7, by decide⟩), .op .GT, .op (.Swap ⟨0, by decide⟩), .op (.Swap ⟨1, by decide⟩),
   .op .ADD, .op (.Swap ⟨5, by decide⟩), .op .POP, .op .JUMP]

def block_redt : Block Artifact.submissionArtifact .Osaka 5227 prog_redt :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 4011 14 5227 prog_redt
    (by decide) (by rfl) (by rfl) (by decide)

/-- pc 4903..4912（idx 3708..3713）。 -/
def prog_r1h : List Instr :=
  [.op .JUMPDEST, .push 2 2432, .op .MLOAD, .push 2 2464, .op .MLOAD, .push 0 0]

def block_r1h : Block Artifact.submissionArtifact .Osaka 4892 prog_r1h :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3704 6 4892 prog_r1h
    (by decide) (by rfl) (by rfl) (by decide)

/-- pc 4914..4947（idx 3715..3748）。 -/
def prog_r1d : List Instr :=
  [.op (.Dup ⟨1, by decide⟩), .op .ADD, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .ADD, .op (.Swap ⟨1, by decide⟩), .op (.Dup ⟨8, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .MULMOD, .op (.Swap ⟨1, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .LT, .op (.Swap ⟨1, by decide⟩), .op .MUL, .op (.Swap ⟨1, by decide⟩), .op .SUB, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .LT, .op .SUB, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨6, by decide⟩), .op .ADD, .op (.Swap ⟨5, by decide⟩), .op (.Dup ⟨6, by decide⟩), .op .LT, .op .SUB, .op .SUB]

def block_r1d : Block Artifact.submissionArtifact .Osaka 4903 prog_r1d :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3711 30 4903 prog_r1d
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)

/-- pc 4948..4976（idx 3749..3775）。 -/
def prog_r1c2 : List Instr :=
  [.push 2 2400, .op .MLOAD, .op (.Dup ⟨8, by decide⟩), .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨2, by decide⟩), .op .MUL, .op (.Swap ⟨1, by decide⟩), .op (.Dup ⟨4, by decide⟩),
   .op .MULMOD, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .GT, .op .SUB,
   .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op .ADD, .op (.Dup ⟨6, by decide⟩),
   .op (.Dup ⟨1, by decide⟩), .op .ADD, .op (.Swap ⟨6, by decide⟩), .op (.Dup ⟨7, by decide⟩),
   .op .LT, .op (.Swap ⟨3, by decide⟩), .op .GT, .op .SUB, .op .SUB, .op .ADD]

def block_r1c2 : Block Artifact.submissionArtifact .Osaka 4933 prog_r1c2 :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3741 27 4933 prog_r1c2
    (by decide) (by rfl) (by rfl) (by decide)

/-- pc 4977..5005（idx 3776..3802）。 -/
def prog_r1c3 : List Instr :=
  [.push 2 2368, .op .MLOAD, .op (.Dup ⟨8, by decide⟩), .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨2, by decide⟩), .op .MUL, .op (.Swap ⟨1, by decide⟩), .op (.Dup ⟨4, by decide⟩),
   .op .MULMOD, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .GT, .op .SUB,
   .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op .ADD, .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨1, by decide⟩), .op .ADD, .op (.Swap ⟨5, by decide⟩), .op (.Dup ⟨6, by decide⟩),
   .op .LT, .op (.Swap ⟨3, by decide⟩), .op .GT, .op .SUB, .op .SUB, .op .ADD]

def block_r1c3 : Block Artifact.submissionArtifact .Osaka 4962 prog_r1c3 :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3768 27 4962 prog_r1c3
    (by decide) (by rfl) (by rfl) (by decide)

/-- pc 5006..5019（idx 3803..3812）。 -/
def prog_r1e : List Instr :=
  [.op (.Dup ⟨6, by decide⟩), .op .ADD, .op (.Swap ⟨5, by decide⟩), .op (.Dup ⟨6, by decide⟩), .op .LT,
   .op (.Swap ⟨0, by decide⟩), .op .POP, .push 2 5005, .push 2 5135, .op .JUMP]

def block_r1e : Block Artifact.submissionArtifact .Osaka 4991 prog_r1e :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3795 10 4991 prog_r1e
    (by decide) (by rfl) (by rfl) (by decide)

/-- pc 5020..5029（idx 3813..3818）。 -/
def prog_r2h : List Instr :=
  [.op .JUMPDEST, .push 2 2400, .op .MLOAD, .push 2 2432, .op .MLOAD, .push 0 0]

def block_r2h : Block Artifact.submissionArtifact .Osaka 5005 prog_r2h :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3805 6 5005 prog_r2h
    (by decide) (by rfl) (by rfl) (by decide)

/-- pc 5031..5064（idx 3820..3853）。 -/
def prog_r2d : List Instr :=
  [.op (.Dup ⟨1, by decide⟩), .op .ADD, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .ADD, .op (.Swap ⟨1, by decide⟩), .op (.Dup ⟨8, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .MULMOD, .op (.Swap ⟨1, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .LT, .op (.Swap ⟨1, by decide⟩), .op .MUL, .op (.Swap ⟨1, by decide⟩), .op .SUB, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .LT, .op .SUB, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨5, by decide⟩), .op .ADD, .op (.Swap ⟨4, by decide⟩), .op (.Dup ⟨5, by decide⟩), .op .LT, .op .SUB, .op .SUB]

def block_r2d : Block Artifact.submissionArtifact .Osaka 5016 prog_r2d :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3812 30 5016 prog_r2d
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)

/-- pc 5065..5093（idx 3854..3880）。 -/
def prog_r2c3 : List Instr :=
  [.push 2 2368, .op .MLOAD, .op (.Dup ⟨8, by decide⟩), .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨2, by decide⟩), .op .MUL, .op (.Swap ⟨1, by decide⟩), .op (.Dup ⟨4, by decide⟩),
   .op .MULMOD, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .GT, .op .SUB,
   .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op .ADD, .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨1, by decide⟩), .op .ADD, .op (.Swap ⟨5, by decide⟩), .op (.Dup ⟨6, by decide⟩),
   .op .LT, .op (.Swap ⟨3, by decide⟩), .op .GT, .op .SUB, .op .SUB, .op .ADD]

def block_r2c3 : Block Artifact.submissionArtifact .Osaka 5046 prog_r2c3 :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3842 27 5046 prog_r2c3
    (by decide) (by rfl) (by rfl) (by decide)

/-- pc 5094..5107（idx 3881..3890）。 -/
def prog_r2e : List Instr :=
  [.op (.Dup ⟨6, by decide⟩), .op .ADD, .op (.Swap ⟨5, by decide⟩), .op (.Dup ⟨6, by decide⟩), .op .LT,
   .op (.Swap ⟨0, by decide⟩), .op .POP, .push 2 5089, .push 2 5135, .op .JUMP]

def block_r2e : Block Artifact.submissionArtifact .Osaka 5075 prog_r2e :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3869 10 5075 prog_r2e
    (by decide) (by rfl) (by rfl) (by decide)

/-- pc 5108..5117（idx 3891..3896）。 -/
def prog_r3h : List Instr :=
  [.op .JUMPDEST, .push 2 2368, .op .MLOAD, .push 2 2400, .op .MLOAD, .push 0 0]

def block_r3h : Block Artifact.submissionArtifact .Osaka 5089 prog_r3h :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3879 6 5089 prog_r3h
    (by decide) (by rfl) (by rfl) (by decide)

/-- pc 5119..5149（idx 3898..3928）。 -/
def prog_r3d : List Instr :=
  [.op (.Dup ⟨1, by decide⟩), .op .ADD, .op (.Swap ⟨0, by decide⟩), .op (.Dup ⟨7, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .MULMOD, .op (.Swap ⟨1, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .LT, .op (.Swap ⟨1, by decide⟩), .op .MUL, .op (.Swap ⟨1, by decide⟩), .op .SUB, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .LT, .op .SUB, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op .ADD, .op (.Swap ⟨2, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op .LT, .op .SUB, .op .SUB]

def block_r3d : Block Artifact.submissionArtifact .Osaka 5100 prog_r3d :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3886 27 5100 prog_r3d
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)

/-- pc 5150..5155（idx 3929..3934）。 -/
def prog_r3e : List Instr :=
  [.op (.Dup ⟨5, by decide⟩), .op .ADD, .op (.Swap ⟨4, by decide⟩), .op (.Dup ⟨5, by decide⟩), .op .LT,
   .push 2 5241]

def block_r3e : Block Artifact.submissionArtifact .Osaka 5127 prog_r3e :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3913 6 5127 prog_r3e
    (by decide) (by rfl) (by rfl) (by decide)

/-- pc 5274..5314（idx 4051..4079）。 -/
def prog_exit : List Instr :=
  [.op .JUMPDEST, .op (.Dup ⟨3, by decide⟩), .push 2 2208, .op .MSTORE,
   .op (.Dup ⟨2, by decide⟩), .push 2 2176, .op .MSTORE, .op (.Dup ⟨1, by decide⟩),
   .push 2 2144, .op .MSTORE, .op (.Dup ⟨0, by decide⟩), .push 2 2112, .op .MSTORE,
   .op (.Dup ⟨4, by decide⟩), .push 2 2080, .op .MSTORE, .op .POP, .op .POP, .op .POP,
   .op .POP, .op .POP, .op .POP, .op .POP, .op .POP, .op .POP, .op .POP, .op .POP,
   .push 2 4377, .op .JUMP]

def block_exit : Block Artifact.submissionArtifact .Osaka 5241 prog_exit :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 4025 29 5241 prog_exit
    (by decide) (by rfl) (by rfl) (by decide)

end Challenge.Modexp.Submission.Proofs.Fast.R4Blocks
