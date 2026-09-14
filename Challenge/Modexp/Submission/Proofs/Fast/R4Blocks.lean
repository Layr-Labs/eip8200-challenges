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

/-- The entry and first diagonal share the scheduled stack window (PC 4799..4824). -/
def prog_prodiag : List Instr :=
  [.op .JUMPDEST, .op (.Dup ⟨7, by decide⟩), .push 0 0, .op .MLOAD,
   .op (.Dup ⟨14, by decide⟩), .op (.Dup ⟨14, by decide⟩), .op (.Dup ⟨12, by decide⟩),
   .push 2 2464, .op .MLOAD, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨0, by decide⟩), .op .ADD,
   .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨0, by decide⟩), .op .MUL,
   .op (.Dup ⟨13, by decide⟩), .op (.Dup ⟨0, by decide⟩), .op (.Swap ⟨3, by decide⟩),
   .op (.Dup ⟨0, by decide⟩), .op .MULMOD, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩),
   .op .GT, .op (.Dup ⟨2, by decide⟩), .op (.Swap ⟨1, by decide⟩), .op .SUB, .op .SUB]

def block_prodiag : Block Artifact.submissionArtifact .Osaka 4809 prog_prodiag :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3639 27 4809 prog_prodiag
    (by decide) (by rfl) (by rfl) (by decide)

/-- pc 4835..4857（idx 3632..3654）。 -/
def prog_r0z1 : List Instr :=
  [.push 2 2432, .op .MLOAD, .op (.Dup ⟨4, by decide⟩), .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨2, by decide⟩), .op .MUL, .op (.Swap ⟨1, by decide⟩), .op (.Dup ⟨5, by decide⟩),
   .op .MULMOD, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .GT, .op .SUB,
   .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op .ADD, .op (.Dup ⟨0, by decide⟩),
   .op (.Swap ⟨3, by decide⟩), .op .GT, .op .SUB, .op .SUB]

def block_r0z1 : Block Artifact.submissionArtifact .Osaka 4838 prog_r0z1 :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3666 21 4838 prog_r0z1
    (by decide) (by rfl) (by rfl) (by decide)

/-- pc 4858..4880（idx 3655..3680）。 -/
def prog_r0z2 : List Instr :=
  [.push 2 2400, .op .MLOAD, .op (.Dup ⟨5, by decide⟩), .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨2, by decide⟩), .op .MUL, .op (.Swap ⟨1, by decide⟩), .op (.Dup ⟨6, by decide⟩),
   .op .MULMOD, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .GT, .op .SUB,
   .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op .ADD, .op (.Dup ⟨0, by decide⟩),
   .op (.Swap ⟨3, by decide⟩), .op .GT, .op .SUB, .op .SUB]

def block_r0z2 : Block Artifact.submissionArtifact .Osaka 4861 prog_r0z2 :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3687 21 4861 prog_r0z2
    (by decide) (by rfl) (by rfl) (by decide)

/-- pc 4881..4903（idx 3679..3699）。 -/
def prog_r0z3 : List Instr :=
  [.push 2 2368, .op .MLOAD, .op (.Dup ⟨6, by decide⟩), .op (.Dup ⟨6, by decide⟩),
   .op (.Dup ⟨2, by decide⟩), .op .MUL, .op (.Swap ⟨1, by decide⟩), .op (.Dup ⟨7, by decide⟩),
   .op .MULMOD, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .GT, .op .SUB,
   .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op .ADD, .op (.Dup ⟨0, by decide⟩),
   .op (.Swap ⟨3, by decide⟩), .op .GT, .op .SUB, .op .SUB]

def block_r0z3 : Block Artifact.submissionArtifact .Osaka 4884 prog_r0z3 :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3708 21 4884 prog_r0z3
    (by decide) (by rfl) (by rfl) (by decide)

/-- pc 4904..4913（idx 3700..3705）。 -/
def prog_r0e : List Instr :=
  [.op (.Swap ⟨4, by decide⟩), .op .POP, .push 0 0, .push 2 4917, .push 2 5157,
   .op .JUMP]

def block_r0e : Block Artifact.submissionArtifact .Osaka 4907 prog_r0e :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3729 6 4907 prog_r0e
    (by decide) (by rfl) (by rfl) (by decide)

/-- pc 5166..5184（idx 3933..3948）。 -/
def prog_redm : List Instr :=
  [.op .JUMPDEST, .op (.Dup ⟨5, by decide⟩), .op (.Dup ⟨13, by decide⟩), .op .MUL,
   .op (.Dup ⟨8, by decide⟩), .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨12, by decide⟩), .op .MULMOD, .op (.Dup ⟨8, by decide⟩), .op .ADDMOD]

def block_redm : Block Artifact.submissionArtifact .Osaka 5157 prog_redm :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3947 11 5157 prog_redm
    (by decide) (by rfl) (by rfl) (by decide)

/-- pc 5182..5209（idx 3949..3976）。 -/
def prog_reds1 : List Instr :=
  [.op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨12, by decide⟩), .op .MUL, .op (.Dup ⟨10, by decide⟩), .op (.Dup ⟨13, by decide⟩),
   .op (.Dup ⟨4, by decide⟩), .op .MULMOD, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .GT,
   .op .SUB, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op .ADD, .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨1, by decide⟩), .op .ADD, .op (.Swap ⟨10, by decide⟩), .op .POP, .op (.Dup ⟨10, by decide⟩),
   .op (.Dup ⟨1, by decide⟩), .op .GT, .op (.Swap ⟨3, by decide⟩), .op .GT, .op .SUB,
   .op .SUB, .op .ADD]

def block_reds1 : Block Artifact.submissionArtifact .Osaka 5168 prog_reds1 :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3958 27 5168 prog_reds1
    (by decide) (by rfl) (by rfl) (by decide)

/-- pc 5210..5237（idx 3977..4002）。 -/
def prog_reds2 : List Instr :=
  [.op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨13, by decide⟩), .op .MUL, .op (.Dup ⟨10, by decide⟩), .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨4, by decide⟩), .op .MULMOD, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .GT,
   .op .SUB, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op .ADD, .op (.Dup ⟨8, by decide⟩),
   .op (.Dup ⟨1, by decide⟩), .op .ADD, .op (.Swap ⟨9, by decide⟩), .op .POP, .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨1, by decide⟩), .op .GT, .op (.Swap ⟨3, by decide⟩), .op .GT, .op .SUB,
   .op .SUB, .op .ADD]

def block_reds2 : Block Artifact.submissionArtifact .Osaka 5195 prog_reds2 :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3985 27 5195 prog_reds2
    (by decide) (by rfl) (by rfl) (by decide)

/-- pc 5238..5265（idx 4002..4034）。 -/
def prog_reds3 : List Instr :=
  [.op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨14, by decide⟩), .op .MUL, .op (.Dup ⟨10, by decide⟩), .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨4, by decide⟩), .op .MULMOD, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .GT,
   .op .SUB, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op .ADD, .op (.Dup ⟨7, by decide⟩),
   .op (.Dup ⟨1, by decide⟩), .op .ADD, .op (.Swap ⟨8, by decide⟩), .op .POP, .op (.Dup ⟨8, by decide⟩),
   .op (.Dup ⟨1, by decide⟩), .op .GT, .op (.Swap ⟨3, by decide⟩), .op .GT, .op .SUB,
   .op .SUB, .op .ADD]

def block_reds3 : Block Artifact.submissionArtifact .Osaka 5222 prog_reds3 :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 4012 27 5222 prog_reds3
    (by decide) (by rfl) (by rfl) (by decide)

/-- pc 5268..5283（idx 4035..4043）。 -/
def prog_redt : List Instr :=
  [.op (.Dup ⟨8, by decide⟩), .op .ADD, .op (.Swap ⟨3, by decide⟩), .op .POP, .op .POP,
   .op (.Dup ⟨2, by decide⟩), .op (.Dup ⟨7, by decide⟩), .op .GT, .op (.Swap ⟨0, by decide⟩), .op (.Swap ⟨1, by decide⟩),
   .op .ADD, .op (.Swap ⟨5, by decide⟩), .op .POP, .op .JUMP]

def block_redt : Block Artifact.submissionArtifact .Osaka 5249 prog_redt :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 4039 14 5249 prog_redt
    (by decide) (by rfl) (by rfl) (by decide)

/-- pc 4916..4925（idx 3706..3711）。 -/
def prog_r1h : List Instr :=
  [.op .JUMPDEST, .push 2 2432, .op .MLOAD, .push 2 2464, .op .MLOAD, .push 0 0]

def block_r1h : Block Artifact.submissionArtifact .Osaka 4917 prog_r1h :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3735 6 4917 prog_r1h
    (by decide) (by rfl) (by rfl) (by decide)

/-- pc 4925..4957（idx 3713..3746）。 -/
def prog_r1d : List Instr :=
  [.op (.Dup ⟨1, by decide⟩), .op .ADD, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .ADD, .op (.Swap ⟨1, by decide⟩), .op (.Dup ⟨8, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨5, by decide⟩), .op .MUL, .op (.Swap ⟨4, by decide⟩), .op .LT, .op (.Swap ⟨2, by decide⟩), .op .MULMOD, .op .SUB, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .LT, .op .SUB, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨6, by decide⟩), .op .ADD, .op (.Swap ⟨5, by decide⟩), .op (.Dup ⟨6, by decide⟩), .op .LT, .op .SUB, .op .SUB]

def block_r1d : Block Artifact.submissionArtifact .Osaka 4928 prog_r1d :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3742 29 4928 prog_r1d
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)

/-- pc 4960..4986（idx 3747..3773）。 -/
def prog_r1c2 : List Instr :=
  [.push 2 2400, .op .MLOAD, .op (.Dup ⟨8, by decide⟩), .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨2, by decide⟩), .op .MUL, .op (.Swap ⟨1, by decide⟩), .op (.Dup ⟨4, by decide⟩),
   .op .MULMOD, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .GT, .op .SUB,
   .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op .ADD, .op (.Dup ⟨6, by decide⟩),
   .op (.Dup ⟨1, by decide⟩), .op .ADD, .op (.Swap ⟨6, by decide⟩), .op (.Dup ⟨7, by decide⟩),
   .op .LT, .op (.Swap ⟨3, by decide⟩), .op .GT, .op .SUB, .op .SUB, .op .ADD]

def block_r1c2 : Block Artifact.submissionArtifact .Osaka 4957 prog_r1c2 :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3771 27 4957 prog_r1c2
    (by decide) (by rfl) (by rfl) (by decide)

/-- pc 4992..5015（idx 3776..3800）。 -/
def prog_r1c3 : List Instr :=
  [.push 2 2368, .op .MLOAD, .op (.Dup ⟨8, by decide⟩), .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨2, by decide⟩), .op .MUL, .op (.Swap ⟨1, by decide⟩), .op (.Dup ⟨4, by decide⟩),
   .op .MULMOD, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .GT, .op .SUB,
   .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op .ADD, .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨1, by decide⟩), .op .ADD, .op (.Swap ⟨5, by decide⟩), .op (.Dup ⟨6, by decide⟩),
   .op .LT, .op (.Swap ⟨3, by decide⟩), .op .GT, .op .SUB, .op .SUB, .op .ADD]

def block_r1c3 : Block Artifact.submissionArtifact .Osaka 4986 prog_r1c3 :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3798 27 4986 prog_r1c3
    (by decide) (by rfl) (by rfl) (by decide)

/-- pc 5016..5029（idx 3801..3810）。 -/
def prog_r1e : List Instr :=
  [.op (.Dup ⟨6, by decide⟩), .op .ADD, .op (.Swap ⟨5, by decide⟩), .op (.Dup ⟨6, by decide⟩), .op .LT,
   .op (.Swap ⟨0, by decide⟩), .op .POP, .push 2 5029, .push 2 5157, .op .JUMP]

def block_r1e : Block Artifact.submissionArtifact .Osaka 5015 prog_r1e :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3825 10 5015 prog_r1e
    (by decide) (by rfl) (by rfl) (by decide)

/-- pc 5030..5039（idx 3811..3818）。 -/
def prog_r2h : List Instr :=
  [.op .JUMPDEST, .push 2 2400, .op .MLOAD, .push 2 2432, .op .MLOAD, .push 0 0]

def block_r2h : Block Artifact.submissionArtifact .Osaka 5029 prog_r2h :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3835 6 5029 prog_r2h
    (by decide) (by rfl) (by rfl) (by decide)

/-- pc 5041..5073（idx 3818..3851）。 -/
def prog_r2d : List Instr :=
  [.op (.Dup ⟨1, by decide⟩), .op .ADD, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .ADD, .op (.Swap ⟨1, by decide⟩), .op (.Dup ⟨8, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨5, by decide⟩), .op .MUL, .op (.Swap ⟨4, by decide⟩), .op .LT, .op (.Swap ⟨2, by decide⟩), .op .MULMOD, .op .SUB, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .LT, .op .SUB, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨5, by decide⟩), .op .ADD, .op (.Swap ⟨4, by decide⟩), .op (.Dup ⟨5, by decide⟩), .op .LT, .op .SUB, .op .SUB]

def block_r2d : Block Artifact.submissionArtifact .Osaka 5040 prog_r2d :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3842 29 5040 prog_r2d
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)

/-- pc 5074..5102（idx 3852..3880）。 -/
def prog_r2c3 : List Instr :=
  [.push 2 2368, .op .MLOAD, .op (.Dup ⟨8, by decide⟩), .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨2, by decide⟩), .op .MUL, .op (.Swap ⟨1, by decide⟩), .op (.Dup ⟨4, by decide⟩),
   .op .MULMOD, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .GT, .op .SUB,
   .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op .ADD, .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨1, by decide⟩), .op .ADD, .op (.Swap ⟨5, by decide⟩), .op (.Dup ⟨6, by decide⟩),
   .op .LT, .op (.Swap ⟨3, by decide⟩), .op .GT, .op .SUB, .op .SUB, .op .ADD]

def block_r2c3 : Block Artifact.submissionArtifact .Osaka 5069 prog_r2c3 :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3871 27 5069 prog_r2c3
    (by decide) (by rfl) (by rfl) (by decide)

/-- pc 5103..5120（idx 3881..3888）。 -/
def prog_r2e : List Instr :=
  [.op (.Dup ⟨6, by decide⟩), .op .ADD, .op (.Swap ⟨5, by decide⟩), .op (.Dup ⟨6, by decide⟩), .op .LT,
   .op (.Swap ⟨0, by decide⟩), .op .POP, .push 2 5112, .push 2 5157, .op .JUMP]

def block_r2e : Block Artifact.submissionArtifact .Osaka 5098 prog_r2e :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3898 10 5098 prog_r2e
    (by decide) (by rfl) (by rfl) (by decide)

/-- pc 5117..5126（idx 3889..3894）。 -/
def prog_r3h : List Instr :=
  [.op .JUMPDEST, .push 2 2368, .op .MLOAD, .push 2 2400, .op .MLOAD, .push 0 0]

def block_r3h : Block Artifact.submissionArtifact .Osaka 5112 prog_r3h :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3908 6 5112 prog_r3h
    (by decide) (by rfl) (by rfl) (by decide)

/-- pc 5128..5157（idx 3896..3926）。 -/
def prog_r3d : List Instr :=
  [.op (.Dup ⟨1, by decide⟩), .op .ADD, .op (.Swap ⟨0, by decide⟩), .op (.Dup ⟨7, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨5, by decide⟩), .op .MUL, .op (.Swap ⟨4, by decide⟩), .op .LT, .op (.Swap ⟨2, by decide⟩), .op .MULMOD, .op .SUB, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .LT, .op .SUB, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op .ADD, .op (.Swap ⟨2, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op .LT, .op .SUB, .op .SUB]

def block_r3d : Block Artifact.submissionArtifact .Osaka 5123 prog_r3d :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3915 26 5123 prog_r3d
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)

/-- pc 5158..5163（idx 3929..3932）。 -/
def prog_r3e : List Instr :=
  [.op (.Dup ⟨5, by decide⟩), .op .ADD, .op (.Swap ⟨4, by decide⟩), .op (.Dup ⟨5, by decide⟩), .op .LT,
   .push 2 5263]

def block_r3e : Block Artifact.submissionArtifact .Osaka 5149 prog_r3e :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3941 6 5149 prog_r3e
    (by decide) (by rfl) (by rfl) (by decide)

/-- pc 5283..4459（idx 4044..4072）。 -/
def prog_exit : List Instr :=
  [.op .JUMPDEST, .op (.Dup ⟨3, by decide⟩), .push 2 2208, .op .MSTORE,
   .op (.Dup ⟨2, by decide⟩), .push 2 2176, .op .MSTORE, .op (.Dup ⟨1, by decide⟩),
   .push 2 2144, .op .MSTORE, .op (.Dup ⟨0, by decide⟩), .push 2 2112, .op .MSTORE,
   .op (.Dup ⟨4, by decide⟩), .push 2 2080, .op .MSTORE, .op .POP, .op .POP, .op .POP,
   .op .POP, .op .POP, .op .POP, .op .POP, .op .POP, .op .POP, .op .POP, .op .POP,
   .push 2 4362, .op .JUMP]

def block_exit : Block Artifact.submissionArtifact .Osaka 5263 prog_exit :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 4053 29 5263 prog_exit
    (by decide) (by rfl) (by rfl) (by decide)

end Challenge.Modexp.Submission.Proofs.Fast.R4Blocks
