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
# R4 program slices and location certificates

Re-derived from the artifact image (Phase 23): every slice now sits at its true
instruction index, and the row tails carry the true return addresses — row 0
returns to 4687 (the row-1 head), row 1 to 4799, row 2 to 4882, row 3 pushes
5031 and falls into RED at 4927; the exit jumps to 4198.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.R4Blocks

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel WindowTwentyOneBinding

/-- The entry and first diagonal (pc 4579..4608, idx 3631..3657). -/
def prog_prodiag : List Instr :=
  [.op .JUMPDEST, .op (.Dup ⟨7, by decide⟩), .push 0 0, .op .MLOAD,
   .op (.Dup ⟨14, by decide⟩), .op (.Dup ⟨14, by decide⟩), .op (.Dup ⟨12, by decide⟩),
   .push 2 2464, .op .MLOAD, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨0, by decide⟩), .op .ADD,
   .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨0, by decide⟩), .op .MUL,
   .op (.Dup ⟨13, by decide⟩), .op (.Dup ⟨0, by decide⟩), .op (.Swap ⟨3, by decide⟩),
   .op (.Dup ⟨0, by decide⟩), .op .MULMOD, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩),
   .op .GT, .op (.Dup ⟨2, by decide⟩), .op (.Swap ⟨1, by decide⟩), .op .SUB, .op .SUB]

def block_prodiag : Block Artifact.submissionArtifact .Osaka 4579 prog_prodiag :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3631 27 4579 prog_prodiag
    (by decide) (by rfl) (by rfl) (by decide)

/-- Row 0, word 1 (pc 4608..4631, idx 3658..3678). -/
def prog_r0z1 : List Instr :=
  [.push 2 2432, .op .MLOAD, .op (.Dup ⟨4, by decide⟩), .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨2, by decide⟩), .op .MUL, .op (.Swap ⟨1, by decide⟩), .op (.Dup ⟨5, by decide⟩),
   .op .MULMOD, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .GT, .op .SUB,
   .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op .ADD, .op (.Dup ⟨0, by decide⟩),
   .op (.Swap ⟨3, by decide⟩), .op .GT, .op .SUB, .op .SUB]

def block_r0z1 : Block Artifact.submissionArtifact .Osaka 4608 prog_r0z1 :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3658 21 4608 prog_r0z1
    (by decide) (by rfl) (by rfl) (by decide)

/-- Row 0, word 2 (pc 4631..4654, idx 3679..3699). -/
def prog_r0z2 : List Instr :=
  [.push 2 2400, .op .MLOAD, .op (.Dup ⟨5, by decide⟩), .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨2, by decide⟩), .op .MUL, .op (.Swap ⟨1, by decide⟩), .op (.Dup ⟨6, by decide⟩),
   .op .MULMOD, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .GT, .op .SUB,
   .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op .ADD, .op (.Dup ⟨0, by decide⟩),
   .op (.Swap ⟨3, by decide⟩), .op .GT, .op .SUB, .op .SUB]

def block_r0z2 : Block Artifact.submissionArtifact .Osaka 4631 prog_r0z2 :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3679 21 4631 prog_r0z2
    (by decide) (by rfl) (by rfl) (by decide)

/-- Row 0, word 3 (pc 4654..4677, idx 3700..3720). -/
def prog_r0z3 : List Instr :=
  [.push 2 2368, .op .MLOAD, .op (.Dup ⟨6, by decide⟩), .op (.Dup ⟨6, by decide⟩),
   .op (.Dup ⟨2, by decide⟩), .op .MUL, .op (.Swap ⟨1, by decide⟩), .op (.Dup ⟨7, by decide⟩),
   .op .MULMOD, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .GT, .op .SUB,
   .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op .ADD, .op (.Dup ⟨0, by decide⟩),
   .op (.Swap ⟨3, by decide⟩), .op .GT, .op .SUB, .op .SUB]

def block_r0z3 : Block Artifact.submissionArtifact .Osaka 4654 prog_r0z3 :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3700 21 4654 prog_r0z3
    (by decide) (by rfl) (by rfl) (by decide)

/-- Row 0 tail: push the return address 4687 and v = 0, then jump to RED (4927). -/
def prog_r0e : List Instr :=
  [.op (.Swap ⟨4, by decide⟩), .op .POP, .push 0 0, .push 2 4687, .push 2 4927,
   .op .JUMP]

def block_r0e : Block Artifact.submissionArtifact .Osaka 4677 prog_r0e :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3721 6 4677 prog_r0e
    (by decide) (by rfl) (by rfl) (by decide)

/-- RED entry (pc 4927..4938, idx 3939..3949). -/
def prog_redm : List Instr :=
  [.op .JUMPDEST, .op (.Dup ⟨5, by decide⟩), .op (.Dup ⟨13, by decide⟩), .op .MUL,
   .op (.Dup ⟨8, by decide⟩), .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨12, by decide⟩), .op .MULMOD, .op (.Dup ⟨8, by decide⟩), .op .ADDMOD]

def block_redm : Block Artifact.submissionArtifact .Osaka 4927 prog_redm :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3939 11 4927 prog_redm
    (by decide) (by rfl) (by rfl) (by decide)

/-- RED slice 1 (pc 4938..4965, idx 3950..3976). -/
def prog_reds1 : List Instr :=
  [.op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨12, by decide⟩), .op .MUL, .op (.Dup ⟨10, by decide⟩), .op (.Dup ⟨13, by decide⟩),
   .op (.Dup ⟨4, by decide⟩), .op .MULMOD, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .GT,
   .op .SUB, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op .ADD, .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨1, by decide⟩), .op .ADD, .op (.Swap ⟨10, by decide⟩), .op .POP, .op (.Dup ⟨10, by decide⟩),
   .op (.Dup ⟨1, by decide⟩), .op .GT, .op (.Swap ⟨3, by decide⟩), .op .GT, .op .SUB,
   .op .SUB, .op .ADD]

def block_reds1 : Block Artifact.submissionArtifact .Osaka 4938 prog_reds1 :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3950 27 4938 prog_reds1
    (by decide) (by rfl) (by rfl) (by decide)

/-- RED slice 2 (pc 4965..4992, idx 3977..4003). -/
def prog_reds2 : List Instr :=
  [.op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨13, by decide⟩), .op .MUL, .op (.Dup ⟨10, by decide⟩), .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨4, by decide⟩), .op .MULMOD, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .GT,
   .op .SUB, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op .ADD, .op (.Dup ⟨8, by decide⟩),
   .op (.Dup ⟨1, by decide⟩), .op .ADD, .op (.Swap ⟨9, by decide⟩), .op .POP, .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨1, by decide⟩), .op .GT, .op (.Swap ⟨3, by decide⟩), .op .GT, .op .SUB,
   .op .SUB, .op .ADD]

def block_reds2 : Block Artifact.submissionArtifact .Osaka 4965 prog_reds2 :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3977 27 4965 prog_reds2
    (by decide) (by rfl) (by rfl) (by decide)

/-- RED slice 3 (pc 4992..5019, idx 4004..4030). -/
def prog_reds3 : List Instr :=
  [.op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨14, by decide⟩), .op .MUL, .op (.Dup ⟨10, by decide⟩), .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨4, by decide⟩), .op .MULMOD, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .GT,
   .op .SUB, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op .ADD, .op (.Dup ⟨7, by decide⟩),
   .op (.Dup ⟨1, by decide⟩), .op .ADD, .op (.Swap ⟨8, by decide⟩), .op .POP, .op (.Dup ⟨8, by decide⟩),
   .op (.Dup ⟨1, by decide⟩), .op .GT, .op (.Swap ⟨3, by decide⟩), .op .GT, .op .SUB,
   .op .SUB, .op .ADD]

def block_reds3 : Block Artifact.submissionArtifact .Osaka 4992 prog_reds3 :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 4004 27 4992 prog_reds3
    (by decide) (by rfl) (by rfl) (by decide)

/-- RED tail (pc 5019.., idx 4031..4041): returns to the `ret` under the window. -/
def prog_redt : List Instr :=
  [.op (.Dup ⟨8, by decide⟩), .op .ADD, .op (.Swap ⟨3, by decide⟩), .op .POP, .op .POP,
   .op (.Swap ⟨5, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .LT,
   .op .ADD, .op (.Swap ⟨4, by decide⟩), .op .JUMP]

def block_redt : Block Artifact.submissionArtifact .Osaka 5019 prog_redt :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 4031 11 5019 prog_redt
    (by decide) (by rfl) (by rfl) (by decide)

/-- pc 4687..4697（idx 3727..3732）: the return landing of the row-1 head trampoline. -/
def prog_r1h : List Instr :=
  [.op .JUMPDEST, .push 2 2432, .op .MLOAD, .push 2 2464, .op .MLOAD, .push 0 0]

def block_r1h : Block Artifact.submissionArtifact .Osaka 4687 prog_r1h :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3727 6 4687 prog_r1h
    (by decide) (by rfl) (by rfl) (by decide)

/-- Row 1 diagonal (pc 4698..4727, idx 3734..3762). -/
def prog_r1d : List Instr :=
  [.op (.Dup ⟨1, by decide⟩), .op .ADD, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .ADD, .op (.Swap ⟨1, by decide⟩), .op (.Dup ⟨8, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨5, by decide⟩), .op .MUL, .op (.Swap ⟨4, by decide⟩), .op .LT, .op (.Swap ⟨2, by decide⟩), .op .MULMOD, .op .SUB, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .LT, .op .SUB, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨6, by decide⟩), .op .ADD, .op (.Swap ⟨5, by decide⟩), .op (.Dup ⟨6, by decide⟩), .op .LT, .op .SUB, .op .SUB]

def block_r1d : Block Artifact.submissionArtifact .Osaka 4698 prog_r1d :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3734 29 4698 prog_r1d
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)

/-- Row 1, word 2 (pc 4727..4756, idx 3763..3789). -/
def prog_r1c2 : List Instr :=
  [.push 2 2400, .op .MLOAD, .op (.Dup ⟨8, by decide⟩), .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨2, by decide⟩), .op .MUL, .op (.Swap ⟨1, by decide⟩), .op (.Dup ⟨4, by decide⟩),
   .op .MULMOD, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .GT, .op .SUB,
   .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op .ADD, .op (.Dup ⟨6, by decide⟩),
   .op (.Dup ⟨1, by decide⟩), .op .ADD, .op (.Swap ⟨6, by decide⟩), .op (.Dup ⟨7, by decide⟩),
   .op .LT, .op (.Swap ⟨3, by decide⟩), .op .GT, .op .SUB, .op .SUB, .op .ADD]

def block_r1c2 : Block Artifact.submissionArtifact .Osaka 4727 prog_r1c2 :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3763 27 4727 prog_r1c2
    (by decide) (by rfl) (by rfl) (by decide)

/-- Row 1, word 3 (pc 4756..4785, idx 3790..3816). -/
def prog_r1c3 : List Instr :=
  [.push 2 2368, .op .MLOAD, .op (.Dup ⟨8, by decide⟩), .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨2, by decide⟩), .op .MUL, .op (.Swap ⟨1, by decide⟩), .op (.Dup ⟨4, by decide⟩),
   .op .MULMOD, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .GT, .op .SUB,
   .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op .ADD, .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨1, by decide⟩), .op .ADD, .op (.Swap ⟨5, by decide⟩), .op (.Dup ⟨6, by decide⟩),
   .op .LT, .op (.Swap ⟨3, by decide⟩), .op .GT, .op .SUB, .op .SUB, .op .ADD]

def block_r1c3 : Block Artifact.submissionArtifact .Osaka 4756 prog_r1c3 :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3790 27 4756 prog_r1c3
    (by decide) (by rfl) (by rfl) (by decide)

/-- Row 1 tail: return address 4799, then RED. -/
def prog_r1e : List Instr :=
  [.op (.Dup ⟨6, by decide⟩), .op .ADD, .op (.Swap ⟨5, by decide⟩), .op (.Dup ⟨6, by decide⟩), .op .LT,
   .op (.Swap ⟨0, by decide⟩), .op .POP, .push 2 4799, .push 2 4927, .op .JUMP]

def block_r1e : Block Artifact.submissionArtifact .Osaka 4785 prog_r1e :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3817 10 4785 prog_r1e
    (by decide) (by rfl) (by rfl) (by decide)

/-- pc 4799..4809（idx 3827..3832）: the return landing of the row-2 head trampoline. -/
def prog_r2h : List Instr :=
  [.op .JUMPDEST, .push 2 2400, .op .MLOAD, .push 2 2432, .op .MLOAD, .push 0 0]

def block_r2h : Block Artifact.submissionArtifact .Osaka 4799 prog_r2h :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3827 6 4799 prog_r2h
    (by decide) (by rfl) (by rfl) (by decide)

/-- Row 2 diagonal (pc 4810..4839, idx 3834..3862). -/
def prog_r2d : List Instr :=
  [.op (.Dup ⟨1, by decide⟩), .op .ADD, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .ADD, .op (.Swap ⟨1, by decide⟩), .op (.Dup ⟨8, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨5, by decide⟩), .op .MUL, .op (.Swap ⟨4, by decide⟩), .op .LT, .op (.Swap ⟨2, by decide⟩), .op .MULMOD, .op .SUB, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .LT, .op .SUB, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨5, by decide⟩), .op .ADD, .op (.Swap ⟨4, by decide⟩), .op (.Dup ⟨5, by decide⟩), .op .LT, .op .SUB, .op .SUB]

def block_r2d : Block Artifact.submissionArtifact .Osaka 4810 prog_r2d :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3834 29 4810 prog_r2d
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)

/-- Row 2, word 3 (pc 4839..4868, idx 3863..3889). -/
def prog_r2c3 : List Instr :=
  [.push 2 2368, .op .MLOAD, .op (.Dup ⟨8, by decide⟩), .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨2, by decide⟩), .op .MUL, .op (.Swap ⟨1, by decide⟩), .op (.Dup ⟨4, by decide⟩),
   .op .MULMOD, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .GT, .op .SUB,
   .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op .ADD, .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨1, by decide⟩), .op .ADD, .op (.Swap ⟨5, by decide⟩), .op (.Dup ⟨6, by decide⟩),
   .op .LT, .op (.Swap ⟨3, by decide⟩), .op .GT, .op .SUB, .op .SUB, .op .ADD]

def block_r2c3 : Block Artifact.submissionArtifact .Osaka 4839 prog_r2c3 :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3863 27 4839 prog_r2c3
    (by decide) (by rfl) (by rfl) (by decide)

/-- Row 2 tail: return address 4882, then RED. -/
def prog_r2e : List Instr :=
  [.op (.Dup ⟨6, by decide⟩), .op .ADD, .op (.Swap ⟨5, by decide⟩), .op (.Dup ⟨6, by decide⟩), .op .LT,
   .op (.Swap ⟨0, by decide⟩), .op .POP, .push 2 4882, .push 2 4927, .op .JUMP]

def block_r2e : Block Artifact.submissionArtifact .Osaka 4868 prog_r2e :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3890 10 4868 prog_r2e
    (by decide) (by rfl) (by rfl) (by decide)

/-- pc 4882..4892（idx 3900..3905）: the return landing of the row-3 head trampoline. -/
def prog_r3h : List Instr :=
  [.op .JUMPDEST, .push 2 2368, .op .MLOAD, .push 2 2400, .op .MLOAD, .push 0 0]

def block_r3h : Block Artifact.submissionArtifact .Osaka 4882 prog_r3h :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3900 6 4882 prog_r3h
    (by decide) (by rfl) (by rfl) (by decide)

/-- Row 3 diagonal (pc 4893..4919, idx 3907..3932). -/
def prog_r3d : List Instr :=
  [.op (.Dup ⟨1, by decide⟩), .op .ADD, .op (.Swap ⟨0, by decide⟩), .op (.Dup ⟨7, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨5, by decide⟩), .op .MUL, .op (.Swap ⟨4, by decide⟩), .op .LT, .op (.Swap ⟨2, by decide⟩), .op .MULMOD, .op .SUB, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .LT, .op .SUB, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op .ADD, .op (.Swap ⟨2, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op .LT, .op .SUB, .op .SUB]

def block_r3d : Block Artifact.submissionArtifact .Osaka 4893 prog_r3d :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3907 26 4893 prog_r3d
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)

/-- Row 3 tail: pushes the exit address 5031 and falls into RED (4927). -/
def prog_r3e : List Instr :=
  [.op (.Dup ⟨5, by decide⟩), .op .ADD, .op (.Swap ⟨4, by decide⟩), .op (.Dup ⟨5, by decide⟩), .op .LT,
   .push 2 5031]

def block_r3e : Block Artifact.submissionArtifact .Osaka 4919 prog_r3e :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3933 6 4919 prog_r3e
    (by decide) (by rfl) (by rfl) (by decide)

/-- pc 5031..5061（idx 4043..4061）。

Rider: the five stores consume the top five stack values in stack order instead of `DUP`ing
them.  The slots the `DUP`s vacated are absorbed into the neighbouring `PUSH` by widening it
and left-padding the immediate with zero bytes, so the pcs and the instruction boundaries are
still preserved, and the pushed values are bit-identical — but the padding now costs nothing,
where a `JUMPDEST` cost 1 gas on every execution.  The five target words `0x820 .. 0x8a0` are
pairwise disjoint and word-aligned, so the reordered writes commute
(`writeBytes_comm_disjoint`), and the highest touched word is unchanged, so the
memory-expansion charge is identical.  The eleven incoming values are dead either way: the
block leaves with stack depth 0 and jumps to `0x1066` (4198).

Ten instructions are deleted, so every instruction index after 3705 shifts down by 10; the
pcs, and hence every jump destination and every pushed code pointer, are untouched. -/
def prog_exit : List Instr :=
  [.op .JUMPDEST, .push 2 2112, .op .MSTORE, .push 2 2144, .op .MSTORE, .push 2 2176, .op .MSTORE, .push 2 2208, .op .MSTORE, .push 2 2080, .op .MSTORE, .op .POP, .op .POP, .op .POP, .op .POP, .op .POP, .op .POP, .push 2 4198, .op .JUMP]

def block_exit : Block Artifact.submissionArtifact .Osaka 5031 prog_exit :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 4043 19 5031 prog_exit
    (by decide) (by rfl) (by rfl) (by decide)

end Challenge.Modexp.Submission.Proofs.Fast.R4Blocks
