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
returns to 4688 (the row-1 head), row 1 to 4800, row 2 to 4883, row 3 pushes
5032 and falls into RED at 4928; the tail at 5032 either stores the window (`st4`) or first
subtracts the modulus (`rare4`), then loops back to 4580 or leaves through 4248.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.R4Blocks

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel WindowTwentyOneBinding

/-- The entry and first diagonal (pc 4579..4608, idx 3631..3657).  P1: the entry copies the
Montgomery inverse from frame word 12 (`DUP12`), modulus[32] from word 5 (`DUP7`) and
modulus[64] from word 8 (`DUP11`). -/
def prog_prodiag : List Instr :=
  [.op .JUMPDEST, .op (.Dup ⟨11, by decide⟩), .push 0 0, .op .MLOAD,
   .op (.Dup ⟨6, by decide⟩), .op (.Dup ⟨10, by decide⟩), .op (.Dup ⟨12, by decide⟩),
   .push 2 2208, .op .MLOAD, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨0, by decide⟩), .op .ADD,
   .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨0, by decide⟩), .op .MUL,
   .op (.Dup ⟨13, by decide⟩), .op (.Dup ⟨0, by decide⟩), .op (.Swap ⟨3, by decide⟩),
   .op (.Dup ⟨0, by decide⟩), .op .MULMOD, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩),
   .op .GT, .op (.Dup ⟨2, by decide⟩), .op (.Swap ⟨1, by decide⟩), .op .SUB, .op .SUB]

def block_prodiag : Block Artifact.submissionArtifact .Osaka 4561 prog_prodiag :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3558 27 4561 prog_prodiag
    (by decide) (by rfl) (by rfl) (by decide)

/-- Row 0, word 1 (pc 4608..4631, idx 3658..3678). -/
def prog_r0z1 : List Instr :=
  [.push 2 2176, .op .MLOAD, .op (.Dup ⟨4, by decide⟩), .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨2, by decide⟩), .op .MUL, .op (.Swap ⟨1, by decide⟩), .op (.Dup ⟨5, by decide⟩),
   .op .MULMOD, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .GT, .op .SUB,
   .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op .ADD, .op (.Dup ⟨0, by decide⟩),
   .op (.Swap ⟨3, by decide⟩), .op .GT, .op .SUB, .op .SUB]

def block_r0z1 : Block Artifact.submissionArtifact .Osaka 4590 prog_r0z1 :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3585 21 4590 prog_r0z1
    (by decide) (by rfl) (by rfl) (by decide)

/-- Row 0, word 2 (pc 4631..4654, idx 3679..3699). -/
def prog_r0z2 : List Instr :=
  [.push 2 2144, .op .MLOAD, .op (.Dup ⟨5, by decide⟩), .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨2, by decide⟩), .op .MUL, .op (.Swap ⟨1, by decide⟩), .op (.Dup ⟨6, by decide⟩),
   .op .MULMOD, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .GT, .op .SUB,
   .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op .ADD, .op (.Dup ⟨0, by decide⟩),
   .op (.Swap ⟨3, by decide⟩), .op .GT, .op .SUB, .op .SUB]

def block_r0z2 : Block Artifact.submissionArtifact .Osaka 4613 prog_r0z2 :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3606 21 4613 prog_r0z2
    (by decide) (by rfl) (by rfl) (by decide)

/-- Row 0, word 3 (pc 4654..4677, idx 3700..3720). -/
def prog_r0z3 : List Instr :=
  [.push 2 2112, .op .MLOAD, .op (.Dup ⟨6, by decide⟩), .op (.Dup ⟨6, by decide⟩),
   .op (.Dup ⟨2, by decide⟩), .op .MUL, .op (.Swap ⟨1, by decide⟩), .op (.Dup ⟨7, by decide⟩),
   .op .MULMOD, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .GT, .op .SUB,
   .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op .ADD, .op (.Dup ⟨0, by decide⟩),
   .op (.Swap ⟨3, by decide⟩), .op .GT, .op .SUB, .op .SUB]

def block_r0z3 : Block Artifact.submissionArtifact .Osaka 4636 prog_r0z3 :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3627 21 4636 prog_r0z3
    (by decide) (by rfl) (by rfl) (by decide)

/-- Row 0 tail: push the return address 4687 and v = 0, then jump to RED (4927). -/
def prog_r0e : List Instr :=
  [.op (.Swap ⟨4, by decide⟩), .op .POP, .push 0 0, .push 2 4669, .push 2 4909,
   .op .JUMP]

def block_r0e : Block Artifact.submissionArtifact .Osaka 4659 prog_r0e :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3648 6 4659 prog_r0e
    (by decide) (by rfl) (by rfl) (by decide)

/-- RED entry (pc 4927..4938, idx 3939..3949). -/
def prog_redm : List Instr :=
  [.op .JUMPDEST, .op (.Dup ⟨5, by decide⟩), .op (.Dup ⟨13, by decide⟩), .op .MUL,
   .op (.Dup ⟨8, by decide⟩), .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨12, by decide⟩), .op .MULMOD, .op (.Dup ⟨8, by decide⟩), .op .ADDMOD]

def block_redm : Block Artifact.submissionArtifact .Osaka 4909 prog_redm :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3866 11 4909 prog_redm
    (by decide) (by rfl) (by rfl) (by decide)

/-- RED slice 1 (pc 4938..4965, idx 3950..3976). -/
def prog_reds1 : List Instr :=
  [.op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨12, by decide⟩), .op .MUL, .op (.Dup ⟨10, by decide⟩), .op (.Dup ⟨13, by decide⟩),
   .op (.Dup ⟨4, by decide⟩), .op .MULMOD, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .GT,
   .op .SUB, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op .ADD, .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨1, by decide⟩), .op .ADD, .op (.Swap ⟨10, by decide⟩), .op .POP, .op (.Dup ⟨10, by decide⟩),
   .op (.Dup ⟨1, by decide⟩), .op .GT, .op (.Swap ⟨3, by decide⟩), .op .GT, .op .SUB,
   .op .SUB, .op .ADD]

def block_reds1 : Block Artifact.submissionArtifact .Osaka 4920 prog_reds1 :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3877 27 4920 prog_reds1
    (by decide) (by rfl) (by rfl) (by decide)

/-- RED slice 2 (pc 4965..4992, idx 3977..4003). -/
def prog_reds2 : List Instr :=
  [.op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨13, by decide⟩), .op .MUL, .op (.Dup ⟨10, by decide⟩), .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨4, by decide⟩), .op .MULMOD, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .GT,
   .op .SUB, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op .ADD, .op (.Dup ⟨8, by decide⟩),
   .op (.Dup ⟨1, by decide⟩), .op .ADD, .op (.Swap ⟨9, by decide⟩), .op .POP, .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨1, by decide⟩), .op .GT, .op (.Swap ⟨3, by decide⟩), .op .GT, .op .SUB,
   .op .SUB, .op .ADD]

def block_reds2 : Block Artifact.submissionArtifact .Osaka 4947 prog_reds2 :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3904 27 4947 prog_reds2
    (by decide) (by rfl) (by rfl) (by decide)

/-- RED slice 3 (pc 4992..5019, idx 4004..4030). -/
def prog_reds3 : List Instr :=
  [.op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨14, by decide⟩), .op .MUL, .op (.Dup ⟨10, by decide⟩), .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨4, by decide⟩), .op .MULMOD, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .GT,
   .op .SUB, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op .ADD, .op (.Dup ⟨7, by decide⟩),
   .op (.Dup ⟨1, by decide⟩), .op .ADD, .op (.Swap ⟨8, by decide⟩), .op .POP, .op (.Dup ⟨8, by decide⟩),
   .op (.Dup ⟨1, by decide⟩), .op .GT, .op (.Swap ⟨3, by decide⟩), .op .GT, .op .SUB,
   .op .SUB, .op .ADD]

def block_reds3 : Block Artifact.submissionArtifact .Osaka 4974 prog_reds3 :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3931 27 4974 prog_reds3
    (by decide) (by rfl) (by rfl) (by decide)

/-- RED tail (pc 5019.., idx 4031..4041): returns to the `ret` under the window. -/
def prog_redt : List Instr :=
  [.op (.Dup ⟨8, by decide⟩), .op .ADD, .op (.Swap ⟨3, by decide⟩), .op .POP, .op .POP,
   .op (.Swap ⟨5, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .LT,
   .op .ADD, .op (.Swap ⟨4, by decide⟩), .op .JUMP]

def block_redt : Block Artifact.submissionArtifact .Osaka 5001 prog_redt :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3958 11 5001 prog_redt
    (by decide) (by rfl) (by rfl) (by decide)

/-- pc 4687..4697（idx 3727..3732）: the return landing of the row-1 head trampoline. -/
def prog_r1h : List Instr :=
  [.op .JUMPDEST, .push 2 2176, .op .MLOAD, .push 2 2208, .op .MLOAD, .push 0 0]

def block_r1h : Block Artifact.submissionArtifact .Osaka 4669 prog_r1h :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3654 6 4669 prog_r1h
    (by decide) (by rfl) (by rfl) (by decide)

/-- Row 1 diagonal (pc 4698..4727, idx 3734..3762). -/
def prog_r1d : List Instr :=
  [.op (.Dup ⟨1, by decide⟩), .op .ADD, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .ADD, .op (.Swap ⟨1, by decide⟩), .op (.Dup ⟨8, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨5, by decide⟩), .op .MUL, .op (.Swap ⟨4, by decide⟩), .op .LT, .op (.Swap ⟨2, by decide⟩), .op .MULMOD, .op .SUB, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .LT, .op .SUB, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨6, by decide⟩), .op .ADD, .op (.Swap ⟨5, by decide⟩), .op (.Dup ⟨6, by decide⟩), .op .LT, .op .SUB, .op .SUB]

def block_r1d : Block Artifact.submissionArtifact .Osaka 4680 prog_r1d :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3661 29 4680 prog_r1d
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)

/-- Row 1, word 2 (pc 4727..4756, idx 3763..3789). -/
def prog_r1c2 : List Instr :=
  [.push 2 2144, .op .MLOAD, .op (.Dup ⟨8, by decide⟩), .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨2, by decide⟩), .op .MUL, .op (.Swap ⟨1, by decide⟩), .op (.Dup ⟨4, by decide⟩),
   .op .MULMOD, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .GT, .op .SUB,
   .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op .ADD, .op (.Dup ⟨6, by decide⟩),
   .op (.Dup ⟨1, by decide⟩), .op .ADD, .op (.Swap ⟨6, by decide⟩), .op (.Dup ⟨7, by decide⟩),
   .op .LT, .op (.Swap ⟨3, by decide⟩), .op .GT, .op .SUB, .op .SUB, .op .ADD]

def block_r1c2 : Block Artifact.submissionArtifact .Osaka 4709 prog_r1c2 :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3690 27 4709 prog_r1c2
    (by decide) (by rfl) (by rfl) (by decide)

/-- Row 1, word 3 (pc 4756..4785, idx 3790..3816). -/
def prog_r1c3 : List Instr :=
  [.push 2 2112, .op .MLOAD, .op (.Dup ⟨8, by decide⟩), .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨2, by decide⟩), .op .MUL, .op (.Swap ⟨1, by decide⟩), .op (.Dup ⟨4, by decide⟩),
   .op .MULMOD, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .GT, .op .SUB,
   .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op .ADD, .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨1, by decide⟩), .op .ADD, .op (.Swap ⟨5, by decide⟩), .op (.Dup ⟨6, by decide⟩),
   .op .LT, .op (.Swap ⟨3, by decide⟩), .op .GT, .op .SUB, .op .SUB, .op .ADD]

def block_r1c3 : Block Artifact.submissionArtifact .Osaka 4738 prog_r1c3 :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3717 27 4738 prog_r1c3
    (by decide) (by rfl) (by rfl) (by decide)

/-- Row 1 tail: return address 4799, then RED. -/
def prog_r1e : List Instr :=
  [.op (.Dup ⟨6, by decide⟩), .op .ADD, .op (.Swap ⟨5, by decide⟩), .op (.Dup ⟨6, by decide⟩), .op .LT,
   .op (.Swap ⟨0, by decide⟩), .op .POP, .push 2 4781, .push 2 4909, .op .JUMP]

def block_r1e : Block Artifact.submissionArtifact .Osaka 4767 prog_r1e :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3744 10 4767 prog_r1e
    (by decide) (by rfl) (by rfl) (by decide)

/-- pc 4799..4809（idx 3827..3832）: the return landing of the row-2 head trampoline. -/
def prog_r2h : List Instr :=
  [.op .JUMPDEST, .push 2 2144, .op .MLOAD, .push 2 2176, .op .MLOAD, .push 0 0]

def block_r2h : Block Artifact.submissionArtifact .Osaka 4781 prog_r2h :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3754 6 4781 prog_r2h
    (by decide) (by rfl) (by rfl) (by decide)

/-- Row 2 diagonal (pc 4810..4839, idx 3834..3862). -/
def prog_r2d : List Instr :=
  [.op (.Dup ⟨1, by decide⟩), .op .ADD, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .ADD, .op (.Swap ⟨1, by decide⟩), .op (.Dup ⟨8, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨5, by decide⟩), .op .MUL, .op (.Swap ⟨4, by decide⟩), .op .LT, .op (.Swap ⟨2, by decide⟩), .op .MULMOD, .op .SUB, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .LT, .op .SUB, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨5, by decide⟩), .op .ADD, .op (.Swap ⟨4, by decide⟩), .op (.Dup ⟨5, by decide⟩), .op .LT, .op .SUB, .op .SUB]

def block_r2d : Block Artifact.submissionArtifact .Osaka 4792 prog_r2d :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3761 29 4792 prog_r2d
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)

/-- Row 2, word 3 (pc 4839..4868, idx 3863..3889). -/
def prog_r2c3 : List Instr :=
  [.push 2 2112, .op .MLOAD, .op (.Dup ⟨8, by decide⟩), .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨2, by decide⟩), .op .MUL, .op (.Swap ⟨1, by decide⟩), .op (.Dup ⟨4, by decide⟩),
   .op .MULMOD, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .GT, .op .SUB,
   .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op .ADD, .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨1, by decide⟩), .op .ADD, .op (.Swap ⟨5, by decide⟩), .op (.Dup ⟨6, by decide⟩),
   .op .LT, .op (.Swap ⟨3, by decide⟩), .op .GT, .op .SUB, .op .SUB, .op .ADD]

def block_r2c3 : Block Artifact.submissionArtifact .Osaka 4821 prog_r2c3 :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3790 27 4821 prog_r2c3
    (by decide) (by rfl) (by rfl) (by decide)

/-- Row 2 tail: return address 4882, then RED. -/
def prog_r2e : List Instr :=
  [.op (.Dup ⟨6, by decide⟩), .op .ADD, .op (.Swap ⟨5, by decide⟩), .op (.Dup ⟨6, by decide⟩), .op .LT,
   .op (.Swap ⟨0, by decide⟩), .op .POP, .push 2 4864, .push 2 4909, .op .JUMP]

def block_r2e : Block Artifact.submissionArtifact .Osaka 4850 prog_r2e :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3817 10 4850 prog_r2e
    (by decide) (by rfl) (by rfl) (by decide)

/-- pc 4882..4892（idx 3900..3905）: the return landing of the row-3 head trampoline. -/
def prog_r3h : List Instr :=
  [.op .JUMPDEST, .push 2 2112, .op .MLOAD, .push 2 2144, .op .MLOAD, .push 0 0]

def block_r3h : Block Artifact.submissionArtifact .Osaka 4864 prog_r3h :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3827 6 4864 prog_r3h
    (by decide) (by rfl) (by rfl) (by decide)

/-- Row 3 diagonal (pc 4893..4919, idx 3907..3932). -/
def prog_r3d : List Instr :=
  [.op (.Dup ⟨1, by decide⟩), .op .ADD, .op (.Swap ⟨0, by decide⟩), .op (.Dup ⟨7, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨5, by decide⟩), .op .MUL, .op (.Swap ⟨4, by decide⟩), .op .LT, .op (.Swap ⟨2, by decide⟩), .op .MULMOD, .op .SUB, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .LT, .op .SUB, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op .ADD, .op (.Swap ⟨2, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op .LT, .op .SUB, .op .SUB]

def block_r3d : Block Artifact.submissionArtifact .Osaka 4875 prog_r3d :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3834 26 4875 prog_r3d
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)

/-- Row 3 tail: pushes the exit address 5031 and falls into RED (4927). -/
def prog_r3e : List Instr :=
  [.op (.Dup ⟨5, by decide⟩), .op .ADD, .op (.Swap ⟨4, by decide⟩), .op (.Dup ⟨5, by decide⟩), .op .LT,
   .push 2 5012]

def block_r3e : Block Artifact.submissionArtifact .Osaka 4901 prog_r3e :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3860 6 4901 prog_r3e
    (by decide) (by rfl) (by rfl) (by decide)

/-- The n=4 tail head (pc 5032, idx 3975): a nonzero overflow word `t4` (`DUP5`) takes `rare4`. -/
def prog_tail : List Instr :=
  [.op .JUMPDEST, .op (.Dup ⟨4, by decide⟩), .push 2 5057, .op .JUMPI]

def block_tail : Block Artifact.submissionArtifact .Osaka 5012 prog_tail :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3969 4 5012 prog_tail
    (by decide) (by rfl) (by rfl) (by decide)

/-- `st4` (pc 5038, idx 3979): store `t3..t0` at 0x840..0x8a0 and the overflow word at 0x820,
drop the six constants, decrement the square counter in the frame's `pdst` slot and jump back
into R4 (4580) while the old count is nonzero. -/
def prog_st4 : List Instr :=
  [.op .JUMPDEST, .push 2 2112, .op .MSTORE, .push 2 2144, .op .MSTORE, .push 2 2176, .op .MSTORE,
   .push 2 2208, .op .MSTORE, .push 2 2080, .op .MSTORE, .op .POP, .op .POP, .op .POP, .op .POP,
   .op .POP, .op .POP, .op (.Dup ⟨14, by decide⟩), .op (.Dup ⟨6, by decide⟩), .op .ADD,
   .op (.Swap ⟨14, by decide⟩), .push 2 4561, .op .JUMPI]

def block_st4 : Block Artifact.submissionArtifact .Osaka 5018 prog_st4 :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3973 23 5018 prog_st4
    (by decide) (by rfl) (by rfl) (by decide)

/-- The last square leaves R4 through `m4j` (4248), the `JUMPDEST` inside `last`. -/
def prog_m4 : List Instr := [.push 2 4234, .op .JUMP]

def block_m4 : Block Artifact.submissionArtifact .Osaka 5053 prog_m4 :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3996 2 5053 prog_m4
    (by decide) (by rfl) (by rfl) (by decide)

/-- `rare4` (pc 5077, idx 4004): subtract the modulus `n0..n3` from `t0..t3` on the stack with a
borrow chain, zero the overflow word and return to `st4`. -/
def prog_rare4 : List Instr :=
  [.op .JUMPDEST, .op (.Dup ⟨6, by decide⟩), .op (.Dup ⟨4, by decide⟩), .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨1, by decide⟩), .op .SUB, .op (.Swap ⟨5, by decide⟩), .op .POP, .op .LT,
   .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨9, by decide⟩), .op .ADD, .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨5, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .SUB,
   .op (.Swap ⟨6, by decide⟩), .op .POP, .op .LT, .op (.Swap ⟨1, by decide⟩), .op .GT, .op .OR,
   .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨10, by decide⟩), .op .ADD, .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨4, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .SUB,
   .op (.Swap ⟨5, by decide⟩), .op .POP, .op .LT, .op (.Swap ⟨1, by decide⟩), .op .GT, .op .OR,
   .op (.Dup ⟨10, by decide⟩), .op .ADD, .op (.Swap ⟨0, by decide⟩), .op .SUB, .push 0 0,
   .op (.Swap ⟨4, by decide⟩), .op .POP, .push 2 5018, .op .JUMP]

def block_rare4 : Block Artifact.submissionArtifact .Osaka 5057 prog_rare4 :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3998 46 5057 prog_rare4
    (by decide) (by rfl) (by rfl) (by decide)

end Challenge.Modexp.Submission.Proofs.Fast.R4Blocks
