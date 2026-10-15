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

def block_prodiag : Block Artifact.submissionArtifact .Osaka 4268 prog_prodiag :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3320 27 4268 prog_prodiag
    (by decide) (by rfl) (by rfl) (by decide)

/-- Row 0, word 1 (pc 4608..4631, idx 3658..3678). -/
def prog_r0z1 : List Instr :=
  [.push 2 2176, .op .MLOAD, .op (.Dup ⟨4, by decide⟩), .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨2, by decide⟩), .op .MUL, .op (.Swap ⟨1, by decide⟩), .op (.Dup ⟨5, by decide⟩),
   .op .MULMOD, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .GT, .op .SUB,
   .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op .ADD, .op (.Dup ⟨0, by decide⟩),
   .op (.Swap ⟨3, by decide⟩), .op .GT, .op .SUB, .op .SUB]

def block_r0z1 : Block Artifact.submissionArtifact .Osaka 4297 prog_r0z1 :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3347 21 4297 prog_r0z1
    (by decide) (by rfl) (by rfl) (by decide)

/-- Row 0, word 2 (pc 4631..4654, idx 3679..3699). -/
def prog_r0z2 : List Instr :=
  [.push 2 2144, .op .MLOAD, .op (.Dup ⟨5, by decide⟩), .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨2, by decide⟩), .op .MUL, .op (.Swap ⟨1, by decide⟩), .op (.Dup ⟨6, by decide⟩),
   .op .MULMOD, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .GT, .op .SUB,
   .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op .ADD, .op (.Dup ⟨0, by decide⟩),
   .op (.Swap ⟨3, by decide⟩), .op .GT, .op .SUB, .op .SUB]

def block_r0z2 : Block Artifact.submissionArtifact .Osaka 4320 prog_r0z2 :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3368 21 4320 prog_r0z2
    (by decide) (by rfl) (by rfl) (by decide)

/-- Row 0, word 3 (pc 4654..4677, idx 3700..3720). -/
def prog_r0z3 : List Instr :=
  [.push 2 2112, .op .MLOAD, .op (.Dup ⟨6, by decide⟩), .op (.Dup ⟨6, by decide⟩),
   .op (.Dup ⟨2, by decide⟩), .op .MUL, .op (.Swap ⟨1, by decide⟩), .op (.Dup ⟨7, by decide⟩),
   .op .MULMOD, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .GT, .op .SUB,
   .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op .ADD, .op (.Dup ⟨0, by decide⟩),
   .op (.Swap ⟨3, by decide⟩), .op .GT, .op .SUB, .op .SUB]

def block_r0z3 : Block Artifact.submissionArtifact .Osaka 4343 prog_r0z3 :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3389 21 4343 prog_r0z3
    (by decide) (by rfl) (by rfl) (by decide)

/-- Row 0 tail: push the return address 4687 and v = 0, then jump to RED (4927). -/
def prog_r0e : List Instr :=
  [.op (.Swap ⟨4, by decide⟩), .op .POP, .push 0 0, .push 2 4376, .push 2 4616,
   .op .JUMP]

def block_r0e : Block Artifact.submissionArtifact .Osaka 4366 prog_r0e :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3410 6 4366 prog_r0e
    (by decide) (by rfl) (by rfl) (by decide)

/-- RED entry (pc 4927..4938, idx 3939..3949). -/
def prog_redm : List Instr :=
  [.op .JUMPDEST, .op (.Dup ⟨5, by decide⟩), .op (.Dup ⟨13, by decide⟩), .op .MUL,
   .op (.Dup ⟨8, by decide⟩), .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨12, by decide⟩), .op .MULMOD, .op (.Dup ⟨8, by decide⟩), .op .ADDMOD]

def block_redm : Block Artifact.submissionArtifact .Osaka 4616 prog_redm :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3628 11 4616 prog_redm
    (by decide) (by rfl) (by rfl) (by decide)

/-- RED slice 1 (pc 4627..4652, idx 3639..3664).  `T`-carry form: the stored sum goes to
the destination slot and the dead source slot receives the destination's old word. -/
def prog_reds1 : List Instr :=
  [.op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨12, by decide⟩), .op .MUL, .op (.Dup ⟨10, by decide⟩), .op (.Dup ⟨13, by decide⟩),
   .op (.Dup ⟨4, by decide⟩), .op .MULMOD, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .GT,
   .op .SUB, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op .ADD, .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨1, by decide⟩), .op .ADD, .op (.Dup ⟨0, by decide⟩), .op (.Swap ⟨11, by decide⟩), .op (.Swap ⟨10, by decide⟩),
   .op .GT, .op (.Swap ⟨3, by decide⟩), .op .GT, .op .SUB,
   .op .SUB, .op .ADD]

def block_reds1 : Block Artifact.submissionArtifact .Osaka 4627 prog_reds1 :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3639 26 4627 prog_reds1
    (by decide) (by rfl) (by rfl) (by decide)

/-- RED slice 2 (pc 4653..4678, idx 3665..3690). -/
def prog_reds2 : List Instr :=
  [.op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨13, by decide⟩), .op .MUL, .op (.Dup ⟨10, by decide⟩), .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨4, by decide⟩), .op .MULMOD, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .GT,
   .op .SUB, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op .ADD, .op (.Dup ⟨8, by decide⟩),
   .op (.Dup ⟨1, by decide⟩), .op .ADD, .op (.Dup ⟨0, by decide⟩), .op (.Swap ⟨10, by decide⟩), .op (.Swap ⟨9, by decide⟩),
   .op .GT, .op (.Swap ⟨3, by decide⟩), .op .GT, .op .SUB,
   .op .SUB, .op .ADD]

def block_reds2 : Block Artifact.submissionArtifact .Osaka 4653 prog_reds2 :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3665 26 4653 prog_reds2
    (by decide) (by rfl) (by rfl) (by decide)

/-- RED slice 3 (pc 4679..4704, idx 3691..3716). -/
def prog_reds3 : List Instr :=
  [.op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨14, by decide⟩), .op .MUL, .op (.Dup ⟨10, by decide⟩), .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨4, by decide⟩), .op .MULMOD, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .GT,
   .op .SUB, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op .ADD, .op (.Dup ⟨7, by decide⟩),
   .op (.Dup ⟨1, by decide⟩), .op .ADD, .op (.Dup ⟨0, by decide⟩), .op (.Swap ⟨9, by decide⟩), .op (.Swap ⟨8, by decide⟩),
   .op .GT, .op (.Swap ⟨3, by decide⟩), .op .GT, .op .SUB,
   .op .SUB, .op .ADD]

def block_reds3 : Block Artifact.submissionArtifact .Osaka 4679 prog_reds3 :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3691 26 4679 prog_reds3
    (by decide) (by rfl) (by rfl) (by decide)

/-- RED tail (pc 4705..4715, idx 3717..3727): returns to the `ret` under the window.
Three unreachable `JUMPDEST` pads follow (pc 4716..4718), so pc 4719 and idx 3731 stay. -/
def prog_redt : List Instr :=
  [.op (.Dup ⟨8, by decide⟩), .op .ADD, .op (.Swap ⟨3, by decide⟩), .op .POP, .op .POP,
   .op (.Swap ⟨5, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .LT,
   .op .ADD, .op (.Swap ⟨4, by decide⟩), .op .JUMP]

def block_redt : Block Artifact.submissionArtifact .Osaka 4705 prog_redt :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3717 11 4705 prog_redt
    (by decide) (by rfl) (by rfl) (by decide)

/-- pc 4687..4697（idx 3727..3732）: the return landing of the row-1 head trampoline. -/
def prog_r1h : List Instr :=
  [.op .JUMPDEST, .push 2 2176, .op .MLOAD, .push 2 2208, .op .MLOAD, .push 0 0]

def block_r1h : Block Artifact.submissionArtifact .Osaka 4376 prog_r1h :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3416 6 4376 prog_r1h
    (by decide) (by rfl) (by rfl) (by decide)

/-- Row 1 diagonal (pc 4698..4727, idx 3734..3762). -/
def prog_r1d : List Instr :=
  [.op (.Dup ⟨1, by decide⟩), .op .ADD, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .ADD, .op (.Swap ⟨1, by decide⟩), .op (.Dup ⟨8, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨5, by decide⟩), .op .MUL, .op (.Swap ⟨4, by decide⟩), .op .LT, .op (.Swap ⟨2, by decide⟩), .op .MULMOD, .op .SUB, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .LT, .op .SUB, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨6, by decide⟩), .op .ADD, .op (.Swap ⟨5, by decide⟩), .op (.Dup ⟨6, by decide⟩), .op .LT, .op .SUB, .op .SUB]

def block_r1d : Block Artifact.submissionArtifact .Osaka 4387 prog_r1d :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3423 29 4387 prog_r1d
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)

/-- Row 1, word 2 (pc 4727..4756, idx 3763..3789). -/
def prog_r1c2 : List Instr :=
  [.push 2 2144, .op .MLOAD, .op (.Dup ⟨8, by decide⟩), .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨2, by decide⟩), .op .MUL, .op (.Swap ⟨1, by decide⟩), .op (.Dup ⟨4, by decide⟩),
   .op .MULMOD, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .GT, .op .SUB,
   .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op .ADD, .op (.Dup ⟨6, by decide⟩),
   .op (.Dup ⟨1, by decide⟩), .op .ADD, .op (.Swap ⟨6, by decide⟩), .op (.Dup ⟨7, by decide⟩),
   .op .LT, .op (.Swap ⟨3, by decide⟩), .op .GT, .op .SUB, .op .SUB, .op .ADD]

def block_r1c2 : Block Artifact.submissionArtifact .Osaka 4416 prog_r1c2 :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3452 27 4416 prog_r1c2
    (by decide) (by rfl) (by rfl) (by decide)

/-- Row 1, word 3 (pc 4756..4785, idx 3790..3816). -/
def prog_r1c3 : List Instr :=
  [.push 2 2112, .op .MLOAD, .op (.Dup ⟨8, by decide⟩), .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨2, by decide⟩), .op .MUL, .op (.Swap ⟨1, by decide⟩), .op (.Dup ⟨4, by decide⟩),
   .op .MULMOD, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .GT, .op .SUB,
   .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op .ADD, .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨1, by decide⟩), .op .ADD, .op (.Swap ⟨5, by decide⟩), .op (.Dup ⟨6, by decide⟩),
   .op .LT, .op (.Swap ⟨3, by decide⟩), .op .GT, .op .SUB, .op .SUB, .op .ADD]

def block_r1c3 : Block Artifact.submissionArtifact .Osaka 4445 prog_r1c3 :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3479 27 4445 prog_r1c3
    (by decide) (by rfl) (by rfl) (by decide)

/-- Row 1 tail: return address 4799, then RED. -/
def prog_r1e : List Instr :=
  [.op (.Dup ⟨6, by decide⟩), .op .ADD, .op (.Swap ⟨5, by decide⟩), .op (.Dup ⟨6, by decide⟩), .op .LT,
   .op (.Swap ⟨0, by decide⟩), .op .POP, .push 2 4488, .push 2 4616, .op .JUMP]

def block_r1e : Block Artifact.submissionArtifact .Osaka 4474 prog_r1e :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3506 10 4474 prog_r1e
    (by decide) (by rfl) (by rfl) (by decide)

/-- pc 4799..4809（idx 3827..3832）: the return landing of the row-2 head trampoline. -/
def prog_r2h : List Instr :=
  [.op .JUMPDEST, .push 2 2144, .op .MLOAD, .push 2 2176, .op .MLOAD, .push 0 0]

def block_r2h : Block Artifact.submissionArtifact .Osaka 4488 prog_r2h :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3516 6 4488 prog_r2h
    (by decide) (by rfl) (by rfl) (by decide)

/-- Row 2 diagonal (pc 4810..4839, idx 3834..3862). -/
def prog_r2d : List Instr :=
  [.op (.Dup ⟨1, by decide⟩), .op .ADD, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .ADD, .op (.Swap ⟨1, by decide⟩), .op (.Dup ⟨8, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨5, by decide⟩), .op .MUL, .op (.Swap ⟨4, by decide⟩), .op .LT, .op (.Swap ⟨2, by decide⟩), .op .MULMOD, .op .SUB, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .LT, .op .SUB, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨5, by decide⟩), .op .ADD, .op (.Swap ⟨4, by decide⟩), .op (.Dup ⟨5, by decide⟩), .op .LT, .op .SUB, .op .SUB]

def block_r2d : Block Artifact.submissionArtifact .Osaka 4499 prog_r2d :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3523 29 4499 prog_r2d
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)

/-- Row 2, word 3 (pc 4839..4868, idx 3863..3889). -/
def prog_r2c3 : List Instr :=
  [.push 2 2112, .op .MLOAD, .op (.Dup ⟨8, by decide⟩), .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨2, by decide⟩), .op .MUL, .op (.Swap ⟨1, by decide⟩), .op (.Dup ⟨4, by decide⟩),
   .op .MULMOD, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .GT, .op .SUB,
   .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op .ADD, .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨1, by decide⟩), .op .ADD, .op (.Swap ⟨5, by decide⟩), .op (.Dup ⟨6, by decide⟩),
   .op .LT, .op (.Swap ⟨3, by decide⟩), .op .GT, .op .SUB, .op .SUB, .op .ADD]

def block_r2c3 : Block Artifact.submissionArtifact .Osaka 4528 prog_r2c3 :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3552 27 4528 prog_r2c3
    (by decide) (by rfl) (by rfl) (by decide)

/-- Row 2 tail: return address 4882, then RED. -/
def prog_r2e : List Instr :=
  [.op (.Dup ⟨6, by decide⟩), .op .ADD, .op (.Swap ⟨5, by decide⟩), .op (.Dup ⟨6, by decide⟩), .op .LT,
   .op (.Swap ⟨0, by decide⟩), .op .POP, .push 2 4571, .push 2 4616, .op .JUMP]

def block_r2e : Block Artifact.submissionArtifact .Osaka 4557 prog_r2e :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3579 10 4557 prog_r2e
    (by decide) (by rfl) (by rfl) (by decide)

/-- pc 4882..4892（idx 3900..3905）: the return landing of the row-3 head trampoline. -/
def prog_r3h : List Instr :=
  [.op .JUMPDEST, .push 2 2112, .op .MLOAD, .push 2 2144, .op .MLOAD, .push 0 0]

def block_r3h : Block Artifact.submissionArtifact .Osaka 4571 prog_r3h :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3589 6 4571 prog_r3h
    (by decide) (by rfl) (by rfl) (by decide)

/-- Row 3 diagonal (pc 4582..4607, idx 3596..3621).  The overflow bit is `GT a f` and the
product `a * f` is formed before the `MULMOD`; one `JUMPDEST` keeps the pc/index layout. -/
def prog_r3d : List Instr :=
  [.op (.Dup ⟨1, by decide⟩), .op .ADD, .op (.Dup ⟨7, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨4, by decide⟩), .op .GT, .op (.Swap ⟨2, by decide⟩), .op (.Dup ⟨4, by decide⟩), .op .MUL, .op (.Swap ⟨3, by decide⟩), .op .JUMPDEST, .op .MULMOD, .op .SUB, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .LT, .op .SUB, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op .ADD, .op (.Swap ⟨2, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op .LT, .op .SUB, .op .SUB]

def block_r3d : Block Artifact.submissionArtifact .Osaka 4582 prog_r3d :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3596 26 4582 prog_r3d
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)

/-- Row 3 tail: pushes the exit address 5031 and falls into RED (4927). -/
def prog_r3e : List Instr :=
  [.op (.Dup ⟨5, by decide⟩), .op .ADD, .op (.Swap ⟨4, by decide⟩), .op (.Dup ⟨5, by decide⟩), .op .LT,
   .push 2 4719]

def block_r3e : Block Artifact.submissionArtifact .Osaka 4608 prog_r3e :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3622 6 4608 prog_r3e
    (by decide) (by rfl) (by rfl) (by decide)

/-- The n=4 tail head (pc 5032, idx 3975): a nonzero overflow word `t4` (`DUP5`) takes `rare4`. -/
def prog_tail : List Instr :=
  [.op .JUMPDEST, .op (.Dup ⟨4, by decide⟩), .push 2 4764, .op .JUMPI]

def block_tail : Block Artifact.submissionArtifact .Osaka 4719 prog_tail :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3731 4 4719 prog_tail
    (by decide) (by rfl) (by rfl) (by decide)

/-- `st4` (pc 5038, idx 3979): store `t3..t0` at 0x840..0x8a0 and the overflow word at 0x820,
drop the six constants, decrement the square counter in the frame's `pdst` slot and jump back
into R4 (4580) while the old count is nonzero. -/
def prog_st4 : List Instr :=
  [.op .JUMPDEST, .push 2 2112, .op .MSTORE, .push 2 2144, .op .MSTORE, .push 2 2176, .op .MSTORE,
   .push 2 2208, .op .MSTORE, .push 2 2080, .op .MSTORE, .op .POP, .op .POP, .op .POP, .op .POP,
   .op .POP, .op .POP, .op (.Dup ⟨14, by decide⟩), .op (.Dup ⟨6, by decide⟩), .op .ADD,
   .op (.Swap ⟨14, by decide⟩), .push 2 4268, .op .JUMPI]

def block_st4 : Block Artifact.submissionArtifact .Osaka 4725 prog_st4 :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3735 23 4725 prog_st4
    (by decide) (by rfl) (by rfl) (by decide)

/-- The last square leaves R4 through `m4j` (4248), the `JUMPDEST` inside `last`. -/
def prog_m4 : List Instr := [.push 2 3999, .op .JUMP]

def block_m4 : Block Artifact.submissionArtifact .Osaka 4760 prog_m4 :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3758 2 4760 prog_m4
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
   .op (.Swap ⟨4, by decide⟩), .op .POP, .push 2 4725, .op .JUMP]

def block_rare4 : Block Artifact.submissionArtifact .Osaka 4764 prog_rare4 :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3760 46 4764 prog_rare4
    (by decide) (by rfl) (by rfl) (by decide)

end Challenge.Modexp.Submission.Proofs.Fast.R4Blocks
