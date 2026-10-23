import Challenge.Modexp.Submission.Proofs.Fast.R4SliceFast
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
# Retained-frame n=4 squaring program slices

Each block is bound to the exact candidate artifact. Repeat entry receives five cached
modulus/inverse words above the loop frame. The unchanged arithmetic rows share the reduction
subroutine and reach the carry-handling tail. Four limb stores preserve the zero carry word;
the branch retains the cached words for another round or restores the original frame on exit.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.R4Blocks

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel WindowTwentyOneBinding

/-- The entry and first diagonal (pc 4581..4610, idx 3631..3657).  P1: the entry copies the
Montgomery inverse from frame word 12 (`DUP12`), modulus[32] from word 5 (`DUP7`) and
modulus[64] from word 8 (`DUP11`). -/
def prog_prodiag : List Instr :=
  [.op .JUMPDEST, .push 2 2208, .op .MLOAD, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨0, by decide⟩), .op .ADD, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨0, by decide⟩), .op .MUL, .op (.Dup ⟨13, by decide⟩), .op (.Dup ⟨0, by decide⟩), .op (.Swap ⟨3, by decide⟩), .op (.Dup ⟨0, by decide⟩), .op .MULMOD, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .GT, .op (.Dup ⟨2, by decide⟩), .op (.Swap ⟨1, by decide⟩), .op .SUB, .op .SUB]

def block_prodiag : Block Artifact.submissionArtifact .Osaka 8998 prog_prodiag :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 6940 21 8998 prog_prodiag
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 6940 + 21 ≤ 8721) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rw [R4SliceFast.locations_map]; rfl) (by decide)

/-- Row 0, word 1 (pc 4610..4633, idx 3658..3678). -/
def prog_r0z1 : List Instr :=
  [.push 2 2176, .op .MLOAD, .op (.Dup ⟨4, by decide⟩), .op (.Dup ⟨4, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .MUL, .op (.Swap ⟨1, by decide⟩), .op (.Dup ⟨5, by decide⟩), .op .MULMOD, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .GT, .op .SUB, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op .ADD, .op (.Dup ⟨0, by decide⟩), .op (.Swap ⟨3, by decide⟩), .op .GT, .op .SUB, .op .SUB]

def block_r0z1 : Block Artifact.submissionArtifact .Osaka 4303 prog_r0z1 :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3348 21 4303 prog_r0z1
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 3348 + 21 ≤ 8721) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rw [R4SliceFast.locations_map]; rfl) (by decide)

/-- Row 0, word 2 (pc 4633..4656, idx 3679..3699). -/
def prog_r0z2 : List Instr :=
  [.push 2 2144, .op .MLOAD, .op (.Dup ⟨5, by decide⟩), .op (.Dup ⟨5, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .MUL, .op (.Swap ⟨1, by decide⟩), .op (.Dup ⟨6, by decide⟩), .op .MULMOD, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .GT, .op .SUB, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op .ADD, .op (.Dup ⟨0, by decide⟩), .op (.Swap ⟨3, by decide⟩), .op .GT, .op .SUB, .op .SUB]

def block_r0z2 : Block Artifact.submissionArtifact .Osaka 4326 prog_r0z2 :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3369 21 4326 prog_r0z2
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 3369 + 21 ≤ 8721) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rw [R4SliceFast.locations_map]; rfl) (by decide)

/-- Row 0, word 3 (pc 4656..4679, idx 3700..3720). -/
def prog_r0z3 : List Instr :=
  [.push 2 2112, .op .MLOAD, .op (.Dup ⟨6, by decide⟩), .op (.Dup ⟨6, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .MUL, .op (.Swap ⟨1, by decide⟩), .op (.Dup ⟨7, by decide⟩), .op .MULMOD, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .GT, .op .SUB, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op .ADD, .op (.Dup ⟨0, by decide⟩), .op (.Swap ⟨3, by decide⟩), .op .GT, .op .SUB, .op .SUB]

def block_r0z3 : Block Artifact.submissionArtifact .Osaka 4349 prog_r0z3 :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3390 21 4349 prog_r0z3
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 3390 + 21 ≤ 8721) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rw [R4SliceFast.locations_map]; rfl) (by decide)

/-- Row 0 tail: push the return address 4689 and v = 0, then jump to RED (4929). -/
def prog_r0e : List Instr :=
  [.op (.Swap ⟨4, by decide⟩), .op .POP, .push 0 0, .push 2 4382, .push 2 4621, .op .JUMP]

def block_r0e : Block Artifact.submissionArtifact .Osaka 4372 prog_r0e :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3411 6 4372 prog_r0e
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 3411 + 6 ≤ 8721) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rw [R4SliceFast.locations_map]; rfl) (by decide)

/-- RED entry (pc 4929..4940, idx 3939..3949). -/
def prog_redm : List Instr :=
  [.op .JUMPDEST, .op (.Dup ⟨5, by decide⟩), .op (.Dup ⟨13, by decide⟩), .op .MUL, .op (.Dup ⟨8, by decide⟩), .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op (.Dup ⟨12, by decide⟩), .op .MULMOD, .op (.Dup ⟨8, by decide⟩), .op .ADDMOD]

def block_redm : Block Artifact.submissionArtifact .Osaka 4621 prog_redm :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3628 11 4621 prog_redm
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 3628 + 11 ≤ 8721) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rw [R4SliceFast.locations_map]; rfl) (by decide)

/-- RED slice 1 (pc 4940..4967, idx 3950..3976). -/
def prog_reds1 : List Instr :=
  [.op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨12, by decide⟩), .op .MUL, .op (.Dup ⟨10, by decide⟩), .op (.Dup ⟨13, by decide⟩), .op (.Dup ⟨4, by decide⟩), .op .MULMOD, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .GT, .op .SUB, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op .ADD, .op (.Dup ⟨9, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .ADD, .op (.Dup ⟨0, by decide⟩), .op (.Swap ⟨11, by decide⟩), .op (.Swap ⟨10, by decide⟩), .op .GT, .op (.Swap ⟨3, by decide⟩), .op .GT, .op .SUB, .op .SUB, .op .ADD]

def block_reds1 : Block Artifact.submissionArtifact .Osaka 4632 prog_reds1 :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3639 26 4632 prog_reds1
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 3639 + 26 ≤ 8721) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rw [R4SliceFast.locations_map]; rfl) (by decide)

/-- RED slice 2 (pc 4967..4994, idx 3977..4003). -/
def prog_reds2 : List Instr :=
  [.op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨13, by decide⟩), .op .MUL, .op (.Dup ⟨10, by decide⟩), .op (.Dup ⟨14, by decide⟩), .op (.Dup ⟨4, by decide⟩), .op .MULMOD, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .GT, .op .SUB, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op .ADD, .op (.Dup ⟨8, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .ADD, .op (.Dup ⟨0, by decide⟩), .op (.Swap ⟨10, by decide⟩), .op (.Swap ⟨9, by decide⟩), .op .GT, .op (.Swap ⟨3, by decide⟩), .op .GT, .op .SUB, .op .SUB, .op .ADD]

def block_reds2 : Block Artifact.submissionArtifact .Osaka 4658 prog_reds2 :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3665 26 4658 prog_reds2
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 3665 + 26 ≤ 8721) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rw [R4SliceFast.locations_map]; rfl) (by decide)

/-- RED slice 3 (pc 4994..5021, idx 4004..4030). -/
def prog_reds3 : List Instr :=
  [.op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨14, by decide⟩), .op .MUL, .op (.Dup ⟨10, by decide⟩), .op (.Dup ⟨15, by decide⟩), .op (.Dup ⟨4, by decide⟩), .op .MULMOD, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .GT, .op .SUB, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op .ADD, .op (.Dup ⟨7, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .ADD, .op (.Dup ⟨0, by decide⟩), .op (.Swap ⟨9, by decide⟩), .op (.Swap ⟨8, by decide⟩), .op .GT, .op (.Swap ⟨3, by decide⟩), .op .GT, .op .SUB, .op .SUB, .op .ADD]

def block_reds3 : Block Artifact.submissionArtifact .Osaka 4684 prog_reds3 :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3691 26 4684 prog_reds3
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 3691 + 26 ≤ 8721) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rw [R4SliceFast.locations_map]; rfl) (by decide)

/-- RED tail (pc 5021.., idx 4031..4041): returns to the `ret` under the window. -/
def prog_redt : List Instr :=
  [.op (.Dup ⟨8, by decide⟩), .op .ADD, .op (.Swap ⟨3, by decide⟩), .op .POP, .op .POP, .op (.Swap ⟨5, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .LT, .op .ADD, .op (.Swap ⟨4, by decide⟩), .op .JUMP]

def block_redt : Block Artifact.submissionArtifact .Osaka 4710 prog_redt :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3717 11 4710 prog_redt
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 3717 + 11 ≤ 8721) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rw [R4SliceFast.locations_map]; rfl) (by decide)

/-- pc 4689..4699（idx 3727..3732）: the return landing of the row-1 head trampoline. -/
def prog_r1h : List Instr :=
  [.op .JUMPDEST, .push 2 2176, .op .MLOAD, .push 2 2208, .op .MLOAD, .push 0 0]

def block_r1h : Block Artifact.submissionArtifact .Osaka 4382 prog_r1h :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3417 6 4382 prog_r1h
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 3417 + 6 ≤ 8721) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rw [R4SliceFast.locations_map]; rfl) (by decide)

/-- Row 1 diagonal (pc 4700..4729, idx 3734..3762). -/
def prog_r1d : List Instr :=
  [.op (.Dup ⟨1, by decide⟩), .op .ADD, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .GT, .op (.Dup ⟨8, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op (.Dup ⟨4, by decide⟩), .op .ADD, .op (.Swap ⟨3, by decide⟩), .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨4, by decide⟩), .op .MUL, .op (.Swap ⟨3, by decide⟩), .op .MULMOD, .op .SUB, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .LT, .op .SUB, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨6, by decide⟩), .op .ADD, .op (.Swap ⟨5, by decide⟩), .op (.Dup ⟨6, by decide⟩), .op .LT, .op .SUB, .op .SUB]

def block_r1d : Block Artifact.submissionArtifact .Osaka 4393 prog_r1d :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3424 28 4393 prog_r1d
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)

/-- Row 1, word 2 (pc 4729..4758, idx 3763..3789). -/
def prog_r1c2 : List Instr :=
  [.push 2 2144, .op .MLOAD, .op (.Dup ⟨8, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .MUL, .op (.Swap ⟨1, by decide⟩), .op (.Dup ⟨4, by decide⟩), .op .MULMOD, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .GT, .op .SUB, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op .ADD, .op (.Dup ⟨6, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .ADD, .op (.Swap ⟨6, by decide⟩), .op (.Dup ⟨7, by decide⟩), .op .LT, .op (.Swap ⟨3, by decide⟩), .op .GT, .op .SUB, .op .SUB, .op .ADD]

def block_r1c2 : Block Artifact.submissionArtifact .Osaka 4421 prog_r1c2 :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3452 27 4421 prog_r1c2
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 3452 + 27 ≤ 8721) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rw [R4SliceFast.locations_map]; rfl) (by decide)

/-- Row 1, word 3 (pc 4758..4787, idx 3790..3816). -/
def prog_r1c3 : List Instr :=
  [.push 2 2112, .op .MLOAD, .op (.Dup ⟨8, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .MUL, .op (.Swap ⟨1, by decide⟩), .op (.Dup ⟨4, by decide⟩), .op .MULMOD, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .GT, .op .SUB, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op .ADD, .op (.Dup ⟨5, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .ADD, .op (.Swap ⟨5, by decide⟩), .op (.Dup ⟨6, by decide⟩), .op .LT, .op (.Swap ⟨3, by decide⟩), .op .GT, .op .SUB, .op .SUB, .op .ADD]

def block_r1c3 : Block Artifact.submissionArtifact .Osaka 4450 prog_r1c3 :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3479 27 4450 prog_r1c3
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 3479 + 27 ≤ 8721) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rw [R4SliceFast.locations_map]; rfl) (by decide)

/-- Row 1 tail: return address 4801, then RED. -/
def prog_r1e : List Instr :=
  [.op (.Dup ⟨6, by decide⟩), .op .ADD, .op (.Swap ⟨5, by decide⟩), .op (.Dup ⟨6, by decide⟩), .op .LT, .op (.Swap ⟨0, by decide⟩), .op .POP, .push 2 4494, .push 2 4621, .op .JUMP]

def block_r1e : Block Artifact.submissionArtifact .Osaka 4479 prog_r1e :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3506 10 4479 prog_r1e
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 3506 + 10 ≤ 8721) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rw [R4SliceFast.locations_map]; rfl) (by decide)

/-- pc 4801..4811（idx 3827..3832）: the return landing of the row-2 head trampoline. -/
def prog_r2h : List Instr :=
  [.op .JUMPDEST, .push 2 2144, .op .MLOAD, .push 2 2176, .op .MLOAD, .push 0 0]

def block_r2h : Block Artifact.submissionArtifact .Osaka 4494 prog_r2h :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3517 6 4494 prog_r2h
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 3517 + 6 ≤ 8721) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rw [R4SliceFast.locations_map]; rfl) (by decide)

/-- Row 2 diagonal (pc 4812..4841, idx 3834..3862). -/
def prog_r2d : List Instr :=
  [.op (.Dup ⟨1, by decide⟩), .op .ADD, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .GT, .op (.Dup ⟨8, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op (.Dup ⟨4, by decide⟩), .op .ADD, .op (.Swap ⟨3, by decide⟩), .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨4, by decide⟩), .op .MUL, .op (.Swap ⟨3, by decide⟩), .op .MULMOD, .op .SUB, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .LT, .op .SUB, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨5, by decide⟩), .op .ADD, .op (.Swap ⟨4, by decide⟩), .op (.Dup ⟨5, by decide⟩), .op .LT, .op .SUB, .op .SUB]

def block_r2d : Block Artifact.submissionArtifact .Osaka 4505 prog_r2d :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3524 28 4505 prog_r2d
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)

/-- Row 2, word 3 (pc 4841..4870, idx 3863..3889). -/
def prog_r2c3 : List Instr :=
  [.push 2 2112, .op .MLOAD, .op (.Dup ⟨8, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .MUL, .op (.Swap ⟨1, by decide⟩), .op (.Dup ⟨4, by decide⟩), .op .MULMOD, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .GT, .op .SUB, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op .ADD, .op (.Dup ⟨5, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .ADD, .op (.Swap ⟨5, by decide⟩), .op (.Dup ⟨6, by decide⟩), .op .LT, .op (.Swap ⟨3, by decide⟩), .op .GT, .op .SUB, .op .SUB, .op .ADD]

def block_r2c3 : Block Artifact.submissionArtifact .Osaka 4533 prog_r2c3 :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3552 27 4533 prog_r2c3
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 3552 + 27 ≤ 8721) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rw [R4SliceFast.locations_map]; rfl) (by decide)

/-- Row 2 tail: return address 4884, then RED. -/
def prog_r2e : List Instr :=
  [.op (.Dup ⟨6, by decide⟩), .op .ADD, .op (.Swap ⟨5, by decide⟩), .op (.Dup ⟨6, by decide⟩), .op .LT, .op (.Swap ⟨0, by decide⟩), .op .POP, .push 2 4577, .push 2 4621, .op .JUMP]

def block_r2e : Block Artifact.submissionArtifact .Osaka 4562 prog_r2e :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3579 10 4562 prog_r2e
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 3579 + 10 ≤ 8721) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rw [R4SliceFast.locations_map]; rfl) (by decide)

/-- pc 4884..4894（idx 3900..3905）: the return landing of the row-3 head trampoline. -/
def prog_r3h : List Instr :=
  [.op .JUMPDEST, .push 2 2112, .op .MLOAD, .push 2 2144, .op .MLOAD, .push 0 0]

def block_r3h : Block Artifact.submissionArtifact .Osaka 4577 prog_r3h :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3590 6 4577 prog_r3h
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 3590 + 6 ≤ 8721) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rw [R4SliceFast.locations_map]; rfl) (by decide)

/-- Row 3 diagonal (pc 4895..4921, idx 3907..3932). -/
def prog_r3d : List Instr :=
  [.op (.Dup ⟨1, by decide⟩), .op .ADD, .op (.Dup ⟨7, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨4, by decide⟩), .op .GT, .op (.Swap ⟨2, by decide⟩), .op (.Dup ⟨4, by decide⟩), .op .MUL, .op (.Swap ⟨3, by decide⟩), .op .MULMOD, .op .SUB, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .LT, .op .SUB, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op .ADD, .op (.Swap ⟨2, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op .LT, .op .SUB, .op .SUB]

def block_r3d : Block Artifact.submissionArtifact .Osaka 4588 prog_r3d :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3597 25 4588 prog_r3d
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)

/-- Row 3 tail: pushes the exit address 5033 and falls into RED (4929). -/
def prog_r3e : List Instr :=
  [.op (.Dup ⟨5, by decide⟩), .op .ADD, .op (.Swap ⟨4, by decide⟩), .op (.Dup ⟨5, by decide⟩), .op .LT, .push 2 4725]

def block_r3e : Block Artifact.submissionArtifact .Osaka 4613 prog_r3e :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3622 6 4613 prog_r3e
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 3622 + 6 ≤ 8721) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rw [R4SliceFast.locations_map]; rfl) (by decide)

/-- The n=4 tail head (pc 5034, idx 3975): a nonzero overflow word `t4` (`DUP5`) takes `rare4`. -/
def prog_tail : List Instr :=
  [.op .JUMPDEST, .op (.Dup ⟨4, by decide⟩), .push 2 4768, .op .JUMPI]

def block_tail : Block Artifact.submissionArtifact .Osaka 4725 prog_tail :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3732 4 4725 prog_tail
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 3732 + 4 ≤ 8721) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rw [R4SliceFast.locations_map]; rfl) (by decide)

/-- Store the four reduced limbs; retain the modulus/inverse frame for the next square. -/
def prog_st4 : List Instr :=
  [.op .JUMPDEST, .push 2 2112, .op .MSTORE, .push 2 2144, .op .MSTORE, .push 2 2176, .op .MSTORE, .push 2 2208, .op .MSTORE]

def block_st4 : Block Artifact.submissionArtifact .Osaka 4731 prog_st4 :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3736 9 4731 prog_st4
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 3736 + 9 ≤ 8721) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rw [R4SliceFast.locations_map]; rfl) (by decide)

def prog_branch : List Instr :=
  [.op .POP, .op .POP, .op (.Dup ⟨5, by decide⟩), .op (.Dup ⟨11, by decide⟩), .op .ADD, .op (.Swap ⟨5, by decide⟩), .push 2 8998, .op .JUMPI]

def block_branch : Block Artifact.submissionArtifact .Osaka 4748 prog_branch :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3745 8 4748 prog_branch
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 3745 + 8 ≤ 8721) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rw [R4SliceFast.locations_map]; rfl) (by decide)

def prog_m4 : List Instr :=
  [.op .POP, .op .POP, .op .POP, .op .POP, .op .POP, .op (.Swap ⟨13, by decide⟩), .push 2 3999, .op .JUMP]

def block_m4 : Block Artifact.submissionArtifact .Osaka 4758 prog_m4 :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3753 8 4758 prog_m4
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 3753 + 8 ≤ 8721) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rw [R4SliceFast.locations_map]; rfl) (by decide)

/-- `rare4` (pc 5077, idx 4004): subtract the modulus `n0..n3` from `t0..t3` on the stack with a
borrow chain, zero the overflow word and return to `st4`. -/
def prog_rare4 : List Instr :=
  [.op .JUMPDEST, .op (.Dup ⟨6, by decide⟩), .op (.Dup ⟨4, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .SUB, .op (.Swap ⟨5, by decide⟩), .op .POP, .op .LT, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨9, by decide⟩), .op .ADD, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨5, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .SUB, .op (.Swap ⟨6, by decide⟩), .op .POP, .op .LT, .op (.Swap ⟨1, by decide⟩), .op .GT, .op .OR, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨10, by decide⟩), .op .ADD, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨4, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .SUB, .op (.Swap ⟨5, by decide⟩), .op .POP, .op .LT, .op (.Swap ⟨1, by decide⟩), .op .GT, .op .OR, .op (.Dup ⟨10, by decide⟩), .op .ADD, .op (.Swap ⟨0, by decide⟩), .op .SUB, .push 0 0, .op (.Swap ⟨4, by decide⟩), .op .POP, .push 2 4731, .op .JUMP]

def block_rare4 : Block Artifact.submissionArtifact .Osaka 4768 prog_rare4 :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3761 46 4768 prog_rare4
    (by change _ ≤ Artifact.submissionInstructions.length; exact Nat.le_trans (by decide : 3761 + 46 ≤ 8721) (Nat.le_of_eq Artifact.submissionInstructions_count.symm)) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rw [R4SliceFast.locations_map]; rfl) (by decide)

end Challenge.Modexp.Submission.Proofs.Fast.R4Blocks
