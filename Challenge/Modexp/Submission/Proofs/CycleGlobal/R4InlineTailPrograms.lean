import Challenge.Modexp.Submission.Proofs.CycleGlobal.Binding
import Challenge.Modexp.Submission.Proofs.Fast.R4Blocks
noncomputable section
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
namespace CycleSubmission.Global.Fast.R4InlineTailBlocks
open Challenge.Modexp
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
def prog_tail : List Instr :=
  [.op (.Dup ⟨4, by decide⟩), .push 2 4769, .op .JUMPI]
def prog_st4 : List Instr :=
  [.op .JUMPDEST, .push 2 2112, .op .MSTORE, .push 2 2144, .op .MSTORE, .push 2 2176, .op .MSTORE, .push 2 2208, .op .MSTORE]
def prog_branchOld116 : List Instr :=
  [.op .POP, .op .POP, .op (.Dup ⟨5, by decide⟩), .op (.Dup ⟨11, by decide⟩), .op .ADD, .op (.Swap ⟨5, by decide⟩), .push 2 4037, .op .JUMPI]
/-- Consume the first copy of the loop decrement, instead of discarding it
and duplicating the equal cached copy. A wider PUSH absorbs the former two
JUMPDEST fillers, preserving every downstream byte PC without executing padding. -/
def prog_branch : List Instr :=
  [.op .POP, .op (.Dup ⟨6, by decide⟩), .op .ADD, .op (.Swap ⟨5, by decide⟩),
   .push 4 4037, .op .JUMPI]
def prog_m4 : List Instr :=
  [.op .POP, .op .POP, .op .POP, .op .POP, .op .POP, .op (.Swap ⟨13, by decide⟩), .push 2 3482, .op .JUMP]
def prog_rare4 : List Instr :=
  [.op .JUMPDEST, .op (.Dup ⟨6, by decide⟩), .op (.Dup ⟨4, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .SUB, .op (.Swap ⟨5, by decide⟩), .op .POP, .op .LT, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨9, by decide⟩), .op .ADD, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨5, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .SUB, .op (.Swap ⟨6, by decide⟩), .op .POP, .op .LT, .op (.Swap ⟨1, by decide⟩), .op .GT, .op .OR, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨10, by decide⟩), .op .ADD, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨4, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .SUB, .op (.Swap ⟨5, by decide⟩), .op .POP, .op .LT, .op (.Swap ⟨1, by decide⟩), .op .GT, .op .OR, .op (.Dup ⟨10, by decide⟩), .op .ADD, .op (.Swap ⟨0, by decide⟩), .op .SUB, .push 0 0, .op (.Swap ⟨4, by decide⟩), .op .POP, .push 2 4732, .op .JUMP]
end CycleSubmission.Global.Fast.R4InlineTailBlocks
