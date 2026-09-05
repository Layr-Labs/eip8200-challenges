import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTemplate
import YulEvmCompiler.Instr

set_option warningAsError true
set_option maxRecDepth 30000

/-!
# H12 shared round helper templates

These templates describe the straight-line helper before its final `JUMP`.
The helper receives `[X-address, rotation, return-PC, A, B, C, D, E]` in
top-first order.  The final `JUMP` is deliberately not part of a template.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.SharedRoundTemplate

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.EvmProof
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTemplate

def dup7 : Instr := .op (.Dup ⟨6, by decide⟩)
def dup8 : Instr := .op (.Dup ⟨7, by decide⟩)
def swap5 : Instr := .op (.Swap ⟨4, by decide⟩)

/-! The H10 Boolean instruction lists with every `DUP` index increased by 3. -/

def booleanOps (j : Nat) : List Instr :=
  match j with
  | 0 => [dup5, dup7, op .XOR, dup8, op .XOR]
  | 1 => [dup6, dup8, op .XOR, dup6, op .AND, dup8, op .XOR]
  | 2 => [dup6, op .NOT, dup6, op .OR, dup8, op .XOR,
      push4 mask, op .AND]
  | 3 => [dup5, dup7, op .XOR, dup8, op .AND, dup7, op .XOR]
  | _ => [dup7, op .NOT, dup7, op .OR, dup6, op .XOR,
      push4 mask, op .AND]

def helperBeforeJumpTemplate (j : Nat) (_xAddress : UInt256)
    (_rotation : Nat) (constant : UInt256) : List Instr :=
  [op .JUMPDEST, op .MLOAD] ++ booleanOps j ++
    [op .ADD, dup4, op .ADD] ++
    (if j = 0 then [] else [push4 constant, op .ADD]) ++
    [push4 mask, op .AND, swap3, op .POP,
      dup3, dup2, op .SHL, dup4, dup3, push1 (UInt256.ofNat 32), op .SUB,
      op .SHR, op .OR, dup8, op .ADD, push4 mask, op .AND,
      swap1, op .POP, swap2, op .POP,
      dup4, dup1, push1 c10, op .SHL, dup2, push1 c22, op .SHR,
      op .OR, swap1, op .POP, push4 mask, op .AND,
      swap4, op .POP, swap1, swap2, swap3, swap4, swap5, swap1]

def template (j : Nat) (xAddress : UInt256)
    (rotation : Nat) (constant : UInt256) : List Instr :=
  helperBeforeJumpTemplate j xAddress rotation constant

def f0Template (xAddress : UInt256) (rotation : Nat) : List Instr :=
  helperBeforeJumpTemplate 0 xAddress rotation 0

def f1Template (xAddress : UInt256) (rotation : Nat)
    (constant : UInt256) : List Instr :=
  helperBeforeJumpTemplate 1 xAddress rotation constant

def f2Template (xAddress : UInt256) (rotation : Nat)
    (constant : UInt256) : List Instr :=
  helperBeforeJumpTemplate 2 xAddress rotation constant

def f3Template (xAddress : UInt256) (rotation : Nat)
    (constant : UInt256) : List Instr :=
  helperBeforeJumpTemplate 3 xAddress rotation constant

def f4Template (xAddress : UInt256) (rotation : Nat)
    (constant : UInt256) : List Instr :=
  helperBeforeJumpTemplate 4 xAddress rotation constant

@[simp] theorem booleanOps_length_zero :
    (booleanOps 0).length = 5 := by rfl

@[simp] theorem booleanOps_length_one :
    (booleanOps 1).length = 7 := by rfl

@[simp] theorem booleanOps_length_two :
    (booleanOps 2).length = 8 := by rfl

@[simp] theorem booleanOps_length_three :
    (booleanOps 3).length = 7 := by rfl

@[simp] theorem booleanOps_length_four :
    (booleanOps 4).length = 8 := by rfl

@[simp] theorem f0Template_length (xAddress : UInt256) (rotation : Nat) :
    (f0Template xAddress rotation).length = 51 := by
  rfl

@[simp] theorem f1Template_length (xAddress : UInt256) (rotation : Nat)
    (constant : UInt256) :
    (f1Template xAddress rotation constant).length = 55 := by
  rfl

@[simp] theorem f2Template_length (xAddress : UInt256) (rotation : Nat)
    (constant : UInt256) :
    (f2Template xAddress rotation constant).length = 56 := by
  rfl

@[simp] theorem f3Template_length (xAddress : UInt256) (rotation : Nat)
    (constant : UInt256) :
    (f3Template xAddress rotation constant).length = 55 := by
  rfl

@[simp] theorem f4Template_length (xAddress : UInt256) (rotation : Nat)
    (constant : UInt256) :
    (f4Template xAddress rotation constant).length = 56 := by
  rfl

end Challenge.Ripemd160.Submission.Proofs.Bytecode.SharedRoundTemplate
