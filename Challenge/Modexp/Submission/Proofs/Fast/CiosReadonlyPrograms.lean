import Challenge.Modexp.Submission.Proofs.Fast.CiosNoDummyCarry
import Challenge.Modexp.Submission.Proofs.Fast.CiosReadonlyComponents

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Fast.CiosReadonly
open EvmSemantics YulEvmCompiler

/-- First operand and accumulator pointers remain cached across every row. -/

def commonFirstLoad : List Instr :=
  [.op (.Dup ⟨14, by decide⟩), .op .MLOAD, .op (.Dup ⟨7, by decide⟩)]

/-- The first-limb tail with the carry-in `0` folded away (the J/#1392 fusion applied to
the multiply rows): `hi' = lt(mm, lo) - mm`, `s = t + lo` is stored at `t[n-1]`, and the
carry out is `(gt(lo, s) - hi') - lo`. -/
def commonFusedLoad : List Instr :=
  [.op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .LT, .op .SUB,
   .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨13, by decide⟩), .op .MLOAD, .op .ADD]

def commonFusedStore : List Instr :=
  [.op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨14, by decide⟩), .op .MSTORE,
   .op (.Dup ⟨2, by decide⟩), .op .GT, .op .SUB, .op .SUB]

def commonFirstProgram : List Instr :=
  (commonFirstLoad ++ CiosNoDummyCarry.multiplyProgram) ++
    (commonFusedLoad ++ commonFusedStore)

/-- `commonFusedLoad` with the accumulator word at the constant address `t` (`PUSH2 t`). -/
def commonFusedLoadC (t : Nat) : List Instr :=
  [.op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .LT, .op .SUB,
   .op (.Dup ⟨1, by decide⟩), .push 2 (UInt256.ofNat t), .op .MLOAD, .op .ADD]

/-- `commonFusedStore` with the accumulator word at the constant address `t` (`PUSH2 t`). -/
def commonFusedStoreC (t : Nat) : List Instr :=
  [.op (.Dup ⟨0, by decide⟩), .push 2 (UInt256.ofNat t), .op .MSTORE,
   .op (.Dup ⟨2, by decide⟩), .op .GT, .op .SUB, .op .SUB]

/-- The first-limb program of one width: the accumulator word `t[n-1]` is a code constant. -/
def commonFirstProgramC (t : Nat) : List Instr :=
  (commonFirstLoad ++ CiosNoDummyCarry.multiplyProgram) ++
    (commonFusedLoadC t ++ commonFusedStoreC t)

end Challenge.Modexp.Submission.Proofs.Fast.CiosReadonly
