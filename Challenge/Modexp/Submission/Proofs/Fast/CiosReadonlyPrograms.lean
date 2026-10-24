import Challenge.Modexp.Submission.Proofs.Fast.CiosNoDummyCarry
import Challenge.Modexp.Submission.Proofs.Fast.CiosReadonlyComponents

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Fast.CiosReadonly
open EvmSemantics YulEvmCompiler

def commonFirstLoad : List Instr :=
  [.op (.Dup ⟨14, by decide⟩), .op .MLOAD, .op (.Dup ⟨7, by decide⟩)]

def commonFusedLoad : List Instr :=
  [.op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .LT, .op .SUB,
   .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨13, by decide⟩), .op .MLOAD, .op .ADD]

def commonFusedStore : List Instr :=
  [.op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨14, by decide⟩), .op .MSTORE,
   .op (.Dup ⟨2, by decide⟩), .op .GT, .op .SUB, .op .SUB]

def commonFirstProgram : List Instr :=
  (commonFirstLoad ++ CiosNoDummyCarry.multiplyProgram) ++
    (commonFusedLoad ++ commonFusedStore)

def commonFusedLoadC (t : Nat) : List Instr :=
  [.op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .LT, .op .SUB,
   .op (.Dup ⟨1, by decide⟩), .push 2 (UInt256.ofNat t), .op .MLOAD, .op .ADD]

def commonFusedStoreC (t : Nat) : List Instr :=
  [.op (.Dup ⟨0, by decide⟩), .push 2 (UInt256.ofNat t), .op .MSTORE,
   .op (.Dup ⟨2, by decide⟩), .op .GT, .op .SUB, .op .SUB]

def commonFirstProgramC (t : Nat) : List Instr :=
  (commonFirstLoad ++ CiosNoDummyCarry.multiplyProgram) ++
    (commonFusedLoadC t ++ commonFusedStoreC t)

end Challenge.Modexp.Submission.Proofs.Fast.CiosReadonly
