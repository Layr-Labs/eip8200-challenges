import Challenge.Modexp.Submission.Proofs.Bytecode.WindowNineEntry
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowNineTableBuild
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowNineInit
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowNineLoop
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowNineReturn
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowNineSlice

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowNineLayoutCheck

open YulEvmCompiler

def widthInstructions : List Instr :=
  [.op .JUMPDEST,
   .push 1 32,
   .op (.Dup ⟨1, by decide⟩),
   .op .GT,
   .op (.Dup ⟨2, by decide⟩),
   .push 1 32,
   .op .XOR,
   .op .OR,
   .op (.Dup ⟨3, by decide⟩),
   .push 1 32,
   .op .XOR,
   .op .OR,
   .op .ISZERO,
   .push 2 2657,
   .op .JUMPI]

theorem width_eq : WindowNineEntry.widthProgram = widthInstructions := by rfl

theorem width_linear : WindowNineSlice.linearProgram widthInstructions = true := by decide

def missInstructions : List Instr :=
  [.push 2 517,
   .op .JUMP]

theorem miss_eq : WindowNineEntry.missProgram = missInstructions := by rfl

theorem miss_linear : WindowNineSlice.linearProgram missInstructions = true := by decide

def baseInstructions : List Instr :=
  [.op .JUMPDEST,
   .op (.Dup ⟨0, by decide⟩),
   .op .ISZERO,
   .push 2 3042,
   .op .JUMPI]

theorem base_eq : WindowNineEntry.baseProgram = baseInstructions := by rfl

theorem base_linear : WindowNineSlice.linearProgram baseInstructions = true := by decide

def modulusInstructions : List Instr :=
  [.op (.Dup ⟨5, by decide⟩),
   .op .CALLDATALOAD,
   .op (.Dup ⟨0, by decide⟩),
   .op .ISZERO,
   .push 2 3034,
   .op .JUMPI]

theorem modulus_eq : WindowNineEntry.modulusProgram = modulusInstructions := by rfl

theorem modulus_linear : WindowNineSlice.linearProgram modulusInstructions = true := by decide

def normalizeInstructions : List Instr :=
  [.op (.Dup ⟨4, by decide⟩),
   .op .CALLDATALOAD,
   .op (.Dup ⟨2, by decide⟩),
   .push 1 32,
   .op .SUB,
   .push 1 3,
   .op .SHL,
   .op .SHR]

theorem normalize_eq : WindowNineEntry.normalizeProgram = normalizeInstructions := by rfl

theorem normalize_linear : WindowNineSlice.linearProgram normalizeInstructions = true := by decide

def tableInstructions : List Instr :=
  [.push 1 1,
   .push 0 0,
   .op .MSTORE,
   .op (.Dup ⟨0, by decide⟩),
   .push 1 32,
   .op .MSTORE,
   .op (.Dup ⟨6, by decide⟩),
   .op .CALLDATALOAD,
   .op (.Swap ⟨1, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨0, by decide⟩),
   .push 1 64,
   .op .MSTORE,
   .op (.Dup ⟨14, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨0, by decide⟩),
   .push 1 96,
   .op .MSTORE,
   .op (.Dup ⟨13, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨0, by decide⟩),
   .push 1 128,
   .op .MSTORE,
   .op (.Dup ⟨12, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨0, by decide⟩),
   .push 1 160,
   .op .MSTORE,
   .op (.Dup ⟨11, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨0, by decide⟩),
   .push 1 192,
   .op .MSTORE,
   .op (.Dup ⟨10, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨0, by decide⟩),
   .push 1 224,
   .op .MSTORE,
   .op (.Dup ⟨9, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨0, by decide⟩),
   .push 2 256,
   .op .MSTORE,
   .op (.Dup ⟨8, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨0, by decide⟩),
   .push 2 288,
   .op .MSTORE,
   .op (.Dup ⟨7, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨0, by decide⟩),
   .push 2 320,
   .op .MSTORE,
   .op (.Dup ⟨6, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨0, by decide⟩),
   .push 2 352,
   .op .MSTORE,
   .op (.Dup ⟨5, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨0, by decide⟩),
   .push 2 384,
   .op .MSTORE,
   .op (.Dup ⟨4, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨0, by decide⟩),
   .push 2 416,
   .op .MSTORE,
   .op (.Dup ⟨3, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨0, by decide⟩),
   .push 2 448,
   .op .MSTORE,
   .op (.Dup ⟨2, by decide⟩),
   .op .MULMOD,
   .op .JUMPDEST,
   .push 2 480,
   .op .MSTORE]

theorem table_eq : WindowNineTableBuild.program = tableInstructions := by rfl

theorem table_linear : WindowNineSlice.linearProgram tableInstructions = true := by decide

def initInstructions : List Instr :=
  [.op .JUMPDEST,
   .op .POP,
   .push 2 480,
   .op (.Dup ⟨1, by decide⟩),
   .push 1 247,
   .op .SHR,
   .op (.Dup ⟨1, by decide⟩),
   .op .AND,
   .op .MLOAD,
   .op (.Swap ⟨1, by decide⟩),
   .push 1 4,
   .op .SHL,
   .push 1 6,
   .op (.Swap ⟨2, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op .CALLDATALOAD,
   .op (.Swap ⟨0, by decide⟩)]

theorem init_eq : WindowNineInit.program = initInstructions := by rfl

theorem init_linear : WindowNineSlice.linearProgram initInstructions = true := by decide

def iterationInstructions : List Instr :=
  [.op .JUMPDEST,
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op (.Swap ⟨14, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨0, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨0, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨0, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨13, by decide⟩),
   .push 1 247,
   .op .SHR,
   .op (.Dup ⟨15, by decide⟩),
   .op .AND,
   .op .MLOAD,
   .op .MULMOD,
   .op (.Dup ⟨0, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨0, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨0, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨0, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨8, by decide⟩),
   .push 1 243,
   .op .SHR,
   .op (.Dup ⟨10, by decide⟩),
   .op .AND,
   .op .MLOAD,
   .op .MULMOD,
   .op (.Dup ⟨0, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨0, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨0, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨0, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨3, by decide⟩),
   .push 1 239,
   .op .SHR,
   .op (.Dup ⟨5, by decide⟩),
   .op .AND,
   .op .MLOAD,
   .op .MULMOD,
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op (.Swap ⟨14, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨0, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨0, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨0, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨13, by decide⟩),
   .push 1 235,
   .op .SHR,
   .op (.Dup ⟨15, by decide⟩),
   .op .AND,
   .op .MLOAD,
   .op .MULMOD,
   .op (.Dup ⟨0, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨0, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨0, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨0, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨8, by decide⟩),
   .push 1 231,
   .op .SHR,
   .op (.Dup ⟨10, by decide⟩),
   .op .AND,
   .op .MLOAD,
   .op .MULMOD,
   .op (.Dup ⟨0, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨0, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨0, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨0, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨3, by decide⟩),
   .push 1 227,
   .op .SHR,
   .op (.Dup ⟨5, by decide⟩),
   .op .AND,
   .op .MLOAD,
   .op .MULMOD,
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op (.Swap ⟨14, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨0, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨0, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨0, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨13, by decide⟩),
   .push 1 223,
   .op .SHR,
   .op (.Dup ⟨15, by decide⟩),
   .op .AND,
   .op .MLOAD,
   .op .MULMOD,
   .op (.Dup ⟨0, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨0, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨0, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨0, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨8, by decide⟩),
   .push 1 219,
   .op .SHR,
   .op (.Dup ⟨10, by decide⟩),
   .op .AND,
   .op .MLOAD,
   .op .MULMOD,
   .op (.Dup ⟨0, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨0, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨0, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨0, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨3, by decide⟩),
   .push 1 215,
   .op .SHR,
   .op (.Dup ⟨5, by decide⟩),
   .op .AND,
   .op .MLOAD,
   .op .MULMOD,
   .op (.Swap ⟨1, by decide⟩),
   .push 1 36,
   .op .SHL,
   .op (.Swap ⟨1, by decide⟩),
   .push 1 1,
   .op (.Dup ⟨5, by decide⟩),
   .op .SUB,
   .op (.Swap ⟨4, by decide⟩),
   .push 2 2821,
   .op .JUMPI]

theorem iteration_eq : WindowNineLoop.iterationProgram = iterationInstructions := by rfl

theorem iteration_linear : WindowNineSlice.linearProgram iterationInstructions = true := by decide

def finishInstructions : List Instr :=
  [.push 0 0,
   .op .MSTORE,
   .push 1 32,
   .push 0 0,
   .op .RETURN]

theorem finish_eq : WindowNineReturn.program = finishInstructions := by rfl

theorem finish_linear : WindowNineSlice.linearProgram finishInstructions = true := by decide

def zeroReturnInstructions : List Instr :=
  [.op .JUMPDEST,
   .push 0 0,
   .push 0 0,
   .op .MSTORE,
   .push 1 32,
   .push 0 0,
   .op .RETURN]

theorem zeroReturn_eq : WindowNineReturn.zeroProgram = zeroReturnInstructions := by rfl

theorem zeroReturn_linear : WindowNineSlice.linearProgram zeroReturnInstructions = true := by decide

def emptyReturnInstructions : List Instr :=
  [.op .JUMPDEST,
   .op (.Dup ⟨4, by decide⟩),
   .op .CALLDATALOAD,
   .op .ISZERO,
   .op (.Dup ⟨6, by decide⟩),
   .op .CALLDATALOAD,
   .push 1 1,
   .op .MOD,
   .op .MUL,
   .push 0 0,
   .op .MSTORE,
   .push 1 32,
   .push 0 0,
   .op .RETURN]

theorem emptyReturn_eq : WindowNineReturn.emptyProgram = emptyReturnInstructions := by rfl

theorem emptyReturn_linear : WindowNineSlice.linearProgram emptyReturnInstructions = true := by decide

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowNineLayoutCheck
