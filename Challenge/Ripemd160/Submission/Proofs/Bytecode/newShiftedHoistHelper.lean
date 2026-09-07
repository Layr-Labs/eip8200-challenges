import Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedMaskHoistHelper
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RotationParameter

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.ShiftedHoistHelper

open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTemplate StackRoundTrace QuadRoundState QuadRoundTemplate
open PairRoundTemplate QuadGapTemplate

def shiftedFactor (r : Nat) : UInt256 :=
  UInt256.ofNat ((0x100000001 : Nat) <<< r)

def controlWidth (r : Nat) : Fin 33 :=
  if r < 8 then 5 else if r < 16 then 6 else if r < 24 then 7 else 8

@[simp] theorem controlWidth_ne_zero (r : Nat) : controlWidth r ≠ 0 := by
  unfold controlWidth
  split <;> first | decide | (split <;> first | decide | (split <;> decide))

@[simp] theorem controlWidth_val_ne_zero (r : Nat) : (controlWidth r).val ≠ 0 := by
  unfold controlWidth
  split <;> first | decide | (split <;> first | decide | (split <;> decide))

def controlPush (r : Nat) : Instr := .push (controlWidth r) (shiftedFactor r)

def quadHelperEntry (s : State) (startPC p0 p1 p2 p3 returnPC : UInt256)
    (r0 r1 r2 r3 : Nat) (working : Compression.EvmWorking)
    (rho : List UInt256) : State :=
  { s with
    pc := startPC
    stack := [p0, returnPC, shiftedFactor r0, p1, shiftedFactor r1,
      p2, shiftedFactor r2, p3, shiftedFactor r3] ++ roundWords working ++
      [QuadRoundTemplate.factor] ++ rho }

/-- Explicit shared-helper templates. Each variable rotation uses
MUL; PUSH1 32; SHR. Cached-mask accesses and fixed C rotations are retained. -/
def leftTemplate0 (_constant : UInt256) : List Instr :=
  [.op .JUMPDEST,
     .op .MLOAD,
     .op (.Dup ⟨10, by decide⟩),
     .op (.Dup ⟨12, by decide⟩),
     .op .XOR,
     .op (.Dup ⟨13, by decide⟩),
     .op .XOR,
     .op .ADD,
     .op (.Swap ⟨0, by decide⟩),
     .op (.Swap ⟨8, by decide⟩),
     .op .ADD,
     .op (.Dup ⟨14, by decide⟩),
     .op .AND,
     .op .MUL,
     .push 1 (UInt256.ofNat 32),
     .op .SHR,
     .op (.Dup ⟨11, by decide⟩),
     .op .ADD,
     .op (.Dup ⟨13, by decide⟩),
     .op .AND,
     .op (.Swap ⟨8, by decide⟩),
     .op (.Dup ⟨12, by decide⟩),
     .op .MUL,
     .push 1 (UInt256.ofNat 22),
     .op .SHR,
     .op (.Swap ⟨10, by decide⟩),
     .op (.Swap ⟨0, by decide⟩),
     .op .MLOAD,
     .op (.Dup ⟨9, by decide⟩),
     .op (.Dup ⟨9, by decide⟩),
     .op .XOR,
     .op (.Dup ⟨12, by decide⟩),
     .op .XOR,
     .op .ADD,
     .op .ADD,
     .op (.Dup ⟨12, by decide⟩),
     .op .AND,
     .op .MUL,
     .push 1 (UInt256.ofNat 32),
     .op .SHR,
     .op (.Dup ⟨8, by decide⟩),
     .op .ADD,
     .op (.Dup ⟨11, by decide⟩),
     .op .AND,
     .op (.Swap ⟨5, by decide⟩),
     .op (.Dup ⟨10, by decide⟩),
     .op .MUL,
     .push 1 (UInt256.ofNat 22),
     .op .SHR,
     .op (.Swap ⟨7, by decide⟩),
     .op (.Swap ⟨0, by decide⟩),
     .op .MLOAD,
     .op (.Dup ⟨6, by decide⟩),
     .op (.Dup ⟨8, by decide⟩),
     .op .XOR,
     .op (.Dup ⟨9, by decide⟩),
     .op .XOR,
     .op .ADD,
     .op .ADD,
     .op (.Dup ⟨10, by decide⟩),
     .op .AND,
     .op .MUL,
     .push 1 (UInt256.ofNat 32),
     .op .SHR,
     .op (.Dup ⟨7, by decide⟩),
     .op .ADD,
     .op (.Dup ⟨9, by decide⟩),
     .op .AND,
     .op (.Swap ⟨4, by decide⟩),
     .op (.Dup ⟨8, by decide⟩),
     .op .MUL,
     .push 1 (UInt256.ofNat 22),
     .op .SHR,
     .op (.Swap ⟨6, by decide⟩),
     .op (.Swap ⟨0, by decide⟩),
     .op .MLOAD,
     .op (.Dup ⟨5, by decide⟩),
     .op (.Dup ⟨5, by decide⟩),
     .op .XOR,
     .op (.Dup ⟨8, by decide⟩),
     .op .XOR,
     .op .ADD,
     .op .ADD,
     .op (.Dup ⟨8, by decide⟩),
     .op .AND,
     .op .MUL,
     .push 1 (UInt256.ofNat 32),
     .op .SHR,
     .op (.Dup ⟨4, by decide⟩),
     .op .ADD,
     .op (.Dup ⟨7, by decide⟩),
     .op .AND,
     .op (.Swap ⟨1, by decide⟩),
     .op (.Dup ⟨6, by decide⟩),
     .op .MUL,
     .push 1 (UInt256.ofNat 22),
     .op .SHR,
     .op (.Swap ⟨3, by decide⟩),
     .op (.Swap ⟨0, by decide⟩)]

def leftTemplate1 (constant : UInt256) : List Instr :=
  [.op .JUMPDEST,
     .op .MLOAD,
     .op (.Dup ⟨11, by decide⟩),
     .op (.Dup ⟨13, by decide⟩),
     .op .XOR,
     .op (.Dup ⟨11, by decide⟩),
     .op .AND,
     .op (.Dup ⟨13, by decide⟩),
     .op .XOR,
     .op .ADD,
     .op (.Swap ⟨0, by decide⟩),
     .op (.Swap ⟨8, by decide⟩),
     .op .ADD,
     .push 4 constant,
     .op .ADD,
     .op (.Dup ⟨14, by decide⟩),
     .op .AND,
     .op .MUL,
     .push 1 (UInt256.ofNat 32),
     .op .SHR,
     .op (.Dup ⟨11, by decide⟩),
     .op .ADD,
     .op (.Dup ⟨13, by decide⟩),
     .op .AND,
     .op (.Swap ⟨8, by decide⟩),
     .op (.Dup ⟨12, by decide⟩),
     .op .MUL,
     .push 1 (UInt256.ofNat 22),
     .op .SHR,
     .op (.Swap ⟨10, by decide⟩),
     .op (.Swap ⟨0, by decide⟩),
     .op .MLOAD,
     .op (.Dup ⟨8, by decide⟩),
     .op (.Dup ⟨12, by decide⟩),
     .op .XOR,
     .op (.Dup ⟨10, by decide⟩),
     .op .AND,
     .op (.Dup ⟨12, by decide⟩),
     .op .XOR,
     .op .ADD,
     .op .ADD,
     .push 4 constant,
     .op .ADD,
     .op (.Dup ⟨12, by decide⟩),
     .op .AND,
     .op .MUL,
     .push 1 (UInt256.ofNat 32),
     .op .SHR,
     .op (.Dup ⟨8, by decide⟩),
     .op .ADD,
     .op (.Dup ⟨11, by decide⟩),
     .op .AND,
     .op (.Swap ⟨5, by decide⟩),
     .op (.Dup ⟨10, by decide⟩),
     .op .MUL,
     .push 1 (UInt256.ofNat 22),
     .op .SHR,
     .op (.Swap ⟨7, by decide⟩),
     .op (.Swap ⟨0, by decide⟩),
     .op .MLOAD,
     .op (.Dup ⟨7, by decide⟩),
     .op (.Dup ⟨9, by decide⟩),
     .op .XOR,
     .op (.Dup ⟨7, by decide⟩),
     .op .AND,
     .op (.Dup ⟨9, by decide⟩),
     .op .XOR,
     .op .ADD,
     .op .ADD,
     .push 4 constant,
     .op .ADD,
     .op (.Dup ⟨10, by decide⟩),
     .op .AND,
     .op .MUL,
     .push 1 (UInt256.ofNat 32),
     .op .SHR,
     .op (.Dup ⟨7, by decide⟩),
     .op .ADD,
     .op (.Dup ⟨9, by decide⟩),
     .op .AND,
     .op (.Swap ⟨4, by decide⟩),
     .op (.Dup ⟨8, by decide⟩),
     .op .MUL,
     .push 1 (UInt256.ofNat 22),
     .op .SHR,
     .op (.Swap ⟨6, by decide⟩),
     .op (.Swap ⟨0, by decide⟩),
     .op .MLOAD,
     .op (.Dup ⟨4, by decide⟩),
     .op (.Dup ⟨8, by decide⟩),
     .op .XOR,
     .op (.Dup ⟨6, by decide⟩),
     .op .AND,
     .op (.Dup ⟨8, by decide⟩),
     .op .XOR,
     .op .ADD,
     .op .ADD,
     .push 4 constant,
     .op .ADD,
     .op (.Dup ⟨8, by decide⟩),
     .op .AND,
     .op .MUL,
     .push 1 (UInt256.ofNat 32),
     .op .SHR,
     .op (.Dup ⟨4, by decide⟩),
     .op .ADD,
     .op (.Dup ⟨7, by decide⟩),
     .op .AND,
     .op (.Swap ⟨1, by decide⟩),
     .op (.Dup ⟨6, by decide⟩),
     .op .MUL,
     .push 1 (UInt256.ofNat 22),
     .op .SHR,
     .op (.Swap ⟨3, by decide⟩),
     .op (.Swap ⟨0, by decide⟩)]

def leftTemplate2 (constant : UInt256) : List Instr :=
  [.op .JUMPDEST,
     .op .MLOAD,
     .op (.Dup ⟨11, by decide⟩),
     .op .NOT,
     .op (.Dup ⟨11, by decide⟩),
     .op .OR,
     .op (.Dup ⟨13, by decide⟩),
     .op .XOR,
     .op .ADD,
     .op (.Swap ⟨0, by decide⟩),
     .op (.Swap ⟨8, by decide⟩),
     .op .ADD,
     .push 4 constant,
     .op .ADD,
     .op (.Dup ⟨14, by decide⟩),
     .op .AND,
     .op .MUL,
     .push 1 (UInt256.ofNat 32),
     .op .SHR,
     .op (.Dup ⟨11, by decide⟩),
     .op .ADD,
     .op (.Dup ⟨13, by decide⟩),
     .op .AND,
     .op (.Swap ⟨8, by decide⟩),
     .op (.Dup ⟨12, by decide⟩),
     .op .MUL,
     .push 1 (UInt256.ofNat 22),
     .op .SHR,
     .op (.Swap ⟨10, by decide⟩),
     .op (.Swap ⟨0, by decide⟩),
     .op .MLOAD,
     .op (.Dup ⟨8, by decide⟩),
     .op .NOT,
     .op (.Dup ⟨10, by decide⟩),
     .op .OR,
     .op (.Dup ⟨12, by decide⟩),
     .op .XOR,
     .op .ADD,
     .op .ADD,
     .push 4 constant,
     .op .ADD,
     .op (.Dup ⟨12, by decide⟩),
     .op .AND,
     .op .MUL,
     .push 1 (UInt256.ofNat 32),
     .op .SHR,
     .op (.Dup ⟨8, by decide⟩),
     .op .ADD,
     .op (.Dup ⟨11, by decide⟩),
     .op .AND,
     .op (.Swap ⟨5, by decide⟩),
     .op (.Dup ⟨10, by decide⟩),
     .op .MUL,
     .push 1 (UInt256.ofNat 22),
     .op .SHR,
     .op (.Swap ⟨7, by decide⟩),
     .op (.Swap ⟨0, by decide⟩),
     .op .MLOAD,
     .op (.Dup ⟨7, by decide⟩),
     .op .NOT,
     .op (.Dup ⟨7, by decide⟩),
     .op .OR,
     .op (.Dup ⟨9, by decide⟩),
     .op .XOR,
     .op .ADD,
     .op .ADD,
     .push 4 constant,
     .op .ADD,
     .op (.Dup ⟨10, by decide⟩),
     .op .AND,
     .op .MUL,
     .push 1 (UInt256.ofNat 32),
     .op .SHR,
     .op (.Dup ⟨7, by decide⟩),
     .op .ADD,
     .op (.Dup ⟨9, by decide⟩),
     .op .AND,
     .op (.Swap ⟨4, by decide⟩),
     .op (.Dup ⟨8, by decide⟩),
     .op .MUL,
     .push 1 (UInt256.ofNat 22),
     .op .SHR,
     .op (.Swap ⟨6, by decide⟩),
     .op (.Swap ⟨0, by decide⟩),
     .op .MLOAD,
     .op (.Dup ⟨4, by decide⟩),
     .op .NOT,
     .op (.Dup ⟨6, by decide⟩),
     .op .OR,
     .op (.Dup ⟨8, by decide⟩),
     .op .XOR,
     .op .ADD,
     .op .ADD,
     .push 4 constant,
     .op .ADD,
     .op (.Dup ⟨8, by decide⟩),
     .op .AND,
     .op .MUL,
     .push 1 (UInt256.ofNat 32),
     .op .SHR,
     .op (.Dup ⟨4, by decide⟩),
     .op .ADD,
     .op (.Dup ⟨7, by decide⟩),
     .op .AND,
     .op (.Swap ⟨1, by decide⟩),
     .op (.Dup ⟨6, by decide⟩),
     .op .MUL,
     .push 1 (UInt256.ofNat 22),
     .op .SHR,
     .op (.Swap ⟨3, by decide⟩),
     .op (.Swap ⟨0, by decide⟩)]

def leftTemplate3 (constant : UInt256) : List Instr :=
  [.op .JUMPDEST,
     .op .MLOAD,
     .op (.Dup ⟨10, by decide⟩),
     .op (.Dup ⟨12, by decide⟩),
     .op .XOR,
     .op (.Dup ⟨13, by decide⟩),
     .op .AND,
     .op (.Dup ⟨12, by decide⟩),
     .op .XOR,
     .op .ADD,
     .op (.Swap ⟨0, by decide⟩),
     .op (.Swap ⟨8, by decide⟩),
     .op .ADD,
     .push 4 constant,
     .op .ADD,
     .op (.Dup ⟨14, by decide⟩),
     .op .AND,
     .op .MUL,
     .push 1 (UInt256.ofNat 32),
     .op .SHR,
     .op (.Dup ⟨11, by decide⟩),
     .op .ADD,
     .op (.Dup ⟨13, by decide⟩),
     .op .AND,
     .op (.Swap ⟨8, by decide⟩),
     .op (.Dup ⟨12, by decide⟩),
     .op .MUL,
     .push 1 (UInt256.ofNat 22),
     .op .SHR,
     .op (.Swap ⟨10, by decide⟩),
     .op (.Swap ⟨0, by decide⟩),
     .op .MLOAD,
     .op (.Dup ⟨9, by decide⟩),
     .op (.Dup ⟨9, by decide⟩),
     .op .XOR,
     .op (.Dup ⟨12, by decide⟩),
     .op .AND,
     .op (.Dup ⟨9, by decide⟩),
     .op .XOR,
     .op .ADD,
     .op .ADD,
     .push 4 constant,
     .op .ADD,
     .op (.Dup ⟨12, by decide⟩),
     .op .AND,
     .op .MUL,
     .push 1 (UInt256.ofNat 32),
     .op .SHR,
     .op (.Dup ⟨8, by decide⟩),
     .op .ADD,
     .op (.Dup ⟨11, by decide⟩),
     .op .AND,
     .op (.Swap ⟨5, by decide⟩),
     .op (.Dup ⟨10, by decide⟩),
     .op .MUL,
     .push 1 (UInt256.ofNat 22),
     .op .SHR,
     .op (.Swap ⟨7, by decide⟩),
     .op (.Swap ⟨0, by decide⟩),
     .op .MLOAD,
     .op (.Dup ⟨6, by decide⟩),
     .op (.Dup ⟨8, by decide⟩),
     .op .XOR,
     .op (.Dup ⟨9, by decide⟩),
     .op .AND,
     .op (.Dup ⟨8, by decide⟩),
     .op .XOR,
     .op .ADD,
     .op .ADD,
     .push 4 constant,
     .op .ADD,
     .op (.Dup ⟨10, by decide⟩),
     .op .AND,
     .op .MUL,
     .push 1 (UInt256.ofNat 32),
     .op .SHR,
     .op (.Dup ⟨7, by decide⟩),
     .op .ADD,
     .op (.Dup ⟨9, by decide⟩),
     .op .AND,
     .op (.Swap ⟨4, by decide⟩),
     .op (.Dup ⟨8, by decide⟩),
     .op .MUL,
     .push 1 (UInt256.ofNat 22),
     .op .SHR,
     .op (.Swap ⟨6, by decide⟩),
     .op (.Swap ⟨0, by decide⟩),
     .op .MLOAD,
     .op (.Dup ⟨5, by decide⟩),
     .op (.Dup ⟨5, by decide⟩),
     .op .XOR,
     .op (.Dup ⟨8, by decide⟩),
     .op .AND,
     .op (.Dup ⟨5, by decide⟩),
     .op .XOR,
     .op .ADD,
     .op .ADD,
     .push 4 constant,
     .op .ADD,
     .op (.Dup ⟨8, by decide⟩),
     .op .AND,
     .op .MUL,
     .push 1 (UInt256.ofNat 32),
     .op .SHR,
     .op (.Dup ⟨4, by decide⟩),
     .op .ADD,
     .op (.Dup ⟨7, by decide⟩),
     .op .AND,
     .op (.Swap ⟨1, by decide⟩),
     .op (.Dup ⟨6, by decide⟩),
     .op .MUL,
     .push 1 (UInt256.ofNat 22),
     .op .SHR,
     .op (.Swap ⟨3, by decide⟩),
     .op (.Swap ⟨0, by decide⟩)]

def leftTemplate4 (constant : UInt256) : List Instr :=
  [.op .JUMPDEST,
     .op .MLOAD,
     .op (.Dup ⟨12, by decide⟩),
     .op .NOT,
     .op (.Dup ⟨12, by decide⟩),
     .op .OR,
     .op (.Dup ⟨11, by decide⟩),
     .op .XOR,
     .op .ADD,
     .op (.Swap ⟨0, by decide⟩),
     .op (.Swap ⟨8, by decide⟩),
     .op .ADD,
     .push 4 constant,
     .op .ADD,
     .op (.Dup ⟨14, by decide⟩),
     .op .AND,
     .op .MUL,
     .push 1 (UInt256.ofNat 32),
     .op .SHR,
     .op (.Dup ⟨11, by decide⟩),
     .op .ADD,
     .op (.Dup ⟨13, by decide⟩),
     .op .AND,
     .op (.Swap ⟨8, by decide⟩),
     .op (.Dup ⟨12, by decide⟩),
     .op .MUL,
     .push 1 (UInt256.ofNat 22),
     .op .SHR,
     .op (.Swap ⟨10, by decide⟩),
     .op (.Swap ⟨0, by decide⟩),
     .op .MLOAD,
     .op (.Dup ⟨11, by decide⟩),
     .op .NOT,
     .op (.Dup ⟨9, by decide⟩),
     .op .OR,
     .op (.Dup ⟨10, by decide⟩),
     .op .XOR,
     .op .ADD,
     .op .ADD,
     .push 4 constant,
     .op .ADD,
     .op (.Dup ⟨12, by decide⟩),
     .op .AND,
     .op .MUL,
     .push 1 (UInt256.ofNat 32),
     .op .SHR,
     .op (.Dup ⟨8, by decide⟩),
     .op .ADD,
     .op (.Dup ⟨11, by decide⟩),
     .op .AND,
     .op (.Swap ⟨5, by decide⟩),
     .op (.Dup ⟨10, by decide⟩),
     .op .MUL,
     .push 1 (UInt256.ofNat 22),
     .op .SHR,
     .op (.Swap ⟨7, by decide⟩),
     .op (.Swap ⟨0, by decide⟩),
     .op .MLOAD,
     .op (.Dup ⟨8, by decide⟩),
     .op .NOT,
     .op (.Dup ⟨8, by decide⟩),
     .op .OR,
     .op (.Dup ⟨7, by decide⟩),
     .op .XOR,
     .op .ADD,
     .op .ADD,
     .push 4 constant,
     .op .ADD,
     .op (.Dup ⟨10, by decide⟩),
     .op .AND,
     .op .MUL,
     .push 1 (UInt256.ofNat 32),
     .op .SHR,
     .op (.Dup ⟨7, by decide⟩),
     .op .ADD,
     .op (.Dup ⟨9, by decide⟩),
     .op .AND,
     .op (.Swap ⟨4, by decide⟩),
     .op (.Dup ⟨8, by decide⟩),
     .op .MUL,
     .push 1 (UInt256.ofNat 22),
     .op .SHR,
     .op (.Swap ⟨6, by decide⟩),
     .op (.Swap ⟨0, by decide⟩),
     .op .MLOAD,
     .op (.Dup ⟨7, by decide⟩),
     .op .NOT,
     .op (.Dup ⟨5, by decide⟩),
     .op .OR,
     .op (.Dup ⟨6, by decide⟩),
     .op .XOR,
     .op .ADD,
     .op .ADD,
     .push 4 constant,
     .op .ADD,
     .op (.Dup ⟨8, by decide⟩),
     .op .AND,
     .op .MUL,
     .push 1 (UInt256.ofNat 32),
     .op .SHR,
     .op (.Dup ⟨4, by decide⟩),
     .op .ADD,
     .op (.Dup ⟨7, by decide⟩),
     .op .AND,
     .op (.Swap ⟨1, by decide⟩),
     .op (.Dup ⟨6, by decide⟩),
     .op .MUL,
     .push 1 (UInt256.ofNat 22),
     .op .SHR,
     .op (.Swap ⟨3, by decide⟩),
     .op (.Swap ⟨0, by decide⟩)]

def rightTemplate0 (_constant : UInt256) : List Instr :=
  [.op .JUMPDEST,
     .op .MLOAD,
     .op (.Dup ⟨10, by decide⟩),
     .op (.Dup ⟨12, by decide⟩),
     .op .XOR,
     .op (.Dup ⟨13, by decide⟩),
     .op .XOR,
     .op .ADD,
     .op (.Swap ⟨0, by decide⟩),
     .op (.Swap ⟨8, by decide⟩),
     .op .ADD,
     .push 4 (UInt256.ofNat 4294967295),
     .op .AND,
     .op .MUL,
     .push 1 (UInt256.ofNat 32),
     .op .SHR,
     .op (.Dup ⟨11, by decide⟩),
     .op .ADD,
     .push 4 (UInt256.ofNat 4294967295),
     .op .AND,
     .op (.Swap ⟨8, by decide⟩),
     .op (.Dup ⟨12, by decide⟩),
     .op .MUL,
     .push 1 (UInt256.ofNat 22),
     .op .SHR,
     .op (.Swap ⟨10, by decide⟩),
     .op (.Swap ⟨0, by decide⟩),
     .op .MLOAD,
     .op (.Dup ⟨9, by decide⟩),
     .op (.Dup ⟨9, by decide⟩),
     .op .XOR,
     .op (.Dup ⟨12, by decide⟩),
     .op .XOR,
     .op .ADD,
     .op .ADD,
     .push 4 (UInt256.ofNat 4294967295),
     .op .AND,
     .op .MUL,
     .push 1 (UInt256.ofNat 32),
     .op .SHR,
     .op (.Dup ⟨8, by decide⟩),
     .op .ADD,
     .push 4 (UInt256.ofNat 4294967295),
     .op .AND,
     .op (.Swap ⟨5, by decide⟩),
     .op (.Dup ⟨10, by decide⟩),
     .op .MUL,
     .push 1 (UInt256.ofNat 22),
     .op .SHR,
     .op (.Swap ⟨7, by decide⟩),
     .op (.Swap ⟨0, by decide⟩),
     .op .MLOAD,
     .op (.Dup ⟨6, by decide⟩),
     .op (.Dup ⟨8, by decide⟩),
     .op .XOR,
     .op (.Dup ⟨9, by decide⟩),
     .op .XOR,
     .op .ADD,
     .op .ADD,
     .op (.Dup ⟨15, by decide⟩),
     .op .AND,
     .op .MUL,
     .push 1 (UInt256.ofNat 32),
     .op .SHR,
     .op (.Dup ⟨7, by decide⟩),
     .op .ADD,
     .op (.Dup ⟨14, by decide⟩),
     .op .AND,
     .op (.Swap ⟨4, by decide⟩),
     .op (.Dup ⟨8, by decide⟩),
     .op .MUL,
     .push 1 (UInt256.ofNat 22),
     .op .SHR,
     .op (.Swap ⟨6, by decide⟩),
     .op (.Swap ⟨0, by decide⟩),
     .op .MLOAD,
     .op (.Dup ⟨5, by decide⟩),
     .op (.Dup ⟨5, by decide⟩),
     .op .XOR,
     .op (.Dup ⟨8, by decide⟩),
     .op .XOR,
     .op .ADD,
     .op .ADD,
     .op (.Dup ⟨13, by decide⟩),
     .op .AND,
     .op .MUL,
     .push 1 (UInt256.ofNat 32),
     .op .SHR,
     .op (.Dup ⟨4, by decide⟩),
     .op .ADD,
     .op (.Dup ⟨12, by decide⟩),
     .op .AND,
     .op (.Swap ⟨1, by decide⟩),
     .op (.Dup ⟨6, by decide⟩),
     .op .MUL,
     .push 1 (UInt256.ofNat 22),
     .op .SHR,
     .op (.Swap ⟨3, by decide⟩),
     .op (.Swap ⟨0, by decide⟩)]

def rightTemplate1 (constant : UInt256) : List Instr :=
  [.op .JUMPDEST,
     .op .MLOAD,
     .op (.Dup ⟨11, by decide⟩),
     .op (.Dup ⟨13, by decide⟩),
     .op .XOR,
     .op (.Dup ⟨11, by decide⟩),
     .op .AND,
     .op (.Dup ⟨13, by decide⟩),
     .op .XOR,
     .op .ADD,
     .op (.Swap ⟨0, by decide⟩),
     .op (.Swap ⟨8, by decide⟩),
     .op .ADD,
     .push 4 constant,
     .op .ADD,
     .push 4 (UInt256.ofNat 4294967295),
     .op .AND,
     .op .MUL,
     .push 1 (UInt256.ofNat 32),
     .op .SHR,
     .op (.Dup ⟨11, by decide⟩),
     .op .ADD,
     .push 4 (UInt256.ofNat 4294967295),
     .op .AND,
     .op (.Swap ⟨8, by decide⟩),
     .op (.Dup ⟨12, by decide⟩),
     .op .MUL,
     .push 1 (UInt256.ofNat 22),
     .op .SHR,
     .op (.Swap ⟨10, by decide⟩),
     .op (.Swap ⟨0, by decide⟩),
     .op .MLOAD,
     .op (.Dup ⟨8, by decide⟩),
     .op (.Dup ⟨12, by decide⟩),
     .op .XOR,
     .op (.Dup ⟨10, by decide⟩),
     .op .AND,
     .op (.Dup ⟨12, by decide⟩),
     .op .XOR,
     .op .ADD,
     .op .ADD,
     .push 4 constant,
     .op .ADD,
     .push 4 (UInt256.ofNat 4294967295),
     .op .AND,
     .op .MUL,
     .push 1 (UInt256.ofNat 32),
     .op .SHR,
     .op (.Dup ⟨8, by decide⟩),
     .op .ADD,
     .push 4 (UInt256.ofNat 4294967295),
     .op .AND,
     .op (.Swap ⟨5, by decide⟩),
     .op (.Dup ⟨10, by decide⟩),
     .op .MUL,
     .push 1 (UInt256.ofNat 22),
     .op .SHR,
     .op (.Swap ⟨7, by decide⟩),
     .op (.Swap ⟨0, by decide⟩),
     .op .MLOAD,
     .op (.Dup ⟨7, by decide⟩),
     .op (.Dup ⟨9, by decide⟩),
     .op .XOR,
     .op (.Dup ⟨7, by decide⟩),
     .op .AND,
     .op (.Dup ⟨9, by decide⟩),
     .op .XOR,
     .op .ADD,
     .op .ADD,
     .push 4 constant,
     .op .ADD,
     .op (.Dup ⟨15, by decide⟩),
     .op .AND,
     .op .MUL,
     .push 1 (UInt256.ofNat 32),
     .op .SHR,
     .op (.Dup ⟨7, by decide⟩),
     .op .ADD,
     .op (.Dup ⟨14, by decide⟩),
     .op .AND,
     .op (.Swap ⟨4, by decide⟩),
     .op (.Dup ⟨8, by decide⟩),
     .op .MUL,
     .push 1 (UInt256.ofNat 22),
     .op .SHR,
     .op (.Swap ⟨6, by decide⟩),
     .op (.Swap ⟨0, by decide⟩),
     .op .MLOAD,
     .op (.Dup ⟨4, by decide⟩),
     .op (.Dup ⟨8, by decide⟩),
     .op .XOR,
     .op (.Dup ⟨6, by decide⟩),
     .op .AND,
     .op (.Dup ⟨8, by decide⟩),
     .op .XOR,
     .op .ADD,
     .op .ADD,
     .push 4 constant,
     .op .ADD,
     .op (.Dup ⟨13, by decide⟩),
     .op .AND,
     .op .MUL,
     .push 1 (UInt256.ofNat 32),
     .op .SHR,
     .op (.Dup ⟨4, by decide⟩),
     .op .ADD,
     .op (.Dup ⟨12, by decide⟩),
     .op .AND,
     .op (.Swap ⟨1, by decide⟩),
     .op (.Dup ⟨6, by decide⟩),
     .op .MUL,
     .push 1 (UInt256.ofNat 22),
     .op .SHR,
     .op (.Swap ⟨3, by decide⟩),
     .op (.Swap ⟨0, by decide⟩)]

def rightTemplate2 (constant : UInt256) : List Instr :=
  [.op .JUMPDEST,
     .op .MLOAD,
     .op (.Dup ⟨11, by decide⟩),
     .op .NOT,
     .op (.Dup ⟨11, by decide⟩),
     .op .OR,
     .op (.Dup ⟨13, by decide⟩),
     .op .XOR,
     .op .ADD,
     .op (.Swap ⟨0, by decide⟩),
     .op (.Swap ⟨8, by decide⟩),
     .op .ADD,
     .push 4 constant,
     .op .ADD,
     .push 4 (UInt256.ofNat 4294967295),
     .op .AND,
     .op .MUL,
     .push 1 (UInt256.ofNat 32),
     .op .SHR,
     .op (.Dup ⟨11, by decide⟩),
     .op .ADD,
     .push 4 (UInt256.ofNat 4294967295),
     .op .AND,
     .op (.Swap ⟨8, by decide⟩),
     .op (.Dup ⟨12, by decide⟩),
     .op .MUL,
     .push 1 (UInt256.ofNat 22),
     .op .SHR,
     .op (.Swap ⟨10, by decide⟩),
     .op (.Swap ⟨0, by decide⟩),
     .op .MLOAD,
     .op (.Dup ⟨8, by decide⟩),
     .op .NOT,
     .op (.Dup ⟨10, by decide⟩),
     .op .OR,
     .op (.Dup ⟨12, by decide⟩),
     .op .XOR,
     .op .ADD,
     .op .ADD,
     .push 4 constant,
     .op .ADD,
     .push 4 (UInt256.ofNat 4294967295),
     .op .AND,
     .op .MUL,
     .push 1 (UInt256.ofNat 32),
     .op .SHR,
     .op (.Dup ⟨8, by decide⟩),
     .op .ADD,
     .push 4 (UInt256.ofNat 4294967295),
     .op .AND,
     .op (.Swap ⟨5, by decide⟩),
     .op (.Dup ⟨10, by decide⟩),
     .op .MUL,
     .push 1 (UInt256.ofNat 22),
     .op .SHR,
     .op (.Swap ⟨7, by decide⟩),
     .op (.Swap ⟨0, by decide⟩),
     .op .MLOAD,
     .op (.Dup ⟨7, by decide⟩),
     .op .NOT,
     .op (.Dup ⟨7, by decide⟩),
     .op .OR,
     .op (.Dup ⟨9, by decide⟩),
     .op .XOR,
     .op .ADD,
     .op .ADD,
     .push 4 constant,
     .op .ADD,
     .op (.Dup ⟨15, by decide⟩),
     .op .AND,
     .op .MUL,
     .push 1 (UInt256.ofNat 32),
     .op .SHR,
     .op (.Dup ⟨7, by decide⟩),
     .op .ADD,
     .op (.Dup ⟨14, by decide⟩),
     .op .AND,
     .op (.Swap ⟨4, by decide⟩),
     .op (.Dup ⟨8, by decide⟩),
     .op .MUL,
     .push 1 (UInt256.ofNat 22),
     .op .SHR,
     .op (.Swap ⟨6, by decide⟩),
     .op (.Swap ⟨0, by decide⟩),
     .op .MLOAD,
     .op (.Dup ⟨4, by decide⟩),
     .op .NOT,
     .op (.Dup ⟨6, by decide⟩),
     .op .OR,
     .op (.Dup ⟨8, by decide⟩),
     .op .XOR,
     .op .ADD,
     .op .ADD,
     .push 4 constant,
     .op .ADD,
     .op (.Dup ⟨13, by decide⟩),
     .op .AND,
     .op .MUL,
     .push 1 (UInt256.ofNat 32),
     .op .SHR,
     .op (.Dup ⟨4, by decide⟩),
     .op .ADD,
     .op (.Dup ⟨12, by decide⟩),
     .op .AND,
     .op (.Swap ⟨1, by decide⟩),
     .op (.Dup ⟨6, by decide⟩),
     .op .MUL,
     .push 1 (UInt256.ofNat 22),
     .op .SHR,
     .op (.Swap ⟨3, by decide⟩),
     .op (.Swap ⟨0, by decide⟩)]

def rightTemplate3 (constant : UInt256) : List Instr :=
  [.op .JUMPDEST,
     .op .MLOAD,
     .op (.Dup ⟨10, by decide⟩),
     .op (.Dup ⟨12, by decide⟩),
     .op .XOR,
     .op (.Dup ⟨13, by decide⟩),
     .op .AND,
     .op (.Dup ⟨12, by decide⟩),
     .op .XOR,
     .op .ADD,
     .op (.Swap ⟨0, by decide⟩),
     .op (.Swap ⟨8, by decide⟩),
     .op .ADD,
     .push 4 constant,
     .op .ADD,
     .push 4 (UInt256.ofNat 4294967295),
     .op .AND,
     .op .MUL,
     .push 1 (UInt256.ofNat 32),
     .op .SHR,
     .op (.Dup ⟨11, by decide⟩),
     .op .ADD,
     .push 4 (UInt256.ofNat 4294967295),
     .op .AND,
     .op (.Swap ⟨8, by decide⟩),
     .op (.Dup ⟨12, by decide⟩),
     .op .MUL,
     .push 1 (UInt256.ofNat 22),
     .op .SHR,
     .op (.Swap ⟨10, by decide⟩),
     .op (.Swap ⟨0, by decide⟩),
     .op .MLOAD,
     .op (.Dup ⟨9, by decide⟩),
     .op (.Dup ⟨9, by decide⟩),
     .op .XOR,
     .op (.Dup ⟨12, by decide⟩),
     .op .AND,
     .op (.Dup ⟨9, by decide⟩),
     .op .XOR,
     .op .ADD,
     .op .ADD,
     .push 4 constant,
     .op .ADD,
     .push 4 (UInt256.ofNat 4294967295),
     .op .AND,
     .op .MUL,
     .push 1 (UInt256.ofNat 32),
     .op .SHR,
     .op (.Dup ⟨8, by decide⟩),
     .op .ADD,
     .push 4 (UInt256.ofNat 4294967295),
     .op .AND,
     .op (.Swap ⟨5, by decide⟩),
     .op (.Dup ⟨10, by decide⟩),
     .op .MUL,
     .push 1 (UInt256.ofNat 22),
     .op .SHR,
     .op (.Swap ⟨7, by decide⟩),
     .op (.Swap ⟨0, by decide⟩),
     .op .MLOAD,
     .op (.Dup ⟨6, by decide⟩),
     .op (.Dup ⟨8, by decide⟩),
     .op .XOR,
     .op (.Dup ⟨9, by decide⟩),
     .op .AND,
     .op (.Dup ⟨8, by decide⟩),
     .op .XOR,
     .op .ADD,
     .op .ADD,
     .push 4 constant,
     .op .ADD,
     .op (.Dup ⟨15, by decide⟩),
     .op .AND,
     .op .MUL,
     .push 1 (UInt256.ofNat 32),
     .op .SHR,
     .op (.Dup ⟨7, by decide⟩),
     .op .ADD,
     .op (.Dup ⟨14, by decide⟩),
     .op .AND,
     .op (.Swap ⟨4, by decide⟩),
     .op (.Dup ⟨8, by decide⟩),
     .op .MUL,
     .push 1 (UInt256.ofNat 22),
     .op .SHR,
     .op (.Swap ⟨6, by decide⟩),
     .op (.Swap ⟨0, by decide⟩),
     .op .MLOAD,
     .op (.Dup ⟨5, by decide⟩),
     .op (.Dup ⟨5, by decide⟩),
     .op .XOR,
     .op (.Dup ⟨8, by decide⟩),
     .op .AND,
     .op (.Dup ⟨5, by decide⟩),
     .op .XOR,
     .op .ADD,
     .op .ADD,
     .push 4 constant,
     .op .ADD,
     .op (.Dup ⟨13, by decide⟩),
     .op .AND,
     .op .MUL,
     .push 1 (UInt256.ofNat 32),
     .op .SHR,
     .op (.Dup ⟨4, by decide⟩),
     .op .ADD,
     .op (.Dup ⟨12, by decide⟩),
     .op .AND,
     .op (.Swap ⟨1, by decide⟩),
     .op (.Dup ⟨6, by decide⟩),
     .op .MUL,
     .push 1 (UInt256.ofNat 22),
     .op .SHR,
     .op (.Swap ⟨3, by decide⟩),
     .op (.Swap ⟨0, by decide⟩)]

def rightTemplate4 (constant : UInt256) : List Instr :=
  [.op .JUMPDEST,
     .op .MLOAD,
     .op (.Dup ⟨12, by decide⟩),
     .op .NOT,
     .op (.Dup ⟨12, by decide⟩),
     .op .OR,
     .op (.Dup ⟨11, by decide⟩),
     .op .XOR,
     .op .ADD,
     .op (.Swap ⟨0, by decide⟩),
     .op (.Swap ⟨8, by decide⟩),
     .op .ADD,
     .push 4 constant,
     .op .ADD,
     .push 4 (UInt256.ofNat 4294967295),
     .op .AND,
     .op .MUL,
     .push 1 (UInt256.ofNat 32),
     .op .SHR,
     .op (.Dup ⟨11, by decide⟩),
     .op .ADD,
     .push 4 (UInt256.ofNat 4294967295),
     .op .AND,
     .op (.Swap ⟨8, by decide⟩),
     .op (.Dup ⟨12, by decide⟩),
     .op .MUL,
     .push 1 (UInt256.ofNat 22),
     .op .SHR,
     .op (.Swap ⟨10, by decide⟩),
     .op (.Swap ⟨0, by decide⟩),
     .op .MLOAD,
     .op (.Dup ⟨11, by decide⟩),
     .op .NOT,
     .op (.Dup ⟨9, by decide⟩),
     .op .OR,
     .op (.Dup ⟨10, by decide⟩),
     .op .XOR,
     .op .ADD,
     .op .ADD,
     .push 4 constant,
     .op .ADD,
     .push 4 (UInt256.ofNat 4294967295),
     .op .AND,
     .op .MUL,
     .push 1 (UInt256.ofNat 32),
     .op .SHR,
     .op (.Dup ⟨8, by decide⟩),
     .op .ADD,
     .push 4 (UInt256.ofNat 4294967295),
     .op .AND,
     .op (.Swap ⟨5, by decide⟩),
     .op (.Dup ⟨10, by decide⟩),
     .op .MUL,
     .push 1 (UInt256.ofNat 22),
     .op .SHR,
     .op (.Swap ⟨7, by decide⟩),
     .op (.Swap ⟨0, by decide⟩),
     .op .MLOAD,
     .op (.Dup ⟨8, by decide⟩),
     .op .NOT,
     .op (.Dup ⟨8, by decide⟩),
     .op .OR,
     .op (.Dup ⟨7, by decide⟩),
     .op .XOR,
     .op .ADD,
     .op .ADD,
     .push 4 constant,
     .op .ADD,
     .op (.Dup ⟨15, by decide⟩),
     .op .AND,
     .op .MUL,
     .push 1 (UInt256.ofNat 32),
     .op .SHR,
     .op (.Dup ⟨7, by decide⟩),
     .op .ADD,
     .op (.Dup ⟨14, by decide⟩),
     .op .AND,
     .op (.Swap ⟨4, by decide⟩),
     .op (.Dup ⟨8, by decide⟩),
     .op .MUL,
     .push 1 (UInt256.ofNat 22),
     .op .SHR,
     .op (.Swap ⟨6, by decide⟩),
     .op (.Swap ⟨0, by decide⟩),
     .op .MLOAD,
     .op (.Dup ⟨7, by decide⟩),
     .op .NOT,
     .op (.Dup ⟨5, by decide⟩),
     .op .OR,
     .op (.Dup ⟨6, by decide⟩),
     .op .XOR,
     .op .ADD,
     .op .ADD,
     .push 4 constant,
     .op .ADD,
     .op (.Dup ⟨13, by decide⟩),
     .op .AND,
     .op .MUL,
     .push 1 (UInt256.ofNat 32),
     .op .SHR,
     .op (.Dup ⟨4, by decide⟩),
     .op .ADD,
     .op (.Dup ⟨12, by decide⟩),
     .op .AND,
     .op (.Swap ⟨1, by decide⟩),
     .op (.Dup ⟨6, by decide⟩),
     .op .MUL,
     .push 1 (UInt256.ofNat 22),
     .op .SHR,
     .op (.Swap ⟨3, by decide⟩),
     .op (.Swap ⟨0, by decide⟩)]

def leftTemplate (j : Nat) (constant : UInt256) : List Instr :=
  match j with
  | 0 => leftTemplate0 constant
  | 1 => leftTemplate1 constant
  | 2 => leftTemplate2 constant
  | 3 => leftTemplate3 constant
  | _ => leftTemplate4 constant

def rightTemplate (j : Nat) (constant : UInt256) : List Instr :=
  match j with
  | 0 => rightTemplate0 constant
  | 1 => rightTemplate1 constant
  | 2 => rightTemplate2 constant
  | 3 => rightTemplate3 constant
  | _ => rightTemplate4 constant

theorem shiftedFactor_eq_shiftLeft (r : Nat)
    (hr0 : 0 < r) (hr32 : r < 32) :
    shiftedFactor r =
      UInt256.shiftLeft (UInt256.ofNat (0x100000001 : Nat))
        (UInt256.ofNat r) := by
  have hbound : (0x100000001 : Nat) * 2 ^ r < 2 ^ 256 := by
    have hpow : 2 ^ r ≤ 2 ^ 31 := by
      exact Nat.pow_le_pow_right Nat.zero_lt_two (by omega)
    calc
      (0x100000001 : Nat) * 2 ^ r ≤ 0x100000001 * 2 ^ 31 :=
        Nat.mul_le_mul_left _ hpow
      _ < 2 ^ 256 := by norm_num [← Nat.pow_add]
  unfold shiftedFactor
  symm
  rw [Challenge.EvmProof.Word.shiftLeft_ofNat (by norm_num) (by omega) hbound]
  congr 1
  simp [Nat.shiftLeft_eq]

set_option linter.unusedSimpArgs false in
theorem left_equiv (j : Nat) (hj : j < 5)
    (s : State) (startPC p0 p1 p2 p3 returnPC : UInt256)
    (r0 r1 r2 r3 : Nat) (constant : UInt256)
    (working : Compression.EvmWorking) (rho : List UInt256)
    (hrot0 : 0 < r0) (hrot0' : r0 < 32)
    (hrot1 : 0 < r1) (hrot1' : r1 < 32)
    (hrot2 : 0 < r2) (hrot2' : r2 < 32)
    (hrot3 : 0 < r3) (hrot3' : r3 < 32)
    (hstack : rho.length < 1006) (hrun : s.halt = .Running) :
    runInstrSeq (leftTemplate j constant)
      (quadHelperEntry s startPC p0 p1 p2 p3 returnPC
        r0 r1 r2 r3 working (mask :: rho)) =
    Option.map (fun out => {out with pc := pcAfter startPC (leftTemplate j constant)})
      (runInstrSeq (CachedMaskHoistHelper.leftTemplate j constant)
        (QuadRoundState.quadHelperEntry s startPC p0 p1 p2 p3 returnPC
          r0 r1 r2 r3 working (mask :: rho))) := by
  have hrot (u : UInt256) (r : Nat) (hr0 : 0 < r) (hr32 : r < 32) :
      UInt256.shiftRight (UInt256.land mask u * shiftedFactor r) (UInt256.ofNat 32) =
        UInt256.shiftRight (QuadRoundTemplate.factor * UInt256.land mask u)
          (UInt256.ofNat (32 - r)) := by
    rw [shiftedFactor_eq_shiftLeft r hr0 hr32]
    exact (RotationParameter.factor_shift_eq _ r
      (SharedRoundTrace.mask_land_toNat_lt u) hr0 hr32).symm
  have hrot0eq (u : UInt256) := hrot u r0 hrot0 hrot0'
  have hrot1eq (u : UInt256) := hrot u r1 hrot1 hrot1'
  have hrot2eq (u : UInt256) := hrot u r2 hrot2 hrot2'
  have hrot3eq (u : UInt256) := hrot u r3 hrot3 hrot3'
  have hmul (u v : UInt256) : u.mul v = u * v := rfl
  have hcap (m : Nat) (hm : m ≤ 18) : rho.length + m < 1024 := by omega
  have hadd (u v : UInt256) : u.add v = u + v := rfl
  have hassoc (u v w : UInt256) : (u + v) + w = u + (v + w) := by
    apply Word.word_ext
    change ((u.val + v.val) + w.val).val = (u.val + (v.val + w.val)).val
    simp [Fin.add_def, Nat.add_assoc]
  have hpc (u : UInt256) (a b : Nat) :
      (u + UInt256.ofNat a) + UInt256.ofNat b =
        u + UInt256.ofNat (a + b) := by
    rw [hassoc, Word.ofNat_add_mod]
  interval_cases j <;>
    dsimp only [leftTemplate, leftTemplate0, leftTemplate1,
      leftTemplate2, leftTemplate3, leftTemplate4,
      CachedMaskHoistHelper.leftTemplate,
      CachedMaskHoistHelper.leftTemplate0, CachedMaskHoistHelper.leftTemplate1,
      CachedMaskHoistHelper.leftTemplate2, CachedMaskHoistHelper.leftTemplate3,
      CachedMaskHoistHelper.leftTemplate4] <;>
    simp (config := { maxSteps := 5000000 })
      [quadHelperEntry, QuadRoundState.quadHelperEntry, roundWords,
       runInstrSeq, Stepper.runInstr, pcAfter, List.exchange,
       hrun, hcap, hmul, hrot0eq, hrot1eq, hrot2eq, hrot3eq, UInt256.succ, Instr.size, Instr.size_op, Instr.size_push,
       State.activeWordsAfterUInt256, hadd, Word.word_add_comm, hpc,
       Word.ofNat_add_mod, Word.word_toNat_ofNat, Nat.add_assoc]


set_option linter.unusedSimpArgs false in
theorem right_equiv (j : Nat) (hj : j < 5)
    (s : State) (startPC p0 p1 p2 p3 returnPC : UInt256)
    (r0 r1 r2 r3 : Nat) (constant : UInt256)
    (working : Compression.EvmWorking) (a b c d e : UInt256)
    (rho : List UInt256)
    (hrot0 : 0 < r0) (hrot0' : r0 < 32)
    (hrot1 : 0 < r1) (hrot1' : r1 < 32)
    (hrot2 : 0 < r2) (hrot2' : r2 < 32)
    (hrot3 : 0 < r3) (hrot3' : r3 < 32)
    (hstack : rho.length < 1001) (hrun : s.halt = .Running) :
    runInstrSeq (rightTemplate j constant)
      (quadHelperEntry s startPC p0 p1 p2 p3 returnPC
        r0 r1 r2 r3 working (a :: b :: c :: d :: e :: mask :: rho)) =
    Option.map (fun out => {out with pc := pcAfter startPC (rightTemplate j constant)})
      (runInstrSeq (CachedMaskHoistHelper.rightTemplate j constant)
        (QuadRoundState.quadHelperEntry s startPC p0 p1 p2 p3 returnPC
          r0 r1 r2 r3 working (a :: b :: c :: d :: e :: mask :: rho))) := by
  have hrot (u : UInt256) (r : Nat) (hr0 : 0 < r) (hr32 : r < 32) :
      UInt256.shiftRight (UInt256.land mask u * shiftedFactor r) (UInt256.ofNat 32) =
        UInt256.shiftRight (QuadRoundTemplate.factor * UInt256.land mask u)
          (UInt256.ofNat (32 - r)) := by
    rw [shiftedFactor_eq_shiftLeft r hr0 hr32]
    exact (RotationParameter.factor_shift_eq _ r
      (SharedRoundTrace.mask_land_toNat_lt u) hr0 hr32).symm
  have hrot0eq (u : UInt256) := hrot u r0 hrot0 hrot0'
  have hrot1eq (u : UInt256) := hrot u r1 hrot1 hrot1'
  have hrot2eq (u : UInt256) := hrot u r2 hrot2 hrot2'
  have hrot3eq (u : UInt256) := hrot u r3 hrot3 hrot3'
  have hmul (u v : UInt256) : u.mul v = u * v := rfl
  have hmaskLiteral : UInt256.ofNat 4294967295 = mask := rfl
  have hcap (m : Nat) (hm : m ≤ 23) : rho.length + m < 1024 := by omega
  have hadd (u v : UInt256) : u.add v = u + v := rfl
  have hassoc (u v w : UInt256) : (u + v) + w = u + (v + w) := by
    apply Word.word_ext
    change ((u.val + v.val) + w.val).val = (u.val + (v.val + w.val)).val
    simp [Fin.add_def, Nat.add_assoc]
  have hpc (u : UInt256) (a b : Nat) :
      (u + UInt256.ofNat a) + UInt256.ofNat b =
        u + UInt256.ofNat (a + b) := by
    rw [hassoc, Word.ofNat_add_mod]
  interval_cases j <;>
    dsimp only [rightTemplate, rightTemplate0, rightTemplate1,
      rightTemplate2, rightTemplate3, rightTemplate4,
      CachedMaskHoistHelper.rightTemplate,
      CachedMaskHoistHelper.rightTemplate0, CachedMaskHoistHelper.rightTemplate1,
      CachedMaskHoistHelper.rightTemplate2, CachedMaskHoistHelper.rightTemplate3,
      CachedMaskHoistHelper.rightTemplate4] <;>
    simp (config := { maxSteps := 5000000 })
      [quadHelperEntry, QuadRoundState.quadHelperEntry, roundWords,
       runInstrSeq, Stepper.runInstr, pcAfter, List.exchange,
       hrun, hcap, hmul, hmaskLiteral, hrot0eq, hrot1eq, hrot2eq, hrot3eq, UInt256.succ, Instr.size, Instr.size_op, Instr.size_push,
       State.activeWordsAfterUInt256, hadd, Word.word_add_comm, hpc,
       Word.ofNat_add_mod, Word.word_toNat_ofNat, Nat.add_assoc]

theorem run_left (j : Nat) (hj : j < 5)
    (s : State) (startPC p0 p1 p2 p3 returnPC : UInt256)
    (r0 r1 r2 r3 : Nat) (working : Compression.EvmWorking)
    (constant : UInt256) (rho : List UInt256)
    (hzero : j = 0 → constant = 0)
    (hstack : rho.length < 1006) (hrun : s.halt = .Running)
    (hrot0 : 0 < r0) (hrot0' : r0 < 32) (hrot1 : 0 < r1) (hrot1' : r1 < 32)
    (hrot2 : 0 < r2) (hrot2' : r2 < 32) (hrot3 : 0 < r3) (hrot3' : r3 < 32) :
    runInstrSeq (leftTemplate j constant)
      (quadHelperEntry s startPC p0 p1 p2 p3 returnPC
        r0 r1 r2 r3 working (mask :: rho)) =
      some (quadAfterHelperBeforeJump s (pcAfter startPC (leftTemplate j constant))
        returnPC j working p0 p1 p2 p3 r0 r1 r2 r3 constant (mask :: rho)) := by
  rw [left_equiv j hj s startPC p0 p1 p2 p3 returnPC r0 r1 r2 r3
    constant working rho hrot0 hrot0' hrot1 hrot1' hrot2 hrot2' hrot3 hrot3' hstack hrun]
  rw [CachedMaskHoistHelper.run_left j hj s startPC p0 p1 p2 p3 returnPC
    r0 r1 r2 r3 working constant rho hzero hstack hrun
    (by omega) (by omega) (by omega) (by omega)]
  rfl

theorem run_right (j : Nat) (hj : j < 5)
    (s : State) (startPC p0 p1 p2 p3 returnPC : UInt256)
    (r0 r1 r2 r3 : Nat) (working : Compression.EvmWorking)
    (constant a b c d e : UInt256) (rho : List UInt256)
    (hzero : j = 0 → constant = 0)
    (hstack : rho.length < 1001) (hrun : s.halt = .Running)
    (hrot0 : 0 < r0) (hrot0' : r0 < 32) (hrot1 : 0 < r1) (hrot1' : r1 < 32)
    (hrot2 : 0 < r2) (hrot2' : r2 < 32) (hrot3 : 0 < r3) (hrot3' : r3 < 32) :
    runInstrSeq (rightTemplate j constant)
      (quadHelperEntry s startPC p0 p1 p2 p3 returnPC
        r0 r1 r2 r3 working (a :: b :: c :: d :: e :: mask :: rho)) =
      some (quadAfterHelperBeforeJump s (pcAfter startPC (rightTemplate j constant))
        returnPC j working p0 p1 p2 p3 r0 r1 r2 r3 constant
          (a :: b :: c :: d :: e :: mask :: rho)) := by
  rw [right_equiv j hj s startPC p0 p1 p2 p3 returnPC r0 r1 r2 r3
    constant working a b c d e rho hrot0 hrot0' hrot1 hrot1' hrot2 hrot2' hrot3 hrot3' hstack hrun]
  rw [CachedMaskHoistHelper.run_right j hj s startPC p0 p1 p2 p3 returnPC
    r0 r1 r2 r3 working constant a b c d e rho hzero hstack hrun
    (by omega) (by omega) (by omega) (by omega)]
  rfl


set_option linter.unusedSimpArgs false in
theorem left_advances (j : Nat) (hj : j < 5) (constant : UInt256) :
    ∀ instruction ∈ leftTemplate j constant,
      PairMultiplyLift.Advances instruction := by
  intro instruction hmem
  interval_cases j <;>
    dsimp only [leftTemplate, leftTemplate0, leftTemplate1,
      leftTemplate2, leftTemplate3, leftTemplate4,
      CachedMaskHoistHelper.leftTemplate,
      CachedMaskHoistHelper.leftTemplate0, CachedMaskHoistHelper.leftTemplate1,
      CachedMaskHoistHelper.leftTemplate2, CachedMaskHoistHelper.leftTemplate3,
      CachedMaskHoistHelper.leftTemplate4] at hmem <;>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem <;>
    simp_all [PairMultiplyLift.Advances, SharedCallTrace.Advances] <;>
    aesop (add safe constructors StraightLine)


set_option linter.unusedSimpArgs false in
theorem right_advances (j : Nat) (hj : j < 5) (constant : UInt256) :
    ∀ instruction ∈ rightTemplate j constant,
      PairMultiplyLift.Advances instruction := by
  intro instruction hmem
  interval_cases j <;>
    dsimp only [rightTemplate, rightTemplate0, rightTemplate1,
      rightTemplate2, rightTemplate3, rightTemplate4,
      CachedMaskHoistHelper.rightTemplate,
      CachedMaskHoistHelper.rightTemplate0, CachedMaskHoistHelper.rightTemplate1,
      CachedMaskHoistHelper.rightTemplate2, CachedMaskHoistHelper.rightTemplate3,
      CachedMaskHoistHelper.rightTemplate4] at hmem <;>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem <;>
    simp_all [PairMultiplyLift.Advances, SharedCallTrace.Advances] <;>
    aesop (add safe constructors StraightLine)


/-- Exact located execution for any certified pure helper implementation. -/
theorem runLocated_of_raw {artifact : ProgramArtifact} {fork : Fork}
    (helperCode : List Instr)
    (hform : ∀ i ∈ helperCode, PairMultiplyLift.Advances i)
    (j : Nat) (p0 p1 p2 p3 : UInt256) (r0 r1 r2 r3 : Nat)
    (constant : UInt256) (site : GenericRoundSite artifact fork helperCode)
    (s : State) (returnPC : UInt256) (working : Compression.EvmWorking)
    (rho : List UInt256)
    (hraw : runInstrSeq helperCode
      (quadHelperEntry s site.startPC p0 p1 p2 p3 returnPC r0 r1 r2 r3 working rho) =
      some (quadAfterHelperBeforeJump s (pcAfter site.startPC helperCode)
        returnPC j working p0 p1 p2 p3 r0 r1 r2 r3 constant rho)) :
    Stepper.runLocatedBlock site.path
      (quadHelperEntry s site.startPC p0 p1 p2 p3 returnPC r0 r1 r2 r3 working rho) =
      some (quadAfterHelperBeforeJump s site.endPC
        returnPC j working p0 p1 p2 p3 r0 r1 r2 r3 constant rho) := by
  have hend : site.endPC = pcAfter site.startPC helperCode := by
    have h := endPC_eq_pcAfter_sites site.sites site.startPC site.endPC
      site.head_eq site.end_eq site.contiguous
    rwa [site.instruction_eq] at h
  rw [PairMultiplyLift.runLocatedBlock_eq_raw site hform
    (quadHelperEntry s site.startPC p0 p1 p2 p3 returnPC r0 r1 r2 r3 working rho) rfl]
  rw [hraw, ← hend]

def gasSteps_of_raw {artifact : ProgramArtifact} {fork : Fork}
    (helperCode : List Instr)
    (hform : ∀ i ∈ helperCode, PairMultiplyLift.Advances i)
    (j : Nat) (p0 p1 p2 p3 : UInt256) (r0 r1 r2 r3 : Nat)
    (constant : UInt256) (site : GenericRoundSite artifact fork helperCode)
    (s : State) (returnPC : UInt256) (working : Compression.EvmWorking)
    (rho : List UInt256)
    (hraw : runInstrSeq helperCode
      (quadHelperEntry s site.startPC p0 p1 p2 p3 returnPC r0 r1 r2 r3 working rho) =
      some (quadAfterHelperBeforeJump s (pcAfter site.startPC helperCode)
        returnPC j working p0 p1 p2 p3 r0 r1 r2 r3 constant rho))
    (hrun : s.halt = .Running) (hcode : s.executionEnv.code = artifact.code)
    (hfork : s.fork = fork)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps
      (quadHelperEntry s site.startPC p0 p1 p2 p3 returnPC r0 r1 r2 r3 working rho)
      (quadAfterHelperBeforeJump s site.endPC
        returnPC j working p0 p1 p2 p3 r0 r1 r2 r3 constant rho) := by
  exact Stepper.runLocatedBlock_sound artifact fork site.path hcode hfork
    (runLocated_of_raw helperCode hform j p0 p1 p2 p3 r0 r1 r2 r3
      constant site s returnPC working rho hraw) hrun hnp


end Challenge.Ripemd160.Submission.Proofs.Bytecode.ShiftedHoistHelper
