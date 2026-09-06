import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTableMemory
import Challenge.EvmProof.Stepper

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleKernel

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler

def runInstructions : List Instr → State → Option State
  | [], state => some state
  | instruction :: rest, state => do
      let next ← Challenge.EvmProof.Stepper.runInstr instruction state
      runInstructions rest next

def squareProgram : List Instr :=
  [.op (.Dup ⟨5, by decide⟩), .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨0, by decide⟩), .op .MULMOD,
   .op (.Swap ⟨4, by decide⟩), .op .POP]

def lookupLoadProgram : List Instr :=
  [.op (.Dup ⟨0, by decide⟩), .push 1 5, .op .SHL, .op .MLOAD]

def lookupMulProgram : List Instr :=
  [.op (.Dup ⟨6, by decide⟩), .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨6, by decide⟩), .op .MULMOD,
   .op (.Swap ⟨4, by decide⟩), .op .POP]

def lookupProgram : List Instr := lookupLoadProgram ++ lookupMulProgram

def fourSquareProgram : List Instr :=
  squareProgram ++ squareProgram ++ squareProgram ++ squareProgram

def squareLookupProgram : List Instr := fourSquareProgram ++ lookupProgram

def advancePC : Nat → UInt256 → UInt256
  | 0, pc => pc
  | count + 1, pc => (advancePC count pc).succ

theorem word_add_assoc (left middle right : UInt256) :
    (left + middle) + right = left + (middle + right) := by
  cases left with
  | mk left =>
      cases middle with
      | mk middle =>
          cases right with
          | mk right =>
              change UInt256.mk ((left + middle) + right) =
                UInt256.mk (left + (middle + right))
              rw [add_assoc]

theorem advancePC_add (left right : Nat) (pc : UInt256) :
    advancePC (left + right) pc = advancePC right (advancePC left pc) := by
  induction right with
  | zero => simp [advancePC]
  | succ right ih =>
      rw [Nat.add_succ, advancePC, advancePC, ih]

theorem runInstructions_append (left right : List Instr) (state : State) :
    runInstructions (left ++ right) state =
      (runInstructions left state).bind (runInstructions right) := by
  induction left generalizing state with
  | nil => rfl
  | cons instruction left ih =>
      simp [runInstructions, ih, Option.bind_assoc]

theorem runInstructions_append_some (left right : List Instr) (start middle finish : State)
    (hleft : runInstructions left start = some middle)
    (hright : runInstructions right middle = some finish) :
    runInstructions (left ++ right) start = some finish := by
  rw [runInstructions_append, hleft]
  exact hright

def nibbleState (template : State) (pc : UInt256) (base modulus : UInt256)
    (nibble : Nat) (byte word pointer accumulator : UInt256)
    (rest : List UInt256) : State :=
  { template with
    pc := pc
    stack := [UInt256.ofNat nibble, byte, word, pointer, accumulator, modulus] ++
      rest
    memory := WindowTableMemory.tableMemory base modulus
    activeWords := UInt256.ofNat 16 }

def lookupState (template : State) (pc : UInt256) (base modulus : UInt256)
    (nibble : Nat) (byte word pointer accumulator : UInt256)
    (rest : List UInt256) : State :=
  { template with
    pc := pc
    stack := [WindowMath.tableWord base modulus nibble, UInt256.ofNat nibble,
      byte, word, pointer, accumulator, modulus] ++ rest
    memory := WindowTableMemory.tableMemory base modulus
    activeWords := UInt256.ofNat 16 }

theorem shift_nibble (nibble : Nat) (hnibble : nibble < 16) :
    UInt256.shiftLeft (UInt256.ofNat nibble) (UInt256.ofNat 5) =
      UInt256.ofNat (32 * nibble) := by
  rw [Challenge.EvmProof.Word.shiftLeft_ofNat
    (value := nibble) (shift := 5) (by omega) (by norm_num) (by
      norm_num
      omega)]
  congr 1
  omega

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleKernel
