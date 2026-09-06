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

/-- The table lookup and multiply.  `DUP6 DUP6` lift the modulus and the
accumulator into `MULMOD` order *before* the table word is loaded, so the
`SWAP1` the load-first form needed to slide the modulus underneath is gone.
Ten instructions and eleven bytes, exactly as many as the load-first form, with
the freed byte spent on a `JUMPDEST` (1 gas) so that neither the instruction
count nor any program counter outside this window moves.  34 gas -> 32 gas.

Note the operand order: `MULMOD` now pops the table word first and the
accumulator second, so the machine produces `mulMod (tableWord ..) acc m` where
the load-first form produced `mulMod acc (tableWord ..) m`.  Those are equal but
NOT definitionally equal; `mulMod_comm` below is what bridges them, and every
statement downstream keeps the accumulator-first spelling. -/
def lookupProgram : List Instr :=
  [.op (.Dup ⟨5, by decide⟩), .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨2, by decide⟩), .push 1 5, .op .SHL, .op .MLOAD,
   .op .MULMOD, .op (.Swap ⟨4, by decide⟩), .op .POP, .op .JUMPDEST]

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

/-- `UInt256.succ` in `+` form, so `word_add_assoc` applies to it.  A `PUSH1`
advances the program counter by two in one step while `advancePC` advances by
one eleven times; re-associating is what lines the two up. -/
theorem succ_eq_add (x : UInt256) : x.succ = x + UInt256.ofNat 1 := rfl

/-- `MULMOD` is commutative in its two factors.  Needed because the window
loads the table word last and therefore multiplies in the opposite order from
the spelling every downstream statement uses. -/
theorem mulMod_comm (left right modulus : UInt256) :
    UInt256.mulMod left right modulus = UInt256.mulMod right left modulus := by
  unfold UInt256.mulMod
  rw [Nat.mul_comm left.toNat right.toNat]

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
