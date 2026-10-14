import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneTable
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneGroup
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneBits
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneMath

set_option warningAsError true

/-!
# Window route setup, 968..992

The twenty-four bytes between the table build and the first sixteen-digit block
are split in three straight pieces:

* `program` (968..979): push the mask `480`, double the exponent and derive the
  copy shifted right by four;
* `WindowTwentyOneLoop.trampolineProgram` (979..984): the two `MSIZE` stores of
  the exponent copies, proved next to the `MSIZE` evaluator;
* `lookupProgram` (984..992): the spare modulus copy and the first-digit lookup.
  The two padding `JUMPDEST`s that used to end it now sit after the final
  `RETURN` at 2378..2379, off the executed path.

Nothing below the mask is ever read by the ladder, so the original modulus and
exponent words simply stay in place under the frame instead of being swapped
into position.  The layout costs 55 gas against the previous 61.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneInit

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open WindowNibbleKernel

/-- 968..979: `PUSH2 480, DUP3, PUSH1 1, SHL, DUP1, PUSH1 4, SHR`. -/
def program : List Instr :=
  [.push 2 480, .op (.Dup ⟨2, by decide⟩), .push 1 1, .op .SHL,
   .op (.Dup ⟨0, by decide⟩), .push 1 4, .op .SHR]

/-- 984..992: `DUP3, DUP5, PUSH1 247, SHR, DUP4, AND, MLOAD`. -/
def lookupProgram : List Instr :=
  [.op (.Dup ⟨2, by decide⟩), .op (.Dup ⟨4, by decide⟩), .push 1 247, .op .SHR,
   .op (.Dup ⟨3, by decide⟩), .op .AND, .op .MLOAD]

/-- The doubled exponent kept on the stack (and stored at 544). -/
def doubled (exponent : UInt256) : UInt256 :=
  UInt256.shiftLeft exponent (UInt256.ofNat 1)

/-- The exponent copy stored at 512. -/
def quartered (exponent : UInt256) : UInt256 :=
  UInt256.shiftRight (doubled exponent) (UInt256.ofNat 4)

def address (exponent : UInt256) : UInt256 :=
  UInt256.land (UInt256.ofNat 480) (UInt256.shiftRight exponent (UInt256.ofNat 247))

private theorem land_comm (a b : UInt256) : UInt256.land a b = UInt256.land b a := by
  apply Challenge.EvmProof.Word.word_ext
  rw [Challenge.EvmProof.Word.word_toNat_land,
    Challenge.EvmProof.Word.word_toNat_land, Nat.and_comm]

theorem first_address (exponent : UInt256) :
    (UInt256.land (UInt256.ofNat 480)
      (UInt256.shiftRight exponent (UInt256.ofNat 247))).toNat =
      32 * WindowTwentyOneMath.nibble exponent.toNat 0 := by
  rw [land_comm]
  have h := WindowTwentyOneBits.lookupAddress_toNat exponent 247 (by decide)
  simpa only [WindowTwentyOneBits.lookupAddress, WindowTwentyOneMath.nibble,
    Nat.shiftRight_eq_div_pow, show 247 + 5 = 252 by decide,
    show (2 : Nat) ^ 252 = 16 ^ 63 by decide] using h

/-- The stack the setup leaves at 979, above the untouched modulus and exponent. -/
def setupStack (modulus exponent : UInt256) (rest : List UInt256) : List UInt256 :=
  [quartered exponent, doubled exponent, UInt256.ofNat 480, modulus, exponent] ++ rest

theorem run_program (template : State) (pc base modulus exponent : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1000) :
    runInstructions program
      (WindowTwentyOneTable.framed template pc base modulus 16 ([modulus, exponent] ++ rest)) =
    some (WindowTwentyOneTable.framed template (advancePC 11 pc) base modulus 16
      (setupStack modulus exponent rest)) := by
  have hcap2 : rest.length + 2 < 1024 := by omega
  have hcap3 : rest.length + 3 < 1024 := by omega
  have hcap4 : rest.length + 4 < 1024 := by omega
  have hcap5 : rest.length + 5 < 1024 := by omega
  have hcap6 : rest.length + 6 < 1024 := by omega
  have hp2 : UInt256.ofNat 2 = UInt256.ofNat 1 + UInt256.ofNat 1 := by decide
  have hp3 : UInt256.ofNat 3 = UInt256.ofNat 1 + (UInt256.ofNat 1 + UInt256.ofNat 1) := by decide
  simp [runInstructions, program, setupStack, doubled, quartered, WindowTwentyOneTable.framed,
    Challenge.EvmProof.Stepper.runInstr, hcap2, hcap3, hcap4, hcap5, hcap6, Nat.add_assoc,
    Challenge.EvmProof.Word.literal_eq_ofNat, advancePC, succ_eq_add, hp2, hp3, word_add_assoc]

theorem run_enter (template : State) (base modulus exponent : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1000) :
    runInstructions program
      (WindowTwentyOneTable.framed template (UInt256.ofNat 837) base modulus 16
        ([modulus, exponent] ++ rest)) =
    some (WindowTwentyOneTable.framed template (UInt256.ofNat 848) base modulus 16
      (setupStack modulus exponent rest)) := by
  have h := run_program template (UInt256.ofNat 837) base modulus exponent rest hrest
  have hpc : advancePC 11 (UInt256.ofNat 837) = UInt256.ofNat 848 := by decide
  rw [hpc] at h
  exact h

/-- The first-digit lookup after the exponent copies are in place: the table is
still readable below 512, the active-word count stays at 18, and the spare
modulus copy is dropped in above the frame. -/
theorem run_lookup (template : State) (pc : UInt256) (mem : ByteArray)
    (base modulus exponent : UInt256)
    (htable : ∀ i, i < 16 →
      MachineState.readWord mem (32 * i) = WindowMath.tableWord base modulus i)
    (rest : List UInt256) (hrest : rest.length ≤ 1000) :
    runInstructions lookupProgram
      (WindowTwentyOneLookup.framed template pc mem 18
        ([doubled exponent, UInt256.ofNat 480, modulus, exponent] ++ rest)) =
    some (WindowTwentyOneGroup.state template (advancePC 8 pc) mem 18 modulus
      (WindowTwentyOneMath.initialAccumulator base modulus exponent.toNat)
      (doubled exponent) modulus 0 (exponent :: rest)) := by
  have hcap4 : rest.length + 4 < 1024 := by omega
  have hcap5 : rest.length + 5 < 1024 := by omega
  have hcap6 : rest.length + 6 < 1024 := by omega
  have hcap7 : rest.length + 7 < 1024 := by omega
  have hread : MachineState.readWord mem (32 * WindowTwentyOneMath.nibble exponent.toNat 0) =
      WindowMath.tableWord base modulus (WindowTwentyOneMath.nibble exponent.toNat 0) :=
    htable _ (WindowTwentyOneMath.nibble_lt _ _)
  have hactive := WindowTwentyOneLookup.activeWordsAfter_table
    (WindowTwentyOneMath.nibble exponent.toNat 0) (WindowTwentyOneMath.nibble_lt _ _)
  have h18 : (UInt256.ofNat 18).toNat = 18 := rfl
  have hp2 : UInt256.ofNat 2 = UInt256.ofNat 1 + UInt256.ofNat 1 := by decide
  simp [runInstructions, lookupProgram, WindowTwentyOneGroup.state, WindowTwentyOneLookup.framed,
    Challenge.EvmProof.Stepper.runInstr, hcap4, hcap5, hcap6, hcap7, Nat.add_assoc,
    first_address, hread, hactive, h18, State.activeWordsAfterUInt256,
    WindowTwentyOneMath.initialAccumulator,
    Challenge.EvmProof.Word.literal_eq_ofNat, advancePC, succ_eq_add, hp2, word_add_assoc]

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneInit
