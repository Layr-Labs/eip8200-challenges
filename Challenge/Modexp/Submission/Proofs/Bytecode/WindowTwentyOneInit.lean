import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneTable
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneGroup
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneBits
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneMath

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneInit

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open WindowNibbleKernel

/-! # Entering the window loop, from the table's hand-over at 1503

The table block now ends with `PUSH2 480; SWAP3; MULMOD; MSIZE; MSTORE`: the
window's `480` lookup mask is pushed *before* the final product so that the
multiply can reach the base with a `SWAP3`, and the mask is then already in
place when the store consumes the product.  That deletes the `POP; PUSH2 480`
prologue this block used to open with, and lets the remaining eleven
instructions run in the order that needs the fewest stack moves: shift the
exponent first, load the frame's modulus and counter, and compute the lookup
address last so the `MLOAD` result lands directly on top as the accumulator.
-/

/-- The mask is already on the stack, so the address is masked in the operand
order `Bits.lookupAddress` already uses. -/
def address (exponent : UInt256) : UInt256 :=
  UInt256.land (UInt256.shiftRight exponent (UInt256.ofNat 247)) (UInt256.ofNat 480)

theorem first_address (exponent : UInt256) :
    (address exponent).toNat = 32 * WindowTwentyOneMath.nibble exponent.toNat 0 := by
  have h := WindowTwentyOneBits.lookupAddress_toNat exponent 247 (by decide)
  simpa only [address, WindowTwentyOneBits.lookupAddress, WindowTwentyOneMath.nibble,
    Nat.shiftRight_eq_div_pow, show 247 + 5 = 252 by decide,
    show (2 : Nat) ^ 252 = 16 ^ 63 by decide] using h

/-- `DUP2; PUSH3 1; SHL`.  The shift amount is pushed as a `PUSH3` rather than a
`PUSH1`: the table's hand-over freed two instructions but no bytes, and the two
padding bytes are cheaper here than anywhere else in the block. -/
def arrangeProgram : List Instr :=
  [.op (.Dup ⟨1, by decide⟩), .push 3 1, .op .SHL]

/-- The loop frame: the spare modulus copy from `rest`, a second mask copy, and
the counter, rotated under the exponent with a single `SWAP5`. -/
def frameLoadProgram : List Instr :=
  [.op (.Dup ⟨3, by decide⟩), .op (.Dup ⟨2, by decide⟩), .push 1 2,
   .op (.Swap ⟨4, by decide⟩)]

def addressProgram : List Instr :=
  [.push 1 247, .op .SHR, .op .AND]

private theorem run_arrange (template : State) (pc base modulus exponent : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1000) :
    runInstructions arrangeProgram
      (WindowTwentyOneTable.framed template pc base modulus 16
        ([UInt256.ofNat 480, exponent] ++ rest)) =
    some (WindowTwentyOneTable.framed template (advancePC 6 pc) base modulus 16
      ([UInt256.shiftLeft exponent (UInt256.ofNat 1), UInt256.ofNat 480, exponent] ++ rest)) := by
  have hcap2 : rest.length + 2 < 1024 := by omega
  have hcap3 : rest.length + 3 < 1024 := by omega
  have hcap4 : rest.length + 4 < 1024 := by omega
  have hp4 : UInt256.ofNat 4 =
      UInt256.ofNat 1 + (UInt256.ofNat 1 + (UInt256.ofNat 1 + UInt256.ofNat 1)) := by decide
  simp [runInstructions, arrangeProgram, WindowTwentyOneTable.framed,
    Challenge.EvmProof.Stepper.runInstr, hcap2, hcap3, hcap4, Nat.add_assoc,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    advancePC, succ_eq_add, hp4, word_add_assoc]

private theorem run_frameLoad (template : State) (pc base modulus exponent : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1000)
    (hmod : rest[0]? = some modulus) :
    runInstructions frameLoadProgram
      (WindowTwentyOneTable.framed template pc base modulus 16
        ([UInt256.shiftLeft exponent (UInt256.ofNat 1), UInt256.ofNat 480, exponent] ++ rest)) =
    some (WindowTwentyOneTable.framed template (advancePC 5 pc) base modulus 16
      ([exponent, UInt256.ofNat 480, modulus,
        UInt256.shiftLeft exponent (UInt256.ofNat 1), UInt256.ofNat 480,
        UInt256.ofNat 2] ++ rest)) := by
  have hcap3 : rest.length + 3 < 1024 := by omega
  have hcap4 : rest.length + 4 < 1024 := by omega
  have hcap5 : rest.length + 5 < 1024 := by omega
  have hcap6 : rest.length + 6 < 1024 := by omega
  have hp2 : UInt256.ofNat 2 = UInt256.ofNat 1 + UInt256.ofNat 1 := by decide
  simp [runInstructions, frameLoadProgram, WindowTwentyOneTable.framed,
    Challenge.EvmProof.Stepper.runInstr, hcap3, hcap4, hcap5, hcap6, Nat.add_assoc,
    List.getElem?_cons_succ, Option.bind_some, hmod, List.exchange,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    advancePC, succ_eq_add, hp2, word_add_assoc]

private theorem run_address (template : State) (pc base modulus exponent : UInt256)
    (tail : List UInt256) (hcap : tail.length + 3 < 1024) :
    runInstructions addressProgram
      (WindowTwentyOneTable.framed template pc base modulus 16
        (exponent :: UInt256.ofNat 480 :: tail)) =
    some (WindowTwentyOneTable.framed template (advancePC 4 pc) base modulus 16
      (address exponent :: tail)) := by
  have hcap2 : tail.length + 2 < 1024 := by omega
  have hp2 : UInt256.ofNat 2 = UInt256.ofNat 1 + UInt256.ofNat 1 := by decide
  simp [runInstructions, addressProgram, address, WindowTwentyOneTable.framed,
    Challenge.EvmProof.Stepper.runInstr, hcap, hcap2, Nat.add_assoc,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    advancePC, succ_eq_add, hp2, word_add_assoc]

private theorem run_load (template : State) (pc base modulus exponent : UInt256)
    (tail : List UInt256) (hcap : tail.length + 1 < 1024) :
    runInstructions [.op .MLOAD]
      (WindowTwentyOneTable.framed template pc base modulus 16 (address exponent :: tail)) =
    some (WindowTwentyOneTable.framed template pc.succ base modulus 16
      (WindowTwentyOneMath.initialAccumulator base modulus exponent.toNat :: tail)) := by
  have hread : MachineState.readWord (WindowTableMemory.tableMemoryThrough base modulus 16)
      (32 * WindowTwentyOneMath.nibble exponent.toNat 0) =
      WindowMath.tableWord base modulus (WindowTwentyOneMath.nibble exponent.toNat 0) :=
    WindowTableMemory.readWord_tableMemory base modulus
      (WindowTwentyOneMath.nibble exponent.toNat 0) (WindowTwentyOneMath.nibble_lt _ _)
  have hactive := WindowTableMemory.activeWordsAfter_lookup
    (WindowTwentyOneMath.nibble exponent.toNat 0) (WindowTwentyOneMath.nibble_lt _ _)
  simp [runInstructions, WindowTwentyOneTable.framed,
    Challenge.EvmProof.Stepper.runInstr, hcap, first_address, hread, hactive,
    WindowTwentyOneMath.initialAccumulator, State.activeWordsAfterUInt256]

def program : List Instr :=
  arrangeProgram ++ frameLoadProgram ++ addressProgram ++ [.op .MLOAD]

theorem run_enter (template : State) (base modulus exponent : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1000)
    (hmod : rest[0]? = some modulus) :
    runInstructions program
      (WindowTwentyOneTable.framed template (UInt256.ofNat 1503) base modulus 16
        ([UInt256.ofNat 480, exponent] ++ rest)) =
    some (WindowTwentyOneGroup.state template (UInt256.ofNat 1519)
      (WindowTableMemory.tableMemory base modulus) 16 modulus
      (WindowTwentyOneMath.initialAccumulator base modulus exponent.toNat)
      (UInt256.shiftLeft exponent (UInt256.ofNat 1)) (UInt256.ofNat 2) 0 rest) := by
  have ha := run_arrange template (UInt256.ofNat 1503) base modulus exponent rest hrest
  have hf := run_frameLoad template (advancePC 6 (UInt256.ofNat 1503)) base modulus exponent
    rest hrest hmod
  have hd := run_address template (advancePC 5 (advancePC 6 (UInt256.ofNat 1503)))
    base modulus exponent
    ([modulus, UInt256.shiftLeft exponent (UInt256.ofNat 1), UInt256.ofNat 480,
      UInt256.ofNat 2] ++ rest) (by simp; omega)
  have hl := run_load template
    (advancePC 4 (advancePC 5 (advancePC 6 (UInt256.ofNat 1503)))) base modulus exponent
    ([modulus, UInt256.shiftLeft exponent (UInt256.ofNat 1), UInt256.ofNat 480,
      UInt256.ofNat 2] ++ rest) (by simp; omega)
  have both := runInstructions_append_some _ _ _ _ _
    (runInstructions_append_some _ _ _ _ _
      (runInstructions_append_some _ _ _ _ _ ha hf) hd) hl
  have hpc : (advancePC 4 (advancePC 5 (advancePC 6 (UInt256.ofNat 1503)))).succ =
      UInt256.ofNat 1519 := by decide
  rw [hpc] at both
  simpa only [program, WindowTwentyOneGroup.state, WindowTwentyOneLookup.framed,
    WindowTwentyOneTable.framed, WindowTableMemory.tableMemory, List.replicate_zero,
    List.nil_append, List.cons_append] using both

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneInit
