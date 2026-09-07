import Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleDefs

set_option warningAsError true
set_option maxHeartbeats 3000000

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleKernel

open EvmSemantics
open EvmSemantics.EVM

set_option linter.unusedSimpArgs false in
/-- One nibble's table lookup and multiply.

The window loads the table word *last*, so there is no intermediate state
worth naming: the whole ten-instruction block reduces in one step.  Two facts
are worth stating rather than rediscovering.

`advancePC 11` is unchanged from the load-first form, which advanced `5` and
then `6`.  `advancePC` counts BYTES, not instructions, and the new block is ten
instructions in eleven bytes exactly as the old one was ten instructions in
eleven bytes.  The instruction stride moved (4 + 6 became 10); the byte stride
did not, and this statement is written in the byte stride.

`h10` is new.  The block's peak stack is one slot deeper than the load-first
form's, because the modulus and the accumulator are duplicated *before* the
`PUSH1 5`, not after the load.  Peak is `rest.length + 10` against the old
`rest.length + 9`; with `hrest` that is at most 1010, and the EVM limit is
1024.  Without `h10` the `stack.length < 1024` guard on the `PUSH1` does not
discharge and the block does not reduce at all. -/
theorem run_lookup (template : State) (pc : UInt256)
    (base modulus : UInt256) (nibble : Nat)
    (byte word pointer accumulator : UInt256) (rest : List UInt256)
    (hnibble : nibble < 16) (hrest : rest.length ≤ 1000) :
    runInstructions lookupProgram
      (nibbleState template pc base modulus nibble byte word pointer
        accumulator rest) =
      some (nibbleState template (advancePC 11 pc) base modulus nibble
        byte word pointer
        (UInt256.mulMod accumulator (WindowMath.tableWord base modulus nibble)
          modulus) rest) := by
  have hshift := shift_nibble nibble hnibble
  have hoffset : (UInt256.ofNat (32 * nibble)).toNat = 32 * nibble := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat]
    apply Nat.mod_eq_of_lt
    omega
  have hread := WindowTableMemory.readWord_tableMemory base modulus nibble hnibble
  have hactive := WindowTableMemory.activeWordsAfter_lookup nibble hnibble
  have h6 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have h7 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have h8 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have h9 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have h10 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by
    omega
  simp (config := { maxSteps := 4000000 }) (disch := omega)
    [runInstructions, lookupProgram, nibbleState,
      Challenge.EvmProof.Stepper.runInstr, hrest, h6, h7, h8, h9, h10,
      List.getElem?_cons_zero, List.getElem?_cons_succ, List.exchange,
      hshift, hoffset, hread, hactive,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      advancePC]
  refine ⟨?_, mulMod_comm _ _ _⟩
  simp only [succ_eq_add,
    show UInt256.ofNat 2 = UInt256.ofNat 1 + UInt256.ofNat 1 by decide,
    word_add_assoc]

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleKernel
