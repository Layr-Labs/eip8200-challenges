import Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleDefs

set_option warningAsError true
set_option maxHeartbeats 3000000

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleKernel

open EvmSemantics
open EvmSemantics.EVM

set_option linter.unusedSimpArgs false in
theorem run_lookupLoad (template : State) (pc : UInt256)
    (base modulus : UInt256) (nibble : Nat)
    (byte word pointer accumulator : UInt256) (rest : List UInt256)
    (hnibble : nibble < 16) (hrest : rest.length ≤ 1000) :
    runInstructions lookupLoadProgram
      (nibbleState template pc base modulus nibble byte word pointer
        accumulator rest) =
      some (lookupState template (advancePC 5 pc) base modulus nibble
        byte word pointer accumulator rest) := by
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
  simp (config := { maxSteps := 100000 }) (disch := omega)
    [runInstructions, lookupLoadProgram, nibbleState, lookupState,
      Challenge.EvmProof.Stepper.runInstr, hrest, h6, h7, h8,
      List.getElem?_cons_zero, List.getElem?_cons_succ, List.exchange,
      hshift, hoffset, hread, hactive,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      advancePC]
  unfold UInt256.succ
  rw [show UInt256.ofNat 2 = UInt256.ofNat 1 + UInt256.ofNat 1 by decide]
  change (((pc + UInt256.ofNat 1) +
      (UInt256.ofNat 1 + UInt256.ofNat 1)) + UInt256.ofNat 1) +
        UInt256.ofNat 1 =
    ((((pc + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) +
      UInt256.ofNat 1) + UInt256.ofNat 1
  simp only [word_add_assoc]

set_option linter.unusedSimpArgs false in
theorem run_lookupMul (template : State) (pc : UInt256)
    (base modulus : UInt256) (nibble : Nat)
    (byte word pointer accumulator : UInt256) (rest : List UInt256)
    (hrest : rest.length ≤ 1000) :
    runInstructions lookupMulProgram
      (lookupState template pc base modulus nibble byte word pointer
        accumulator rest) =
      some (nibbleState template (advancePC 6 pc) base modulus nibble
        byte word pointer
        (UInt256.mulMod accumulator (WindowMath.tableWord base modulus nibble)
          modulus) rest) := by
  have h6 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have h7 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have h8 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have h9 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by
    omega
  simp (config := { maxSteps := 100000 }) (disch := omega)
    [runInstructions, lookupMulProgram, lookupState, nibbleState,
      Challenge.EvmProof.Stepper.runInstr, hrest, h6, h7, h8, h9,
      List.getElem?_cons_zero, List.getElem?_cons_succ, List.exchange,
      advancePC]

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
  rw [lookupProgram, runInstructions_append,
    run_lookupLoad template pc base modulus nibble byte word pointer accumulator
      rest hnibble hrest]
  simp only [Option.bind_some]
  rw [run_lookupMul (hrest := hrest)]
  rw [← advancePC_add]

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleKernel
