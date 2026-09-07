import Challenge.Modexp.Submission.Proofs.Bytecode.WindowByteDefs

set_option warningAsError true
set_option maxHeartbeats 3000000

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowByteKernel

open EvmSemantics
open EvmSemantics.EVM
open WindowNibbleKernel

set_option linter.unusedSimpArgs false in
theorem run_highPrep (template : State) (pc : UInt256)
    (base modulus word pointer accumulator : UInt256) (rest : List UInt256)
    (index : Nat) (hindex : index < 4) (hrest : rest.length ≤ 1000) :
    runInstructions (highPrepProgram index)
      (wordKernelState template pc base modulus word pointer accumulator rest) =
    some (nibbleState template (advancePC (highPrepAdvance index) pc) base modulus
      (highNibble index word) (byteValue index word) word pointer accumulator
      rest) := by
  have h4 : rest.length + 1 + 1 + 1 + 1 < 1024 := by omega
  have h5 : rest.length + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have h6 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have h7 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hindexWord : (UInt256.ofNat index).toNat = index := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt (hindex.trans (by norm_num))]
  have hhigh := shift_highNibble index word
  by_cases hzero : index = 0
  · subst index
    simp (config := { maxSteps := 100000 }) (disch := omega)
      [runInstructions, highPrepProgram, highPrepWidth, highPrepAdvance,
        wordKernelState, nibbleState, byteValue,
        Challenge.EvmProof.Stepper.runInstr, hrest, h4, h5, h6, h7,
        List.getElem?_cons_zero, List.getElem?_cons_succ, List.exchange,
        hhigh, advancePC,
        Challenge.EvmProof.Word.literal_eq_ofNat,
        Challenge.EvmProof.Word.word_toNat_ofNat]
    constructor
    · unfold UInt256.succ
      rw [show UInt256.ofNat 2 = UInt256.ofNat 1 + UInt256.ofNat 1 by decide]
      change (((((pc + UInt256.ofNat 1) + UInt256.ofNat 1) +
          UInt256.ofNat 1) + UInt256.ofNat 1) +
            (UInt256.ofNat 1 + UInt256.ofNat 1)) + UInt256.ofNat 1 =
        (((((((pc + UInt256.ofNat 1) + UInt256.ofNat 1) +
          UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) +
          UInt256.ofNat 1) + UInt256.ofNat 1)
      simp only [word_add_assoc]
    · constructor
      · rw [show ({ val := 0 } : UInt256) = UInt256.ofNat 0 by decide]
        simpa [byteValue] using hhigh
      · rw [show ({ val := 0 } : UInt256) = UInt256.ofNat 0 by decide]
  · simp (config := { maxSteps := 100000 }) (disch := omega)
      [runInstructions, highPrepProgram, highPrepWidth, highPrepAdvance, hzero,
        wordKernelState, nibbleState, byteValue,
        Challenge.EvmProof.Stepper.runInstr, hrest, h4, h5, h6, h7,
        List.getElem?_cons_zero, List.getElem?_cons_succ, List.exchange,
        hindexWord, hhigh, advancePC,
        Challenge.EvmProof.Word.literal_eq_ofNat,
        Challenge.EvmProof.Word.word_toNat_ofNat]
    constructor
    · unfold UInt256.succ
      rw [show UInt256.ofNat 2 = UInt256.ofNat 1 + UInt256.ofNat 1 by decide]
      change (((((pc + UInt256.ofNat 1) +
          (UInt256.ofNat 1 + UInt256.ofNat 1)) + UInt256.ofNat 1) +
            UInt256.ofNat 1) + (UInt256.ofNat 1 + UInt256.ofNat 1)) +
              UInt256.ofNat 1 =
        ((((((((pc + UInt256.ofNat 1) + UInt256.ofNat 1) +
          UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) +
          UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1)
      simp only [word_add_assoc]
    · simpa [byteValue] using hhigh

set_option linter.unusedSimpArgs false in
theorem run_lowPrep (template : State) (pc : UInt256)
    (base modulus : UInt256) (high index : Nat)
    (word pointer accumulator : UInt256) (rest : List UInt256)
    (hrest : rest.length ≤ 1000) :
    runInstructions lowPrepProgram
      (nibbleState template pc base modulus high (byteValue index word) word
        pointer accumulator rest) =
    some (nibbleState template (advancePC 5 pc) base modulus
      (lowNibble index word) (byteValue index word) word pointer accumulator
      rest) := by
  have h5 : rest.length + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have h6 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have h7 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hlow := mask_lowNibble index word
  simp (config := { maxSteps := 100000 }) (disch := omega)
    [runInstructions, lowPrepProgram, nibbleState,
      Challenge.EvmProof.Stepper.runInstr, hrest, h5, h6, h7,
      List.getElem?_cons_zero, List.getElem?_cons_succ, List.exchange,
      hlow, advancePC,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat]
  constructor
  · unfold UInt256.succ
    rw [show UInt256.ofNat 2 = UInt256.ofNat 1 + UInt256.ofNat 1 by decide]
    change (((pc + UInt256.ofNat 1) + UInt256.ofNat 1) +
        (UInt256.ofNat 1 + UInt256.ofNat 1)) + UInt256.ofNat 1 =
      ((((pc + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) +
        UInt256.ofNat 1) + UInt256.ofNat 1
    simp only [word_add_assoc]
  · rw [word_land_comm]
    exact hlow

set_option linter.unusedSimpArgs false in
theorem run_finish (template : State) (pc : UInt256)
    (base modulus : UInt256) (nibble : Nat) (byte word pointer accumulator : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1000) :
    runInstructions finishProgram
      (nibbleState template pc base modulus nibble byte word pointer
        accumulator rest) =
    some (wordKernelState template (advancePC 2 pc) base modulus word pointer
      accumulator rest) := by
  have h5 : rest.length + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have h6 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  simp (config := { maxSteps := 100000 })
    [runInstructions, finishProgram, nibbleState, wordKernelState,
      Challenge.EvmProof.Stepper.runInstr, h5, h6,
      List.getElem?_cons_zero, List.getElem?_cons_succ, List.exchange,
      advancePC]

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowByteKernel
