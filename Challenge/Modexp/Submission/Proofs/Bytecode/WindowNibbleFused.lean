import Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleDefs

set_option warningAsError true
set_option maxHeartbeats 3000000

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleKernel

open EvmSemantics
open EvmSemantics.EVM

/-- The seven-slot state between squarings: current value on top, the entry
accumulator at position 5, the modulus at position 6. -/
def squareTopState (template : State) (pc : UInt256)
    (base modulus : UInt256) (nibble : Nat)
    (byte word pointer original accumulator : UInt256) (rest : List UInt256) : State :=
  { nibbleState template pc base modulus nibble byte word pointer original rest with
    stack := [accumulator, UInt256.ofNat nibble, byte, word, pointer, original, modulus] ++ rest }

set_option linter.unusedSimpArgs false in
/-- The fused block reduces on the square state (peak depth ten plus `rest`)
to the accumulator-first result, replacing the old eight-byte finish and the
ten-instruction lookup in one certificate. -/
theorem run_fusedSquareLookup (template : State) (pc : UInt256)
    (base modulus : UInt256) (nibble : Nat)
    (byte word pointer original accumulator : UInt256) (rest : List UInt256)
    (hnibble : nibble < 16) (hrest : rest.length ≤ 1000) :
    runInstructions fusedSquareLookupProgram
      (squareTopState template pc base modulus nibble byte word pointer
        original accumulator rest) =
      some (nibbleState template (advancePC 19 pc) base modulus nibble
        byte word pointer
        (UInt256.mulMod accumulator
          (WindowMath.tableWord base modulus nibble) modulus) rest) := by
  have hshift := shift_nibble nibble hnibble
  have hoffset : (UInt256.ofNat (32 * nibble)).toNat = 32 * nibble := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat]
    apply Nat.mod_eq_of_lt
    omega
  have hread := WindowTableMemory.readWord_tableMemory base modulus nibble hnibble
  have hactive := WindowTableMemory.activeWordsAfter_lookup nibble hnibble
  have h7 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have h8 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have h9 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have h10 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by
    omega
  simp (config := { maxSteps := 8000000 }) (disch := omega)
    [runInstructions, fusedSquareLookupProgram, squareTopState, nibbleState,
      Challenge.EvmProof.Stepper.runInstr, hrest, h7, h8, h9, h10,
      List.getElem?_cons_zero, List.getElem?_cons_succ, List.exchange,
      hshift, hoffset, hread, hactive,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      advancePC]
  refine ⟨?_, mulMod_comm _ _ _⟩
  simp only [succ_eq_add,
    show UInt256.ofNat 11 = UInt256.ofNat 1 + UInt256.ofNat 10 by decide,
    show UInt256.ofNat 10 = UInt256.ofNat 1 + UInt256.ofNat 9 by decide,
    show UInt256.ofNat 9 = UInt256.ofNat 1 + UInt256.ofNat 8 by decide,
    show UInt256.ofNat 8 = UInt256.ofNat 1 + UInt256.ofNat 7 by decide,
    show UInt256.ofNat 7 = UInt256.ofNat 1 + UInt256.ofNat 6 by decide,
    show UInt256.ofNat 6 = UInt256.ofNat 1 + UInt256.ofNat 5 by decide,
    show UInt256.ofNat 5 = UInt256.ofNat 1 + UInt256.ofNat 4 by decide,
    show UInt256.ofNat 4 = UInt256.ofNat 1 + UInt256.ofNat 3 by decide,
    show UInt256.ofNat 3 = UInt256.ofNat 1 + UInt256.ofNat 2 by decide,
    show UInt256.ofNat 2 = UInt256.ofNat 1 + UInt256.ofNat 1 by decide,
    word_add_assoc]

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleKernel
