import Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitByteSlices
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleLookup

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 5000000

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitByteTrace2

open Challenge.EvmProof.Stepper
open EvmSemantics
open EvmSemantics.EVM
open WindowHitByteSlices
open WindowByteKernel
open WindowNibbleKernel

/-! Concrete table lookup and multiply at the first high-nibble location. -/
set_option linter.unusedSimpArgs false in
theorem run_byte0_highLookup (template : State) (base modulus : UInt256)
    (nibble : Nat) (byte word pointer accumulator : UInt256)
    (rest : List UInt256) (hnibble : nibble < 16)
    (hrest : rest.length ≤ 1000) :
    runLocatedBlock (highLookupPath 0)
      (nibbleState { template with halt := .Running } (UInt256.ofNat 3239)
        base modulus nibble byte word pointer accumulator rest) =
    some (nibbleState { template with halt := .Running } (UInt256.ofNat 3250)
      base modulus nibble byte word pointer
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
  have h9 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by
    omega
  simp (config := { maxSteps := 2000000 }) (disch := omega)
    [highLookupPath, byteStartIndex, locatedSlice,
      Challenge.EvmProof.Stepper.Located.ofIndex,
      Challenge.EvmProof.ProgramArtifact.instructionPC,
      Artifact.submissionArtifact, Artifact.submissionInstructions,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      nibbleState, lookupState,
      List.getElem?_cons_zero, List.getElem?_cons_succ, List.exchange,
      hrest, h6, h7, h8, h9, hshift, hoffset, hread, hactive,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod]

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitByteTrace2
