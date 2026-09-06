import Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitByteSlices
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowBytePrep
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleSquare
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleLookup

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 5000000

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitByte2Low

open Challenge.EvmProof.Stepper EvmSemantics EvmSemantics.EVM
open WindowHitByteSlices WindowByteKernel WindowNibbleKernel

set_option linter.unusedSimpArgs false in
theorem run_prep (template : State) (base modulus : UInt256) (high : Nat)
    (word pointer accumulator : UInt256) (rest : List UInt256)
    (hrest : rest.length ≤ 1000) :
    runLocatedBlock (lowPrepPath 2)
      (nibbleState { template with halt := .Running } (UInt256.ofNat 3420)
        base modulus high (byteValue 2 word) word pointer accumulator rest) =
    some (nibbleState { template with halt := .Running } (UInt256.ofNat 3425)
      base modulus (lowNibble 2 word) (byteValue 2 word) word pointer
      accumulator rest) := by
  have h5 : rest.length + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have h6 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have h7 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hlow := mask_lowNibble 2 word
  simp (config := { maxSteps := 2000000 }) (disch := omega)
    [lowPrepPath, byteStartIndex, locatedSlice,
      Challenge.EvmProof.Stepper.Located.ofIndex,
      Challenge.EvmProof.ProgramArtifact.instructionPC,
      Artifact.submissionArtifact, Artifact.submissionInstructions,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      nibbleState, List.getElem?_cons_zero, List.getElem?_cons_succ,
      List.exchange, hrest, h5, h6, h7, hlow,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod]
  rw [word_land_comm]
  exact hlow

set_option linter.unusedSimpArgs false in
theorem run_square (template : State) (base modulus : UInt256)
    (nibble : Nat) (byte word pointer accumulator : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1000) :
    runLocatedBlock (lowSquarePath 2)
      (nibbleState { template with halt := .Running } (UInt256.ofNat 3425)
        base modulus nibble byte word pointer accumulator rest) =
    some (nibbleState { template with halt := .Running } (UInt256.ofNat 3449)
      base modulus nibble byte word pointer
      (WindowMath.squareWordAfter modulus 4 accumulator) rest) := by
  have h6 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have h7 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have h8 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have h9 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  simp (config := { maxSteps := 2000000 }) (disch := omega)
    [lowSquarePath, byteStartIndex, locatedSlice,
      Challenge.EvmProof.Stepper.Located.ofIndex,
      Challenge.EvmProof.ProgramArtifact.instructionPC,
      Artifact.submissionArtifact, Artifact.submissionInstructions,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      nibbleState, WindowMath.squareWordAfter,
      List.getElem?_cons_zero, List.getElem?_cons_succ, List.exchange,
      hrest, h6, h7, h8, h9,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod]

set_option linter.unusedSimpArgs false in
theorem run_lookup (template : State) (base modulus : UInt256)
    (nibble : Nat) (byte word pointer accumulator : UInt256)
    (rest : List UInt256) (hnibble : nibble < 16)
    (hrest : rest.length ≤ 1000) :
    runLocatedBlock (lowLookupPath 2)
      (nibbleState { template with halt := .Running } (UInt256.ofNat 3449)
        base modulus nibble byte word pointer accumulator rest) =
    some (nibbleState { template with halt := .Running } (UInt256.ofNat 3460)
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
  have h9 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  simp (config := { maxSteps := 2000000 }) (disch := omega)
    [lowLookupPath, byteStartIndex, locatedSlice,
      Challenge.EvmProof.Stepper.Located.ofIndex,
      Challenge.EvmProof.ProgramArtifact.instructionPC,
      Artifact.submissionArtifact, Artifact.submissionInstructions,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      nibbleState, lookupState,
      List.getElem?_cons_zero, List.getElem?_cons_succ, List.exchange,
      hrest, h6, h7, h8, h9, hshift, hoffset, hread, hactive,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod]

set_option linter.unusedSimpArgs false in
theorem run_finish (template : State) (base modulus : UInt256)
    (nibble : Nat) (byte word pointer accumulator : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1000) :
    runLocatedBlock (finishPath 2)
      (nibbleState { template with halt := .Running } (UInt256.ofNat 3460)
        base modulus nibble byte word pointer accumulator rest) =
    some (wordKernelState { template with halt := .Running } (UInt256.ofNat 3462)
      base modulus word pointer accumulator rest) := by
  have h5 : rest.length + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have h6 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  simp (config := { maxSteps := 2000000 }) (disch := omega)
    [finishPath, byteStartIndex, locatedSlice,
      Challenge.EvmProof.Stepper.Located.ofIndex,
      Challenge.EvmProof.ProgramArtifact.instructionPC,
      Artifact.submissionArtifact, Artifact.submissionInstructions,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      nibbleState, wordKernelState,
      List.getElem?_cons_zero, List.getElem?_cons_succ, List.exchange,
      hrest, h5, h6,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod]

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitByte2Low


