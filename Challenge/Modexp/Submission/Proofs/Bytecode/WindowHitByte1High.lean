import Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitByteSlices
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowBytePrep
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleSquare
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleLookup

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 5000000

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitByte1High

open Challenge.EvmProof.Stepper EvmSemantics EvmSemantics.EVM
open WindowHitByteSlices WindowByteKernel WindowNibbleKernel
open WindowNibbleForward

set_option linter.unusedSimpArgs false in
theorem run_prep (template : State) (base modulus word pointer accumulator : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1000) :
    runLocatedBlock (highPrepPath 1)
      (wordKernelState { template with halt := .Running } (UInt256.ofNat 3254)
        base modulus word pointer accumulator rest) =
    some (nibbleState { template with halt := .Running } (UInt256.ofNat 3262)
      base modulus (highNibble 1 word) (byteValue 1 word) word pointer
      accumulator rest) := by
  have h4 : rest.length + 1 + 1 + 1 + 1 < 1024 := by omega
  have h5 : rest.length + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have h6 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have h7 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  simp (config := { maxSteps := 2000000 }) (disch := omega)
    [highPrepPath, byteStartIndex, locatedSlice,
      Challenge.EvmProof.Stepper.Located.ofIndex,
      Challenge.EvmProof.ProgramArtifact.instructionPC,
      Artifact.submissionArtifact, Artifact.submissionInstructions,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      wordKernelState, forwardedNibbleState, nibbleState,
      List.getElem?_cons_zero, List.getElem?_cons_succ, List.exchange,
      hrest, h4, h5, h6, h7,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod]
  exact ⟨shift_highNibble 1 word, rfl⟩

set_option linter.unusedSimpArgs false in
/-- Fused high-nibble block: four squares then the table multiply, 19
instructions in 36 bytes.  The machine loads the table word
last, so the accumulator-first `nibbleWordStep` spelling needs `mulMod_comm`. -/
theorem run_squareLookup (template : State) (base modulus : UInt256)
    (nibble : Nat) (byte word pointer accumulator : UInt256)
    (rest : List UInt256) (hnibble : nibble < 16)
    (hrest : rest.length ≤ 1000) :
    runLocatedBlock (highSquareLookupPath 1)
      (nibbleState { template with halt := .Running } (UInt256.ofNat 3262)
        base modulus nibble byte word pointer accumulator rest) =
    some (forwardedNibbleState { template with halt := .Running } (UInt256.ofNat 3298)
      base modulus nibble byte word pointer accumulator
      (WindowMath.nibbleWordStep modulus base accumulator nibble) rest) := by
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
  have h10 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by
    omega
  have h11 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have h12 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  simp (config := { maxSteps := 2000000 }) (disch := omega)
    [highSquareLookupPath, byteStartIndex, locatedSlice,
      Challenge.EvmProof.Stepper.Located.ofIndex,
      Challenge.EvmProof.ProgramArtifact.instructionPC,
      Artifact.submissionArtifact, Artifact.submissionInstructions,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      forwardedNibbleState, nibbleState, WindowMath.squareWordAfter,
      List.getElem?_cons_zero, List.getElem?_cons_succ, List.exchange,
      hrest, h6, h7, h8, h9, h10, h11, h12, hshift, hoffset, hread, hactive,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod]
  -- The fused block loads the table word last, so `MULMOD` multiplies in the
  -- opposite order from the accumulator-first `nibbleWordStep` spelling.
  -- Equal, but not definitionally equal.
  exact mulMod_comm _ _ _

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitByte1High
