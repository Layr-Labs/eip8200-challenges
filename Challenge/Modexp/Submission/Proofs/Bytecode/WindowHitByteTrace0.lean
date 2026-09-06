import Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitByteSlices
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowByteKernel

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 5000000

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitByteTrace0

open Challenge.EvmProof.Stepper
open EvmSemantics
open EvmSemantics.EVM
open WindowHitByteSlices
open WindowByteKernel
open WindowNibbleKernel

/-! Each theorem binds one small, already-proved kernel segment to the artifact. -/
set_option linter.unusedSimpArgs false in
theorem run_byte0_highPrep (template : State)
    (base modulus word pointer accumulator : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1000) :
    runLocatedBlock (highPrepPath 0)
      (wordKernelState { template with halt := .Running } (UInt256.ofNat 3208)
        base modulus word pointer accumulator rest) =
    some (nibbleState { template with halt := .Running } (UInt256.ofNat 3215)
      base modulus (highNibble 0 word) (byteValue 0 word) word pointer
      accumulator rest) := by
  have h4 : rest.length + 1 + 1 + 1 + 1 < 1024 := by omega
  have h5 : rest.length + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have h6 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have h7 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  simp (config := { maxSteps := 2000000 }) (disch := omega)
      [highPrepPath, byteStartIndex, locatedSlice,
      Challenge.EvmProof.Stepper.Located.ofIndex,
      Challenge.EvmProof.ProgramArtifact.instructionPC,
      Artifact.submissionArtifact,
      Artifact.submissionInstructions,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      wordKernelState, nibbleState,
      highPrepProgram, highPrepWidth, highPrepAdvance, advancePC,
      List.getElem?_cons_zero, List.getElem?_cons_succ, List.exchange,
      hrest, h4, h5, h6, h7,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod]
  rw [show ({ val := 0 } : UInt256) = UInt256.ofNat 0 by decide]
  exact ⟨shift_highNibble 0 word, rfl⟩

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitByteTrace0
