import Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitByteSlices
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowBytePrep
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleSquare
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleLookup

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 5000000

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitByte1Low

open Challenge.EvmProof.Stepper EvmSemantics EvmSemantics.EVM
open WindowHitByteSlices WindowByteKernel WindowNibbleKernel
open WindowNibbleForward

set_option linter.unusedSimpArgs false in
theorem run_prep (template : State) (base modulus : UInt256) (high : Nat)
    (word pointer original accumulator : UInt256) (rest : List UInt256)
    (hrest : rest.length ≤ 1000) :
    runLocatedBlock (lowPrepPath 1)
      (forwardedNibbleState { template with halt := .Running } (UInt256.ofNat 3121)
        base modulus high (byteValue 1 word) word pointer original accumulator rest) =
    some (forwardedNibbleState { template with halt := .Running } (UInt256.ofNat 3121)
      base modulus (lowNibble 1 word) (byteValue 1 word) word pointer
      original accumulator rest)  := by
  have _ := hrest
  rfl

set_option linter.unusedSimpArgs false in
/-- Fused low-nibble block: four squares then the table multiply, 23
instructions in 41 bytes.  The machine loads the table word
last, so the accumulator-first `nibbleWordStep` spelling needs `mulMod_comm`. -/
theorem run_squareLookup (template : State) (base modulus : UInt256)
    (nibble : Nat) (byte word pointer original accumulator : UInt256)
    (rest : List UInt256) (hnibble : nibble < 16)
    (hmask : UInt256.land (UInt256.ofNat 15) byte = UInt256.ofNat nibble)
    (hrest : rest.length ≤ 1000) :
    runLocatedBlock (lowSquareLookupPath 1)
      (forwardedNibbleState { template with halt := .Running } (UInt256.ofNat 3121)
        base modulus nibble byte word pointer original accumulator rest) =
    some (lowResultState { template with halt := .Running } (UInt256.ofNat 3162)
      base modulus nibble byte word pointer
      (WindowMath.nibbleWordStep modulus base accumulator nibble) rest) := by
  have hshift := shift_nibble nibble hnibble
  have hoffset : (UInt256.ofNat (32 * nibble)).toNat = 32 * nibble := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat]
    apply Nat.mod_eq_of_lt
    omega
  have hread := WindowTableMemory.readWord_tableMemory base modulus nibble hnibble
  have hactive := WindowTableMemory.activeWordsAfter_lookup nibble hnibble
  have h5 : rest.length + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
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
    [lowSquareLookupPath, byteStartIndex, locatedSlice,
      Challenge.EvmProof.Stepper.Located.ofIndex,
      Challenge.EvmProof.ProgramArtifact.instructionPC,
      Artifact.submissionArtifact, Artifact.submissionInstructions,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      lowResultState, forwardedNibbleState, lowNibbleState, nibbleState, WindowMath.squareWordAfter,
      List.getElem?_cons_zero, List.getElem?_cons_succ, List.exchange,
      hrest, h5, h6, h7, h8, h9, h10, h11, h12, hmask, hshift, hoffset, hread, hactive,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod]
  -- The fused block loads the table word last, so `MULMOD` multiplies in the
  -- opposite order from the accumulator-first `nibbleWordStep` spelling.
  -- Equal, but not definitionally equal.
  exact mulMod_comm _ _ _

set_option linter.unusedSimpArgs false in
theorem run_finish (template : State) (base modulus : UInt256)
    (nibble : Nat) (byte word pointer accumulator : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1000) :
    runLocatedBlock (finishPath 1)
      (lowResultState { template with halt := .Running } (UInt256.ofNat 3162)
        base modulus nibble byte word pointer accumulator rest) =
    some (wordKernelState { template with halt := .Running } (UInt256.ofNat 3162)
      base modulus word pointer accumulator rest)  := by
  have _ := hrest
  rfl

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitByte1Low
