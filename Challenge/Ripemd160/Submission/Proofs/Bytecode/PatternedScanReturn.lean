import Challenge.Ripemd160.Submission.Proofs.Bytecode.Msize
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Trace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScanTrace

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open PatternedInputData PatternedDigest PatternedGuardSpec

/-- The two return blocks meet at an explicit memory-size step. -/
private def returnStored (input : ByteArray) (pc : Nat) (stack : List UInt256) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat pc, memory := answerMemory,
    activeWords := UInt256.ofNat 1, stack := stack }

def gasSteps_return :
    GasSteps (hitState patternedInput) (returnedState patternedInput) := by
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  have hprefix : run (returnPath.take 3) (hitState patternedInput) =
      some (returnStored patternedInput 420 []) := by
    simp (config := { maxSteps := 1000000 })
      [returnPath, opAt, pushAt, wfOp, hitState, atPC, returnStored, initialState,
       answerMemory, storeWord, paddedDigestWord,
       MachineState.mstore, State.activeWordsAfterUInt256,
       MachineState.activeWordsAfter, hzeroNat,
       Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
       Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod,
       Challenge.EvmProof.Word.ofNat_add_mod, Challenge.EvmProof.Word.word_toNat_ofNat]
  have a := Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka
    (returnPath.take 3) (by rfl) (by rfl) hprefix (by rfl) deployAddress_not_precompile
  have hop : (returnStored patternedInput 420 []).decodedOp = some .MSIZE := by
    apply Trace.decodedOpAt (returnStored patternedInput 420 []) 236 .MSIZE
    · rfl
    · change UInt256.ofNat 420 =
        UInt256.ofNat (Artifact.submissionArtifact.instructionPC 236)
      simp
    · rfl
    · rfl
    · trivial
    · rfl
  have b : GasSteps (returnStored patternedInput 420 [])
      (returnStored patternedInput 421 [32]) :=
    Msize.step hop (by change 0 < 1024; decide) (by rfl) deployAddress_not_precompile
  have hsuffix : run (returnPath.drop 4) (returnStored patternedInput 421 [32]) =
      some (returnedState patternedInput) := by
    simp (config := { maxSteps := 1000000 })
      [returnPath, opAt, pushAt, wfOp, returnStored, returnedState, initialState,
       MachineState.activeWordsAfter, State.activeWordsAfterUInt256,
       Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
       Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod,
       Challenge.EvmProof.Word.ofNat_add_mod, Challenge.EvmProof.Word.word_toNat_ofNat]
  have c := Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka
    (returnPath.drop 4) (by rfl) (by rfl) hsuffix (by rfl) deployAddress_not_precompile
  exact a.trans (b.trans c)

theorem answerMemory_read :
    MachineState.readPadded answerMemory 0 32 = paddedDigest := by
  unfold answerMemory storeWord
  have h := Memory.readPadded_writeBytes_same ByteArray.empty
    (Data.Bytes.natToBytesPadded paddedDigestWord.toNat 32) 0
  simpa only [YulEvmCompiler.BytesLemmas.natToBytesPadded_size,
    wordBytes_eq_paddedDigest, paddedDigest_size] using h

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan
