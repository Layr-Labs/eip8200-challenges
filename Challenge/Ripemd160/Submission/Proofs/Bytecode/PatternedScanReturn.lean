import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScanTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Msize

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open PatternedInputData PatternedDigest PatternedGuardSpec

def returnStored (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 481
    memory := answerMemory
    activeWords := UInt256.ofNat 1 }

def returnSized (input : ByteArray) : State :=
  { returnStored input with
    pc := UInt256.ofNat 482
    stack := [UInt256.ofNat 32] }

theorem run_return_store :
    run (returnPath.take 3) (hitState patternedInput) =
      some (returnStored patternedInput) := by
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp (config := { maxSteps := 1000000 })
    [initialState, returnPath, opAt, pushAt, wfOp, hitState, atPC, returnStored,
    answerMemory, storeWord, paddedDigestWord,
    MachineState.mstore, State.activeWordsAfterUInt256,
    MachineState.activeWordsAfter, hzeroNat,
    Challenge.EvmProof.Stepper.runLocatedBlock, Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod, Challenge.EvmProof.Word.word_toNat_ofNat]

theorem run_return_finish :
    run (returnPath.drop 4) (returnSized patternedInput) =
      some (returnedState patternedInput) := by
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp (config := { maxSteps := 1000000 })
    [initialState, returnPath, opAt, pushAt, wfOp, returnSized, returnStored, returnedState,
    State.activeWordsAfterUInt256, MachineState.activeWordsAfter, hzeroNat,
    Challenge.EvmProof.Stepper.runLocatedBlock, Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod, Challenge.EvmProof.Word.word_toNat_ofNat]

def gasSteps_return :
    GasSteps (hitState patternedInput)
      (returnedState patternedInput) := by
  have gs := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka (returnPath.take 3)
    (by rfl) (by rfl) run_return_store (by rfl) deployAddress_not_precompile
  have hd := Artifact.submissionArtifact.decodeAt_op_index
    238 .MSIZE (by rfl) (by decide) trivial
  have hp : (returnStored patternedInput).pc.toNat =
      Artifact.submissionArtifact.instructionPC 238 := by
    rw [pc2986]
    rfl
  have hop : (returnStored patternedInput).decodedOp = some .MSIZE :=
    Artifact.submissionArtifact.state_decodedOp_of
      (returnStored patternedInput) 238 (by rfl) hp .MSIZE none hd (by decide)
  have gmraw := Msize.step hop (by simp [returnStored, initialState]) (by rfl)
    deployAddress_not_precompile
  have gm : GasSteps (returnStored patternedInput)
      (returnSized patternedInput) := by
    simpa [returnStored, returnSized, initialState,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat] using gmraw
  have gr := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka (returnPath.drop 4)
    (by rfl) (by rfl) run_return_finish (by rfl) deployAddress_not_precompile
  exact gs.trans (gm.trans gr)

#print axioms gasSteps_return


theorem answerMemory_read :
    MachineState.readPadded answerMemory 0 32 = paddedDigest := by
  unfold answerMemory storeWord
  have h := Memory.readPadded_writeBytes_same ByteArray.empty
    (Data.Bytes.natToBytesPadded paddedDigestWord.toNat 32) 0
  simpa only [YulEvmCompiler.BytesLemmas.natToBytesPadded_size,
    wordBytes_eq_paddedDigest, paddedDigest_size] using h

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan
