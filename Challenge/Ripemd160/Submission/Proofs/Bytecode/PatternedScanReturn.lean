import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScanTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Msize

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open PatternedInputData PatternedDigest PatternedGuardSpec

def storedState (input : ByteArray) (pc : Nat) (stk : List UInt256) : State :=
  { atPC input pc with memory := answerMemory, activeWords := UInt256.ofNat 1,
    stack := stk }

def returnPrefixPath : List Located :=
  [pushAt 162 21 766350606435067737561421097975693824639675460820,
   pushAt 163 0 0, opAt 164 .MSTORE]

def returnSuffixPath : List Located :=
  [pushAt 166 0 0, opAt 167 .RETURN]

theorem run_return :
    run returnPath (hitState patternedInput) = some (returnedState patternedInput) := by
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp (config := { maxSteps := 400000 })
    [returnPath, opAt, pushAt, wfOp, hitState, atPC, returnedState,
    answerMemory, storeWord, paddedDigestWord,
    MachineState.mstore, MachineState.msize, State.activeWordsAfterUInt256,
    State.activeWordsAfter, hzeroNat,
    Challenge.EvmProof.Stepper.runLocatedBlock, Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr, initialState,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod, Challenge.EvmProof.Word.word_toNat_ofNat]

private theorem pc165 :
    Artifact.submissionArtifact.instructionPC 165 = 321 := by
  rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

def gasSteps_return :
    GasSteps (hitState patternedInput) (returnedState patternedInput) := by
  have hprefix :
      run returnPrefixPath (hitState patternedInput) =
        some (storedState patternedInput 321 []) := by
    have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
    simp (config := { maxSteps := 200000 })
      [returnPrefixPath, opAt, pushAt, wfOp, hitState, atPC, storedState,
      answerMemory, storeWord, paddedDigestWord,
      MachineState.mstore, State.activeWordsAfterUInt256,
      State.activeWordsAfter, hzeroNat,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr, initialState,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat]
  have hs :
      (storedState patternedInput 321 []).decodedOp = some .MSIZE := by
    have hget : Artifact.submissionInstructions[165]? = some (.op .MSIZE) := by
      decide
    have hdecode := Artifact.submissionArtifact.decodeAt_op_index
      165 .MSIZE hget (by decide) trivial
    apply Artifact.submissionArtifact.state_decodedOp_of
      (storedState patternedInput 321 []) 165
    · rfl
    · change (UInt256.ofNat 321).toNat =
        Artifact.submissionArtifact.instructionPC 165
      rw [pc165]
      rfl
    · exact .MSIZE
    · exact none
    · exact hdecode
    · decide
  have hmraw := Msize.step hs (by simp [storedState, atPC])
    (by simp [storedState, atPC]) deployAddress_not_precompile
  have hm :
      GasSteps (storedState patternedInput 321 [])
        (storedState patternedInput 322 [32]) :=
    GasSteps.cast hmraw rfl (by
      simp [storedState, atPC, Challenge.EvmProof.Word.succ_ofNat_mod])
  have hsuffix :
      run returnSuffixPath (storedState patternedInput 322 [32]) =
        some (returnedState patternedInput) := by
    have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
    simp (config := { maxSteps := 200000 })
      [returnSuffixPath, opAt, pushAt, wfOp, storedState, atPC,
      returnedState, answerMemory, storeWord, paddedDigestWord,
      MachineState.activeWordsAfterUInt256, State.activeWordsAfter,
      hzeroNat, Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr, initialState,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat]
  exact (sound returnPrefixPath hprefix).trans
    (hm.trans (sound returnSuffixPath hsuffix))

theorem answerMemory_read :
    MachineState.readPadded answerMemory 0 32 = paddedDigest := by
  unfold answerMemory storeWord
  have h := Memory.readPadded_writeBytes_same ByteArray.empty
    (Data.Bytes.natToBytesPadded paddedDigestWord.toNat 32) 0
  simpa only [YulEvmCompiler.BytesLemmas.natToBytesPadded_size,
    wordBytes_eq_paddedDigest, paddedDigest_size] using h

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan
