import Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned128Digest
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned128Scan
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Cleanup
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Msize

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned128Finish

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open PatternedScan PatternedSwar

def paddedDigestWord : UInt256 := Patterned128Digest.paddedDigestWord

def paddedDigest : ByteArray := Patterned128Digest.paddedDigest

def answerMemory : ByteArray := storeWord ByteArray.empty 0 paddedDigestWord

def returnRest (sv ov : UInt256) : List UInt256 :=
  [sv, ov, 0, P7, M, m7, P, m8]

def selectorState (input : ByteArray) (sv ov : UInt256) : State :=
  stS input 260 (returnRest sv ov)

def digestEntryState (input : ByteArray) (sv ov : UInt256) : State :=
  stS input 5155 (returnRest sv ov)

def storedState (input : ByteArray) (sv ov : UInt256) : State :=
  { stS input 5179 (returnRest sv ov) with
    memory := answerMemory
    activeWords := UInt256.ofNat 1 }

def sizedState (input : ByteArray) (sv ov : UInt256) : State :=
  { storedState input sv ov with
    pc := UInt256.ofNat 5180
    stack := UInt256.ofNat 32 :: returnRest sv ov }

def returnedState (input : ByteArray) (sv ov : UInt256) : State :=
  { storedState input sv ov with
    pc := UInt256.ofNat 5181
    halt := .Returned
    hReturn := MachineState.readPadded answerMemory 0 32 }

@[simp] theorem paddedDigest_size : paddedDigest.size = 32 := by
  exact Patterned128Digest.paddedDigest_size

theorem wordBytes_eq_paddedDigest :
    Data.Bytes.natToBytesPadded paddedDigestWord.toNat 32 = paddedDigest := by
  exact Patterned128Digest.wordBytes_eq_paddedDigest

theorem answerMemory_read :
    MachineState.readPadded answerMemory 0 32 = paddedDigest := by
  unfold answerMemory storeWord
  have h := Memory.readPadded_writeBytes_same ByteArray.empty
    (Data.Bytes.natToBytesPadded paddedDigestWord.toNat 32) 0
  simpa only [YulEvmCompiler.BytesLemmas.natToBytesPadded_size,
    wordBytes_eq_paddedDigest, paddedDigest_size] using h

@[simp] theorem returnedState_hReturn (input : ByteArray) (sv ov : UInt256) :
    (returnedState input sv ov).hReturn = paddedDigest := by
  exact answerMemory_read

@[simp] theorem returnedState_hReturn_size (input : ByteArray) (sv ov : UInt256) :
    (returnedState input sv ov).hReturn.size = 32 := by
  rw [returnedState_hReturn, paddedDigest_size]

def selectorPath : List Located :=
  [opAt 166 .CALLDATASIZE,
   pushAt 167 1 128,
   opAt 168 .EQ,
   pushAt 169 2 5155,
   opAt 170 .JUMPI]

def digestStorePath : List Located :=
  [opAt 4160 .JUMPDEST,
   pushAt 4161 20 paddedDigestWord,
   pushAt 4162 0 0,
   opAt 4163 .MSTORE]

def digestFinishPath : List Located :=
  [pushAt 4165 0 0, opAt 4166 .RETURN]

@[simp] private theorem selectorPC166 :
    Artifact.submissionArtifact.instructionPC 166 = 260 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem selectorPC167 :
    Artifact.submissionArtifact.instructionPC 167 = 261 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem selectorPC168 :
    Artifact.submissionArtifact.instructionPC 168 = 263 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem selectorPC169 :
    Artifact.submissionArtifact.instructionPC 169 = 264 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem selectorPC170 :
    Artifact.submissionArtifact.instructionPC 170 = 267 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem digestStorePC4160 :
    Artifact.submissionArtifact.instructionPC 4160 = 5155 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem digestStorePC4161 :
    Artifact.submissionArtifact.instructionPC 4161 = 5156 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem digestStorePC4162 :
    Artifact.submissionArtifact.instructionPC 4162 = 5177 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem digestStorePC4163 :
    Artifact.submissionArtifact.instructionPC 4163 = 5178 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem digestFinishPC4165 :
    Artifact.submissionArtifact.instructionPC 4165 = 5180 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem digestFinishPC4166 :
    Artifact.submissionArtifact.instructionPC 4166 = 5181 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

theorem run_selector (input : ByteArray) (sv ov : UInt256)
    (hsize : input.size = 128) :
    run selectorPath (selectorState input sv ov) =
      some (digestEntryState input sv ov) := by
  have hdest : Decode.isValidJumpDest submissionBytecode 5155 = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 4160 (by rfl)
  simp (config := { maxSteps := 400000 })
    [selectorPath, opAt, pushAt, wfOp, selectorState, digestEntryState,
      returnRest, stS, initialState, hsize, hdest, UInt256.eq, UInt256.isTrue,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat]

theorem run_store (input : ByteArray) (sv ov : UInt256) :
    run digestStorePath (digestEntryState input sv ov) =
      some (storedState input sv ov) := by
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp (config := { maxSteps := 400000 })
    [digestStorePath, opAt, pushAt, wfOp, digestEntryState, storedState,
      returnRest, stS, initialState, answerMemory, storeWord, paddedDigestWord,
      State.activeWordsAfterUInt256, MachineState.activeWordsAfter, hzeroNat,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat]

theorem run_finish (input : ByteArray) (sv ov : UInt256) :
    run digestFinishPath (sizedState input sv ov) =
      some (returnedState input sv ov) := by
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp (config := { maxSteps := 400000 })
    [digestFinishPath, opAt, pushAt, wfOp, sizedState, storedState,
      returnRest, stS, initialState, returnedState, answerMemory, storeWord,
      paddedDigestWord, State.activeWordsAfterUInt256,
      MachineState.activeWordsAfter, hzeroNat,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat]

def gasSteps_return (input : ByteArray) (sv ov : UInt256)
    (hsize : input.size = 128) :
    GasSteps (selectorState input sv ov) (returnedState input sv ov) := by
  have gselect := sound selectorPath (run_selector input sv ov hsize)
  have gstore := sound digestStorePath (run_store input sv ov)
  have hd := Artifact.submissionArtifact.decodeAt_op_index 4164 .MSIZE
    (by rfl) (by decide) trivial
  have hp : (storedState input sv ov).pc.toNat =
      Artifact.submissionArtifact.instructionPC 4164 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    rfl
  have hop : (storedState input sv ov).decodedOp = some .MSIZE :=
    Artifact.submissionArtifact.state_decodedOp_of (storedState input sv ov) 4164
      (by rfl) hp .MSIZE none hd (by rfl)
  have gmraw := Msize.step hop
    (by simp [storedState, returnRest, stS, initialState])
    (by rfl) deployAddress_not_precompile
  have gm : GasSteps (storedState input sv ov) (sizedState input sv ov) := by
    simpa [storedState, sizedState, returnRest, stS, initialState,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat] using gmraw
  exact gselect.trans (gstore.trans (gm.trans (sound digestFinishPath
    (run_finish input sv ov))))

def gasSteps_miss (input : ByteArray) (sv ov acc : UInt256)
    (hne : acc ≠ 0) :
    GasSteps (stS input 255 [sv, ov, acc, P7, M, m7, P, m8])
      (fallbackState input) :=
  Prefix256Cleanup.gasSteps_miss input sv ov acc hne

def gasSteps_finish_hit (input : ByteArray) (sv ov acc : UInt256)
    (hz : acc = 0) (hsize : input.size = 128) :
    GasSteps (stS input 255 [sv, ov, acc, P7, M, m7, P, m8])
      (returnedState input sv ov) := by
  subst acc
  exact (Prefix256Cleanup.gasSteps_hit input sv ov).trans
    (gasSteps_return input sv ov hsize)

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned128Finish
