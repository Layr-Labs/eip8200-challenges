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
  stS input 5288 (returnRest sv ov)

def storedState (input : ByteArray) (sv ov : UInt256) : State :=
  { stS input 5312 (returnRest sv ov) with
    memory := answerMemory
    activeWords := UInt256.ofNat 1 }

def sizedState (input : ByteArray) (sv ov : UInt256) : State :=
  { storedState input sv ov with
    pc := UInt256.ofNat 5313
    stack := UInt256.ofNat 32 :: returnRest sv ov }

def returnedState (input : ByteArray) (sv ov : UInt256) : State :=
  { storedState input sv ov with
    pc := UInt256.ofNat 5314
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
   pushAt 169 2 5288,
   opAt 170 .JUMPI]

def digestStorePath : List Located :=
  [opAt 4132 .JUMPDEST,
   pushAt 4133 20 paddedDigestWord,
   pushAt 4134 0 0,
   opAt 4135 .MSTORE]

def digestFinishPath : List Located :=
  [pushAt 4137 0 0, opAt 4138 .RETURN]

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
    Artifact.submissionArtifact.instructionPC 4132 = 5288 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem digestStorePC4161 :
    Artifact.submissionArtifact.instructionPC 4133 = 5289 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem digestStorePC4162 :
    Artifact.submissionArtifact.instructionPC 4134 = 5310 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem digestStorePC4163 :
    Artifact.submissionArtifact.instructionPC 4135 = 5311 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem digestFinishPC4165 :
    Artifact.submissionArtifact.instructionPC 4137 = 5313 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem digestFinishPC4166 :
    Artifact.submissionArtifact.instructionPC 4138 = 5314 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

theorem run_selector (input : ByteArray) (sv ov : UInt256)
    (hsize : input.size = 128) :
    run selectorPath (selectorState input sv ov) =
      some (digestEntryState input sv ov) := by
  change run selectorPath (stS input 260 (returnRest sv ov)) =
    some (stS input 5288 (returnRest sv ov))
  have hdest : Decode.isValidJumpDest submissionBytecode 5288 = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 4132 (by rfl)
  have htrue : UInt256.isTrue (UInt256.eq 128 (UInt256.ofNat input.size)) := by
    rw [hsize]
    decide
  have h0 :
      Challenge.EvmProof.Stepper.runLocatedBlock
          [opAt 166 .CALLDATASIZE]
          (stS input 260 (returnRest sv ov)) =
        some (stS input 261 (UInt256.ofNat input.size :: returnRest sv ov)) := by
    exact blockOfS _
      (pcFactS input 166 260 _ (by norm_num) selectorPC166)
      (stepS_calldatasize input 260 (returnRest sv ov)
        (by simp [returnRest]) (by norm_num))
  have h1 :
      Challenge.EvmProof.Stepper.runLocatedBlock
          [pushAt 167 1 128]
          (stS input 261 (UInt256.ofNat input.size :: returnRest sv ov)) =
        some (stS input 263 (128 :: UInt256.ofNat input.size :: returnRest sv ov)) := by
    exact blockOfS _
      (pcFactS input 167 261 _ (by norm_num) selectorPC167)
      (stepS_push input 261 1 128
        (UInt256.ofNat input.size :: returnRest sv ov)
        (by simp [returnRest]) (by decide) (by decide) (by norm_num))
  have h2 :
      Challenge.EvmProof.Stepper.runLocatedBlock
          [opAt 168 .EQ]
          (stS input 263 (128 :: UInt256.ofNat input.size :: returnRest sv ov)) =
        some (stS input 264
          (UInt256.eq 128 (UInt256.ofNat input.size) :: returnRest sv ov)) := by
    exact blockOfS _
      (pcFactS input 168 263 _ (by norm_num) selectorPC168)
      (stepS_eq input 263 128 (UInt256.ofNat input.size) (returnRest sv ov)
        (by simp [returnRest]) (by norm_num))
  have h3 :
      Challenge.EvmProof.Stepper.runLocatedBlock
          [pushAt 169 2 5288]
          (stS input 264
            (UInt256.eq 128 (UInt256.ofNat input.size) :: returnRest sv ov)) =
        some (stS input 267
          (5288 :: UInt256.eq 128 (UInt256.ofNat input.size) :: returnRest sv ov)) := by
    exact blockOfS _
      (pcFactS input 169 264 _ (by norm_num) selectorPC169)
      (stepS_push input 264 2 5288
        (UInt256.eq 128 (UInt256.ofNat input.size) :: returnRest sv ov)
        (by simp [returnRest]) (by decide) (by decide) (by norm_num))
  have h4 :
      Challenge.EvmProof.Stepper.runLocatedBlock
          [opAt 170 .JUMPI]
          (stS input 267
            (5288 :: UInt256.eq 128 (UInt256.ofNat input.size) :: returnRest sv ov)) =
        some (stS input 5288 (returnRest sv ov)) := by
    exact blockOfS _
      (pcFactS input 170 267 _ (by norm_num) selectorPC170)
      (stepS_jumpi_taken input 267 5288 5288
        (UInt256.eq 128 (UInt256.ofNat input.size)) (returnRest sv ov)
        (by simp [returnRest]) (by norm_num) rfl htrue hdest)
  have h01 :
      Challenge.EvmProof.Stepper.runLocatedBlock
          [opAt 166 .CALLDATASIZE, pushAt 167 1 128]
          (stS input 260 (returnRest sv ov)) =
        some (stS input 263 (128 :: UInt256.ofNat input.size :: returnRest sv ov)) := by
    exact Challenge.EvmProof.Stepper.runLocatedBlock_append
      [opAt 166 .CALLDATASIZE] [pushAt 167 1 128]
      _ _ _ h0 (by rfl) h1
  have h012 :
      Challenge.EvmProof.Stepper.runLocatedBlock
          [opAt 166 .CALLDATASIZE, pushAt 167 1 128, opAt 168 .EQ]
          (stS input 260 (returnRest sv ov)) =
        some (stS input 264
          (UInt256.eq 128 (UInt256.ofNat input.size) :: returnRest sv ov)) := by
    exact Challenge.EvmProof.Stepper.runLocatedBlock_append
      [opAt 166 .CALLDATASIZE, pushAt 167 1 128] [opAt 168 .EQ]
      _ _ _ h01 (by rfl) h2
  have h0123 :
      Challenge.EvmProof.Stepper.runLocatedBlock
          [opAt 166 .CALLDATASIZE, pushAt 167 1 128, opAt 168 .EQ,
            pushAt 169 2 5288]
          (stS input 260 (returnRest sv ov)) =
        some (stS input 267
          (5288 :: UInt256.eq 128 (UInt256.ofNat input.size) :: returnRest sv ov)) := by
    exact Challenge.EvmProof.Stepper.runLocatedBlock_append
      [opAt 166 .CALLDATASIZE, pushAt 167 1 128, opAt 168 .EQ]
      [pushAt 169 2 5288] _ _ _ h012 (by rfl) h3
  have h01234 :
      Challenge.EvmProof.Stepper.runLocatedBlock
          [opAt 166 .CALLDATASIZE, pushAt 167 1 128, opAt 168 .EQ,
            pushAt 169 2 5288, opAt 170 .JUMPI]
          (stS input 260 (returnRest sv ov)) =
        some (stS input 5288 (returnRest sv ov)) := by
    exact Challenge.EvmProof.Stepper.runLocatedBlock_append
      [opAt 166 .CALLDATASIZE, pushAt 167 1 128, opAt 168 .EQ,
        pushAt 169 2 5288] [opAt 170 .JUMPI] _ _ _ h0123 (by rfl) h4
  simpa only [selectorPath] using h01234

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
  have hd := Artifact.submissionArtifact.decodeAt_op_index 4136 .MSIZE
    (by rfl) (by decide) trivial
  have hp : (storedState input sv ov).pc.toNat =
      Artifact.submissionArtifact.instructionPC 4136 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    rfl
  have hop : (storedState input sv ov).decodedOp = some .MSIZE :=
    Artifact.submissionArtifact.state_decodedOp_of (storedState input sv ov) 4136
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
