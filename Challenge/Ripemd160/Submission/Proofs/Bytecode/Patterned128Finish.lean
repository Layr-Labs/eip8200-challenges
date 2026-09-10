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
  stS input 5161 (returnRest sv ov)

def storedState (input : ByteArray) (sv ov : UInt256) : State :=
  { stS input 5185 (returnRest sv ov) with
    memory := answerMemory
    activeWords := UInt256.ofNat 1 }

def sizedState (input : ByteArray) (sv ov : UInt256) : State :=
  { storedState input sv ov with
    pc := UInt256.ofNat 5186
    stack := UInt256.ofNat 32 :: returnRest sv ov }

def returnedState (input : ByteArray) (sv ov : UInt256) : State :=
  { storedState input sv ov with
    pc := UInt256.ofNat 5187
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
  [opAt 160 .CALLDATASIZE, pushAt 161 1 129, opAt 162 .GT,
   pushAt 163 2 5198, opAt 164 .JUMPI,
   opAt 4168 .JUMPDEST, opAt 4169 .CALLDATASIZE, pushAt 4170 1 128,
   opAt 4171 .EQ, pushAt 4172 2 5161, opAt 4173 .JUMPI]

def digestStorePath : List Located :=
  [opAt 4155 .JUMPDEST,
   pushAt 4156 20 paddedDigestWord,
   pushAt 4157 0 0,
   opAt 4158 .MSTORE]

def digestFinishPath : List Located :=
  [pushAt 4160 0 0, opAt 4161 .RETURN]

@[simp] private theorem selectorPC166 :
    Artifact.submissionArtifact.instructionPC 160 = 260 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem selectorPC167 :
    Artifact.submissionArtifact.instructionPC 161 = 261 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem selectorPC168 :
    Artifact.submissionArtifact.instructionPC 162 = 263 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem selectorPC169 :
    Artifact.submissionArtifact.instructionPC 163 = 264 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem selectorPC170 :
    Artifact.submissionArtifact.instructionPC 164 = 267 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem digestStorePC4160 :
    Artifact.submissionArtifact.instructionPC 4155 = 5161 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem digestStorePC4161 :
    Artifact.submissionArtifact.instructionPC 4156 = 5162 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem digestStorePC4162 :
    Artifact.submissionArtifact.instructionPC 4157 = 5183 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem digestStorePC4163 :
    Artifact.submissionArtifact.instructionPC 4158 = 5184 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem digestFinishPC4165 :
    Artifact.submissionArtifact.instructionPC 4160 = 5186 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem digestFinishPC4166 :
    Artifact.submissionArtifact.instructionPC 4161 = 5187 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem shortHelperPC4181 :
    Artifact.submissionArtifact.instructionPC 4168 = 5198 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem shortHelperPC4182 :
    Artifact.submissionArtifact.instructionPC 4169 = 5199 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem shortHelperPC4183 :
    Artifact.submissionArtifact.instructionPC 4170 = 5200 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem shortHelperPC4184 :
    Artifact.submissionArtifact.instructionPC 4171 = 5202 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem shortHelperPC4185 :
    Artifact.submissionArtifact.instructionPC 4172 = 5203 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] private theorem shortHelperPC4186 :
    Artifact.submissionArtifact.instructionPC 4173 = 5206 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

theorem run_selector (input : ByteArray) (sv ov : UInt256)
    (hsize : input.size = 128) :
    run selectorPath (selectorState input sv ov) =
      some (digestEntryState input sv ov) := by
  have ha : run [opAt 160 .CALLDATASIZE, pushAt 161 1 129, opAt 162 .GT, pushAt 163 2 5198, opAt 164 .JUMPI] (stS input 260 (returnRest sv ov)) = some (stS input 5198 (returnRest sv ov)) := by
    have hdest : Decode.isValidJumpDest submissionBytecode 5198 = true :=
      Artifact.submissionArtifact.isValidJumpDest_index 4168 (by rfl)
    have htrue : UInt256.isTrue (UInt256.gt 129 (UInt256.ofNat input.size)) := by
      rw [hsize]
      decide
    have h0 :
        Challenge.EvmProof.Stepper.runLocatedBlock
            [opAt 160 .CALLDATASIZE]
            (stS input 260 (returnRest sv ov)) =
          some (stS input 261 (UInt256.ofNat input.size :: returnRest sv ov)) := by
      exact blockOfS _
        (pcFactS input 160 260 _ (by norm_num) selectorPC166)
        (stepS_calldatasize input 260 (returnRest sv ov)
          (by simp [returnRest]) (by norm_num))
    have h1 :
        Challenge.EvmProof.Stepper.runLocatedBlock
            [pushAt 161 1 129]
            (stS input 261 (UInt256.ofNat input.size :: returnRest sv ov)) =
          some (stS input 263 (129 :: UInt256.ofNat input.size :: returnRest sv ov)) := by
      exact blockOfS _
        (pcFactS input 161 261 _ (by norm_num) selectorPC167)
        (stepS_push input 261 1 129
          (UInt256.ofNat input.size :: returnRest sv ov)
          (by simp [returnRest]) (by decide) (by decide) (by norm_num))
    have h2 :
        Challenge.EvmProof.Stepper.runLocatedBlock
            [opAt 162 .GT]
            (stS input 263 (129 :: UInt256.ofNat input.size :: returnRest sv ov)) =
          some (stS input 264
            (UInt256.gt 129 (UInt256.ofNat input.size) :: returnRest sv ov)) := by
      exact blockOfS _
        (pcFactS input 162 263 _ (by norm_num) selectorPC168)
        (stepS_gt input 263 129 (UInt256.ofNat input.size) (returnRest sv ov)
          (by simp [returnRest]) (by norm_num))
    have h3 :
        Challenge.EvmProof.Stepper.runLocatedBlock
            [pushAt 163 2 5198]
            (stS input 264
              (UInt256.gt 129 (UInt256.ofNat input.size) :: returnRest sv ov)) =
          some (stS input 267
            (5198 :: UInt256.gt 129 (UInt256.ofNat input.size) :: returnRest sv ov)) := by
      exact blockOfS _
        (pcFactS input 163 264 _ (by norm_num) selectorPC169)
        (stepS_push input 264 2 5198
          (UInt256.gt 129 (UInt256.ofNat input.size) :: returnRest sv ov)
          (by simp [returnRest]) (by decide) (by decide) (by norm_num))
    have h4 :
        Challenge.EvmProof.Stepper.runLocatedBlock
            [opAt 164 .JUMPI]
            (stS input 267
              (5198 :: UInt256.gt 129 (UInt256.ofNat input.size) :: returnRest sv ov)) =
          some (stS input 5198 (returnRest sv ov)) := by
      exact blockOfS _
        (pcFactS input 164 267 _ (by norm_num) selectorPC170)
        (stepS_jumpi_taken input 267 5198 5198
          (UInt256.gt 129 (UInt256.ofNat input.size)) (returnRest sv ov)
          (by simp [returnRest]) (by norm_num) rfl htrue hdest)
    have h01 :
        Challenge.EvmProof.Stepper.runLocatedBlock
            [opAt 160 .CALLDATASIZE, pushAt 161 1 129]
            (stS input 260 (returnRest sv ov)) =
          some (stS input 263 (129 :: UInt256.ofNat input.size :: returnRest sv ov)) := by
      exact Challenge.EvmProof.Stepper.runLocatedBlock_append
        [opAt 160 .CALLDATASIZE] [pushAt 161 1 129]
        _ _ _ h0 (by rfl) h1
    have h012 :
        Challenge.EvmProof.Stepper.runLocatedBlock
            [opAt 160 .CALLDATASIZE, pushAt 161 1 129, opAt 162 .GT]
            (stS input 260 (returnRest sv ov)) =
          some (stS input 264
            (UInt256.gt 129 (UInt256.ofNat input.size) :: returnRest sv ov)) := by
      exact Challenge.EvmProof.Stepper.runLocatedBlock_append
        [opAt 160 .CALLDATASIZE, pushAt 161 1 129] [opAt 162 .GT]
        _ _ _ h01 (by rfl) h2
    have h0123 :
        Challenge.EvmProof.Stepper.runLocatedBlock
            [opAt 160 .CALLDATASIZE, pushAt 161 1 129, opAt 162 .GT,
              pushAt 163 2 5198]
            (stS input 260 (returnRest sv ov)) =
          some (stS input 267
            (5198 :: UInt256.gt 129 (UInt256.ofNat input.size) :: returnRest sv ov)) := by
      exact Challenge.EvmProof.Stepper.runLocatedBlock_append
        [opAt 160 .CALLDATASIZE, pushAt 161 1 129, opAt 162 .GT]
        [pushAt 163 2 5198] _ _ _ h012 (by rfl) h3
    have h01234 :
        Challenge.EvmProof.Stepper.runLocatedBlock
            [opAt 160 .CALLDATASIZE, pushAt 161 1 129, opAt 162 .GT,
              pushAt 163 2 5198, opAt 164 .JUMPI]
            (stS input 260 (returnRest sv ov)) =
          some (stS input 5198 (returnRest sv ov)) := by
      exact Challenge.EvmProof.Stepper.runLocatedBlock_append
        [opAt 160 .CALLDATASIZE, pushAt 161 1 129, opAt 162 .GT,
          pushAt 163 2 5198] [opAt 164 .JUMPI] _ _ _ h0123 (by rfl) h4
    exact h01234
  have hb : run [opAt 4168 .JUMPDEST] (stS input 5198 (returnRest sv ov)) = some (stS input 5199 (returnRest sv ov)) := by
    exact blockOfS _ (pcFactS input 4168 5198 _ (by norm_num) shortHelperPC4181)
      (stepS_jumpdest input 5198 (returnRest sv ov) (by simp [returnRest]) (by norm_num))
  have hc : run [opAt 4169 .CALLDATASIZE, pushAt 4170 1 128, opAt 4171 .EQ, pushAt 4172 2 5161, opAt 4173 .JUMPI] (stS input 5199 (returnRest sv ov)) = some (stS input 5161 (returnRest sv ov)) := by
    have hdest : Decode.isValidJumpDest submissionBytecode 5161 = true :=
      Artifact.submissionArtifact.isValidJumpDest_index 4155 (by rfl)
    have htrue : UInt256.isTrue (UInt256.eq 128 (UInt256.ofNat input.size)) := by
      rw [hsize]
      decide
    have h0 :
        Challenge.EvmProof.Stepper.runLocatedBlock
            [opAt 4169 .CALLDATASIZE]
            (stS input 5199 (returnRest sv ov)) =
          some (stS input 5200 (UInt256.ofNat input.size :: returnRest sv ov)) := by
      exact blockOfS _
        (pcFactS input 4169 5199 _ (by norm_num) shortHelperPC4182)
        (stepS_calldatasize input 5199 (returnRest sv ov)
          (by simp [returnRest]) (by norm_num))
    have h1 :
        Challenge.EvmProof.Stepper.runLocatedBlock
            [pushAt 4170 1 128]
            (stS input 5200 (UInt256.ofNat input.size :: returnRest sv ov)) =
          some (stS input 5202 (128 :: UInt256.ofNat input.size :: returnRest sv ov)) := by
      exact blockOfS _
        (pcFactS input 4170 5200 _ (by norm_num) shortHelperPC4183)
        (stepS_push input 5200 1 128
          (UInt256.ofNat input.size :: returnRest sv ov)
          (by simp [returnRest]) (by decide) (by decide) (by norm_num))
    have h2 :
        Challenge.EvmProof.Stepper.runLocatedBlock
            [opAt 4171 .EQ]
            (stS input 5202 (128 :: UInt256.ofNat input.size :: returnRest sv ov)) =
          some (stS input 5203
            (UInt256.eq 128 (UInt256.ofNat input.size) :: returnRest sv ov)) := by
      exact blockOfS _
        (pcFactS input 4171 5202 _ (by norm_num) shortHelperPC4184)
        (stepS_eq input 5202 128 (UInt256.ofNat input.size) (returnRest sv ov)
          (by simp [returnRest]) (by norm_num))
    have h3 :
        Challenge.EvmProof.Stepper.runLocatedBlock
            [pushAt 4172 2 5161]
            (stS input 5203
              (UInt256.eq 128 (UInt256.ofNat input.size) :: returnRest sv ov)) =
          some (stS input 5206
            (5161 :: UInt256.eq 128 (UInt256.ofNat input.size) :: returnRest sv ov)) := by
      exact blockOfS _
        (pcFactS input 4172 5203 _ (by norm_num) shortHelperPC4185)
        (stepS_push input 5203 2 5161
          (UInt256.eq 128 (UInt256.ofNat input.size) :: returnRest sv ov)
          (by simp [returnRest]) (by decide) (by decide) (by norm_num))
    have h4 :
        Challenge.EvmProof.Stepper.runLocatedBlock
            [opAt 4173 .JUMPI]
            (stS input 5206
              (5161 :: UInt256.eq 128 (UInt256.ofNat input.size) :: returnRest sv ov)) =
          some (stS input 5161 (returnRest sv ov)) := by
      exact blockOfS _
        (pcFactS input 4173 5206 _ (by norm_num) shortHelperPC4186)
        (stepS_jumpi_taken input 5206 5161 5161
          (UInt256.eq 128 (UInt256.ofNat input.size)) (returnRest sv ov)
          (by simp [returnRest]) (by norm_num) rfl htrue hdest)
    have h01 :
        Challenge.EvmProof.Stepper.runLocatedBlock
            [opAt 4169 .CALLDATASIZE, pushAt 4170 1 128]
            (stS input 5199 (returnRest sv ov)) =
          some (stS input 5202 (128 :: UInt256.ofNat input.size :: returnRest sv ov)) := by
      exact Challenge.EvmProof.Stepper.runLocatedBlock_append
        [opAt 4169 .CALLDATASIZE] [pushAt 4170 1 128]
        _ _ _ h0 (by rfl) h1
    have h012 :
        Challenge.EvmProof.Stepper.runLocatedBlock
            [opAt 4169 .CALLDATASIZE, pushAt 4170 1 128, opAt 4171 .EQ]
            (stS input 5199 (returnRest sv ov)) =
          some (stS input 5203
            (UInt256.eq 128 (UInt256.ofNat input.size) :: returnRest sv ov)) := by
      exact Challenge.EvmProof.Stepper.runLocatedBlock_append
        [opAt 4169 .CALLDATASIZE, pushAt 4170 1 128] [opAt 4171 .EQ]
        _ _ _ h01 (by rfl) h2
    have h0123 :
        Challenge.EvmProof.Stepper.runLocatedBlock
            [opAt 4169 .CALLDATASIZE, pushAt 4170 1 128, opAt 4171 .EQ,
              pushAt 4172 2 5161]
            (stS input 5199 (returnRest sv ov)) =
          some (stS input 5206
            (5161 :: UInt256.eq 128 (UInt256.ofNat input.size) :: returnRest sv ov)) := by
      exact Challenge.EvmProof.Stepper.runLocatedBlock_append
        [opAt 4169 .CALLDATASIZE, pushAt 4170 1 128, opAt 4171 .EQ]
        [pushAt 4172 2 5161] _ _ _ h012 (by rfl) h3
    have h01234 :
        Challenge.EvmProof.Stepper.runLocatedBlock
            [opAt 4169 .CALLDATASIZE, pushAt 4170 1 128, opAt 4171 .EQ,
              pushAt 4172 2 5161, opAt 4173 .JUMPI]
            (stS input 5199 (returnRest sv ov)) =
          some (stS input 5161 (returnRest sv ov)) := by
      exact Challenge.EvmProof.Stepper.runLocatedBlock_append
        [opAt 4169 .CALLDATASIZE, pushAt 4170 1 128, opAt 4171 .EQ,
          pushAt 4172 2 5161] [opAt 4173 .JUMPI] _ _ _ h0123 (by rfl) h4
    exact h01234
  have hbc := Challenge.EvmProof.Stepper.runLocatedBlock_append
    [opAt 4168 .JUMPDEST] [opAt 4169 .CALLDATASIZE, pushAt 4170 1 128, opAt 4171 .EQ, pushAt 4172 2 5161, opAt 4173 .JUMPI] _ _ _ hb (by rfl) hc
  have habc := Challenge.EvmProof.Stepper.runLocatedBlock_append
    [opAt 160 .CALLDATASIZE, pushAt 161 1 129, opAt 162 .GT, pushAt 163 2 5198, opAt 164 .JUMPI] ([opAt 4168 .JUMPDEST] ++ [opAt 4169 .CALLDATASIZE, pushAt 4170 1 128, opAt 4171 .EQ, pushAt 4172 2 5161, opAt 4173 .JUMPI]) _ _ _ ha (by rfl) hbc
  exact habc

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
  have hd := Artifact.submissionArtifact.decodeAt_op_index 4159 .MSIZE
    (by rfl) (by decide) trivial
  have hp : (storedState input sv ov).pc.toNat =
      Artifact.submissionArtifact.instructionPC 4159 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    rfl
  have hop : (storedState input sv ov).decodedOp = some .MSIZE :=
    Artifact.submissionArtifact.state_decodedOp_of (storedState input sv ov) 4159
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
