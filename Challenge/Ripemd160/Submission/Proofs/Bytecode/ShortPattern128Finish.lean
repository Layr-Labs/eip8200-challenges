import Challenge.Ripemd160.Submission.Proofs.Bytecode.ShortPattern128Hop
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Cleanup
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Msize
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned128Digest
import Challenge.Ripemd160.Submission.Proofs.Bytecode.newArtifactByteLength

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.ShortPattern128Finish

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open PatternedScan PatternedSwar

def paddedDigestWord : UInt256 := Patterned128Digest.paddedDigestWord
def paddedDigest : ByteArray := Patterned128Digest.paddedDigest
def answerMemory : ByteArray :=
  storeWord ByteArray.empty 0 ShortPattern128Hop.digest128

def returnRest (sv ov : UInt256) : List UInt256 :=
  [sv, ov, 0, P7, M, m7, P, m8]

def selectorState (input : ByteArray) (sv ov : UInt256) : State :=
  stS input 255 (returnRest sv ov)

def hopState (input : ByteArray) (sv ov : UInt256) : State :=
  stS input 5284 (returnRest sv ov)

def digestEntryState (input : ByteArray) (sv ov : UInt256) : State :=
  stS input 5297 (returnRest sv ov)

def storedState (input : ByteArray) (sv ov : UInt256) : State :=
  { stS input 5321 (returnRest sv ov) with
    memory := answerMemory
    activeWords := UInt256.ofNat 1 }

def sizedState (input : ByteArray) (sv ov : UInt256) : State :=
  { storedState input sv ov with
    pc := UInt256.ofNat 5322
    stack := UInt256.ofNat 32 :: returnRest sv ov }

def returnedState (input : ByteArray) (sv ov : UInt256) : State :=
  { storedState input sv ov with
    pc := UInt256.ofNat 5323
    halt := .Returned
    hReturn := MachineState.readPadded answerMemory 0 32 }

theorem digest128_eq : ShortPattern128Hop.digest128 = paddedDigestWord := by decide

@[simp] theorem paddedDigest_size : paddedDigest.size = 32 :=
  Patterned128Digest.paddedDigest_size

theorem wordBytes_eq_paddedDigest :
    Data.Bytes.natToBytesPadded ShortPattern128Hop.digest128.toNat 32 = paddedDigest := by
  rw [digest128_eq]
  exact Patterned128Digest.wordBytes_eq_paddedDigest

theorem answerMemory_read :
    MachineState.readPadded answerMemory 0 32 = paddedDigest := by
  unfold answerMemory storeWord
  have h := Memory.readPadded_writeBytes_same ByteArray.empty
    (Data.Bytes.natToBytesPadded ShortPattern128Hop.digest128.toNat 32) 0
  simpa only [YulEvmCompiler.BytesLemmas.natToBytesPadded_size,
    wordBytes_eq_paddedDigest, paddedDigest_size] using h

@[simp] theorem returnedState_hReturn (input : ByteArray) (sv ov : UInt256) :
    (returnedState input sv ov).hReturn = paddedDigest :=
  answerMemory_read

def selectorPath : List Located :=
  [opAt 160 .CALLDATASIZE, pushAt 161 1 129, opAt 162 .GT,
   pushAt 163 2 5284, opAt 164 .JUMPI]

@[simp] private theorem selectorPC160 :
    Artifact.submissionArtifact.instructionPC 160 = 255 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] private theorem selectorPC161 :
    Artifact.submissionArtifact.instructionPC 161 = 256 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] private theorem selectorPC162 :
    Artifact.submissionArtifact.instructionPC 162 = 258 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] private theorem selectorPC163 :
    Artifact.submissionArtifact.instructionPC 163 = 259 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] private theorem selectorPC164 :
    Artifact.submissionArtifact.instructionPC 164 = 262 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

@[simp] private theorem retPC4193 :
    Artifact.submissionArtifact.instructionPC 4193 = 5297 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] private theorem retPC4194 :
    Artifact.submissionArtifact.instructionPC 4194 = 5298 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] private theorem retPC4195 :
    Artifact.submissionArtifact.instructionPC 4195 = 5319 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] private theorem retPC4196 :
    Artifact.submissionArtifact.instructionPC 4196 = 5320 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] private theorem retPC4197 :
    Artifact.submissionArtifact.instructionPC 4197 = 5321 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] private theorem retPC4198 :
    Artifact.submissionArtifact.instructionPC 4198 = 5322 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] private theorem retPC4199 :
    Artifact.submissionArtifact.instructionPC 4199 = 5323 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

theorem run_selector (input : ByteArray) (sv ov : UInt256)
    (hsize : input.size = 128) :
    run selectorPath (selectorState input sv ov) =
      some (hopState input sv ov) := by
  change run selectorPath (stS input 255 (returnRest sv ov)) =
    some (stS input 5284 (returnRest sv ov))
  have hdest : Decode.isValidJumpDest submissionBytecode 5284 = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 4185 (by rfl)
  have htrue : UInt256.isTrue (UInt256.gt 129 (UInt256.ofNat input.size)) := by
    rw [hsize]; decide
  have h0 :
      Challenge.EvmProof.Stepper.runLocatedBlock
          [opAt 160 .CALLDATASIZE]
          (stS input 255 (returnRest sv ov)) =
        some (stS input 256 (UInt256.ofNat input.size :: returnRest sv ov)) := by
    exact blockOfS _
      (pcFactS input 160 255 _ (by norm_num) selectorPC160)
      (stepS_calldatasize input 255 (returnRest sv ov)
        (by simp [returnRest]) (by norm_num))
  have h1 :
      Challenge.EvmProof.Stepper.runLocatedBlock
          [pushAt 161 1 129]
          (stS input 256 (UInt256.ofNat input.size :: returnRest sv ov)) =
        some (stS input 258 (129 :: UInt256.ofNat input.size :: returnRest sv ov)) := by
    exact blockOfS _
      (pcFactS input 161 256 _ (by norm_num) selectorPC161)
      (stepS_push input 256 1 129
        (UInt256.ofNat input.size :: returnRest sv ov)
        (by simp [returnRest]) (by decide) (by decide) (by norm_num))
  have h2 :
      Challenge.EvmProof.Stepper.runLocatedBlock
          [opAt 162 .GT]
          (stS input 258 (129 :: UInt256.ofNat input.size :: returnRest sv ov)) =
        some (stS input 259
          (UInt256.gt 129 (UInt256.ofNat input.size) :: returnRest sv ov)) := by
    exact blockOfS _
      (pcFactS input 162 258 _ (by norm_num) selectorPC162)
      (stepS_gt input 258 129 (UInt256.ofNat input.size) (returnRest sv ov)
        (by simp [returnRest]) (by norm_num))
  have h3 :
      Challenge.EvmProof.Stepper.runLocatedBlock
          [pushAt 163 2 5284]
          (stS input 259
            (UInt256.gt 129 (UInt256.ofNat input.size) :: returnRest sv ov)) =
        some (stS input 262
          (5284 :: UInt256.gt 129 (UInt256.ofNat input.size) :: returnRest sv ov)) := by
    exact blockOfS _
      (pcFactS input 163 259 _ (by norm_num) selectorPC163)
      (stepS_push input 259 2 5284
        (UInt256.gt 129 (UInt256.ofNat input.size) :: returnRest sv ov)
        (by simp [returnRest]) (by decide) (by decide) (by norm_num))
  have h4 :
      Challenge.EvmProof.Stepper.runLocatedBlock
          [opAt 164 .JUMPI]
          (stS input 262
            (5284 :: UInt256.gt 129 (UInt256.ofNat input.size) :: returnRest sv ov)) =
        some (stS input 5284 (returnRest sv ov)) := by
    exact blockOfS _
      (pcFactS input 164 262 _ (by norm_num) selectorPC164)
      (stepS_jumpi_taken input 262 5284 5284
        (UInt256.gt 129 (UInt256.ofNat input.size)) (returnRest sv ov)
        (by simp [returnRest]) (by norm_num) rfl htrue hdest)
  have h01 := Challenge.EvmProof.Stepper.runLocatedBlock_append
    [opAt 160 .CALLDATASIZE] [pushAt 161 1 129]
    _ _ _ h0 (by rfl) h1
  have h012 := Challenge.EvmProof.Stepper.runLocatedBlock_append
    [opAt 160 .CALLDATASIZE, pushAt 161 1 129] [opAt 162 .GT]
    _ _ _ h01 (by rfl) h2
  have h0123 := Challenge.EvmProof.Stepper.runLocatedBlock_append
    [opAt 160 .CALLDATASIZE, pushAt 161 1 129, opAt 162 .GT]
    [pushAt 163 2 5284] _ _ _ h012 (by rfl) h3
  have h01234 :
      Challenge.EvmProof.Stepper.runLocatedBlock
          [opAt 160 .CALLDATASIZE, pushAt 161 1 129, opAt 162 .GT,
            pushAt 163 2 5284, opAt 164 .JUMPI]
          (stS input 255 (returnRest sv ov)) =
        some (stS input 5284 (returnRest sv ov)) := by
    exact Challenge.EvmProof.Stepper.runLocatedBlock_append
      [opAt 160 .CALLDATASIZE, pushAt 161 1 129, opAt 162 .GT,
        pushAt 163 2 5284] [opAt 164 .JUMPI] _ _ _ h0123 (by rfl) h4
  simpa only [selectorPath] using h01234

theorem run_store (input : ByteArray) (sv ov : UInt256) :
    run ShortPattern128Hop.ret128Path (digestEntryState input sv ov) =
      some (storedState input sv ov) := by
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp (config := { maxSteps := 400000 })
    [ShortPattern128Hop.ret128Path, DirectGuard.opAt, DirectGuard.pushAt, DirectGuard.wfOp,
      digestEntryState, storedState, returnRest, stS, initialState,
      answerMemory, storeWord, ShortPattern128Hop.digest128, State.activeWordsAfterUInt256,
      MachineState.activeWordsAfter, hzeroNat,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      retPC4193, retPC4194, retPC4195, retPC4196]

theorem run_finish (input : ByteArray) (sv ov : UInt256) :
    run ShortPattern128Hop.ret128Finish (sizedState input sv ov) =
      some (returnedState input sv ov) := by
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp (config := { maxSteps := 400000 })
    [ShortPattern128Hop.ret128Finish, DirectGuard.opAt, DirectGuard.pushAt, DirectGuard.wfOp,
      sizedState, storedState, returnRest, stS, initialState, returnedState,
      answerMemory, storeWord, ShortPattern128Hop.digest128, State.activeWordsAfterUInt256,
      MachineState.activeWordsAfter, hzeroNat,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      retPC4198, retPC4199]

def gasSteps_return (input : ByteArray) (sv ov : UInt256)
    (hsize : input.size = 128) :
    GasSteps (selectorState input sv ov) (returnedState input sv ov) := by
  have hlen : (returnRest sv ov).length < 1020 := by simp [returnRest]
  have gselect := sound selectorPath (run_selector input sv ov hsize)
  have ghop := ShortPattern128Hop.gasSteps_sel_128 input (returnRest sv ov) hlen hsize
  have gstore := sound ShortPattern128Hop.ret128Path (run_store input sv ov)
  have hd := Artifact.submissionArtifact.decodeAt_op_index 4197 .MSIZE
    (by rfl) (by decide) trivial
  have hp : (storedState input sv ov).pc.toNat =
      Artifact.submissionArtifact.instructionPC 4197 := by
    rw [retPC4197]; rfl
  have hop : (storedState input sv ov).decodedOp = some .MSIZE :=
    Artifact.submissionArtifact.state_decodedOp_of (storedState input sv ov) 4197
      (by rfl) hp .MSIZE none hd (by rfl)
  have gmraw := Msize.step hop
    (by simp [storedState, returnRest, stS, initialState])
    (by rfl) deployAddress_not_precompile
  have gm : GasSteps (storedState input sv ov) (sizedState input sv ov) := by
    simpa [storedState, sizedState, returnRest, stS, initialState,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat] using gmraw
  exact gselect.trans (ghop.trans (gstore.trans (gm.trans
    (sound ShortPattern128Hop.ret128Finish (run_finish input sv ov)))))

def gasSteps_finish_hit (input : ByteArray) (sv ov acc : UInt256)
    (hz : acc = 0) (hsize : input.size = 128) :
    GasSteps (stS input 250 [sv, ov, acc, P7, M, m7, P, m8])
      (returnedState input sv ov) := by
  subst acc
  exact (Prefix256Cleanup.gasSteps_hit input sv ov).trans
    (gasSteps_return input sv ov hsize)

end Challenge.Ripemd160.Submission.Proofs.Bytecode.ShortPattern128Finish
