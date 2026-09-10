import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScanTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Msize

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open PatternedInputData PatternedDigest PatternedGuardSpec

@[simp] private theorem selectPC265 : Artifact.submissionArtifact.instructionPC 171 = 269 := rfl
@[simp] private theorem selectPC270 : Artifact.submissionArtifact.instructionPC 176 = 296 := rfl
@[simp] private theorem selectPC271 : Artifact.submissionArtifact.instructionPC 177 = 297 := rfl
@[simp] private theorem selectPC272 : Artifact.submissionArtifact.instructionPC 178 = 300 := rfl
@[simp] private theorem selectPC273 : Artifact.submissionArtifact.instructionPC 179 = 301 := rfl
@[simp] private theorem selectPC274 : Artifact.submissionArtifact.instructionPC 180 = 322 := rfl
@[simp] private theorem selectPC275 : Artifact.submissionArtifact.instructionPC 181 = 323 := rfl

def selectorPath : List Located :=
  [opAt 165 .CALLDATASIZE,
   pushAt 166 1 129,
   opAt 167 .GT,
   pushAt 168 2 5202,
   opAt 169 .JUMPI]

@[simp] private theorem selectorPC166 :
    Artifact.submissionArtifact.instructionPC 165 = 260 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem selectorPC167 :
    Artifact.submissionArtifact.instructionPC 166 = 261 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem selectorPC168 :
    Artifact.submissionArtifact.instructionPC 167 = 263 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem selectorPC169 :
    Artifact.submissionArtifact.instructionPC 168 = 264 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem selectorPC170 :
    Artifact.submissionArtifact.instructionPC 169 = 267 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def storePath : List Located :=
  selectorPath ++ [opAt 170 .CALLDATASIZE,
   opAt 171 (.Dup ⟨0, by decide⟩),
   pushAt 172 2 376,
   opAt 173 .EQ,
   pushAt 174 20 644824770394507154413287103057882351908521126009,
   opAt 175 .MUL,
   opAt 176 (.Swap ⟨0, by decide⟩),
   pushAt 177 2 256,
   opAt 178 .EQ,
   pushAt 179 20 370937159678419008737987698595703314930111331934,
   opAt 180 .MUL,
   opAt 181 .XOR,
   pushAt 182 20 766350606435067737561421097975693824639675460820,
   opAt 183 .XOR,
   pushAt 184 0 0,
   opAt 185 .MSTORE]

def finishPath : List Located := [pushAt 187 0 0, opAt 188 .RETURN]

def storedState (input : ByteArray) : State :=
  { atPC input 348 with stack := hitRest, memory := answerMemory, activeWords := UInt256.ofNat 1 }

def sizedState (input : ByteArray) : State :=
  { storedState input with pc := UInt256.ofNat 349, stack := UInt256.ofNat 32 :: hitRest }

/-- Both size flags are zero for a 1000-byte input. -/
theorem selector_value :
    (UInt256.ofNat 766350606435067737561421097975693824639675460820).xor
      (((UInt256.ofNat 370937159678419008737987698595703314930111331934).mul
          ((UInt256.ofNat 256).eq (UInt256.ofNat 1000))).xor
        ((UInt256.ofNat 644824770394507154413287103057882351908521126009).mul
          ((UInt256.ofNat 376).eq (UInt256.ofNat 1000)))) = paddedDigestWord := by
  decide

theorem run_store :
    run storePath (hitState patternedInput) = some (storedState patternedInput) := by
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  have hselector :
      (UInt256.ofNat 766350606435067737561421097975693824639675460820).xor
        (((UInt256.ofNat 370937159678419008737987698595703314930111331934).mul
            (UInt256.ofNat 0)).xor
          ((UInt256.ofNat 644824770394507154413287103057882351908521126009).mul
            (UInt256.ofNat 0))) = paddedDigestWord := by
    decide
  simp (config := { maxSteps := 400000 })
    [storePath, selectorPath, List.exchange, opAt, pushAt, wfOp, hitState, atPC, storedState, hitRest, frame,
    answerMemory, storeWord, paddedDigestWord, patternedInput_size, selector_value, hselector,
    UInt256.eq, UInt256.gt, UInt256.isTrue,
    MachineState.mstore, State.activeWordsAfterUInt256,
    MachineState.activeWordsAfter, hzeroNat,
    Challenge.EvmProof.Stepper.runLocatedBlock, Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr, initialState,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod, Challenge.EvmProof.Word.word_toNat_ofNat]

theorem run_finish :
    run finishPath (sizedState patternedInput) = some (returnedState patternedInput) := by
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp (config := { maxSteps := 400000 })
    [finishPath, opAt, pushAt, wfOp, sizedState, storedState, hitRest, frame, atPC, returnedState,
    answerMemory, storeWord, paddedDigestWord,
    State.activeWordsAfterUInt256, MachineState.activeWordsAfter, hzeroNat,
    Challenge.EvmProof.Stepper.runLocatedBlock, Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr, initialState,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod, Challenge.EvmProof.Word.word_toNat_ofNat]

def gasSteps_return :
    GasSteps (hitState patternedInput) (returnedState patternedInput) := by
  have gs := sound storePath run_store
  have hd := Artifact.submissionArtifact.decodeAt_op_index 186 .MSIZE
    (by rfl) (by decide) trivial
  have hp : (storedState patternedInput).pc.toNat =
      Artifact.submissionArtifact.instructionPC 186 := by
    rw [pc2986]; rfl
  have hop : (storedState patternedInput).decodedOp = some .MSIZE :=
    Artifact.submissionArtifact.state_decodedOp_of (storedState patternedInput) 186
      (by rfl) hp .MSIZE none hd (by rfl)
  have gmraw := Msize.step hop (by simp [storedState, hitRest, frame, atPC, initialState]) (by rfl)
    deployAddress_not_precompile
  have gm : GasSteps (storedState patternedInput) (sizedState patternedInput) := by
    simpa [storedState, hitRest, frame, sizedState, atPC, initialState,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat] using gmraw
  exact gs.trans (gm.trans (sound finishPath run_finish))

theorem answerMemory_read :
    MachineState.readPadded answerMemory 0 32 = paddedDigest := by
  unfold answerMemory storeWord
  have h := Memory.readPadded_writeBytes_same ByteArray.empty
    (Data.Bytes.natToBytesPadded paddedDigestWord.toNat 32) 0
  simpa only [YulEvmCompiler.BytesLemmas.natToBytesPadded_size,
    wordBytes_eq_paddedDigest, paddedDigest_size] using h

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan
