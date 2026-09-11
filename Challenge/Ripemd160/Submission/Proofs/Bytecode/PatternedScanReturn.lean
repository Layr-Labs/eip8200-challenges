import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScanTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Msize

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open PatternedInputData PatternedDigest PatternedGuardSpec

@[simp] private theorem selectPC265 : Artifact.submissionArtifact.instructionPC 170 = 261 := rfl
@[simp] private theorem selectPC270 : Artifact.submissionArtifact.instructionPC 175 = 288 := rfl
@[simp] private theorem selectPC271 : Artifact.submissionArtifact.instructionPC 176 = 289 := rfl
@[simp] private theorem selectPC272 : Artifact.submissionArtifact.instructionPC 177 = 292 := rfl
@[simp] private theorem selectPC273 : Artifact.submissionArtifact.instructionPC 178 = 293 := rfl
@[simp] private theorem selectPC274 : Artifact.submissionArtifact.instructionPC 179 = 314 := rfl
@[simp] private theorem selectPC275 : Artifact.submissionArtifact.instructionPC 180 = 315 := rfl

def selectorPath : List Located :=
  [opAt 164 .CALLDATASIZE,
   pushAt 165 1 129,
   opAt 166 .GT,
   pushAt 167 2 5088,
   opAt 168 .JUMPI]

@[simp] private theorem selectorPC166 :
    Artifact.submissionArtifact.instructionPC 164 = 252 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem selectorPC167 :
    Artifact.submissionArtifact.instructionPC 165 = 253 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem selectorPC168 :
    Artifact.submissionArtifact.instructionPC 166 = 255 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem selectorPC169 :
    Artifact.submissionArtifact.instructionPC 167 = 256 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem selectorPC170 :
    Artifact.submissionArtifact.instructionPC 168 = 259 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def storePath : List Located :=
  selectorPath ++ [opAt 169 .CALLDATASIZE,
   opAt 170 (.Dup ⟨0, by decide⟩),
   pushAt 171 2 376,
   opAt 172 .EQ,
   pushAt 173 20 644824770394507154413287103057882351908521126009,
   opAt 174 .MUL,
   opAt 175 (.Swap ⟨0, by decide⟩),
   pushAt 176 2 256,
   opAt 177 .EQ,
   pushAt 178 20 370937159678419008737987698595703314930111331934,
   opAt 179 .MUL,
   opAt 180 .XOR,
   pushAt 181 20 766350606435067737561421097975693824639675460820,
   opAt 182 .XOR,
   pushAt 183 0 0,
   opAt 184 .MSTORE]

def finishPath : List Located := [pushAt 186 0 0, opAt 187 .RETURN]

def storedState (input : ByteArray) : State :=
  { atPC input 340 with stack := hitRest, memory := answerMemory, activeWords := UInt256.ofNat 1 }

def sizedState (input : ByteArray) : State :=
  { storedState input with pc := UInt256.ofNat 341, stack := UInt256.ofNat 32 :: hitRest }

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
  have hd := Artifact.submissionArtifact.decodeAt_op_index 185 .MSIZE
    (by rfl) (by decide) trivial
  have hp : (storedState patternedInput).pc.toNat =
      Artifact.submissionArtifact.instructionPC 185 := by
    rw [pc2986]; rfl
  have hop : (storedState patternedInput).decodedOp = some .MSIZE :=
    Artifact.submissionArtifact.state_decodedOp_of (storedState patternedInput) 185
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
