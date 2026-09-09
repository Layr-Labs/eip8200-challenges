import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedStep
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Msize

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.DigestReturn

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open PatternedScan

def answerMemory (word : UInt256) : ByteArray := storeWord ByteArray.empty 0 word

def storedState (input : ByteArray) (word : UInt256) : State :=
  { stS input 458 [] with memory := answerMemory word, activeWords := UInt256.ofNat 1 }

def sizedState (input : ByteArray) (word : UInt256) : State :=
  { storedState input word with pc := UInt256.ofNat 459, stack := [UInt256.ofNat 32] }

def returnedState (input : ByteArray) (word : UInt256) : State :=
  { storedState input word with pc := UInt256.ofNat 460, halt := .Returned, hReturn := MachineState.readPadded (answerMemory word) 0 32 }

def storePath : List Located := [pushAt 255 0 0, opAt 256 .MSTORE]
def finishPath : List Located := [pushAt 258 0 0, opAt 259 .RETURN]

theorem run_store (input : ByteArray) (word : UInt256) :
    run storePath (stS input 456 [word]) = some (storedState input word) := by
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp [storePath, opAt, pushAt, wfOp, stS, initialState, storedState,
    answerMemory, storeWord, MachineState.mstore, State.activeWordsAfterUInt256,
    MachineState.activeWordsAfter, hzeroNat, Stepper.runLocatedBlock,
    Stepper.runLocated, Stepper.runInstr, Word.literal_eq_ofNat,
    Word.succ_ofNat_mod, Word.ofNat_add_mod, Word.word_toNat_ofNat]

theorem run_finish (input : ByteArray) (word : UInt256) :
    run finishPath (sizedState input word) = some (returnedState input word) := by
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp [finishPath, opAt, pushAt, wfOp, stS, initialState, sizedState,
    storedState, returnedState, State.activeWordsAfterUInt256,
    MachineState.activeWordsAfter, hzeroNat, Stepper.runLocatedBlock,
    Stepper.runLocated, Stepper.runInstr, Word.literal_eq_ofNat,
    Word.succ_ofNat_mod, Word.ofNat_add_mod, Word.word_toNat_ofNat]

def gasSteps_return (input : ByteArray) (word : UInt256) :
    GasSteps (stS input 456 [word]) (returnedState input word) := by
  have gs := sound storePath (run_store input word)
  have hd := Artifact.submissionArtifact.decodeAt_op_index 257 .MSIZE
    (by rfl) (by decide) trivial
  have hp : (storedState input word).pc.toNat =
      Artifact.submissionArtifact.instructionPC 257 := by
    rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]
    rfl
  have hop : (storedState input word).decodedOp = some .MSIZE :=
    Artifact.submissionArtifact.state_decodedOp_of (storedState input word) 257
      (by rfl) hp .MSIZE none hd (by rfl)
  have gmraw := Msize.step hop (by simp [storedState, stS, initialState]) (by rfl)
    deployAddress_not_precompile
  have gm : GasSteps (storedState input word) (sizedState input word) := by
    simpa [storedState, sizedState, stS, initialState,
      Word.succ_ofNat_mod, Word.word_toNat_ofNat] using gmraw
  exact gs.trans (gm.trans (sound finishPath (run_finish input word)))

end Challenge.Ripemd160.Submission.Proofs.Bytecode.DigestReturn
