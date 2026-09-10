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

def storedState (input : ByteArray) (word : UInt256) (rest : List UInt256) : State :=
  { stS input 348 rest with memory := answerMemory word, activeWords := UInt256.ofNat 1 }

def sizedState (input : ByteArray) (word : UInt256) (rest : List UInt256) : State :=
  { storedState input word rest with pc := UInt256.ofNat 349, stack := UInt256.ofNat 32 :: rest }

def returnedState (input : ByteArray) (word : UInt256) (rest : List UInt256) : State :=
  { storedState input word rest with pc := UInt256.ofNat 350, halt := .Returned, hReturn := MachineState.readPadded (answerMemory word) 0 32 }

def storePath : List Located := [pushAt 182 0 0, opAt 183 .MSTORE]
def finishPath : List Located := [pushAt 185 0 0, opAt 186 .RETURN]

theorem run_store (input : ByteArray) (word : UInt256) (rest : List UInt256) (hlen : rest.length < 1020) :
    run storePath (stS input 346 (word :: rest)) = some (storedState input word rest) := by
  have hcap0 : rest.length < 1024 := by omega
  have hcap1 : rest.length + 1 < 1024 := by omega
  have hcap2 : rest.length + 1 + 1 < 1024 := by omega
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp [storePath, opAt, pushAt, wfOp, stS, initialState, storedState,
    answerMemory, storeWord, MachineState.mstore, State.activeWordsAfterUInt256,
    MachineState.activeWordsAfter, hzeroNat, hcap0, hcap1, hcap2, Stepper.runLocatedBlock,
    Stepper.runLocated, Stepper.runInstr, Word.literal_eq_ofNat,
    Word.succ_ofNat_mod, Word.ofNat_add_mod, Word.word_toNat_ofNat]

theorem run_finish (input : ByteArray) (word : UInt256) (rest : List UInt256) (hlen : rest.length < 1020) :
    run finishPath (sizedState input word rest) = some (returnedState input word rest) := by
  have hcap0 : rest.length < 1024 := by omega
  have hcap1 : rest.length + 1 < 1024 := by omega
  have hcap2 : rest.length + 1 + 1 < 1024 := by omega
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp [finishPath, opAt, pushAt, wfOp, stS, initialState, sizedState,
    storedState, returnedState, State.activeWordsAfterUInt256,
    MachineState.activeWordsAfter, hzeroNat, hcap0, hcap1, hcap2, Stepper.runLocatedBlock,
    Stepper.runLocated, Stepper.runInstr, Word.literal_eq_ofNat,
    Word.succ_ofNat_mod, Word.ofNat_add_mod, Word.word_toNat_ofNat]

def gasSteps_return (input : ByteArray) (word : UInt256) (rest : List UInt256) (hlen : rest.length < 1020) :
    GasSteps (stS input 346 (word :: rest)) (returnedState input word rest) := by
  have gs := sound storePath (run_store input word rest hlen)
  have hd := Artifact.submissionArtifact.decodeAt_op_index 184 .MSIZE
    (by rfl) (by decide) trivial
  have hp : (storedState input word rest).pc.toNat =
      Artifact.submissionArtifact.instructionPC 184 := by
    rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]
    rfl
  have hop : (storedState input word rest).decodedOp = some .MSIZE :=
    Artifact.submissionArtifact.state_decodedOp_of (storedState input word rest) 184
      (by rfl) hp .MSIZE none hd (by rfl)
  have gmraw := Msize.step hop (by simp only [storedState, stS, initialState]; omega) (by rfl)
    deployAddress_not_precompile
  have gm : GasSteps (storedState input word rest) (sizedState input word rest) := by
    simpa [storedState, sizedState, stS, initialState,
      Word.succ_ofNat_mod, Word.word_toNat_ofNat] using gmraw
  exact gs.trans (gm.trans (sound finishPath (run_finish input word rest hlen)))

end Challenge.Ripemd160.Submission.Proofs.Bytecode.DigestReturn
