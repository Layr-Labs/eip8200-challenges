import Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Finish
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix64Digest

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix64Finish

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open PatternedScan PatternedSwar

def paddedDigestWord : UInt256 := Prefix64Digest.paddedDigestWord

def answerMemory : ByteArray :=
  storeWord ByteArray.empty 0 paddedDigestWord

def storedState (input : ByteArray) (pc : Nat) (stk : List UInt256) : State :=
  { stS input pc stk with memory := answerMemory, activeWords := UInt256.ofNat 1 }

def returnedState (input : ByteArray) : State :=
  { storedState input 5362 [] with
    halt := .Returned
    hReturn := MachineState.readPadded answerMemory 0 32 }

theorem answerMemory_read :
    MachineState.readPadded answerMemory 0 32 = Prefix64Digest.paddedDigest := by
  unfold answerMemory storeWord
  have h := Memory.readPadded_writeBytes_same ByteArray.empty
    (Data.Bytes.natToBytesPadded paddedDigestWord.toNat 32) 0
  simpa only [YulEvmCompiler.BytesLemmas.natToBytesPadded_size,
    paddedDigestWord, Prefix64Digest.wordBytes_eq_paddedDigest,
    Prefix64Digest.paddedDigest_size] using h

@[simp] theorem returnedState_hReturn (input : ByteArray) :
    (returnedState input).hReturn = Prefix64Digest.paddedDigest := answerMemory_read

@[simp] theorem returnedState_hReturn_size (input : ByteArray) :
    (returnedState input).hReturn.size = 32 := by
  rw [returnedState_hReturn, Prefix64Digest.paddedDigest_size]

private theorem pc3772 : Artifact.submissionArtifact.instructionPC 4545 = 5264 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3773 : Artifact.submissionArtifact.instructionPC 4546 = 5265 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3774 : Artifact.submissionArtifact.instructionPC 4547 = 5267 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3775 : Artifact.submissionArtifact.instructionPC 4548 = 5268 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3776 : Artifact.submissionArtifact.instructionPC 4549 = 5271 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3783 : Artifact.submissionArtifact.instructionPC 4568 = 5335 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3784 : Artifact.submissionArtifact.instructionPC 4569 = 5336 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3785 : Artifact.submissionArtifact.instructionPC 4570 = 5357 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3786 : Artifact.submissionArtifact.instructionPC 4571 = 5358 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3787 : Artifact.submissionArtifact.instructionPC 4572 = 5359 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3788 : Artifact.submissionArtifact.instructionPC 4573 = 5361 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3789 : Artifact.submissionArtifact.instructionPC 4574 = 5362 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl

private theorem returnDest : Decode.isValidJumpDest submissionBytecode 5335 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 4568 (by rfl)

private def gasSteps_selector_test (input : ByteArray) :
    GasSteps (stS input 5264 [])
      (stS input 5271 [5335,
        UInt256.eq 64 (UInt256.ofNat input.size)]) := by
  have a := soundS (opAt 4545 .CALLDATASIZE)
    (blockOfS _ (pcFactS input 4545 5264 _ (by norm_num) pc3772)
      (stepS_calldatasize input 5264 [] (by simp) (by norm_num)))
  have b := soundS (pushAt 4546 1 64)
    (blockOfS _ (pcFactS input 4546 5265 _ (by norm_num) pc3773)
      (stepS_push input 5265 1 64 [UInt256.ofNat input.size]
        (by simp) (by decide) (by decide) (by norm_num)))
  have c := soundS (opAt 4547 .EQ)
    (blockOfS _ (pcFactS input 4547 5267 _ (by norm_num) pc3774)
      (stepS_eq input 5267 64 (UInt256.ofNat input.size) []
        (by simp) (by norm_num)))
  have d := soundS (pushAt 4548 2 5335)
    (blockOfS _ (pcFactS input 4548 5268 _ (by norm_num) pc3775)
      (stepS_push input 5268 2 5335
        [UInt256.eq 64 (UInt256.ofNat input.size)]
        (by simp) (by decide) (by decide) (by norm_num)))
  exact a.trans (b.trans (c.trans d))

def gasSteps_select64 (input : ByteArray) (hsize : input.size = 64) :
    GasSteps (stS input 5264 []) (stS input 5335 []) := by
  have hc : UInt256.isTrue
      (UInt256.eq 64 (UInt256.ofNat input.size)) := by
    rw [hsize]
    decide
  exact (gasSteps_selector_test input).trans
    (soundS (opAt 4549 .JUMPI)
      (blockOfS _ (pcFactS input 4549 5271 _ (by norm_num) pc3776)
        (stepS_jumpi_taken input 5271 5335 5335
          (UInt256.eq 64 (UInt256.ofNat input.size)) []
          (by simp) (by norm_num) rfl hc returnDest)))

def gasSteps_return (input : ByteArray) :
    GasSteps (stS input 5335 []) (returnedState input) := by
  have a := soundS (opAt 4568 .JUMPDEST)
    (blockOfS _ (pcFactS input 4568 5335 _ (by norm_num) pc3783)
      (stepS_jumpdest input 5335 [] (by simp) (by norm_num)))
  have b := soundS (pushAt 4569 20 paddedDigestWord)
    (blockOfS _ (pcFactS input 4569 5336 _ (by norm_num) pc3784)
      (stepS_push input 5336 20 paddedDigestWord []
        (by simp) (by decide) (by decide) (by norm_num)))
  have c := soundS (pushAt 4570 0 0)
    (blockOfS _ (pcFactS input 4570 5357 _ (by norm_num) pc3785)
      (stepS_push0 input 5357 [paddedDigestWord] (by simp) (by norm_num)))
  have hd : Stepper.runInstr (.op .MSTORE)
      (stS input 5358 [0, paddedDigestWord]) = some (storedState input 5359 []) := by
    rfl
  have d := soundS (opAt 4571 .MSTORE)
    (blockOfS _ (pcFactS input 4571 5358 _ (by norm_num) pc3786) hd)
  have he : Stepper.runInstr (.push 1 32) (storedState input 5359 []) =
      some (storedState input 5361 [32]) := by rfl
  have e := soundS (pushAt 4572 1 32)
    (blockOfS _
      (show (storedState input 5359 []).pc.toNat =
        Artifact.submissionArtifact.instructionPC 4572 from
          pcFactS input 4572 5359 [] (by norm_num) pc3787) he)
  have hf : Stepper.runInstr (.push 0 0) (storedState input 5361 [32]) =
      some (storedState input 5362 [0, 32]) := by rfl
  have f := soundS (pushAt 4573 0 0)
    (blockOfS _
      (show (storedState input 5361 [32]).pc.toNat =
        Artifact.submissionArtifact.instructionPC 4573 from
          pcFactS input 4573 5361 [32] (by norm_num) pc3788) hf)
  have hg : Stepper.runInstr (.op .RETURN) (storedState input 5362 [0, 32]) =
      some (returnedState input) := by rfl
  have g := soundS (opAt 4574 .RETURN)
    (blockOfS _
      (show (storedState input 5362 [0, 32]).pc.toNat =
        Artifact.submissionArtifact.instructionPC 4574 from
          pcFactS input 4574 5362 [0, 32] (by norm_num) pc3789) hg)
  exact a.trans (b.trans (c.trans (d.trans (e.trans (f.trans g)))))

def gasSteps_finish_hit (input : ByteArray) (sv ov acc : UInt256)
    (hsize : input.size = 64) (heq : acc = 0) :
    GasSteps (stS input 5251 [sv, ov, acc, P7, M, m7, P, m8])
      (returnedState input) :=
  (Prefix256Finish.gasSteps_hit input sv ov acc heq).trans
    ((gasSteps_select64 input hsize).trans (gasSteps_return input))

#print axioms gasSteps_finish_hit

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix64Finish
