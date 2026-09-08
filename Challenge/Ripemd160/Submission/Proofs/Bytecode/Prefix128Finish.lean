import Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Finish
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix128Digest

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix128Finish

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open PatternedScan PatternedSwar

def paddedDigestWord : UInt256 := Prefix128Digest.paddedDigestWord

def answerMemory : ByteArray :=
  storeWord ByteArray.empty 0 paddedDigestWord

def storedState (input : ByteArray) (pc : Nat) (stk : List UInt256) : State :=
  { stS input pc stk with memory := answerMemory, activeWords := UInt256.ofNat 1 }

def returnedState (input : ByteArray) : State :=
  { storedState input 5334 [] with
    halt := .Returned
    hReturn := MachineState.readPadded answerMemory 0 32 }

theorem answerMemory_read :
    MachineState.readPadded answerMemory 0 32 = Prefix128Digest.paddedDigest := by
  unfold answerMemory storeWord
  have h := Memory.readPadded_writeBytes_same ByteArray.empty
    (Data.Bytes.natToBytesPadded paddedDigestWord.toNat 32) 0
  simpa only [YulEvmCompiler.BytesLemmas.natToBytesPadded_size,
    paddedDigestWord, Prefix128Digest.wordBytes_eq_paddedDigest,
    Prefix128Digest.paddedDigest_size] using h

@[simp] theorem returnedState_hReturn (input : ByteArray) :
    (returnedState input).hReturn = Prefix128Digest.paddedDigest := answerMemory_read

@[simp] theorem returnedState_hReturn_size (input : ByteArray) :
    (returnedState input).hReturn.size = 32 := by
  rw [returnedState_hReturn, Prefix128Digest.paddedDigest_size]

private theorem pc3772 : Artifact.submissionArtifact.instructionPC 4550 = 5272 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3773 : Artifact.submissionArtifact.instructionPC 4551 = 5273 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3774 : Artifact.submissionArtifact.instructionPC 4552 = 5275 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3775 : Artifact.submissionArtifact.instructionPC 4553 = 5276 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3776 : Artifact.submissionArtifact.instructionPC 4554 = 5279 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3783 : Artifact.submissionArtifact.instructionPC 4561 = 5307 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3784 : Artifact.submissionArtifact.instructionPC 4562 = 5308 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3785 : Artifact.submissionArtifact.instructionPC 4563 = 5329 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3786 : Artifact.submissionArtifact.instructionPC 4564 = 5330 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3787 : Artifact.submissionArtifact.instructionPC 4565 = 5331 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3788 : Artifact.submissionArtifact.instructionPC 4566 = 5333 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3789 : Artifact.submissionArtifact.instructionPC 4567 = 5334 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl

private theorem returnDest : Decode.isValidJumpDest submissionBytecode 5307 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 4561 (by rfl)

private def gasSteps_selector_test (input : ByteArray) :
    GasSteps (stS input 5272 [])
      (stS input 5279 [5307,
        UInt256.eq 128 (UInt256.ofNat input.size)]) := by
  have a := soundS (opAt 4550 .CALLDATASIZE)
    (blockOfS _ (pcFactS input 4550 5272 _ (by norm_num) pc3772)
      (stepS_calldatasize input 5272 [] (by simp) (by norm_num)))
  have b := soundS (pushAt 4551 1 128)
    (blockOfS _ (pcFactS input 4551 5273 _ (by norm_num) pc3773)
      (stepS_push input 5273 1 128 [UInt256.ofNat input.size]
        (by simp) (by decide) (by decide) (by norm_num)))
  have c := soundS (opAt 4552 .EQ)
    (blockOfS _ (pcFactS input 4552 5275 _ (by norm_num) pc3774)
      (stepS_eq input 5275 128 (UInt256.ofNat input.size) []
        (by simp) (by norm_num)))
  have d := soundS (pushAt 4553 2 5307)
    (blockOfS _ (pcFactS input 4553 5276 _ (by norm_num) pc3775)
      (stepS_push input 5276 2 5307
        [UInt256.eq 128 (UInt256.ofNat input.size)]
        (by simp) (by decide) (by decide) (by norm_num)))
  exact a.trans (b.trans (c.trans d))

def gasSteps_select128 (input : ByteArray) (hsize : input.size = 128) :
    GasSteps (stS input 5272 []) (stS input 5307 []) := by
  have hc : UInt256.isTrue
      (UInt256.eq 128 (UInt256.ofNat input.size)) := by
    rw [hsize]
    decide
  exact (gasSteps_selector_test input).trans
    (soundS (opAt 4554 .JUMPI)
      (blockOfS _ (pcFactS input 4554 5279 _ (by norm_num) pc3776)
        (stepS_jumpi_taken input 5279 5307 5307
          (UInt256.eq 128 (UInt256.ofNat input.size)) []
          (by simp) (by norm_num) rfl hc returnDest)))

def gasSteps_return (input : ByteArray) :
    GasSteps (stS input 5307 []) (returnedState input) := by
  have a := soundS (opAt 4561 .JUMPDEST)
    (blockOfS _ (pcFactS input 4561 5307 _ (by norm_num) pc3783)
      (stepS_jumpdest input 5307 [] (by simp) (by norm_num)))
  have b := soundS (pushAt 4562 20 paddedDigestWord)
    (blockOfS _ (pcFactS input 4562 5308 _ (by norm_num) pc3784)
      (stepS_push input 5308 20 paddedDigestWord []
        (by simp) (by decide) (by decide) (by norm_num)))
  have c := soundS (pushAt 4563 0 0)
    (blockOfS _ (pcFactS input 4563 5329 _ (by norm_num) pc3785)
      (stepS_push0 input 5329 [paddedDigestWord] (by simp) (by norm_num)))
  have hd : Stepper.runInstr (.op .MSTORE)
      (stS input 5330 [0, paddedDigestWord]) = some (storedState input 5331 []) := by
    rfl
  have d := soundS (opAt 4564 .MSTORE)
    (blockOfS _ (pcFactS input 4564 5330 _ (by norm_num) pc3786) hd)
  have he : Stepper.runInstr (.push 1 32) (storedState input 5331 []) =
      some (storedState input 5333 [32]) := by rfl
  have e := soundS (pushAt 4565 1 32)
    (blockOfS _
      (show (storedState input 5331 []).pc.toNat =
        Artifact.submissionArtifact.instructionPC 4565 from
          pcFactS input 4565 5331 [] (by norm_num) pc3787) he)
  have hf : Stepper.runInstr (.push 0 0) (storedState input 5333 [32]) =
      some (storedState input 5334 [0, 32]) := by rfl
  have f := soundS (pushAt 4566 0 0)
    (blockOfS _
      (show (storedState input 5333 [32]).pc.toNat =
        Artifact.submissionArtifact.instructionPC 4566 from
          pcFactS input 4566 5333 [32] (by norm_num) pc3788) hf)
  have hg : Stepper.runInstr (.op .RETURN) (storedState input 5334 [0, 32]) =
      some (returnedState input) := by rfl
  have g := soundS (opAt 4567 .RETURN)
    (blockOfS _
      (show (storedState input 5334 [0, 32]).pc.toNat =
        Artifact.submissionArtifact.instructionPC 4567 from
          pcFactS input 4567 5334 [0, 32] (by norm_num) pc3789) hg)
  exact a.trans (b.trans (c.trans (d.trans (e.trans (f.trans g)))))

def gasSteps_finish_hit (input : ByteArray) (sv ov acc : UInt256)
    (hsize : input.size = 128) (heq : acc = 0) :
    GasSteps (stS input 5251 [sv, ov, acc, P7, M, m7, P, m8])
      (returnedState input) :=
  (Prefix256Finish.gasSteps_hit input sv ov acc heq).trans
    ((Prefix256Finish.gasSteps_skip64 input (Or.inl hsize)).trans
      ((gasSteps_select128 input hsize).trans (gasSteps_return input)))

#print axioms gasSteps_finish_hit

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix128Finish
