import Challenge.Ripemd160.Submission.Proofs.Bytecode.Msize
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Trace
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
  { storedState input 5302 [] with
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

private theorem pc3772 : Artifact.submissionArtifact.instructionPC 4080 = 5205 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3773 : Artifact.submissionArtifact.instructionPC 4081 = 5206 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3774 : Artifact.submissionArtifact.instructionPC 4082 = 5208 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3775 : Artifact.submissionArtifact.instructionPC 4083 = 5209 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3776 : Artifact.submissionArtifact.instructionPC 4084 = 5212 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3783 : Artifact.submissionArtifact.instructionPC 4104 = 5276 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3784 : Artifact.submissionArtifact.instructionPC 4105 = 5277 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3785 : Artifact.submissionArtifact.instructionPC 4106 = 5298 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3786 : Artifact.submissionArtifact.instructionPC 4107 = 5299 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3787 : Artifact.submissionArtifact.instructionPC 4108 = 5300 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3788 : Artifact.submissionArtifact.instructionPC 4109 = 5301 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3789 : Artifact.submissionArtifact.instructionPC 4110 = 5302 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl

private theorem returnDest : Decode.isValidJumpDest submissionBytecode 5276 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 4104 (by rfl)

private def gasSteps_selector_test (input : ByteArray) :
    GasSteps (stS input 5205 [])
      (stS input 5212 [5276,
        UInt256.eq 64 (UInt256.ofNat input.size)]) := by
  have a := soundS (opAt 4080 .CALLDATASIZE)
    (blockOfS _ (pcFactS input 4080 5205 _ (by norm_num) pc3772)
      (stepS_calldatasize input 5205 [] (by simp) (by norm_num)))
  have b := soundS (pushAt 4081 1 64)
    (blockOfS _ (pcFactS input 4081 5206 _ (by norm_num) pc3773)
      (stepS_push input 5206 1 64 [UInt256.ofNat input.size]
        (by simp) (by decide) (by decide) (by norm_num)))
  have c := soundS (opAt 4082 .EQ)
    (blockOfS _ (pcFactS input 4082 5208 _ (by norm_num) pc3774)
      (stepS_eq input 5208 64 (UInt256.ofNat input.size) []
        (by simp) (by norm_num)))
  have d := soundS (pushAt 4083 2 5276)
    (blockOfS _ (pcFactS input 4083 5209 _ (by norm_num) pc3775)
      (stepS_push input 5209 2 5276
        [UInt256.eq 64 (UInt256.ofNat input.size)]
        (by simp) (by decide) (by decide) (by norm_num)))
  exact a.trans (b.trans (c.trans d))

def gasSteps_select64 (input : ByteArray) (hsize : input.size = 64) :
    GasSteps (stS input 5205 []) (stS input 5276 []) := by
  have hc : UInt256.isTrue
      (UInt256.eq 64 (UInt256.ofNat input.size)) := by
    rw [hsize]
    decide
  exact (gasSteps_selector_test input).trans
    (soundS (opAt 4084 .JUMPI)
      (blockOfS _ (pcFactS input 4084 5212 _ (by norm_num) pc3776)
        (stepS_jumpi_taken input 5212 5276 5276
          (UInt256.eq 64 (UInt256.ofNat input.size)) []
          (by simp) (by norm_num) rfl hc returnDest)))

def gasSteps_return (input : ByteArray) :
    GasSteps (stS input 5276 []) (returnedState input) := by
  have a := soundS (opAt 4104 .JUMPDEST)
    (blockOfS _ (pcFactS input 4104 5276 _ (by norm_num) pc3783)
      (stepS_jumpdest input 5276 [] (by simp) (by norm_num)))
  have b := soundS (pushAt 4105 20 paddedDigestWord)
    (blockOfS _ (pcFactS input 4105 5277 _ (by norm_num) pc3784)
      (stepS_push input 5277 20 paddedDigestWord []
        (by simp) (by decide) (by decide) (by norm_num)))
  have c := soundS (pushAt 4106 0 0)
    (blockOfS _ (pcFactS input 4106 5298 _ (by norm_num) pc3785)
      (stepS_push0 input 5298 [paddedDigestWord] (by simp) (by norm_num)))
  have hd : Stepper.runInstr (.op .MSTORE)
      (stS input 5299 [0, paddedDigestWord]) = some (storedState input 5300 []) := by
    rfl
  have d := soundS (opAt 4107 .MSTORE)
    (blockOfS _ (pcFactS input 4107 5299 _ (by norm_num) pc3786) hd)
  have hop : (storedState input 5300 []).decodedOp = some .MSIZE := by
    apply Trace.decodedOpAt (storedState input 5300 []) 4108 .MSIZE
    · rfl
    · change UInt256.ofNat 5300 =
        UInt256.ofNat (Artifact.submissionArtifact.instructionPC 4108)
      rw [pc3787]
    · rfl
    · rfl
    · trivial
    · rfl
  have e : GasSteps (storedState input 5300 []) (storedState input 5301 [32]) := by
    exact Msize.step hop (by change 0 < 1024; decide) (by rfl)
      deployAddress_not_precompile
  have hf : Stepper.runInstr (.push 0 0) (storedState input 5301 [32]) =
      some (storedState input 5302 [0, 32]) := by rfl
  have f := soundS (pushAt 4109 0 0)
    (blockOfS _
      (show (storedState input 5301 [32]).pc.toNat =
        Artifact.submissionArtifact.instructionPC 4109 from
          pcFactS input 4109 5301 [32] (by norm_num) pc3788) hf)
  have hg : Stepper.runInstr (.op .RETURN) (storedState input 5302 [0, 32]) =
      some (returnedState input) := by rfl
  have g := soundS (opAt 4110 .RETURN)
    (blockOfS _
      (show (storedState input 5302 [0, 32]).pc.toNat =
        Artifact.submissionArtifact.instructionPC 4110 from
          pcFactS input 4110 5302 [0, 32] (by norm_num) pc3789) hg)
  exact a.trans (b.trans (c.trans (d.trans (e.trans (f.trans g)))))

def gasSteps_finish_hit (input : ByteArray) (sv ov acc : UInt256)
    (hsize : input.size = 64) (heq : acc = 0) :
    GasSteps (stS input 5192 [sv, ov, acc, P7, M, m7, P, m8])
      (returnedState input) :=
  (Prefix256Finish.gasSteps_hit input sv ov acc heq).trans
    ((gasSteps_select64 input hsize).trans (gasSteps_return input))

#print axioms gasSteps_finish_hit

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix64Finish
