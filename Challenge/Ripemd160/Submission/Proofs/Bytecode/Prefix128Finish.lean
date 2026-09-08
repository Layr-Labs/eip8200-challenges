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
  { storedState input 5275 [] with
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

private theorem pc3772 : Artifact.submissionArtifact.instructionPC 4085 = 5213 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3773 : Artifact.submissionArtifact.instructionPC 4086 = 5214 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3774 : Artifact.submissionArtifact.instructionPC 4087 = 5216 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3775 : Artifact.submissionArtifact.instructionPC 4088 = 5217 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3776 : Artifact.submissionArtifact.instructionPC 4089 = 5220 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3783 : Artifact.submissionArtifact.instructionPC 4097 = 5248 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3784 : Artifact.submissionArtifact.instructionPC 4098 = 5249 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3785 : Artifact.submissionArtifact.instructionPC 4099 = 5270 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3786 : Artifact.submissionArtifact.instructionPC 4100 = 5271 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3787 : Artifact.submissionArtifact.instructionPC 4101 = 5272 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3788 : Artifact.submissionArtifact.instructionPC 4102 = 5274 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3789 : Artifact.submissionArtifact.instructionPC 4103 = 5275 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl

private theorem returnDest : Decode.isValidJumpDest submissionBytecode 5248 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 4097 (by rfl)

private def gasSteps_selector_test (input : ByteArray) :
    GasSteps (stS input 5213 [])
      (stS input 5220 [5248,
        UInt256.eq 128 (UInt256.ofNat input.size)]) := by
  have a := soundS (opAt 4085 .CALLDATASIZE)
    (blockOfS _ (pcFactS input 4085 5213 _ (by norm_num) pc3772)
      (stepS_calldatasize input 5213 [] (by simp) (by norm_num)))
  have b := soundS (pushAt 4086 1 128)
    (blockOfS _ (pcFactS input 4086 5214 _ (by norm_num) pc3773)
      (stepS_push input 5214 1 128 [UInt256.ofNat input.size]
        (by simp) (by decide) (by decide) (by norm_num)))
  have c := soundS (opAt 4087 .EQ)
    (blockOfS _ (pcFactS input 4087 5216 _ (by norm_num) pc3774)
      (stepS_eq input 5216 128 (UInt256.ofNat input.size) []
        (by simp) (by norm_num)))
  have d := soundS (pushAt 4088 2 5248)
    (blockOfS _ (pcFactS input 4088 5217 _ (by norm_num) pc3775)
      (stepS_push input 5217 2 5248
        [UInt256.eq 128 (UInt256.ofNat input.size)]
        (by simp) (by decide) (by decide) (by norm_num)))
  exact a.trans (b.trans (c.trans d))

def gasSteps_select128 (input : ByteArray) (hsize : input.size = 128) :
    GasSteps (stS input 5213 []) (stS input 5248 []) := by
  have hc : UInt256.isTrue
      (UInt256.eq 128 (UInt256.ofNat input.size)) := by
    rw [hsize]
    decide
  exact (gasSteps_selector_test input).trans
    (soundS (opAt 4089 .JUMPI)
      (blockOfS _ (pcFactS input 4089 5220 _ (by norm_num) pc3776)
        (stepS_jumpi_taken input 5220 5248 5248
          (UInt256.eq 128 (UInt256.ofNat input.size)) []
          (by simp) (by norm_num) rfl hc returnDest)))

def gasSteps_return (input : ByteArray) :
    GasSteps (stS input 5248 []) (returnedState input) := by
  have a := soundS (opAt 4097 .JUMPDEST)
    (blockOfS _ (pcFactS input 4097 5248 _ (by norm_num) pc3783)
      (stepS_jumpdest input 5248 [] (by simp) (by norm_num)))
  have b := soundS (pushAt 4098 20 paddedDigestWord)
    (blockOfS _ (pcFactS input 4098 5249 _ (by norm_num) pc3784)
      (stepS_push input 5249 20 paddedDigestWord []
        (by simp) (by decide) (by decide) (by norm_num)))
  have c := soundS (pushAt 4099 0 0)
    (blockOfS _ (pcFactS input 4099 5270 _ (by norm_num) pc3785)
      (stepS_push0 input 5270 [paddedDigestWord] (by simp) (by norm_num)))
  have hd : Stepper.runInstr (.op .MSTORE)
      (stS input 5271 [0, paddedDigestWord]) = some (storedState input 5272 []) := by
    rfl
  have d := soundS (opAt 4100 .MSTORE)
    (blockOfS _ (pcFactS input 4100 5271 _ (by norm_num) pc3786) hd)
  have he : Stepper.runInstr (.push 1 32) (storedState input 5272 []) =
      some (storedState input 5274 [32]) := by rfl
  have e := soundS (pushAt 4101 1 32)
    (blockOfS _
      (show (storedState input 5272 []).pc.toNat =
        Artifact.submissionArtifact.instructionPC 4101 from
          pcFactS input 4101 5272 [] (by norm_num) pc3787) he)
  have hf : Stepper.runInstr (.push 0 0) (storedState input 5274 [32]) =
      some (storedState input 5275 [0, 32]) := by rfl
  have f := soundS (pushAt 4102 0 0)
    (blockOfS _
      (show (storedState input 5274 [32]).pc.toNat =
        Artifact.submissionArtifact.instructionPC 4102 from
          pcFactS input 4102 5274 [32] (by norm_num) pc3788) hf)
  have hg : Stepper.runInstr (.op .RETURN) (storedState input 5275 [0, 32]) =
      some (returnedState input) := by rfl
  have g := soundS (opAt 4103 .RETURN)
    (blockOfS _
      (show (storedState input 5275 [0, 32]).pc.toNat =
        Artifact.submissionArtifact.instructionPC 4103 from
          pcFactS input 4103 5275 [0, 32] (by norm_num) pc3789) hg)
  exact a.trans (b.trans (c.trans (d.trans (e.trans (f.trans g)))))

def gasSteps_finish_hit (input : ByteArray) (sv ov acc : UInt256)
    (hsize : input.size = 128) (heq : acc = 0) :
    GasSteps (stS input 5192 [sv, ov, acc, P7, M, m7, P, m8])
      (returnedState input) :=
  (Prefix256Finish.gasSteps_hit input sv ov acc heq).trans
    ((Prefix256Finish.gasSteps_skip64 input (Or.inl hsize)).trans
      ((gasSteps_select128 input hsize).trans (gasSteps_return input)))

#print axioms gasSteps_finish_hit

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix128Finish
