import Challenge.Ripemd160.Submission.Proofs.Bytecode.Msize
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Finish
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix64Digest
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Trace

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
  { storedState input 5296 [] with
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

private theorem pc3772 : Artifact.submissionArtifact.instructionPC 4075 = 5200 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3773 : Artifact.submissionArtifact.instructionPC 4076 = 5201 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3774 : Artifact.submissionArtifact.instructionPC 4077 = 5203 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3775 : Artifact.submissionArtifact.instructionPC 4078 = 5204 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3776 : Artifact.submissionArtifact.instructionPC 4079 = 5207 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3783 : Artifact.submissionArtifact.instructionPC 4098 = 5270 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3784 : Artifact.submissionArtifact.instructionPC 4099 = 5271 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3785 : Artifact.submissionArtifact.instructionPC 4100 = 5292 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3786 : Artifact.submissionArtifact.instructionPC 4101 = 5293 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3787 : Artifact.submissionArtifact.instructionPC 4102 = 5294 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3788 : Artifact.submissionArtifact.instructionPC 4103 = 5295 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3789 : Artifact.submissionArtifact.instructionPC 4104 = 5296 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl

private theorem returnDest : Decode.isValidJumpDest submissionBytecode 5270 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 4098 (by rfl)

private def gasSteps_selector_test (input : ByteArray) :
    GasSteps (stS input 5200 [])
      (stS input 5207 [5275,
        UInt256.eq 64 (UInt256.ofNat input.size)]) := by
  have a := soundS (opAt 4075 .CALLDATASIZE)
    (blockOfS _ (pcFactS input 4075 5200 _ (by norm_num) pc3772)
      (stepS_calldatasize input 5200 [] (by simp) (by norm_num)))
  have b := soundS (pushAt 4076 1 64)
    (blockOfS _ (pcFactS input 4076 5201 _ (by norm_num) pc3773)
      (stepS_push input 5201 1 64 [UInt256.ofNat input.size]
        (by simp) (by decide) (by decide) (by norm_num)))
  have c := soundS (opAt 4077 .EQ)
    (blockOfS _ (pcFactS input 4077 5203 _ (by norm_num) pc3774)
      (stepS_eq input 5203 64 (UInt256.ofNat input.size) []
        (by simp) (by norm_num)))
  have d := soundS (pushAt 4078 2 5270)
    (blockOfS _ (pcFactS input 4078 5204 _ (by norm_num) pc3775)
      (stepS_push input 5204 2 5270
        [UInt256.eq 64 (UInt256.ofNat input.size)]
        (by simp) (by decide) (by decide) (by norm_num)))
  exact a.trans (b.trans (c.trans d))

def gasSteps_select64 (input : ByteArray) (hsize : input.size = 64) :
    GasSteps (stS input 5200 []) (stS input 5270 []) := by
  have hc : UInt256.isTrue
      (UInt256.eq 64 (UInt256.ofNat input.size)) := by
    rw [hsize]
    decide
  exact (gasSteps_selector_test input).trans
    (soundS (opAt 4079 .JUMPI)
      (blockOfS _ (pcFactS input 4079 5207 _ (by norm_num) pc3776)
        (stepS_jumpi_taken input 5207 5270 5270
          (UInt256.eq 64 (UInt256.ofNat input.size)) []
          (by simp) (by norm_num) rfl hc returnDest)))

def gasSteps_return (input : ByteArray) :
    GasSteps (stS input 5270 []) (returnedState input) := by
  have a := soundS (opAt 4098 .JUMPDEST)
    (blockOfS _ (pcFactS input 4098 5270 _ (by norm_num) pc3783)
      (stepS_jumpdest input 5270 [] (by simp) (by norm_num)))
  have b := soundS (pushAt 4104 20 paddedDigestWord)
    (blockOfS _ (pcFactS input 4099 5271 _ (by norm_num) pc3784)
      (stepS_push input 5271 20 paddedDigestWord []
        (by simp) (by decide) (by decide) (by norm_num)))
  have c := soundS (pushAt 4100 0 0)
    (blockOfS _ (pcFactS input 4100 5292 _ (by norm_num) pc3785)
      (stepS_push0 input 5292 [paddedDigestWord] (by simp) (by norm_num)))
  have hd : Stepper.runInstr (.op .MSTORE)
      (stS input 5293 [0, paddedDigestWord]) = some (storedState input 5294 []) := by
    rfl
  have d := soundS (opAt 4101 .MSTORE)
    (blockOfS _ (pcFactS input 4101 5293 _ (by norm_num) pc3786) hd)
  have hop : (storedState input 5294 []).decodedOp = some .MSIZE := by
    apply Trace.decodedOpAt (storedState input 5294 []) 4107 .MSIZE
    · rfl
    · change UInt256.ofNat 5299 =
        UInt256.ofNat (Artifact.submissionArtifact.instructionPC 4107)
      rw [pc3787]
    · rfl
    · rfl
    · trivial
    · rfl
  have e : GasSteps (storedState input 5294 []) (storedState input 5295 [32]) := by
    exact Msize.step hop (by change 0 < 1024; decide) (by rfl) deployAddress_not_precompile
  have hf : Stepper.runInstr (.push 0 0) (storedState input 5295 [32]) =
      some (storedState input 5296 [0, 32]) := by rfl
  have f := soundS (pushAt 4103 0 0)
    (blockOfS _
      (show (storedState input 5295 [32]).pc.toNat =
        Artifact.submissionArtifact.instructionPC 4108 from
          pcFactS input 4103 5295 [32] (by norm_num) pc3788) hf)
  have hg : Stepper.runInstr (.op .RETURN) (storedState input 5296 [0, 32]) =
      some (returnedState input) := by rfl
  have g := soundS (opAt 4104 .RETURN)
    (blockOfS _
      (show (storedState input 5296 [0, 32]).pc.toNat =
        Artifact.submissionArtifact.instructionPC 4109 from
          pcFactS input 4104 5296 [0, 32] (by norm_num) pc3789) hg)
  exact a.trans (b.trans (c.trans (d.trans (e.trans (f.trans g)))))

def gasSteps_finish_hit (input : ByteArray) (sv ov acc : UInt256)
    (hsize : input.size = 64) (heq : acc = 0) :
    GasSteps (stS input 5187 [sv, ov, acc, P7, M, m7, P, m8])
      (returnedState input) :=
  (Prefix256Finish.gasSteps_hit input sv ov acc heq).trans
    ((gasSteps_select64 input hsize).trans (gasSteps_return input))

#print axioms gasSteps_finish_hit

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix64Finish
