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
  { storedState input 5358 [] with
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

private theorem pc3772 : Artifact.submissionArtifact.instructionPC 3772 = 5296 := rfl
private theorem pc3773 : Artifact.submissionArtifact.instructionPC 3773 = 5297 := rfl
private theorem pc3774 : Artifact.submissionArtifact.instructionPC 3774 = 5299 := rfl
private theorem pc3775 : Artifact.submissionArtifact.instructionPC 3775 = 5300 := rfl
private theorem pc3776 : Artifact.submissionArtifact.instructionPC 3776 = 5303 := rfl
private theorem pc3783 : Artifact.submissionArtifact.instructionPC 3783 = 5331 := rfl
private theorem pc3784 : Artifact.submissionArtifact.instructionPC 3784 = 5332 := rfl
private theorem pc3785 : Artifact.submissionArtifact.instructionPC 3785 = 5353 := rfl
private theorem pc3786 : Artifact.submissionArtifact.instructionPC 3786 = 5354 := rfl
private theorem pc3787 : Artifact.submissionArtifact.instructionPC 3787 = 5355 := rfl
private theorem pc3788 : Artifact.submissionArtifact.instructionPC 3788 = 5357 := rfl
private theorem pc3789 : Artifact.submissionArtifact.instructionPC 3789 = 5358 := rfl

private theorem returnDest : Decode.isValidJumpDest submissionBytecode 5331 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 3783 (by rfl)

private def gasSteps_selector_test (input : ByteArray) :
    GasSteps (stS input 5296 [])
      (stS input 5303 [5331,
        UInt256.eq 128 (UInt256.ofNat input.size)]) := by
  have a := soundS (opAt 3772 .CALLDATASIZE)
    (blockOfS _ (pcFactS input 3772 5296 _ (by norm_num) pc3772)
      (stepS_calldatasize input 5296 [] (by simp) (by norm_num)))
  have b := soundS (pushAt 3773 1 128)
    (blockOfS _ (pcFactS input 3773 5297 _ (by norm_num) pc3773)
      (stepS_push input 5297 1 128 [UInt256.ofNat input.size]
        (by simp) (by decide) (by decide) (by norm_num)))
  have c := soundS (opAt 3774 .EQ)
    (blockOfS _ (pcFactS input 3774 5299 _ (by norm_num) pc3774)
      (stepS_eq input 5299 128 (UInt256.ofNat input.size) []
        (by simp) (by norm_num)))
  have d := soundS (pushAt 3775 2 5331)
    (blockOfS _ (pcFactS input 3775 5300 _ (by norm_num) pc3775)
      (stepS_push input 5300 2 5331
        [UInt256.eq 128 (UInt256.ofNat input.size)]
        (by simp) (by decide) (by decide) (by norm_num)))
  exact a.trans (b.trans (c.trans d))

def gasSteps_select128 (input : ByteArray) (hsize : input.size = 128) :
    GasSteps (stS input 5296 []) (stS input 5331 []) := by
  have hc : UInt256.isTrue
      (UInt256.eq 128 (UInt256.ofNat input.size)) := by
    rw [hsize]
    decide
  exact (gasSteps_selector_test input).trans
    (soundS (opAt 3776 .JUMPI)
      (blockOfS _ (pcFactS input 3776 5303 _ (by norm_num) pc3776)
        (stepS_jumpi_taken input 5303 5331 5331
          (UInt256.eq 128 (UInt256.ofNat input.size)) []
          (by simp) (by norm_num) rfl hc returnDest)))

def gasSteps_return (input : ByteArray) :
    GasSteps (stS input 5331 []) (returnedState input) := by
  have a := soundS (opAt 3783 .JUMPDEST)
    (blockOfS _ (pcFactS input 3783 5331 _ (by norm_num) pc3783)
      (stepS_jumpdest input 5331 [] (by simp) (by norm_num)))
  have b := soundS (pushAt 3784 20 paddedDigestWord)
    (blockOfS _ (pcFactS input 3784 5332 _ (by norm_num) pc3784)
      (stepS_push input 5332 20 paddedDigestWord []
        (by simp) (by decide) (by decide) (by norm_num)))
  have c := soundS (pushAt 3785 0 0)
    (blockOfS _ (pcFactS input 3785 5353 _ (by norm_num) pc3785)
      (stepS_push0 input 5353 [paddedDigestWord] (by simp) (by norm_num)))
  have hd : Stepper.runInstr (.op .MSTORE)
      (stS input 5354 [0, paddedDigestWord]) = some (storedState input 5355 []) := by
    rfl
  have d := soundS (opAt 3786 .MSTORE)
    (blockOfS _ (pcFactS input 3786 5354 _ (by norm_num) pc3786) hd)
  have he : Stepper.runInstr (.push 1 32) (storedState input 5355 []) =
      some (storedState input 5357 [32]) := by rfl
  have e := soundS (pushAt 3787 1 32)
    (blockOfS _
      (show (storedState input 5355 []).pc.toNat =
        Artifact.submissionArtifact.instructionPC 3787 from
          pcFactS input 3787 5355 [] (by norm_num) pc3787) he)
  have hf : Stepper.runInstr (.push 0 0) (storedState input 5357 [32]) =
      some (storedState input 5358 [0, 32]) := by rfl
  have f := soundS (pushAt 3788 0 0)
    (blockOfS _
      (show (storedState input 5357 [32]).pc.toNat =
        Artifact.submissionArtifact.instructionPC 3788 from
          pcFactS input 3788 5357 [32] (by norm_num) pc3788) hf)
  have hg : Stepper.runInstr (.op .RETURN) (storedState input 5358 [0, 32]) =
      some (returnedState input) := by rfl
  have g := soundS (opAt 3789 .RETURN)
    (blockOfS _
      (show (storedState input 5358 [0, 32]).pc.toNat =
        Artifact.submissionArtifact.instructionPC 3789 from
          pcFactS input 3789 5358 [0, 32] (by norm_num) pc3789) hg)
  exact a.trans (b.trans (c.trans (d.trans (e.trans (f.trans g)))))

def gasSteps_finish_hit (input : ByteArray) (sv ov acc : UInt256)
    (hsize : input.size = 128) (heq : acc = 0) :
    GasSteps (stS input 5283 [sv, ov, acc, P7, M, m7, P, m8])
      (returnedState input) :=
  (Prefix256Finish.gasSteps_hit input sv ov acc heq).trans
    ((gasSteps_select128 input hsize).trans (gasSteps_return input))

#print axioms gasSteps_finish_hit

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix128Finish
