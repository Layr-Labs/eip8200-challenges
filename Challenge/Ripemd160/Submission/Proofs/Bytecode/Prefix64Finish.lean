import Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Finish
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Msize
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
  { storedState input 5290 [] with
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

private theorem pc3772 : Artifact.submissionArtifact.instructionPC 4072 = 5193 := rfl
private theorem pc3773 : Artifact.submissionArtifact.instructionPC 4073 = 5194 := rfl
private theorem pc3774 : Artifact.submissionArtifact.instructionPC 4074 = 5196 := rfl
private theorem pc3775 : Artifact.submissionArtifact.instructionPC 4075 = 5197 := rfl
private theorem pc3776 : Artifact.submissionArtifact.instructionPC 4076 = 5200 := rfl
private theorem pc3783 : Artifact.submissionArtifact.instructionPC 4095 = 5264 := rfl
private theorem pc3784 : Artifact.submissionArtifact.instructionPC 4096 = 5265 := rfl
private theorem pc3785 : Artifact.submissionArtifact.instructionPC 4097 = 5286 := rfl
private theorem pc3786 : Artifact.submissionArtifact.instructionPC 4098 = 5287 := rfl
private theorem pc3787 : Artifact.submissionArtifact.instructionPC 4099 = 5288 := rfl
private theorem pc3788 : Artifact.submissionArtifact.instructionPC 4100 = 5289 := rfl
private theorem pc3789 : Artifact.submissionArtifact.instructionPC 4101 = 5290 := rfl

private theorem returnDest : Decode.isValidJumpDest submissionBytecode 5264 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 4095 (by rfl)

private theorem msizeDecoded (input : ByteArray) :
    (storedState input 5288 []).decodedOp = some .MSIZE := by
  have hget : Artifact.submissionInstructions[4099]? = some (.op .MSIZE) := by
    rfl
  have hdecode := Artifact.submissionArtifact.decodeAt_op_index
    4099 .MSIZE hget (by decide) trivial
  have hpcNat : (storedState input 5288 []).pc.toNat =
      Artifact.submissionArtifact.instructionPC 4099 := by
    rw [show (storedState input 5288 []).pc = UInt256.ofNat 5288 by rfl,
      Challenge.EvmProof.Word.word_toNat_ofNat]
    rfl
  exact Artifact.submissionArtifact.state_decodedOp_of
    (storedState input 5288 []) 4099 (by rfl) hpcNat .MSIZE none hdecode
    (by decide)

private def gasSteps_msize (input : ByteArray) :
    GasSteps (storedState input 5288 []) (storedState input 5289 [32]) := by
  have h := Msize.step (s := storedState input 5288 [])
    (msizeDecoded input) (by simp) (by rfl) deployAddress_not_precompile
  exact GasSteps.cast h rfl (by
    simp [storedState, stS, Challenge.EvmProof.Word.succ_ofNat_mod])

private def gasSteps_selector_test (input : ByteArray) :
    GasSteps (stS input 5193 [])
      (stS input 5200 [5264,
        UInt256.eq 64 (UInt256.ofNat input.size)]) := by
  have a := soundS (opAt 4072 .CALLDATASIZE)
    (blockOfS _ (pcFactS input 4072 5193 _ (by norm_num) pc3772)
      (stepS_calldatasize input 5193 [] (by simp) (by norm_num)))
  have b := soundS (pushAt 4073 1 64)
    (blockOfS _ (pcFactS input 4073 5194 _ (by norm_num) pc3773)
      (stepS_push input 5194 1 64 [UInt256.ofNat input.size]
        (by simp) (by decide) (by decide) (by norm_num)))
  have c := soundS (opAt 4074 .EQ)
    (blockOfS _ (pcFactS input 4074 5196 _ (by norm_num) pc3774)
      (stepS_eq input 5196 64 (UInt256.ofNat input.size) []
        (by simp) (by norm_num)))
  have d := soundS (pushAt 4075 2 5264)
    (blockOfS _ (pcFactS input 4075 5197 _ (by norm_num) pc3775)
      (stepS_push input 5197 2 5264
        [UInt256.eq 64 (UInt256.ofNat input.size)]
        (by simp) (by decide) (by decide) (by norm_num)))
  exact a.trans (b.trans (c.trans d))

def gasSteps_select64 (input : ByteArray) (hsize : input.size = 64) :
    GasSteps (stS input 5193 []) (stS input 5264 []) := by
  have hc : UInt256.isTrue
      (UInt256.eq 64 (UInt256.ofNat input.size)) := by
    rw [hsize]
    decide
  exact (gasSteps_selector_test input).trans
    (soundS (opAt 4076 .JUMPI)
      (blockOfS _ (pcFactS input 4076 5200 _ (by norm_num) pc3776)
        (stepS_jumpi_taken input 5200 5264 5264
          (UInt256.eq 64 (UInt256.ofNat input.size)) []
          (by simp) (by norm_num) rfl hc returnDest)))

def gasSteps_return (input : ByteArray) :
    GasSteps (stS input 5264 []) (returnedState input) := by
  have a := soundS (opAt 4095 .JUMPDEST)
    (blockOfS _ (pcFactS input 4095 5264 _ (by norm_num) pc3783)
      (stepS_jumpdest input 5264 [] (by simp) (by norm_num)))
  have b := soundS (pushAt 4096 20 paddedDigestWord)
    (blockOfS _ (pcFactS input 4096 5265 _ (by norm_num) pc3784)
      (stepS_push input 5265 20 paddedDigestWord []
        (by simp) (by decide) (by decide) (by norm_num)))
  have c := soundS (pushAt 4097 0 0)
    (blockOfS _ (pcFactS input 4097 5286 _ (by norm_num) pc3785)
      (stepS_push0 input 5286 [paddedDigestWord] (by simp) (by norm_num)))
  have hd : Stepper.runInstr (.op .MSTORE)
      (stS input 5287 [0, paddedDigestWord]) = some (storedState input 5288 []) := by
    rfl
  have d := soundS (opAt 4098 .MSTORE)
    (blockOfS _ (pcFactS input 4098 5287 _ (by norm_num) pc3786) hd)
  have e := gasSteps_msize input
  have f := soundS (pushAt 4100 0 0)
    (blockOfS _
      (show (storedState input 5289 [32]).pc.toNat =
        Artifact.submissionArtifact.instructionPC 4100 from
          pcFactS input 4100 5289 [32] (by norm_num) pc3788)
      (by
        have h : Stepper.runInstr (.push 0 0)
            (storedState input 5289 [32]) =
            some (storedState input 5290 [0, 32]) := by rfl
        exact h))
  have g := soundS (opAt 4101 .RETURN)
    (blockOfS _
      (show (storedState input 5290 [0, 32]).pc.toNat =
        Artifact.submissionArtifact.instructionPC 4101 from
          pcFactS input 4101 5290 [0, 32] (by norm_num) pc3789)
      (by
        have h : Stepper.runInstr (.op .RETURN)
            (storedState input 5290 [0, 32]) =
            some (returnedState input) := by rfl
        exact h))
  exact a.trans (b.trans (c.trans (d.trans (e.trans (f.trans g)))))

def gasSteps_finish_hit (input : ByteArray) (sv ov acc : UInt256)
    (hsize : input.size = 64) (heq : acc = 0) :
    GasSteps (stS input 5180 [sv, ov, acc, P7, M, m7, P, m8])
      (returnedState input) :=
  (Prefix256Finish.gasSteps_hit input sv ov acc heq).trans
    ((gasSteps_select64 input hsize).trans (gasSteps_return input))

#print axioms gasSteps_finish_hit

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix64Finish
