import Challenge.Ripemd160.Submission.Proofs.Bytecode.Msize
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Finish
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix128Digest
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Trace
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
  { storedState input 5269 [] with
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

private theorem pc3772 : Artifact.submissionArtifact.instructionPC 4080 = 5208 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3773 : Artifact.submissionArtifact.instructionPC 4081 = 5209 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3774 : Artifact.submissionArtifact.instructionPC 4082 = 5211 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3775 : Artifact.submissionArtifact.instructionPC 4083 = 5212 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3776 : Artifact.submissionArtifact.instructionPC 4084 = 5215 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3783 : Artifact.submissionArtifact.instructionPC 4091 = 5243 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3784 : Artifact.submissionArtifact.instructionPC 4092 = 5244 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3785 : Artifact.submissionArtifact.instructionPC 4093 = 5265 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3786 : Artifact.submissionArtifact.instructionPC 4094 = 5266 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3787 : Artifact.submissionArtifact.instructionPC 4095 = 5267 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3788 : Artifact.submissionArtifact.instructionPC 4096 = 5268 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3789 : Artifact.submissionArtifact.instructionPC 4097 = 5269 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl

private theorem returnDest : Decode.isValidJumpDest submissionBytecode 5243 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 4091 (by rfl)

private def gasSteps_selector_test (input : ByteArray) :
    GasSteps (stS input 5208 [])
      (stS input 5215 [5248,
        UInt256.eq 128 (UInt256.ofNat input.size)]) := by
  have a := soundS (opAt 4080 .CALLDATASIZE)
    (blockOfS _ (pcFactS input 4080 5208 _ (by norm_num) pc3772)
      (stepS_calldatasize input 5208 [] (by simp) (by norm_num)))
  have b := soundS (pushAt 4081 1 128)
    (blockOfS _ (pcFactS input 4081 5209 _ (by norm_num) pc3773)
      (stepS_push input 5209 1 128 [UInt256.ofNat input.size]
        (by simp) (by decide) (by decide) (by norm_num)))
  have c := soundS (opAt 4082 .EQ)
    (blockOfS _ (pcFactS input 4082 5211 _ (by norm_num) pc3774)
      (stepS_eq input 5211 128 (UInt256.ofNat input.size) []
        (by simp) (by norm_num)))
  have d := soundS (pushAt 4083 2 5243)
    (blockOfS _ (pcFactS input 4083 5212 _ (by norm_num) pc3775)
      (stepS_push input 5212 2 5243
        [UInt256.eq 128 (UInt256.ofNat input.size)]
        (by simp) (by decide) (by decide) (by norm_num)))
  exact a.trans (b.trans (c.trans d))

def gasSteps_select128 (input : ByteArray) (hsize : input.size = 128) :
    GasSteps (stS input 5208 []) (stS input 5243 []) := by
  have hc : UInt256.isTrue
      (UInt256.eq 128 (UInt256.ofNat input.size)) := by
    rw [hsize]
    decide
  exact (gasSteps_selector_test input).trans
    (soundS (opAt 4084 .JUMPI)
      (blockOfS _ (pcFactS input 4084 5215 _ (by norm_num) pc3776)
        (stepS_jumpi_taken input 5215 5243 5243
          (UInt256.eq 128 (UInt256.ofNat input.size)) []
          (by simp) (by norm_num) rfl hc returnDest)))

def gasSteps_return (input : ByteArray) :
    GasSteps (stS input 5243 []) (returnedState input) := by
  have a := soundS (opAt 4091 .JUMPDEST)
    (blockOfS _ (pcFactS input 4091 5243 _ (by norm_num) pc3783)
      (stepS_jumpdest input 5243 [] (by simp) (by norm_num)))
  have b := soundS (pushAt 4097 20 paddedDigestWord)
    (blockOfS _ (pcFactS input 4092 5244 _ (by norm_num) pc3784)
      (stepS_push input 5244 20 paddedDigestWord []
        (by simp) (by decide) (by decide) (by norm_num)))
  have c := soundS (pushAt 4093 0 0)
    (blockOfS _ (pcFactS input 4093 5265 _ (by norm_num) pc3785)
      (stepS_push0 input 5265 [paddedDigestWord] (by simp) (by norm_num)))
  have hd : Stepper.runInstr (.op .MSTORE)
      (stS input 5266 [0, paddedDigestWord]) = some (storedState input 5267 []) := by
    rfl
  have d := soundS (opAt 4094 .MSTORE)
    (blockOfS _ (pcFactS input 4094 5266 _ (by norm_num) pc3786) hd)
  have hop : (storedState input 5267 []).decodedOp = some .MSIZE := by
    apply Trace.decodedOpAt (storedState input 5267 []) 4100 .MSIZE
    · rfl
    · change UInt256.ofNat 5272 =
        UInt256.ofNat (Artifact.submissionArtifact.instructionPC 4100)
      rw [pc3787]
    · rfl
    · rfl
    · trivial
    · rfl
  have e : GasSteps (storedState input 5267 []) (storedState input 5268 [32]) := by
    exact Msize.step hop (by change 0 < 1024; decide) (by rfl) deployAddress_not_precompile
  have hf : Stepper.runInstr (.push 0 0) (storedState input 5268 [32]) =
      some (storedState input 5269 [0, 32]) := by rfl
  have f := soundS (pushAt 4096 0 0)
    (blockOfS _
      (show (storedState input 5268 [32]).pc.toNat =
        Artifact.submissionArtifact.instructionPC 4101 from
          pcFactS input 4096 5268 [32] (by norm_num) pc3788) hf)
  have hg : Stepper.runInstr (.op .RETURN) (storedState input 5269 [0, 32]) =
      some (returnedState input) := by rfl
  have g := soundS (opAt 4097 .RETURN)
    (blockOfS _
      (show (storedState input 5269 [0, 32]).pc.toNat =
        Artifact.submissionArtifact.instructionPC 4102 from
          pcFactS input 4097 5269 [0, 32] (by norm_num) pc3789) hg)
  exact a.trans (b.trans (c.trans (d.trans (e.trans (f.trans g)))))

def gasSteps_finish_hit (input : ByteArray) (sv ov acc : UInt256)
    (hsize : input.size = 128) (heq : acc = 0) :
    GasSteps (stS input 5187 [sv, ov, acc, P7, M, m7, P, m8])
      (returnedState input) :=
  (Prefix256Finish.gasSteps_hit input sv ov acc heq).trans
    ((Prefix256Finish.gasSteps_skip64 input (Or.inl hsize)).trans
      ((gasSteps_select128 input hsize).trans (gasSteps_return input)))

#print axioms gasSteps_finish_hit

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix128Finish
