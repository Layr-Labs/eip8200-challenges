import Challenge.Ripemd160.Submission.Proofs.Bytecode.ShortPatternDigest
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned128Scan
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Cleanup
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Msize

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.ShortPatternFinish

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open PatternedScan PatternedSwar

def paddedDigestWord (n : Nat) : UInt256 :=
  if n = 56 then 0x0d8e2e84bad19fc85dbadb55fa5467631ce141503
  else 0x04de20b6b1fb2af442370c40e53a50aca360fc3bc

def paddedDigest (n : Nat) : ByteArray :=
  if n = 56 then ShortPatternDigest.paddedDigest56
  else ShortPatternDigest.paddedDigest120

def answerMemory (n : Nat) : ByteArray := storeWord ByteArray.empty 0 (paddedDigestWord n)

def returnRest (sv ov : UInt256) : List UInt256 :=
  [sv, ov, 0, P7, M, m7, P, m8]

def selectorState (_n : Nat) (input : ByteArray) (sv ov : UInt256) : State :=
  stS input 260 (returnRest sv ov)

def digestEntryState (_n : Nat) (input : ByteArray) (sv ov : UInt256) : State :=
  stS input 5198 (returnRest sv ov)

def storedState (n : Nat) (input : ByteArray) (sv ov : UInt256) : State :=
  { stS input 5257 (returnRest sv ov) with
    memory := answerMemory n
    activeWords := UInt256.ofNat 1 }

def sizedState (n : Nat) (input : ByteArray) (sv ov : UInt256) : State :=
  { storedState n input sv ov with
    pc := UInt256.ofNat 5258
    stack := UInt256.ofNat 32 :: returnRest sv ov }

def returnedState (n : Nat) (input : ByteArray) (sv ov : UInt256) : State :=
  { storedState n input sv ov with
    pc := UInt256.ofNat 5259
    halt := .Returned
    hReturn := MachineState.readPadded (answerMemory n) 0 32 }

@[simp] theorem paddedDigest_size (n : Nat) : (paddedDigest n).size = 32 := by
  unfold paddedDigest
  split <;> decide

theorem wordBytes_eq_paddedDigest (n : Nat) :
    Data.Bytes.natToBytesPadded (paddedDigestWord n).toNat 32 = paddedDigest n := by
  rw [Memory.natToBytesPadded_eq_natToBE]
  unfold paddedDigestWord paddedDigest
  split <;> decide

theorem answerMemory_read (n : Nat) :
    MachineState.readPadded (answerMemory n) 0 32 = paddedDigest n := by
  unfold answerMemory storeWord
  have h := Memory.readPadded_writeBytes_same ByteArray.empty
    (Data.Bytes.natToBytesPadded (paddedDigestWord n).toNat 32) 0
  simpa only [YulEvmCompiler.BytesLemmas.natToBytesPadded_size,
    wordBytes_eq_paddedDigest, paddedDigest_size] using h

@[simp] theorem returnedState_hReturn (n : Nat) (input : ByteArray) (sv ov : UInt256) :
    (returnedState n input sv ov).hReturn = paddedDigest n := answerMemory_read n

def selectorPath : List Located :=
  [opAt 164 .CALLDATASIZE, pushAt 165 1 129, opAt 166 .GT,
   pushAt 167 2 5198, opAt 168 .JUMPI]

def digestStorePath : List Located :=
  [opAt 4174 .JUMPDEST, opAt 4175 .CALLDATASIZE, pushAt 4176 1 128,
   opAt 4177 .EQ, pushAt 4178 2 5151, opAt 4179 .JUMPI,
   pushAt 4180 20 (paddedDigestWord 56),
   pushAt 4181 20 (UInt256.xor (paddedDigestWord 56) (paddedDigestWord 120)),
   opAt 4182 .CALLDATASIZE, pushAt 4183 1 120, opAt 4184 .EQ,
   opAt 4185 .MUL, opAt 4186 .XOR, pushAt 4187 0 0, opAt 4188 .MSTORE]

def digestFinishPath : List Located :=
  [pushAt 4190 0 0, opAt 4191 .RETURN]

@[simp] private theorem shortPC166 : Artifact.submissionArtifact.instructionPC 164 = 260 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem shortPC167 : Artifact.submissionArtifact.instructionPC 165 = 261 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem shortPC168 : Artifact.submissionArtifact.instructionPC 166 = 263 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem shortPC169 : Artifact.submissionArtifact.instructionPC 167 = 264 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem shortPC170 : Artifact.submissionArtifact.instructionPC 168 = 267 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem shortPC4181 : Artifact.submissionArtifact.instructionPC 4174 = 5198 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem shortPC4182 : Artifact.submissionArtifact.instructionPC 4175 = 5199 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem shortPC4183 : Artifact.submissionArtifact.instructionPC 4176 = 5200 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem shortPC4184 : Artifact.submissionArtifact.instructionPC 4177 = 5202 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem shortPC4185 : Artifact.submissionArtifact.instructionPC 4178 = 5203 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem shortPC4186 : Artifact.submissionArtifact.instructionPC 4179 = 5206 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem shortPC4187 : Artifact.submissionArtifact.instructionPC 4180 = 5207 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem shortPC4188 : Artifact.submissionArtifact.instructionPC 4181 = 5228 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem shortPC4189 : Artifact.submissionArtifact.instructionPC 4182 = 5249 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem shortPC4190 : Artifact.submissionArtifact.instructionPC 4183 = 5250 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem shortPC4191 : Artifact.submissionArtifact.instructionPC 4184 = 5252 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem shortPC4192 : Artifact.submissionArtifact.instructionPC 4185 = 5253 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem shortPC4193 : Artifact.submissionArtifact.instructionPC 4186 = 5254 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem shortPC4194 : Artifact.submissionArtifact.instructionPC 4187 = 5255 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem shortPC4195 : Artifact.submissionArtifact.instructionPC 4188 = 5256 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem shortPC4196 : Artifact.submissionArtifact.instructionPC 4189 = 5257 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem shortPC4197 : Artifact.submissionArtifact.instructionPC 4190 = 5258 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem shortPC4198 : Artifact.submissionArtifact.instructionPC 4191 = 5259 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

theorem run_selector (n : Nat) (input : ByteArray) (sv ov : UInt256)
    (hn : n = 56 ∨ n = 120) (hsize : input.size = n) :
    run selectorPath (selectorState n input sv ov) =
      some (digestEntryState n input sv ov) := by
  change run selectorPath (stS input 260 (returnRest sv ov)) =
    some (stS input 5198 (returnRest sv ov))
  have hdest : Decode.isValidJumpDest submissionBytecode 5198 = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 4174 (by rfl)
  have htrue : UInt256.isTrue (UInt256.gt 129 (UInt256.ofNat input.size)) := by
    rw [hsize]
    rcases hn with rfl | rfl <;> decide
  have h0 :
      Challenge.EvmProof.Stepper.runLocatedBlock
          [opAt 164 .CALLDATASIZE]
          (stS input 260 (returnRest sv ov)) =
        some (stS input 261 (UInt256.ofNat input.size :: returnRest sv ov)) := by
    exact blockOfS _
      (pcFactS input 164 260 _ (by norm_num) shortPC166)
      (stepS_calldatasize input 260 (returnRest sv ov)
        (by simp [returnRest]) (by norm_num))
  have h1 :
      Challenge.EvmProof.Stepper.runLocatedBlock
          [pushAt 165 1 129]
          (stS input 261 (UInt256.ofNat input.size :: returnRest sv ov)) =
        some (stS input 263 (129 :: UInt256.ofNat input.size :: returnRest sv ov)) := by
    exact blockOfS _
      (pcFactS input 165 261 _ (by norm_num) shortPC167)
      (stepS_push input 261 1 129
        (UInt256.ofNat input.size :: returnRest sv ov)
        (by simp [returnRest]) (by decide) (by decide) (by norm_num))
  have h2 :
      Challenge.EvmProof.Stepper.runLocatedBlock
          [opAt 166 .GT]
          (stS input 263 (129 :: UInt256.ofNat input.size :: returnRest sv ov)) =
        some (stS input 264
          (UInt256.gt 129 (UInt256.ofNat input.size) :: returnRest sv ov)) := by
    exact blockOfS _
      (pcFactS input 166 263 _ (by norm_num) shortPC168)
      (stepS_gt input 263 129 (UInt256.ofNat input.size) (returnRest sv ov)
        (by simp [returnRest]) (by norm_num))
  have h3 :
      Challenge.EvmProof.Stepper.runLocatedBlock
          [pushAt 167 2 5198]
          (stS input 264
            (UInt256.gt 129 (UInt256.ofNat input.size) :: returnRest sv ov)) =
        some (stS input 267
          (5198 :: UInt256.gt 129 (UInt256.ofNat input.size) :: returnRest sv ov)) := by
    exact blockOfS _
      (pcFactS input 167 264 _ (by norm_num) shortPC169)
      (stepS_push input 264 2 5198
        (UInt256.gt 129 (UInt256.ofNat input.size) :: returnRest sv ov)
        (by simp [returnRest]) (by decide) (by decide) (by norm_num))
  have h4 :
      Challenge.EvmProof.Stepper.runLocatedBlock
          [opAt 168 .JUMPI]
          (stS input 267
            (5198 :: UInt256.gt 129 (UInt256.ofNat input.size) :: returnRest sv ov)) =
        some (stS input 5198 (returnRest sv ov)) := by
    exact blockOfS _
      (pcFactS input 168 267 _ (by norm_num) shortPC170)
      (stepS_jumpi_taken input 267 5198 5198
        (UInt256.gt 129 (UInt256.ofNat input.size)) (returnRest sv ov)
        (by simp [returnRest]) (by norm_num) rfl htrue hdest)
  have h01 :
      Challenge.EvmProof.Stepper.runLocatedBlock
          [opAt 164 .CALLDATASIZE, pushAt 165 1 129]
          (stS input 260 (returnRest sv ov)) =
        some (stS input 263 (129 :: UInt256.ofNat input.size :: returnRest sv ov)) := by
    exact Challenge.EvmProof.Stepper.runLocatedBlock_append
      [opAt 164 .CALLDATASIZE] [pushAt 165 1 129]
      _ _ _ h0 (by rfl) h1
  have h012 :
      Challenge.EvmProof.Stepper.runLocatedBlock
          [opAt 164 .CALLDATASIZE, pushAt 165 1 129, opAt 166 .GT]
          (stS input 260 (returnRest sv ov)) =
        some (stS input 264
          (UInt256.gt 129 (UInt256.ofNat input.size) :: returnRest sv ov)) := by
    exact Challenge.EvmProof.Stepper.runLocatedBlock_append
      [opAt 164 .CALLDATASIZE, pushAt 165 1 129] [opAt 166 .GT]
      _ _ _ h01 (by rfl) h2
  have h0123 :
      Challenge.EvmProof.Stepper.runLocatedBlock
          [opAt 164 .CALLDATASIZE, pushAt 165 1 129, opAt 166 .GT,
            pushAt 167 2 5198]
          (stS input 260 (returnRest sv ov)) =
        some (stS input 267
          (5198 :: UInt256.gt 129 (UInt256.ofNat input.size) :: returnRest sv ov)) := by
    exact Challenge.EvmProof.Stepper.runLocatedBlock_append
      [opAt 164 .CALLDATASIZE, pushAt 165 1 129, opAt 166 .GT]
      [pushAt 167 2 5198] _ _ _ h012 (by rfl) h3
  have h01234 :
      Challenge.EvmProof.Stepper.runLocatedBlock
          [opAt 164 .CALLDATASIZE, pushAt 165 1 129, opAt 166 .GT,
            pushAt 167 2 5198, opAt 168 .JUMPI]
          (stS input 260 (returnRest sv ov)) =
        some (stS input 5198 (returnRest sv ov)) := by
    exact Challenge.EvmProof.Stepper.runLocatedBlock_append
      [opAt 164 .CALLDATASIZE, pushAt 165 1 129, opAt 166 .GT,
        pushAt 167 2 5198] [opAt 168 .JUMPI] _ _ _ h0123 (by rfl) h4
  simpa only [selectorPath] using h01234


end Challenge.Ripemd160.Submission.Proofs.Bytecode.ShortPatternFinish
