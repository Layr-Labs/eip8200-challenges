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
  stS input 261 (returnRest sv ov)

def digestEntryState (_n : Nat) (input : ByteArray) (sv ov : UInt256) : State :=
  stS input 5189 (returnRest sv ov)

def storedState (n : Nat) (input : ByteArray) (sv ov : UInt256) : State :=
  { stS input 5248 (returnRest sv ov) with
    memory := answerMemory n
    activeWords := UInt256.ofNat 1 }

def sizedState (n : Nat) (input : ByteArray) (sv ov : UInt256) : State :=
  { storedState n input sv ov with
    pc := UInt256.ofNat 5249
    stack := UInt256.ofNat 32 :: returnRest sv ov }

def returnedState (n : Nat) (input : ByteArray) (sv ov : UInt256) : State :=
  { storedState n input sv ov with
    pc := UInt256.ofNat 5250
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
  [opAt 160 .CALLDATASIZE, pushAt 161 1 129, opAt 162 .GT,
   pushAt 163 2 5189, opAt 164 .JUMPI]

def digestStorePath : List Located :=
  [opAt 4162 .JUMPDEST, opAt 4163 .CALLDATASIZE, pushAt 4164 1 63,
   opAt 4165 .EQ, pushAt 4166 2 5162, opAt 4167 .JUMPI,
   pushAt 4168 20 (paddedDigestWord 56),
   pushAt 4169 20 (UInt256.xor (paddedDigestWord 56) (paddedDigestWord 120)),
   opAt 4170 .CALLDATASIZE, pushAt 4171 1 120, opAt 4172 .EQ,
   opAt 4173 .MUL, opAt 4174 .XOR, pushAt 4175 0 0, opAt 4176 .MSTORE]

def digestFinishPath : List Located :=
  [pushAt 4178 0 0, opAt 4179 .RETURN]

@[simp] private theorem shortPC166 : Artifact.submissionArtifact.instructionPC 160 = 261 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem shortPC167 : Artifact.submissionArtifact.instructionPC 161 = 262 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem shortPC168 : Artifact.submissionArtifact.instructionPC 162 = 264 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem shortPC169 : Artifact.submissionArtifact.instructionPC 163 = 265 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem shortPC170 : Artifact.submissionArtifact.instructionPC 164 = 268 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem shortPC4181 : Artifact.submissionArtifact.instructionPC 4162 = 5189 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem shortPC4182 : Artifact.submissionArtifact.instructionPC 4163 = 5190 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem shortPC4183 : Artifact.submissionArtifact.instructionPC 4164 = 5191 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem shortPC4184 : Artifact.submissionArtifact.instructionPC 4165 = 5193 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem shortPC4185 : Artifact.submissionArtifact.instructionPC 4166 = 5194 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem shortPC4186 : Artifact.submissionArtifact.instructionPC 4167 = 5197 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem shortPC4187 : Artifact.submissionArtifact.instructionPC 4168 = 5198 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem shortPC4188 : Artifact.submissionArtifact.instructionPC 4169 = 5219 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem shortPC4189 : Artifact.submissionArtifact.instructionPC 4170 = 5240 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem shortPC4190 : Artifact.submissionArtifact.instructionPC 4171 = 5241 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem shortPC4191 : Artifact.submissionArtifact.instructionPC 4172 = 5243 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem shortPC4192 : Artifact.submissionArtifact.instructionPC 4173 = 5244 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem shortPC4193 : Artifact.submissionArtifact.instructionPC 4174 = 5245 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem shortPC4194 : Artifact.submissionArtifact.instructionPC 4175 = 5246 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem shortPC4195 : Artifact.submissionArtifact.instructionPC 4176 = 5247 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem shortPC4196 : Artifact.submissionArtifact.instructionPC 4177 = 5248 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem shortPC4197 : Artifact.submissionArtifact.instructionPC 4178 = 5249 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem shortPC4198 : Artifact.submissionArtifact.instructionPC 4179 = 5250 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

theorem run_selector (n : Nat) (input : ByteArray) (sv ov : UInt256)
    (hn : n = 56 ∨ n = 120) (hsize : input.size = n) :
    run selectorPath (selectorState n input sv ov) =
      some (digestEntryState n input sv ov) := by
  change run selectorPath (stS input 261 (returnRest sv ov)) =
    some (stS input 5189 (returnRest sv ov))
  have hdest : Decode.isValidJumpDest submissionBytecode 5189 = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 4162 (by rfl)
  have htrue : UInt256.isTrue (UInt256.gt 129 (UInt256.ofNat input.size)) := by
    rw [hsize]
    rcases hn with rfl | rfl <;> decide
  have h0 :
      Challenge.EvmProof.Stepper.runLocatedBlock
          [opAt 160 .CALLDATASIZE]
          (stS input 261 (returnRest sv ov)) =
        some (stS input 262 (UInt256.ofNat input.size :: returnRest sv ov)) := by
    exact blockOfS _
      (pcFactS input 160 261 _ (by norm_num) shortPC166)
      (stepS_calldatasize input 261 (returnRest sv ov)
        (by simp [returnRest]) (by norm_num))
  have h1 :
      Challenge.EvmProof.Stepper.runLocatedBlock
          [pushAt 161 1 129]
          (stS input 262 (UInt256.ofNat input.size :: returnRest sv ov)) =
        some (stS input 264 (129 :: UInt256.ofNat input.size :: returnRest sv ov)) := by
    exact blockOfS _
      (pcFactS input 161 262 _ (by norm_num) shortPC167)
      (stepS_push input 262 1 129
        (UInt256.ofNat input.size :: returnRest sv ov)
        (by simp [returnRest]) (by decide) (by decide) (by norm_num))
  have h2 :
      Challenge.EvmProof.Stepper.runLocatedBlock
          [opAt 162 .GT]
          (stS input 264 (129 :: UInt256.ofNat input.size :: returnRest sv ov)) =
        some (stS input 265
          (UInt256.gt 129 (UInt256.ofNat input.size) :: returnRest sv ov)) := by
    exact blockOfS _
      (pcFactS input 162 264 _ (by norm_num) shortPC168)
      (stepS_gt input 264 129 (UInt256.ofNat input.size) (returnRest sv ov)
        (by simp [returnRest]) (by norm_num))
  have h3 :
      Challenge.EvmProof.Stepper.runLocatedBlock
          [pushAt 163 2 5189]
          (stS input 265
            (UInt256.gt 129 (UInt256.ofNat input.size) :: returnRest sv ov)) =
        some (stS input 268
          (5189 :: UInt256.gt 129 (UInt256.ofNat input.size) :: returnRest sv ov)) := by
    exact blockOfS _
      (pcFactS input 163 265 _ (by norm_num) shortPC169)
      (stepS_push input 265 2 5189
        (UInt256.gt 129 (UInt256.ofNat input.size) :: returnRest sv ov)
        (by simp [returnRest]) (by decide) (by decide) (by norm_num))
  have h4 :
      Challenge.EvmProof.Stepper.runLocatedBlock
          [opAt 164 .JUMPI]
          (stS input 268
            (5189 :: UInt256.gt 129 (UInt256.ofNat input.size) :: returnRest sv ov)) =
        some (stS input 5189 (returnRest sv ov)) := by
    exact blockOfS _
      (pcFactS input 164 268 _ (by norm_num) shortPC170)
      (stepS_jumpi_taken input 268 5189 5189
        (UInt256.gt 129 (UInt256.ofNat input.size)) (returnRest sv ov)
        (by simp [returnRest]) (by norm_num) rfl htrue hdest)
  have h01 :
      Challenge.EvmProof.Stepper.runLocatedBlock
          [opAt 160 .CALLDATASIZE, pushAt 161 1 129]
          (stS input 261 (returnRest sv ov)) =
        some (stS input 264 (129 :: UInt256.ofNat input.size :: returnRest sv ov)) := by
    exact Challenge.EvmProof.Stepper.runLocatedBlock_append
      [opAt 160 .CALLDATASIZE] [pushAt 161 1 129]
      _ _ _ h0 (by rfl) h1
  have h012 :
      Challenge.EvmProof.Stepper.runLocatedBlock
          [opAt 160 .CALLDATASIZE, pushAt 161 1 129, opAt 162 .GT]
          (stS input 261 (returnRest sv ov)) =
        some (stS input 265
          (UInt256.gt 129 (UInt256.ofNat input.size) :: returnRest sv ov)) := by
    exact Challenge.EvmProof.Stepper.runLocatedBlock_append
      [opAt 160 .CALLDATASIZE, pushAt 161 1 129] [opAt 162 .GT]
      _ _ _ h01 (by rfl) h2
  have h0123 :
      Challenge.EvmProof.Stepper.runLocatedBlock
          [opAt 160 .CALLDATASIZE, pushAt 161 1 129, opAt 162 .GT,
            pushAt 163 2 5189]
          (stS input 261 (returnRest sv ov)) =
        some (stS input 268
          (5189 :: UInt256.gt 129 (UInt256.ofNat input.size) :: returnRest sv ov)) := by
    exact Challenge.EvmProof.Stepper.runLocatedBlock_append
      [opAt 160 .CALLDATASIZE, pushAt 161 1 129, opAt 162 .GT]
      [pushAt 163 2 5189] _ _ _ h012 (by rfl) h3
  have h01234 :
      Challenge.EvmProof.Stepper.runLocatedBlock
          [opAt 160 .CALLDATASIZE, pushAt 161 1 129, opAt 162 .GT,
            pushAt 163 2 5189, opAt 164 .JUMPI]
          (stS input 261 (returnRest sv ov)) =
        some (stS input 5189 (returnRest sv ov)) := by
    exact Challenge.EvmProof.Stepper.runLocatedBlock_append
      [opAt 160 .CALLDATASIZE, pushAt 161 1 129, opAt 162 .GT,
        pushAt 163 2 5189] [opAt 164 .JUMPI] _ _ _ h0123 (by rfl) h4
  simpa only [selectorPath] using h01234


end Challenge.Ripemd160.Submission.Proofs.Bytecode.ShortPatternFinish
