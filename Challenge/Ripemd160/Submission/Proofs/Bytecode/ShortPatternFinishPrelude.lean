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
  stS input 255 (returnRest sv ov)

def digestEntryState (_n : Nat) (input : ByteArray) (sv ov : UInt256) : State :=
  stS input 5202 (returnRest sv ov)

def storedState (n : Nat) (input : ByteArray) (sv ov : UInt256) : State :=
  { stS input 5261 (returnRest sv ov) with
    memory := answerMemory n
    activeWords := UInt256.ofNat 1 }

def sizedState (n : Nat) (input : ByteArray) (sv ov : UInt256) : State :=
  { storedState n input sv ov with
    pc := UInt256.ofNat 5262
    stack := UInt256.ofNat 32 :: returnRest sv ov }

def returnedState (n : Nat) (input : ByteArray) (sv ov : UInt256) : State :=
  { storedState n input sv ov with
    pc := UInt256.ofNat 5263
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
   pushAt 163 2 5202, opAt 164 .JUMPI]

def digestStorePath : List Located :=
  [opAt 4150 .JUMPDEST, opAt 4151 .CALLDATASIZE, pushAt 4152 1 63,
   opAt 4153 .EQ, pushAt 4154 2 5175, opAt 4155 .JUMPI,
   pushAt 4156 20 (paddedDigestWord 56),
   pushAt 4157 20 (UInt256.xor (paddedDigestWord 56) (paddedDigestWord 120)),
   opAt 4158 .CALLDATASIZE, pushAt 4159 1 120, opAt 4160 .EQ,
   opAt 4161 .MUL, opAt 4162 .XOR, pushAt 4163 0 0, opAt 4164 .MSTORE]

def digestFinishPath : List Located :=
  [pushAt 4166 0 0, opAt 4167 .RETURN]

@[simp] private theorem shortPC166 : Artifact.submissionArtifact.instructionPC 160 = 255 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem shortPC167 : Artifact.submissionArtifact.instructionPC 161 = 256 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem shortPC168 : Artifact.submissionArtifact.instructionPC 162 = 258 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem shortPC169 : Artifact.submissionArtifact.instructionPC 163 = 259 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem shortPC170 : Artifact.submissionArtifact.instructionPC 164 = 262 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem shortPC4181 : Artifact.submissionArtifact.instructionPC 4150 = 5202 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem shortPC4182 : Artifact.submissionArtifact.instructionPC 4151 = 5203 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem shortPC4183 : Artifact.submissionArtifact.instructionPC 4152 = 5204 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem shortPC4184 : Artifact.submissionArtifact.instructionPC 4153 = 5206 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem shortPC4185 : Artifact.submissionArtifact.instructionPC 4154 = 5207 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem shortPC4186 : Artifact.submissionArtifact.instructionPC 4155 = 5210 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem shortPC4187 : Artifact.submissionArtifact.instructionPC 4156 = 5211 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem shortPC4188 : Artifact.submissionArtifact.instructionPC 4157 = 5232 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem shortPC4189 : Artifact.submissionArtifact.instructionPC 4158 = 5253 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem shortPC4190 : Artifact.submissionArtifact.instructionPC 4159 = 5254 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem shortPC4191 : Artifact.submissionArtifact.instructionPC 4160 = 5256 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem shortPC4192 : Artifact.submissionArtifact.instructionPC 4161 = 5257 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem shortPC4193 : Artifact.submissionArtifact.instructionPC 4162 = 5258 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem shortPC4194 : Artifact.submissionArtifact.instructionPC 4163 = 5259 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem shortPC4195 : Artifact.submissionArtifact.instructionPC 4164 = 5260 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem shortPC4196 : Artifact.submissionArtifact.instructionPC 4165 = 5261 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem shortPC4197 : Artifact.submissionArtifact.instructionPC 4166 = 5262 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem shortPC4198 : Artifact.submissionArtifact.instructionPC 4167 = 5263 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

theorem run_selector (n : Nat) (input : ByteArray) (sv ov : UInt256)
    (hn : n = 56 ∨ n = 120) (hsize : input.size = n) :
    run selectorPath (selectorState n input sv ov) =
      some (digestEntryState n input sv ov) := by
  change run selectorPath (stS input 255 (returnRest sv ov)) =
    some (stS input 5202 (returnRest sv ov))
  have hdest : Decode.isValidJumpDest submissionBytecode 5202 = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 4150 (by rfl)
  have htrue : UInt256.isTrue (UInt256.gt 129 (UInt256.ofNat input.size)) := by
    rw [hsize]
    rcases hn with rfl | rfl <;> decide
  have h0 :
      Challenge.EvmProof.Stepper.runLocatedBlock
          [opAt 160 .CALLDATASIZE]
          (stS input 255 (returnRest sv ov)) =
        some (stS input 256 (UInt256.ofNat input.size :: returnRest sv ov)) := by
    exact blockOfS _
      (pcFactS input 160 255 _ (by norm_num) shortPC166)
      (stepS_calldatasize input 255 (returnRest sv ov)
        (by simp [returnRest]) (by norm_num))
  have h1 :
      Challenge.EvmProof.Stepper.runLocatedBlock
          [pushAt 161 1 129]
          (stS input 256 (UInt256.ofNat input.size :: returnRest sv ov)) =
        some (stS input 258 (129 :: UInt256.ofNat input.size :: returnRest sv ov)) := by
    exact blockOfS _
      (pcFactS input 161 256 _ (by norm_num) shortPC167)
      (stepS_push input 256 1 129
        (UInt256.ofNat input.size :: returnRest sv ov)
        (by simp [returnRest]) (by decide) (by decide) (by norm_num))
  have h2 :
      Challenge.EvmProof.Stepper.runLocatedBlock
          [opAt 162 .GT]
          (stS input 258 (129 :: UInt256.ofNat input.size :: returnRest sv ov)) =
        some (stS input 259
          (UInt256.gt 129 (UInt256.ofNat input.size) :: returnRest sv ov)) := by
    exact blockOfS _
      (pcFactS input 162 258 _ (by norm_num) shortPC168)
      (stepS_gt input 258 129 (UInt256.ofNat input.size) (returnRest sv ov)
        (by simp [returnRest]) (by norm_num))
  have h3 :
      Challenge.EvmProof.Stepper.runLocatedBlock
          [pushAt 163 2 5202]
          (stS input 259
            (UInt256.gt 129 (UInt256.ofNat input.size) :: returnRest sv ov)) =
        some (stS input 262
          (5202 :: UInt256.gt 129 (UInt256.ofNat input.size) :: returnRest sv ov)) := by
    exact blockOfS _
      (pcFactS input 163 259 _ (by norm_num) shortPC169)
      (stepS_push input 259 2 5202
        (UInt256.gt 129 (UInt256.ofNat input.size) :: returnRest sv ov)
        (by simp [returnRest]) (by decide) (by decide) (by norm_num))
  have h4 :
      Challenge.EvmProof.Stepper.runLocatedBlock
          [opAt 164 .JUMPI]
          (stS input 262
            (5202 :: UInt256.gt 129 (UInt256.ofNat input.size) :: returnRest sv ov)) =
        some (stS input 5202 (returnRest sv ov)) := by
    exact blockOfS _
      (pcFactS input 164 262 _ (by norm_num) shortPC170)
      (stepS_jumpi_taken input 262 5202 5202
        (UInt256.gt 129 (UInt256.ofNat input.size)) (returnRest sv ov)
        (by simp [returnRest]) (by norm_num) rfl htrue hdest)
  have h01 :
      Challenge.EvmProof.Stepper.runLocatedBlock
          [opAt 160 .CALLDATASIZE, pushAt 161 1 129]
          (stS input 255 (returnRest sv ov)) =
        some (stS input 258 (129 :: UInt256.ofNat input.size :: returnRest sv ov)) := by
    exact Challenge.EvmProof.Stepper.runLocatedBlock_append
      [opAt 160 .CALLDATASIZE] [pushAt 161 1 129]
      _ _ _ h0 (by rfl) h1
  have h012 :
      Challenge.EvmProof.Stepper.runLocatedBlock
          [opAt 160 .CALLDATASIZE, pushAt 161 1 129, opAt 162 .GT]
          (stS input 255 (returnRest sv ov)) =
        some (stS input 259
          (UInt256.gt 129 (UInt256.ofNat input.size) :: returnRest sv ov)) := by
    exact Challenge.EvmProof.Stepper.runLocatedBlock_append
      [opAt 160 .CALLDATASIZE, pushAt 161 1 129] [opAt 162 .GT]
      _ _ _ h01 (by rfl) h2
  have h0123 :
      Challenge.EvmProof.Stepper.runLocatedBlock
          [opAt 160 .CALLDATASIZE, pushAt 161 1 129, opAt 162 .GT,
            pushAt 163 2 5202]
          (stS input 255 (returnRest sv ov)) =
        some (stS input 262
          (5202 :: UInt256.gt 129 (UInt256.ofNat input.size) :: returnRest sv ov)) := by
    exact Challenge.EvmProof.Stepper.runLocatedBlock_append
      [opAt 160 .CALLDATASIZE, pushAt 161 1 129, opAt 162 .GT]
      [pushAt 163 2 5202] _ _ _ h012 (by rfl) h3
  have h01234 :
      Challenge.EvmProof.Stepper.runLocatedBlock
          [opAt 160 .CALLDATASIZE, pushAt 161 1 129, opAt 162 .GT,
            pushAt 163 2 5202, opAt 164 .JUMPI]
          (stS input 255 (returnRest sv ov)) =
        some (stS input 5202 (returnRest sv ov)) := by
    exact Challenge.EvmProof.Stepper.runLocatedBlock_append
      [opAt 160 .CALLDATASIZE, pushAt 161 1 129, opAt 162 .GT,
        pushAt 163 2 5202] [opAt 164 .JUMPI] _ _ _ h0123 (by rfl) h4
  simpa only [selectorPath] using h01234


end Challenge.Ripemd160.Submission.Proofs.Bytecode.ShortPatternFinish
