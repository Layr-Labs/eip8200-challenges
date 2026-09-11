import Challenge.Ripemd160.Submission.Proofs.Bytecode.ScanDigest119
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ScanDigest64
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ScanDigest65
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ScanDigest128
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
  if n = 119 then 0x2b9567d684dc89cd54620e46029f5bda0ecab787 else
  if n = 56 then 0xd8e2e84bad19fc85dbadb55fa5467631ce141503 else
  if n = 120 then 0x4de20b6b1fb2af442370c40e53a50aca360fc3bc else
  if n = 64 then 0x8a14b0c89287b39b1a2f73aa79a1ce95b04e7817 else
  if n = 65 then 0x475272ba467ca6716dbb1c19a84de355f065829a else
  0x28dfaf14ed9953f49c7abb561308d0c64bc4c179

def paddedDigest (n : Nat) : ByteArray :=
  if n = 119 then ScanDigest119.paddedDigest else
  if n = 56 then ShortPatternDigest.paddedDigest56 else
  if n = 120 then ShortPatternDigest.paddedDigest120 else
  if n = 64 then ScanDigest64.paddedDigest else
  if n = 65 then ScanDigest65.paddedDigest else
  ScanDigest128.paddedDigest

def answerMemory (n : Nat) : ByteArray := storeWord ByteArray.empty 0 (paddedDigestWord n)

def returnRest (sv ov : UInt256) : List UInt256 :=
  [sv, ov, 0, P7, M, m7, P, m8]

def selectorState (_n : Nat) (input : ByteArray) (sv ov : UInt256) : State :=
  stS input 252 (returnRest sv ov)

def digestEntryState (_n : Nat) (input : ByteArray) (sv ov : UInt256) : State :=
  stS input 5086 (returnRest sv ov)

def storedState (n : Nat) (input : ByteArray) (sv ov : UInt256) : State :=
  { stS input 5253 (returnRest sv ov) with
    memory := answerMemory n
    activeWords := UInt256.ofNat 1 }

def sizedState (n : Nat) (input : ByteArray) (sv ov : UInt256) : State :=
  { storedState n input sv ov with
    pc := UInt256.ofNat 5254
    stack := UInt256.ofNat 32 :: returnRest sv ov }

def returnedState (n : Nat) (input : ByteArray) (sv ov : UInt256) : State :=
  { storedState n input sv ov with
    pc := UInt256.ofNat 5255
    halt := .Returned
    hReturn := MachineState.readPadded (answerMemory n) 0 32 }

@[simp] theorem paddedDigest_size (n : Nat) : (paddedDigest n).size = 32 := by
  unfold paddedDigest
  split_ifs <;> decide

theorem wordBytes_eq_paddedDigest (n : Nat) :
    Data.Bytes.natToBytesPadded (paddedDigestWord n).toNat 32 = paddedDigest n := by
  rw [Memory.natToBytesPadded_eq_natToBE]
  unfold paddedDigestWord paddedDigest
  split_ifs <;> decide

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
   pushAt 167 2 5086, opAt 168 .JUMPI]

def digestStorePath : List Located :=
  [opAt 4124 .JUMPDEST,
   opAt 4125 .CALLDATASIZE,
   pushAt 4126 1 63,
   opAt 4127 .EQ,
   pushAt 4128 2 5059,
   opAt 4129 .JUMPI,
   pushAt 4130 20 1238202210714422317976759695583289414507727951107,
   pushAt 4131 20 850659410468186504977334991669309773499464406719,
   opAt 4132 .CALLDATASIZE,
   pushAt 4133 1 120,
   opAt 4134 .EQ,
   opAt 4135 .MUL,
   opAt 4136 .XOR,
   pushAt 4137 20 473630937069108787209769674763880281686549359892,
   opAt 4138 .CALLDATASIZE,
   pushAt 4139 1 64,
   opAt 4140 .EQ,
   opAt 4141 .MUL,
   opAt 4142 .XOR,
   pushAt 4143 20 911667961328910638847190335121045590507535832985,
   opAt 4144 .CALLDATASIZE,
   pushAt 4145 1 65,
   opAt 4146 .EQ,
   opAt 4147 .MUL,
   opAt 4148 .XOR,
   pushAt 4149 20 1371524347839696630419077646800909883779375486074,
   opAt 4150 .CALLDATASIZE,
   pushAt 4151 1 128,
   opAt 4152 .EQ,
   opAt 4153 .MUL,
   opAt 4154 .XOR,
   pushAt 4155 20 1389951056525561605944277671456053382651509121668,
   opAt 4156 .CALLDATASIZE,
   pushAt 4157 1 119,
   opAt 4158 .EQ,
   opAt 4159 .MUL,
   opAt 4160 .XOR,
   pushAt 4161 0 0,
   opAt 4162 .MSTORE]

def digestFinishPath : List Located :=
  [pushAt 4164 0 0, opAt 4165 .RETURN]

@[simp] private theorem shortPC166 : Artifact.submissionArtifact.instructionPC 164 = 252 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem shortPC167 : Artifact.submissionArtifact.instructionPC 165 = 253 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem shortPC168 : Artifact.submissionArtifact.instructionPC 166 = 255 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem shortPC169 : Artifact.submissionArtifact.instructionPC 167 = 256 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem shortPC170 : Artifact.submissionArtifact.instructionPC 168 = 259 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem shortPC4181 : Artifact.submissionArtifact.instructionPC 4124 = 5086 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem shortPC4182 : Artifact.submissionArtifact.instructionPC 4125 = 5087 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem shortPC4183 : Artifact.submissionArtifact.instructionPC 4126 = 5088 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem shortPC4184 : Artifact.submissionArtifact.instructionPC 4127 = 5090 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem shortPC4185 : Artifact.submissionArtifact.instructionPC 4128 = 5091 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem shortPC4186 : Artifact.submissionArtifact.instructionPC 4129 = 5094 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem shortPC4187 : Artifact.submissionArtifact.instructionPC 4130 = 5095 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem shortPC4188 : Artifact.submissionArtifact.instructionPC 4131 = 5116 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem shortPC4189 : Artifact.submissionArtifact.instructionPC 4132 = 5137 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem shortPC4190 : Artifact.submissionArtifact.instructionPC 4133 = 5138 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem shortPC4191 : Artifact.submissionArtifact.instructionPC 4134 = 5140 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem shortPC4192 : Artifact.submissionArtifact.instructionPC 4135 = 5141 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem shortPC4193 : Artifact.submissionArtifact.instructionPC 4136 = 5142 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem shortPC4194 : Artifact.submissionArtifact.instructionPC 4161 = 5251 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem shortPC4195 : Artifact.submissionArtifact.instructionPC 4162 = 5252 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem shortPC4196 : Artifact.submissionArtifact.instructionPC 4163 = 5253 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem shortPC4197 : Artifact.submissionArtifact.instructionPC 4164 = 5254 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem shortPC4198 : Artifact.submissionArtifact.instructionPC 4165 = 5255 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem scanReturnPC4122 : Artifact.submissionArtifact.instructionPC 4137 = 5143 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem scanReturnPC4123 : Artifact.submissionArtifact.instructionPC 4138 = 5164 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem scanReturnPC4124 : Artifact.submissionArtifact.instructionPC 4139 = 5165 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem scanReturnPC4125 : Artifact.submissionArtifact.instructionPC 4140 = 5167 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem scanReturnPC4126 : Artifact.submissionArtifact.instructionPC 4141 = 5168 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem scanReturnPC4127 : Artifact.submissionArtifact.instructionPC 4142 = 5169 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem scanReturnPC4128 : Artifact.submissionArtifact.instructionPC 4143 = 5170 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem scanReturnPC4129 : Artifact.submissionArtifact.instructionPC 4144 = 5191 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem scanReturnPC4130 : Artifact.submissionArtifact.instructionPC 4145 = 5192 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem scanReturnPC4131 : Artifact.submissionArtifact.instructionPC 4146 = 5194 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem scanReturnPC4132 : Artifact.submissionArtifact.instructionPC 4147 = 5195 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem scanReturnPC4133 : Artifact.submissionArtifact.instructionPC 4148 = 5196 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem scanReturnPC4134 : Artifact.submissionArtifact.instructionPC 4149 = 5197 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem scanReturnPC4135 : Artifact.submissionArtifact.instructionPC 4150 = 5218 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem scanReturnPC4136 : Artifact.submissionArtifact.instructionPC 4151 = 5219 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem scanReturnPC4137 : Artifact.submissionArtifact.instructionPC 4152 = 5221 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem scanReturnPC4138 : Artifact.submissionArtifact.instructionPC 4153 = 5222 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem scanReturnPC4139 : Artifact.submissionArtifact.instructionPC 4154 = 5223 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem memo119pc4151 : Artifact.submissionArtifact.instructionPC 4155 = 5224 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem memo119pc4152 : Artifact.submissionArtifact.instructionPC 4156 = 5245 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem memo119pc4153 : Artifact.submissionArtifact.instructionPC 4157 = 5246 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem memo119pc4154 : Artifact.submissionArtifact.instructionPC 4158 = 5248 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem memo119pc4155 : Artifact.submissionArtifact.instructionPC 4159 = 5249 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem memo119pc4156 : Artifact.submissionArtifact.instructionPC 4160 = 5250 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

theorem run_selector (n : Nat) (input : ByteArray) (sv ov : UInt256)
    (hn : n = 56 ∨ n = 120 ∨ n = 64 ∨ n = 65 ∨ n = 128 ∨ n = 119) (hsize : input.size = n) :
    run selectorPath (selectorState n input sv ov) =
      some (digestEntryState n input sv ov) := by
  change run selectorPath (stS input 252 (returnRest sv ov)) =
    some (stS input 5086 (returnRest sv ov))
  have hdest : Decode.isValidJumpDest submissionBytecode 5086 = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 4124 (by rfl)
  have htrue : UInt256.isTrue (UInt256.gt 129 (UInt256.ofNat input.size)) := by
    rw [hsize]
    rcases hn with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have h0 :
      Challenge.EvmProof.Stepper.runLocatedBlock
          [opAt 164 .CALLDATASIZE]
          (stS input 252 (returnRest sv ov)) =
        some (stS input 253 (UInt256.ofNat input.size :: returnRest sv ov)) := by
    exact blockOfS _
      (pcFactS input 164 252 _ (by norm_num) shortPC166)
      (stepS_calldatasize input 252 (returnRest sv ov)
        (by simp [returnRest]) (by norm_num))
  have h1 :
      Challenge.EvmProof.Stepper.runLocatedBlock
          [pushAt 165 1 129]
          (stS input 253 (UInt256.ofNat input.size :: returnRest sv ov)) =
        some (stS input 255 (129 :: UInt256.ofNat input.size :: returnRest sv ov)) := by
    exact blockOfS _
      (pcFactS input 165 253 _ (by norm_num) shortPC167)
      (stepS_push input 253 1 129
        (UInt256.ofNat input.size :: returnRest sv ov)
        (by simp [returnRest]) (by decide) (by decide) (by norm_num))
  have h2 :
      Challenge.EvmProof.Stepper.runLocatedBlock
          [opAt 166 .GT]
          (stS input 255 (129 :: UInt256.ofNat input.size :: returnRest sv ov)) =
        some (stS input 256
          (UInt256.gt 129 (UInt256.ofNat input.size) :: returnRest sv ov)) := by
    exact blockOfS _
      (pcFactS input 166 255 _ (by norm_num) shortPC168)
      (stepS_gt input 255 129 (UInt256.ofNat input.size) (returnRest sv ov)
        (by simp [returnRest]) (by norm_num))
  have h3 :
      Challenge.EvmProof.Stepper.runLocatedBlock
          [pushAt 167 2 5086]
          (stS input 256
            (UInt256.gt 129 (UInt256.ofNat input.size) :: returnRest sv ov)) =
        some (stS input 259
          (5086 :: UInt256.gt 129 (UInt256.ofNat input.size) :: returnRest sv ov)) := by
    exact blockOfS _
      (pcFactS input 167 256 _ (by norm_num) shortPC169)
      (stepS_push input 256 2 5086
        (UInt256.gt 129 (UInt256.ofNat input.size) :: returnRest sv ov)
        (by simp [returnRest]) (by decide) (by decide) (by norm_num))
  have h4 :
      Challenge.EvmProof.Stepper.runLocatedBlock
          [opAt 168 .JUMPI]
          (stS input 259
            (5086 :: UInt256.gt 129 (UInt256.ofNat input.size) :: returnRest sv ov)) =
        some (stS input 5086 (returnRest sv ov)) := by
    exact blockOfS _
      (pcFactS input 168 259 _ (by norm_num) shortPC170)
      (stepS_jumpi_taken input 259 5086 5086
        (UInt256.gt 129 (UInt256.ofNat input.size)) (returnRest sv ov)
        (by simp [returnRest]) (by norm_num) rfl htrue hdest)
  have h01 :
      Challenge.EvmProof.Stepper.runLocatedBlock
          [opAt 164 .CALLDATASIZE, pushAt 165 1 129]
          (stS input 252 (returnRest sv ov)) =
        some (stS input 255 (129 :: UInt256.ofNat input.size :: returnRest sv ov)) := by
    exact Challenge.EvmProof.Stepper.runLocatedBlock_append
      [opAt 164 .CALLDATASIZE] [pushAt 165 1 129]
      _ _ _ h0 (by rfl) h1
  have h012 :
      Challenge.EvmProof.Stepper.runLocatedBlock
          [opAt 164 .CALLDATASIZE, pushAt 165 1 129, opAt 166 .GT]
          (stS input 252 (returnRest sv ov)) =
        some (stS input 256
          (UInt256.gt 129 (UInt256.ofNat input.size) :: returnRest sv ov)) := by
    exact Challenge.EvmProof.Stepper.runLocatedBlock_append
      [opAt 164 .CALLDATASIZE, pushAt 165 1 129] [opAt 166 .GT]
      _ _ _ h01 (by rfl) h2
  have h0123 :
      Challenge.EvmProof.Stepper.runLocatedBlock
          [opAt 164 .CALLDATASIZE, pushAt 165 1 129, opAt 166 .GT,
            pushAt 167 2 5086]
          (stS input 252 (returnRest sv ov)) =
        some (stS input 259
          (5086 :: UInt256.gt 129 (UInt256.ofNat input.size) :: returnRest sv ov)) := by
    exact Challenge.EvmProof.Stepper.runLocatedBlock_append
      [opAt 164 .CALLDATASIZE, pushAt 165 1 129, opAt 166 .GT]
      [pushAt 167 2 5086] _ _ _ h012 (by rfl) h3
  have h01234 :
      Challenge.EvmProof.Stepper.runLocatedBlock
          [opAt 164 .CALLDATASIZE, pushAt 165 1 129, opAt 166 .GT,
            pushAt 167 2 5086, opAt 168 .JUMPI]
          (stS input 252 (returnRest sv ov)) =
        some (stS input 5086 (returnRest sv ov)) := by
    exact Challenge.EvmProof.Stepper.runLocatedBlock_append
      [opAt 164 .CALLDATASIZE, pushAt 165 1 129, opAt 166 .GT,
        pushAt 167 2 5086] [opAt 168 .JUMPI] _ _ _ h0123 (by rfl) h4
  simpa only [selectorPath] using h01234


end Challenge.Ripemd160.Submission.Proofs.Bytecode.ShortPatternFinish
