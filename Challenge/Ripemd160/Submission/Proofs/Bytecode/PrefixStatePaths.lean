import Challenge.Ripemd160.Submission.Proofs.Bytecode.Artifact

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PrefixStatePaths
open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM

private def wfOp {op : Operation}
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op)
    (hplain : YulEvmCompiler.plainOp op)
    (havailable : op.availableInFork .Osaka = true) :
    Stepper.WellFormed .Osaka (.op op) := ⟨hopcode,hplain,havailable⟩

abbrev Located := Stepper.Located Artifact.submissionArtifact .Osaka

@[simp] theorem pc4072 : Artifact.submissionArtifact.instructionPC 4073 = 5156 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4073 : Artifact.submissionArtifact.instructionPC 4074 = 5157 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4074 : Artifact.submissionArtifact.instructionPC 4075 = 5158 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4075 : Artifact.submissionArtifact.instructionPC 4076 = 5161 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4076 : Artifact.submissionArtifact.instructionPC 4077 = 5162 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4077 : Artifact.submissionArtifact.instructionPC 4078 = 5163 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4078 : Artifact.submissionArtifact.instructionPC 4079 = 5164 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4079 : Artifact.submissionArtifact.instructionPC 4080 = 5166 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4080 : Artifact.submissionArtifact.instructionPC 4081 = 5168 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4081 : Artifact.submissionArtifact.instructionPC 4082 = 5169 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4082 : Artifact.submissionArtifact.instructionPC 4083 = 5170 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4083 : Artifact.submissionArtifact.instructionPC 4084 = 5171 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4084 : Artifact.submissionArtifact.instructionPC 4085 = 5172 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4085 : Artifact.submissionArtifact.instructionPC 4086 = 5173 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4086 : Artifact.submissionArtifact.instructionPC 4087 = 5176 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4087 : Artifact.submissionArtifact.instructionPC 4088 = 5177 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4088 : Artifact.submissionArtifact.instructionPC 4089 = 5179 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4089 : Artifact.submissionArtifact.instructionPC 4090 = 5180 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4090 : Artifact.submissionArtifact.instructionPC 4091 = 5213 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4091 : Artifact.submissionArtifact.instructionPC 4092 = 5214 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4092 : Artifact.submissionArtifact.instructionPC 4093 = 5217 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4093 : Artifact.submissionArtifact.instructionPC 4094 = 5218 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4094 : Artifact.submissionArtifact.instructionPC 4095 = 5219 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4095 : Artifact.submissionArtifact.instructionPC 4096 = 5220 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4096 : Artifact.submissionArtifact.instructionPC 4097 = 5225 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4097 : Artifact.submissionArtifact.instructionPC 4098 = 5227 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4098 : Artifact.submissionArtifact.instructionPC 4099 = 5228 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4099 : Artifact.submissionArtifact.instructionPC 4100 = 5233 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4100 : Artifact.submissionArtifact.instructionPC 4101 = 5235 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4101 : Artifact.submissionArtifact.instructionPC 4102 = 5236 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4102 : Artifact.submissionArtifact.instructionPC 4103 = 5241 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4103 : Artifact.submissionArtifact.instructionPC 4104 = 5243 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4104 : Artifact.submissionArtifact.instructionPC 4105 = 5244 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4105 : Artifact.submissionArtifact.instructionPC 4106 = 5249 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4106 : Artifact.submissionArtifact.instructionPC 4107 = 5251 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4107 : Artifact.submissionArtifact.instructionPC 4108 = 5252 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4108 : Artifact.submissionArtifact.instructionPC 4109 = 5257 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4109 : Artifact.submissionArtifact.instructionPC 4110 = 5259 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4110 : Artifact.submissionArtifact.instructionPC 4111 = 5260 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

def laterPath : List Located :=
  [⟨4073, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4074, .op (.Dup ⟨2, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4075, .push ⟨2, by decide⟩ (UInt256.ofNat 536), by rfl, by decide⟩,
   ⟨4076, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩]

def prefixPath : List Located :=
  [⟨4073, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4074, .op (.Dup ⟨2, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4075, .push ⟨2, by decide⟩ (UInt256.ofNat 536), by rfl, by decide⟩,
   ⟨4076, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4077, .push ⟨0, by decide⟩ (UInt256.ofNat 0), by rfl, by decide⟩,
   ⟨4078, .op .CALLDATALOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4079, .push ⟨1, by decide⟩ (UInt256.ofNat 32), by rfl, by decide⟩,
   ⟨4080, .push ⟨1, by decide⟩ (UInt256.ofNat 109), by rfl, by decide⟩,
   ⟨4081, .push ⟨0, by decide⟩ (UInt256.ofNat 0), by rfl, by decide⟩]

def firstComparePath : List Located :=
  [⟨4083, .push ⟨0, by decide⟩ (UInt256.ofNat 0), by rfl, by decide⟩,
   ⟨4084, .op .MLOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4085, .op .XOR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4086, .push ⟨2, by decide⟩ (UInt256.ofNat 536), by rfl, by decide⟩,
   ⟨4087, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩]

def secondComparePath : List Located :=
  [⟨4088, .push ⟨1, by decide⟩ (UInt256.ofNat 32), by rfl, by decide⟩,
   ⟨4089, .op .CALLDATALOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4090, .push ⟨32, by decide⟩ (UInt256.ofNat 75898346434861812577553744355519055536350986179947755549958789636940356975906), by rfl, by decide⟩,
   ⟨4091, .op .XOR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4092, .push ⟨2, by decide⟩ (UInt256.ofNat 536), by rfl, by decide⟩,
   ⟨4093, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩]

def hitPath : List Located :=
  [⟨4094, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4095, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4096, .push ⟨4, by decide⟩ (UInt256.ofNat 1080717082), by rfl, by decide⟩,
   ⟨4097, .push ⟨1, by decide⟩ (UInt256.ofNat 32), by rfl, by decide⟩,
   ⟨4098, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4099, .push ⟨4, by decide⟩ (UInt256.ofNat 2391128076), by rfl, by decide⟩,
   ⟨4100, .push ⟨1, by decide⟩ (UInt256.ofNat 64), by rfl, by decide⟩,
   ⟨4101, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4102, .push ⟨4, by decide⟩ (UInt256.ofNat 621343384), by rfl, by decide⟩,
   ⟨4103, .push ⟨1, by decide⟩ (UInt256.ofNat 96), by rfl, by decide⟩,
   ⟨4104, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4105, .push ⟨4, by decide⟩ (UInt256.ofNat 220066081), by rfl, by decide⟩,
   ⟨4106, .push ⟨1, by decide⟩ (UInt256.ofNat 128), by rfl, by decide⟩,
   ⟨4107, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4108, .push ⟨4, by decide⟩ (UInt256.ofNat 1007308478), by rfl, by decide⟩,
   ⟨4109, .push ⟨1, by decide⟩ (UInt256.ofNat 160), by rfl, by decide⟩,
   ⟨4110, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4111, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PrefixStatePaths
