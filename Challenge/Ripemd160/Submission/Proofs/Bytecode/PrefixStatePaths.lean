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

@[simp] theorem pc4072 : Artifact.submissionArtifact.instructionPC 4067 = 5147 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4073 : Artifact.submissionArtifact.instructionPC 4068 = 5148 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4074 : Artifact.submissionArtifact.instructionPC 4069 = 5149 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4075 : Artifact.submissionArtifact.instructionPC 4070 = 5152 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4076 : Artifact.submissionArtifact.instructionPC 4071 = 5153 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4077 : Artifact.submissionArtifact.instructionPC 4072 = 5154 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4078 : Artifact.submissionArtifact.instructionPC 4073 = 5155 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4079 : Artifact.submissionArtifact.instructionPC 4074 = 5157 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4080 : Artifact.submissionArtifact.instructionPC 4075 = 5159 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4081 : Artifact.submissionArtifact.instructionPC 4076 = 5160 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4082 : Artifact.submissionArtifact.instructionPC 4077 = 5161 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4083 : Artifact.submissionArtifact.instructionPC 4078 = 5162 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4084 : Artifact.submissionArtifact.instructionPC 4079 = 5163 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4085 : Artifact.submissionArtifact.instructionPC 4080 = 5164 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4086 : Artifact.submissionArtifact.instructionPC 4081 = 5167 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4087 : Artifact.submissionArtifact.instructionPC 4082 = 5168 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4088 : Artifact.submissionArtifact.instructionPC 4083 = 5170 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4089 : Artifact.submissionArtifact.instructionPC 4084 = 5171 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4090 : Artifact.submissionArtifact.instructionPC 4085 = 5204 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4091 : Artifact.submissionArtifact.instructionPC 4086 = 5205 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4092 : Artifact.submissionArtifact.instructionPC 4087 = 5208 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4093 : Artifact.submissionArtifact.instructionPC 4088 = 5209 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4094 : Artifact.submissionArtifact.instructionPC 4089 = 5210 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4095 : Artifact.submissionArtifact.instructionPC 4090 = 5211 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4096 : Artifact.submissionArtifact.instructionPC 4091 = 5216 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4097 : Artifact.submissionArtifact.instructionPC 4092 = 5218 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4098 : Artifact.submissionArtifact.instructionPC 4093 = 5219 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4099 : Artifact.submissionArtifact.instructionPC 4094 = 5224 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4100 : Artifact.submissionArtifact.instructionPC 4095 = 5226 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4101 : Artifact.submissionArtifact.instructionPC 4096 = 5227 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4102 : Artifact.submissionArtifact.instructionPC 4097 = 5232 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4103 : Artifact.submissionArtifact.instructionPC 4098 = 5234 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4104 : Artifact.submissionArtifact.instructionPC 4099 = 5235 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4105 : Artifact.submissionArtifact.instructionPC 4100 = 5240 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4106 : Artifact.submissionArtifact.instructionPC 4101 = 5242 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4107 : Artifact.submissionArtifact.instructionPC 4102 = 5243 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4108 : Artifact.submissionArtifact.instructionPC 4103 = 5248 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4109 : Artifact.submissionArtifact.instructionPC 4104 = 5250 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4110 : Artifact.submissionArtifact.instructionPC 4105 = 5251 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

def laterPath : List Located :=
  [⟨4067, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4068, .op (.Dup ⟨2, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4069, .push ⟨2, by decide⟩ (UInt256.ofNat 599), by rfl, by decide⟩,
   ⟨4070, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩]

def prefixPath : List Located :=
  [⟨4067, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4068, .op (.Dup ⟨2, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4069, .push ⟨2, by decide⟩ (UInt256.ofNat 599), by rfl, by decide⟩,
   ⟨4070, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4071, .push ⟨0, by decide⟩ (UInt256.ofNat 0), by rfl, by decide⟩,
   ⟨4072, .op .CALLDATALOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4073, .push ⟨1, by decide⟩ (UInt256.ofNat 32), by rfl, by decide⟩,
   ⟨4074, .push ⟨1, by decide⟩ (UInt256.ofNat 109), by rfl, by decide⟩,
   ⟨4075, .push ⟨0, by decide⟩ (UInt256.ofNat 0), by rfl, by decide⟩]

def firstComparePath : List Located :=
  [⟨4077, .push ⟨0, by decide⟩ (UInt256.ofNat 0), by rfl, by decide⟩,
   ⟨4078, .op .MLOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4079, .op .XOR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4080, .push ⟨2, by decide⟩ (UInt256.ofNat 599), by rfl, by decide⟩,
   ⟨4081, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩]

def secondComparePath : List Located :=
  [⟨4082, .push ⟨1, by decide⟩ (UInt256.ofNat 32), by rfl, by decide⟩,
   ⟨4083, .op .CALLDATALOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4084, .push ⟨32, by decide⟩ (UInt256.ofNat 75898346434861812577553744355519055536350986179947755549958789636940356975906), by rfl, by decide⟩,
   ⟨4085, .op .XOR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4086, .push ⟨2, by decide⟩ (UInt256.ofNat 599), by rfl, by decide⟩,
   ⟨4087, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩]

def hitPath : List Located :=
  [⟨4088, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4089, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4090, .push ⟨4, by decide⟩ (UInt256.ofNat 1080717082), by rfl, by decide⟩,
   ⟨4091, .push ⟨1, by decide⟩ (UInt256.ofNat 32), by rfl, by decide⟩,
   ⟨4092, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4093, .push ⟨4, by decide⟩ (UInt256.ofNat 2391128076), by rfl, by decide⟩,
   ⟨4094, .push ⟨1, by decide⟩ (UInt256.ofNat 64), by rfl, by decide⟩,
   ⟨4095, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4096, .push ⟨4, by decide⟩ (UInt256.ofNat 621343384), by rfl, by decide⟩,
   ⟨4097, .push ⟨1, by decide⟩ (UInt256.ofNat 96), by rfl, by decide⟩,
   ⟨4098, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4099, .push ⟨4, by decide⟩ (UInt256.ofNat 220066081), by rfl, by decide⟩,
   ⟨4100, .push ⟨1, by decide⟩ (UInt256.ofNat 128), by rfl, by decide⟩,
   ⟨4101, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4102, .push ⟨4, by decide⟩ (UInt256.ofNat 1007308478), by rfl, by decide⟩,
   ⟨4103, .push ⟨1, by decide⟩ (UInt256.ofNat 160), by rfl, by decide⟩,
   ⟨4104, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4105, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PrefixStatePaths
