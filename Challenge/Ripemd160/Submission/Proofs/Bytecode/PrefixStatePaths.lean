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

@[simp] theorem pc4072 : Artifact.submissionArtifact.instructionPC 4071 = 4964 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4073 : Artifact.submissionArtifact.instructionPC 4072 = 4965 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4074 : Artifact.submissionArtifact.instructionPC 4073 = 4966 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4075 : Artifact.submissionArtifact.instructionPC 4074 = 4969 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4076 : Artifact.submissionArtifact.instructionPC 4075 = 4970 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4077 : Artifact.submissionArtifact.instructionPC 4076 = 4971 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4078 : Artifact.submissionArtifact.instructionPC 4077 = 4972 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4079 : Artifact.submissionArtifact.instructionPC 4078 = 4974 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4080 : Artifact.submissionArtifact.instructionPC 4079 = 4977 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4081 : Artifact.submissionArtifact.instructionPC 4080 = 4978 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4082 : Artifact.submissionArtifact.instructionPC 4081 = 4979 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4083 : Artifact.submissionArtifact.instructionPC 4082 = 4980 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4084 : Artifact.submissionArtifact.instructionPC 4083 = 4981 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4085 : Artifact.submissionArtifact.instructionPC 4084 = 4982 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4086 : Artifact.submissionArtifact.instructionPC 4085 = 4985 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4087 : Artifact.submissionArtifact.instructionPC 4086 = 4986 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4088 : Artifact.submissionArtifact.instructionPC 4087 = 4988 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4089 : Artifact.submissionArtifact.instructionPC 4088 = 4989 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4090 : Artifact.submissionArtifact.instructionPC 4089 = 5022 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4091 : Artifact.submissionArtifact.instructionPC 4090 = 5023 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4092 : Artifact.submissionArtifact.instructionPC 4091 = 5026 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4093 : Artifact.submissionArtifact.instructionPC 4092 = 5027 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4094 : Artifact.submissionArtifact.instructionPC 4175 = 5139 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4095 : Artifact.submissionArtifact.instructionPC 4175 = 5139 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4096 : Artifact.submissionArtifact.instructionPC 4175 = 5139 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4097 : Artifact.submissionArtifact.instructionPC 4175 = 5139 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4098 : Artifact.submissionArtifact.instructionPC 4175 = 5139 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4099 : Artifact.submissionArtifact.instructionPC 4175 = 5139 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4100 : Artifact.submissionArtifact.instructionPC 4175 = 5139 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4101 : Artifact.submissionArtifact.instructionPC 4175 = 5139 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4102 : Artifact.submissionArtifact.instructionPC 4175 = 5139 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4103 : Artifact.submissionArtifact.instructionPC 4175 = 5139 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4104 : Artifact.submissionArtifact.instructionPC 4175 = 5139 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4105 : Artifact.submissionArtifact.instructionPC 4175 = 5139 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4106 : Artifact.submissionArtifact.instructionPC 4176 = 5140 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4107 : Artifact.submissionArtifact.instructionPC 4177 = 5141 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4108 : Artifact.submissionArtifact.instructionPC 4178 = 5142 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4109 : Artifact.submissionArtifact.instructionPC 4179 = 5144 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4110 : Artifact.submissionArtifact.instructionPC 4180 = 5145 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4111 : Artifact.submissionArtifact.instructionPC 4181 = 5150 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4112 : Artifact.submissionArtifact.instructionPC 4182 = 5152 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4113 : Artifact.submissionArtifact.instructionPC 4183 = 5153 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4114 : Artifact.submissionArtifact.instructionPC 4184 = 5158 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4115 : Artifact.submissionArtifact.instructionPC 4185 = 5160 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4116 : Artifact.submissionArtifact.instructionPC 4186 = 5161 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4117 : Artifact.submissionArtifact.instructionPC 4187 = 5166 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4118 : Artifact.submissionArtifact.instructionPC 4188 = 5168 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4119 : Artifact.submissionArtifact.instructionPC 4189 = 5169 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4120 : Artifact.submissionArtifact.instructionPC 4190 = 5174 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4121 : Artifact.submissionArtifact.instructionPC 4191 = 5176 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4122 : Artifact.submissionArtifact.instructionPC 4192 = 5177 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4123 : Artifact.submissionArtifact.instructionPC 4193 = 5182 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4124 : Artifact.submissionArtifact.instructionPC 4194 = 5184 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4125 : Artifact.submissionArtifact.instructionPC 4195 = 5185 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4126 : Artifact.submissionArtifact.instructionPC 4196 = 5186 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4127 : Artifact.submissionArtifact.instructionPC 4197 = 5187 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4128 : Artifact.submissionArtifact.instructionPC 4198 = 5188 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4129 : Artifact.submissionArtifact.instructionPC 4199 = 5193 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4130 : Artifact.submissionArtifact.instructionPC 4200 = 5195 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4131 : Artifact.submissionArtifact.instructionPC 4201 = 5196 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4132 : Artifact.submissionArtifact.instructionPC 4202 = 5201 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4133 : Artifact.submissionArtifact.instructionPC 4203 = 5203 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4134 : Artifact.submissionArtifact.instructionPC 4204 = 5204 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4135 : Artifact.submissionArtifact.instructionPC 4205 = 5209 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4136 : Artifact.submissionArtifact.instructionPC 4206 = 5211 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4137 : Artifact.submissionArtifact.instructionPC 4207 = 5212 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4138 : Artifact.submissionArtifact.instructionPC 4208 = 5217 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4139 : Artifact.submissionArtifact.instructionPC 4209 = 5219 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4140 : Artifact.submissionArtifact.instructionPC 4210 = 5220 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4141 : Artifact.submissionArtifact.instructionPC 4211 = 5225 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4142 : Artifact.submissionArtifact.instructionPC 4212 = 5227 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4143 : Artifact.submissionArtifact.instructionPC 4213 = 5228 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

def laterPath : List Located :=
  [⟨4071, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4072, .op (.Dup ⟨2, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4073, .push ⟨2, by decide⟩ (UInt256.ofNat 464), by rfl, by decide⟩,
   ⟨4074, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩]

def prefixPath : List Located :=
  [⟨4071, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4072, .op (.Dup ⟨2, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4073, .push ⟨2, by decide⟩ (UInt256.ofNat 464), by rfl, by decide⟩,
   ⟨4074, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4075, .push ⟨0, by decide⟩ (UInt256.ofNat 0), by rfl, by decide⟩,
   ⟨4076, .op .CALLDATALOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4077, .push ⟨1, by decide⟩ (UInt256.ofNat 32), by rfl, by decide⟩,
   ⟨4078, .push ⟨2, by decide⟩ (UInt256.ofNat 262), by rfl, by decide⟩,
   ⟨4079, .push ⟨0, by decide⟩ (UInt256.ofNat 0), by rfl, by decide⟩]

def firstComparePath : List Located :=
  [⟨4081, .push ⟨0, by decide⟩ (UInt256.ofNat 0), by rfl, by decide⟩,
   ⟨4082, .op .MLOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4083, .op .XOR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4084, .push ⟨2, by decide⟩ (UInt256.ofNat 464), by rfl, by decide⟩,
   ⟨4085, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩]

def secondComparePath : List Located :=
  [⟨4086, .push ⟨1, by decide⟩ (UInt256.ofNat 32), by rfl, by decide⟩,
   ⟨4087, .op .CALLDATALOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4088, .push ⟨32, by decide⟩ (UInt256.ofNat 75898346434861812577553744355519055536350986179947755549958789636940356975906), by rfl, by decide⟩,
   ⟨4089, .op .XOR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4090, .push ⟨2, by decide⟩ (UInt256.ofNat 464), by rfl, by decide⟩,
   ⟨4091, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩]



def hit2Path : List Located :=
  [⟨4175, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4176, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4177, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4178, .push ⟨1, by decide⟩ (UInt256.ofNat 192), by rfl, by decide⟩,
   ⟨4179, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4180, .push ⟨4, by decide⟩ (UInt256.ofNat 4072035125), by rfl, by decide⟩,
   ⟨4181, .push ⟨1, by decide⟩ (UInt256.ofNat 32), by rfl, by decide⟩,
   ⟨4182, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4183, .push ⟨4, by decide⟩ (UInt256.ofNat 1663407839), by rfl, by decide⟩,
   ⟨4184, .push ⟨1, by decide⟩ (UInt256.ofNat 64), by rfl, by decide⟩,
   ⟨4185, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4186, .push ⟨4, by decide⟩ (UInt256.ofNat 3044672391), by rfl, by decide⟩,
   ⟨4187, .push ⟨1, by decide⟩ (UInt256.ofNat 96), by rfl, by decide⟩,
   ⟨4188, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4189, .push ⟨4, by decide⟩ (UInt256.ofNat 4264519132), by rfl, by decide⟩,
   ⟨4190, .push ⟨1, by decide⟩ (UInt256.ofNat 128), by rfl, by decide⟩,
   ⟨4191, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4192, .push ⟨4, by decide⟩ (UInt256.ofNat 737150935), by rfl, by decide⟩,
   ⟨4193, .push ⟨1, by decide⟩ (UInt256.ofNat 160), by rfl, by decide⟩,
   ⟨4194, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4195, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def hitPath : List Located :=
  [⟨4196, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4197, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4198, .push ⟨4, by decide⟩ (UInt256.ofNat 1080717082), by rfl, by decide⟩,
   ⟨4199, .push ⟨1, by decide⟩ (UInt256.ofNat 32), by rfl, by decide⟩,
   ⟨4200, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4201, .push ⟨4, by decide⟩ (UInt256.ofNat 2391128076), by rfl, by decide⟩,
   ⟨4202, .push ⟨1, by decide⟩ (UInt256.ofNat 64), by rfl, by decide⟩,
   ⟨4203, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4204, .push ⟨4, by decide⟩ (UInt256.ofNat 621343384), by rfl, by decide⟩,
   ⟨4205, .push ⟨1, by decide⟩ (UInt256.ofNat 96), by rfl, by decide⟩,
   ⟨4206, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4207, .push ⟨4, by decide⟩ (UInt256.ofNat 220066081), by rfl, by decide⟩,
   ⟨4208, .push ⟨1, by decide⟩ (UInt256.ofNat 128), by rfl, by decide⟩,
   ⟨4209, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4210, .push ⟨4, by decide⟩ (UInt256.ofNat 1007308478), by rfl, by decide⟩,
   ⟨4211, .push ⟨1, by decide⟩ (UInt256.ofNat 160), by rfl, by decide⟩,
   ⟨4212, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4213, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]
def compactPreparePath : List Located :=
  [⟨4092, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4093, .push ⟨1, by decide⟩ (UInt256.ofNat 255), by rfl, by decide⟩,
   ⟨4094, .push ⟨0, by decide⟩ (UInt256.ofNat 0), by rfl, by decide⟩,
   ⟨4095, .op .NOT, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4096, .op .DIV, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4097, .push ⟨1, by decide⟩ (UInt256.ofNat 64), by rfl, by decide⟩,
   ⟨4098, .op .MUL, by rfl, wfOp (by decide) trivial rfl⟩]

def compactWord2Path : List Located :=
  [⟨4099, .push ⟨0, by decide⟩ (UInt256.ofNat 0), by rfl, by decide⟩,
   ⟨4100, .op .CALLDATALOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4101, .op (.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4102, .op (.Dup ⟨2, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4103, .op .AND, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4104, .op (.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4105, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4106, .op .XOR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4107, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4108, .op .XOR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4109, .push ⟨1, by decide⟩ (UInt256.ofNat 64), by rfl, by decide⟩,
   ⟨4110, .op .CALLDATALOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4111, .op .XOR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4112, .push ⟨2, by decide⟩ (UInt256.ofNat 5186), by rfl, by decide⟩,
   ⟨4113, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩]

def compactWord3Path : List Located :=
  [⟨4114, .push ⟨1, by decide⟩ (UInt256.ofNat 32), by rfl, by decide⟩,
   ⟨4115, .op .CALLDATALOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4116, .op (.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4117, .op (.Dup ⟨2, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4118, .op .AND, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4119, .op (.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4120, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4121, .op .XOR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4122, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4123, .op .XOR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4124, .push ⟨1, by decide⟩ (UInt256.ofNat 96), by rfl, by decide⟩,
   ⟨4125, .op .CALLDATALOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4126, .op .XOR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4127, .push ⟨2, by decide⟩ (UInt256.ofNat 5186), by rfl, by decide⟩,
   ⟨4128, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩]

def compactWord4Path : List Located :=
  [⟨4129, .push ⟨0, by decide⟩ (UInt256.ofNat 0), by rfl, by decide⟩,
   ⟨4130, .op .CALLDATALOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4131, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4132, .op (.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4133, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4134, .op .XOR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4135, .push ⟨1, by decide⟩ (UInt256.ofNat 128), by rfl, by decide⟩,
   ⟨4136, .op .CALLDATALOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4137, .op .XOR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4138, .push ⟨2, by decide⟩ (UInt256.ofNat 5186), by rfl, by decide⟩,
   ⟨4139, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩]

def compactWord5Path : List Located :=
  [⟨4140, .push ⟨1, by decide⟩ (UInt256.ofNat 32), by rfl, by decide⟩,
   ⟨4141, .op .CALLDATALOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4142, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4143, .op (.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4144, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4145, .op .XOR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4146, .push ⟨1, by decide⟩ (UInt256.ofNat 160), by rfl, by decide⟩,
   ⟨4147, .op .CALLDATALOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4148, .op .XOR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4149, .push ⟨2, by decide⟩ (UInt256.ofNat 5186), by rfl, by decide⟩,
   ⟨4150, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩]

def compactWord6Path : List Located :=
  [⟨4151, .push ⟨1, by decide⟩ (UInt256.ofNat 64), by rfl, by decide⟩,
   ⟨4152, .op .CALLDATALOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4153, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4154, .op (.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4155, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4156, .op .XOR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4157, .push ⟨1, by decide⟩ (UInt256.ofNat 192), by rfl, by decide⟩,
   ⟨4158, .op .CALLDATALOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4159, .op .XOR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4160, .push ⟨2, by decide⟩ (UInt256.ofNat 5186), by rfl, by decide⟩,
   ⟨4161, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩]

def compactWord7Path : List Located :=
  [⟨4162, .push ⟨1, by decide⟩ (UInt256.ofNat 96), by rfl, by decide⟩,
   ⟨4163, .op .CALLDATALOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4164, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4165, .op (.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4166, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4167, .op .XOR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4168, .push ⟨5, by decide⟩ (UInt256.ofNat 99006248207), by rfl, by decide⟩,
   ⟨4169, .op .XOR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4170, .push ⟨1, by decide⟩ (UInt256.ofNat 224), by rfl, by decide⟩,
   ⟨4171, .op .CALLDATALOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4172, .op .XOR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4173, .push ⟨2, by decide⟩ (UInt256.ofNat 5186), by rfl, by decide⟩,
   ⟨4174, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩]

@[simp] theorem compactPc4092 : Artifact.submissionArtifact.instructionPC 4092 = 5027 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem compactPc4093 : Artifact.submissionArtifact.instructionPC 4093 = 5028 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem compactPc4094 : Artifact.submissionArtifact.instructionPC 4094 = 5030 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem compactPc4095 : Artifact.submissionArtifact.instructionPC 4095 = 5031 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem compactPc4096 : Artifact.submissionArtifact.instructionPC 4096 = 5032 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem compactPc4097 : Artifact.submissionArtifact.instructionPC 4097 = 5033 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem compactPc4098 : Artifact.submissionArtifact.instructionPC 4098 = 5035 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem compactPc4099 : Artifact.submissionArtifact.instructionPC 4099 = 5036 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem compactPc4100 : Artifact.submissionArtifact.instructionPC 4100 = 5037 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem compactPc4101 : Artifact.submissionArtifact.instructionPC 4101 = 5038 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem compactPc4102 : Artifact.submissionArtifact.instructionPC 4102 = 5039 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem compactPc4103 : Artifact.submissionArtifact.instructionPC 4103 = 5040 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem compactPc4104 : Artifact.submissionArtifact.instructionPC 4104 = 5041 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem compactPc4105 : Artifact.submissionArtifact.instructionPC 4105 = 5042 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem compactPc4106 : Artifact.submissionArtifact.instructionPC 4106 = 5043 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem compactPc4107 : Artifact.submissionArtifact.instructionPC 4107 = 5044 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem compactPc4108 : Artifact.submissionArtifact.instructionPC 4108 = 5045 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem compactPc4109 : Artifact.submissionArtifact.instructionPC 4109 = 5046 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem compactPc4110 : Artifact.submissionArtifact.instructionPC 4110 = 5048 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem compactPc4111 : Artifact.submissionArtifact.instructionPC 4111 = 5049 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem compactPc4112 : Artifact.submissionArtifact.instructionPC 4112 = 5050 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem compactPc4113 : Artifact.submissionArtifact.instructionPC 4113 = 5053 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem compactPc4114 : Artifact.submissionArtifact.instructionPC 4114 = 5054 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem compactPc4115 : Artifact.submissionArtifact.instructionPC 4115 = 5056 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem compactPc4116 : Artifact.submissionArtifact.instructionPC 4116 = 5057 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem compactPc4117 : Artifact.submissionArtifact.instructionPC 4117 = 5058 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem compactPc4118 : Artifact.submissionArtifact.instructionPC 4118 = 5059 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem compactPc4119 : Artifact.submissionArtifact.instructionPC 4119 = 5060 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem compactPc4120 : Artifact.submissionArtifact.instructionPC 4120 = 5061 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem compactPc4121 : Artifact.submissionArtifact.instructionPC 4121 = 5062 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem compactPc4122 : Artifact.submissionArtifact.instructionPC 4122 = 5063 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem compactPc4123 : Artifact.submissionArtifact.instructionPC 4123 = 5064 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem compactPc4124 : Artifact.submissionArtifact.instructionPC 4124 = 5065 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem compactPc4125 : Artifact.submissionArtifact.instructionPC 4125 = 5067 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem compactPc4126 : Artifact.submissionArtifact.instructionPC 4126 = 5068 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem compactPc4127 : Artifact.submissionArtifact.instructionPC 4127 = 5069 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem compactPc4128 : Artifact.submissionArtifact.instructionPC 4128 = 5072 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem compactPc4129 : Artifact.submissionArtifact.instructionPC 4129 = 5073 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem compactPc4130 : Artifact.submissionArtifact.instructionPC 4130 = 5074 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem compactPc4131 : Artifact.submissionArtifact.instructionPC 4131 = 5075 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem compactPc4132 : Artifact.submissionArtifact.instructionPC 4132 = 5076 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem compactPc4133 : Artifact.submissionArtifact.instructionPC 4133 = 5077 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem compactPc4134 : Artifact.submissionArtifact.instructionPC 4134 = 5078 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem compactPc4135 : Artifact.submissionArtifact.instructionPC 4135 = 5079 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem compactPc4136 : Artifact.submissionArtifact.instructionPC 4136 = 5081 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem compactPc4137 : Artifact.submissionArtifact.instructionPC 4137 = 5082 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem compactPc4138 : Artifact.submissionArtifact.instructionPC 4138 = 5083 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem compactPc4139 : Artifact.submissionArtifact.instructionPC 4139 = 5086 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem compactPc4140 : Artifact.submissionArtifact.instructionPC 4140 = 5087 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem compactPc4141 : Artifact.submissionArtifact.instructionPC 4141 = 5089 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem compactPc4142 : Artifact.submissionArtifact.instructionPC 4142 = 5090 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem compactPc4143 : Artifact.submissionArtifact.instructionPC 4143 = 5091 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem compactPc4144 : Artifact.submissionArtifact.instructionPC 4144 = 5092 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem compactPc4145 : Artifact.submissionArtifact.instructionPC 4145 = 5093 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem compactPc4146 : Artifact.submissionArtifact.instructionPC 4146 = 5094 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem compactPc4147 : Artifact.submissionArtifact.instructionPC 4147 = 5096 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem compactPc4148 : Artifact.submissionArtifact.instructionPC 4148 = 5097 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem compactPc4149 : Artifact.submissionArtifact.instructionPC 4149 = 5098 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem compactPc4150 : Artifact.submissionArtifact.instructionPC 4150 = 5101 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem compactPc4151 : Artifact.submissionArtifact.instructionPC 4151 = 5102 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem compactPc4152 : Artifact.submissionArtifact.instructionPC 4152 = 5104 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem compactPc4153 : Artifact.submissionArtifact.instructionPC 4153 = 5105 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem compactPc4154 : Artifact.submissionArtifact.instructionPC 4154 = 5106 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem compactPc4155 : Artifact.submissionArtifact.instructionPC 4155 = 5107 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem compactPc4156 : Artifact.submissionArtifact.instructionPC 4156 = 5108 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem compactPc4157 : Artifact.submissionArtifact.instructionPC 4157 = 5109 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem compactPc4158 : Artifact.submissionArtifact.instructionPC 4158 = 5111 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem compactPc4159 : Artifact.submissionArtifact.instructionPC 4159 = 5112 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem compactPc4160 : Artifact.submissionArtifact.instructionPC 4160 = 5113 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem compactPc4161 : Artifact.submissionArtifact.instructionPC 4161 = 5116 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem compactPc4162 : Artifact.submissionArtifact.instructionPC 4162 = 5117 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem compactPc4163 : Artifact.submissionArtifact.instructionPC 4163 = 5119 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem compactPc4164 : Artifact.submissionArtifact.instructionPC 4164 = 5120 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem compactPc4165 : Artifact.submissionArtifact.instructionPC 4165 = 5121 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem compactPc4166 : Artifact.submissionArtifact.instructionPC 4166 = 5122 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem compactPc4167 : Artifact.submissionArtifact.instructionPC 4167 = 5123 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem compactPc4168 : Artifact.submissionArtifact.instructionPC 4168 = 5124 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem compactPc4169 : Artifact.submissionArtifact.instructionPC 4169 = 5130 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem compactPc4170 : Artifact.submissionArtifact.instructionPC 4170 = 5131 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem compactPc4171 : Artifact.submissionArtifact.instructionPC 4171 = 5133 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem compactPc4172 : Artifact.submissionArtifact.instructionPC 4172 = 5134 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem compactPc4173 : Artifact.submissionArtifact.instructionPC 4173 = 5135 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem compactPc4174 : Artifact.submissionArtifact.instructionPC 4174 = 5138 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem compactPc4175 : Artifact.submissionArtifact.instructionPC 4175 = 5139 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem compactPc4176 : Artifact.submissionArtifact.instructionPC 4176 = 5140 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem compactPc4177 : Artifact.submissionArtifact.instructionPC 4177 = 5141 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem compactPc4178 : Artifact.submissionArtifact.instructionPC 4178 = 5142 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem compactPc4179 : Artifact.submissionArtifact.instructionPC 4179 = 5144 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem compactPc4180 : Artifact.submissionArtifact.instructionPC 4180 = 5145 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem compactPc4181 : Artifact.submissionArtifact.instructionPC 4181 = 5150 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem compactPc4182 : Artifact.submissionArtifact.instructionPC 4182 = 5152 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem compactPc4183 : Artifact.submissionArtifact.instructionPC 4183 = 5153 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem compactPc4184 : Artifact.submissionArtifact.instructionPC 4184 = 5158 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem compactPc4185 : Artifact.submissionArtifact.instructionPC 4185 = 5160 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem compactPc4186 : Artifact.submissionArtifact.instructionPC 4186 = 5161 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem compactPc4187 : Artifact.submissionArtifact.instructionPC 4187 = 5166 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem compactPc4188 : Artifact.submissionArtifact.instructionPC 4188 = 5168 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem compactPc4189 : Artifact.submissionArtifact.instructionPC 4189 = 5169 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem compactPc4190 : Artifact.submissionArtifact.instructionPC 4190 = 5174 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem compactPc4191 : Artifact.submissionArtifact.instructionPC 4191 = 5176 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem compactPc4192 : Artifact.submissionArtifact.instructionPC 4192 = 5177 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem compactPc4193 : Artifact.submissionArtifact.instructionPC 4193 = 5182 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem compactPc4194 : Artifact.submissionArtifact.instructionPC 4194 = 5184 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem compactPc4195 : Artifact.submissionArtifact.instructionPC 4195 = 5185 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem compactPc4196 : Artifact.submissionArtifact.instructionPC 4196 = 5186 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem compactPc4197 : Artifact.submissionArtifact.instructionPC 4197 = 5187 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem compactPc4198 : Artifact.submissionArtifact.instructionPC 4198 = 5188 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem compactPc4199 : Artifact.submissionArtifact.instructionPC 4199 = 5193 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem compactPc4200 : Artifact.submissionArtifact.instructionPC 4200 = 5195 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem compactPc4201 : Artifact.submissionArtifact.instructionPC 4201 = 5196 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem compactPc4202 : Artifact.submissionArtifact.instructionPC 4202 = 5201 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem compactPc4203 : Artifact.submissionArtifact.instructionPC 4203 = 5203 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem compactPc4204 : Artifact.submissionArtifact.instructionPC 4204 = 5204 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem compactPc4205 : Artifact.submissionArtifact.instructionPC 4205 = 5209 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem compactPc4206 : Artifact.submissionArtifact.instructionPC 4206 = 5211 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem compactPc4207 : Artifact.submissionArtifact.instructionPC 4207 = 5212 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem compactPc4208 : Artifact.submissionArtifact.instructionPC 4208 = 5217 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem compactPc4209 : Artifact.submissionArtifact.instructionPC 4209 = 5219 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem compactPc4210 : Artifact.submissionArtifact.instructionPC 4210 = 5220 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem compactPc4211 : Artifact.submissionArtifact.instructionPC 4211 = 5225 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem compactPc4212 : Artifact.submissionArtifact.instructionPC 4212 = 5227 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem compactPc4213 : Artifact.submissionArtifact.instructionPC 4213 = 5228 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl


end Challenge.Ripemd160.Submission.Proofs.Bytecode.PrefixStatePaths
