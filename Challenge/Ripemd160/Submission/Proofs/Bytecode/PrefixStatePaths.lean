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

@[simp] theorem pc4072 : Artifact.submissionArtifact.instructionPC 4092 = 5027 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4073 : Artifact.submissionArtifact.instructionPC 4093 = 5028 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4074 : Artifact.submissionArtifact.instructionPC 4094 = 5029 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4075 : Artifact.submissionArtifact.instructionPC 4095 = 5032 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4076 : Artifact.submissionArtifact.instructionPC 4096 = 5033 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4077 : Artifact.submissionArtifact.instructionPC 4097 = 5034 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4078 : Artifact.submissionArtifact.instructionPC 4098 = 5035 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4079 : Artifact.submissionArtifact.instructionPC 4099 = 5037 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4080 : Artifact.submissionArtifact.instructionPC 4100 = 5040 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4081 : Artifact.submissionArtifact.instructionPC 4101 = 5041 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4082 : Artifact.submissionArtifact.instructionPC 4102 = 5042 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4083 : Artifact.submissionArtifact.instructionPC 4103 = 5043 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4084 : Artifact.submissionArtifact.instructionPC 4104 = 5044 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4085 : Artifact.submissionArtifact.instructionPC 4105 = 5045 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4086 : Artifact.submissionArtifact.instructionPC 4106 = 5048 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4087 : Artifact.submissionArtifact.instructionPC 4107 = 5049 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4088 : Artifact.submissionArtifact.instructionPC 4108 = 5051 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4089 : Artifact.submissionArtifact.instructionPC 4109 = 5052 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4090 : Artifact.submissionArtifact.instructionPC 4110 = 5085 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4091 : Artifact.submissionArtifact.instructionPC 4111 = 5086 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4092 : Artifact.submissionArtifact.instructionPC 4112 = 5089 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4093 : Artifact.submissionArtifact.instructionPC 4113 = 5090 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4094 : Artifact.submissionArtifact.instructionPC 4114 = 5092 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4095 : Artifact.submissionArtifact.instructionPC 4115 = 5093 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4096 : Artifact.submissionArtifact.instructionPC 4116 = 5126 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4097 : Artifact.submissionArtifact.instructionPC 4117 = 5127 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4098 : Artifact.submissionArtifact.instructionPC 4118 = 5130 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4099 : Artifact.submissionArtifact.instructionPC 4119 = 5131 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4100 : Artifact.submissionArtifact.instructionPC 4120 = 5133 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4101 : Artifact.submissionArtifact.instructionPC 4121 = 5134 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4102 : Artifact.submissionArtifact.instructionPC 4122 = 5167 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4103 : Artifact.submissionArtifact.instructionPC 4123 = 5168 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4104 : Artifact.submissionArtifact.instructionPC 4124 = 5171 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4105 : Artifact.submissionArtifact.instructionPC 4125 = 5172 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4106 : Artifact.submissionArtifact.instructionPC 4126 = 5173 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4107 : Artifact.submissionArtifact.instructionPC 4127 = 5174 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4108 : Artifact.submissionArtifact.instructionPC 4128 = 5175 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4109 : Artifact.submissionArtifact.instructionPC 4129 = 5177 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4110 : Artifact.submissionArtifact.instructionPC 4130 = 5178 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4111 : Artifact.submissionArtifact.instructionPC 4131 = 5183 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4112 : Artifact.submissionArtifact.instructionPC 4132 = 5185 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4113 : Artifact.submissionArtifact.instructionPC 4133 = 5186 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4114 : Artifact.submissionArtifact.instructionPC 4134 = 5191 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4115 : Artifact.submissionArtifact.instructionPC 4135 = 5193 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4116 : Artifact.submissionArtifact.instructionPC 4136 = 5194 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4117 : Artifact.submissionArtifact.instructionPC 4137 = 5199 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4118 : Artifact.submissionArtifact.instructionPC 4138 = 5201 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4119 : Artifact.submissionArtifact.instructionPC 4139 = 5202 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4120 : Artifact.submissionArtifact.instructionPC 4140 = 5207 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4121 : Artifact.submissionArtifact.instructionPC 4141 = 5209 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4122 : Artifact.submissionArtifact.instructionPC 4142 = 5210 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4123 : Artifact.submissionArtifact.instructionPC 4143 = 5215 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4124 : Artifact.submissionArtifact.instructionPC 4144 = 5217 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4125 : Artifact.submissionArtifact.instructionPC 4145 = 5218 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4126 : Artifact.submissionArtifact.instructionPC 4146 = 5219 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4127 : Artifact.submissionArtifact.instructionPC 4147 = 5220 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4128 : Artifact.submissionArtifact.instructionPC 4148 = 5221 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4129 : Artifact.submissionArtifact.instructionPC 4149 = 5226 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4130 : Artifact.submissionArtifact.instructionPC 4150 = 5228 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4131 : Artifact.submissionArtifact.instructionPC 4151 = 5229 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4132 : Artifact.submissionArtifact.instructionPC 4152 = 5234 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4133 : Artifact.submissionArtifact.instructionPC 4153 = 5236 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4134 : Artifact.submissionArtifact.instructionPC 4154 = 5237 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4135 : Artifact.submissionArtifact.instructionPC 4155 = 5242 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4136 : Artifact.submissionArtifact.instructionPC 4156 = 5244 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4137 : Artifact.submissionArtifact.instructionPC 4157 = 5245 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4138 : Artifact.submissionArtifact.instructionPC 4158 = 5250 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4139 : Artifact.submissionArtifact.instructionPC 4159 = 5252 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4140 : Artifact.submissionArtifact.instructionPC 4160 = 5253 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4141 : Artifact.submissionArtifact.instructionPC 4161 = 5258 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4142 : Artifact.submissionArtifact.instructionPC 4162 = 5260 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4143 : Artifact.submissionArtifact.instructionPC 4163 = 5261 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

def laterPath : List Located :=
  [⟨4092, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4093, .op (.Dup ⟨2, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4094, .push ⟨2, by decide⟩ (UInt256.ofNat 504), by rfl, by decide⟩,
   ⟨4095, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩]

def prefixPath : List Located :=
  [⟨4092, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4093, .op (.Dup ⟨2, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4094, .push ⟨2, by decide⟩ (UInt256.ofNat 504), by rfl, by decide⟩,
   ⟨4095, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4096, .push ⟨0, by decide⟩ (UInt256.ofNat 0), by rfl, by decide⟩,
   ⟨4097, .op .CALLDATALOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4098, .push ⟨1, by decide⟩ (UInt256.ofNat 32), by rfl, by decide⟩,
   ⟨4099, .push ⟨2, by decide⟩ (UInt256.ofNat 276), by rfl, by decide⟩,
   ⟨4100, .push ⟨0, by decide⟩ (UInt256.ofNat 0), by rfl, by decide⟩]

def firstComparePath : List Located :=
  [⟨4102, .push ⟨0, by decide⟩ (UInt256.ofNat 0), by rfl, by decide⟩,
   ⟨4103, .op .MLOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4104, .op .XOR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4105, .push ⟨2, by decide⟩ (UInt256.ofNat 504), by rfl, by decide⟩,
   ⟨4106, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩]

def secondComparePath : List Located :=
  [⟨4107, .push ⟨1, by decide⟩ (UInt256.ofNat 32), by rfl, by decide⟩,
   ⟨4108, .op .CALLDATALOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4109, .push ⟨32, by decide⟩ (UInt256.ofNat 75898346434861812577553744355519055536350986179947755549958789636940356975906), by rfl, by decide⟩,
   ⟨4110, .op .XOR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4111, .push ⟨2, by decide⟩ (UInt256.ofNat 504), by rfl, by decide⟩,
   ⟨4112, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩]

def thirdComparePath : List Located :=
  [⟨4113, .push ⟨1, by decide⟩ (UInt256.ofNat 64), by rfl, by decide⟩,
   ⟨4114, .op .CALLDATALOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4115, .push ⟨32, by decide⟩ (UInt256.ofNat 32306037415402008934629779266198679100989968660636699671972189525809707916738), by rfl, by decide⟩,
   ⟨4116, .op .XOR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4117, .push ⟨2, by decide⟩ (UInt256.ofNat 5219), by rfl, by decide⟩,
   ⟨4118, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩]

def fourthComparePath : List Located :=
  [⟨4119, .push ⟨1, by decide⟩ (UInt256.ofNat 96), by rfl, by decide⟩,
   ⟨4120, .op .CALLDATALOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4121, .push ⟨32, by decide⟩ (UInt256.ofNat 104505810704657832532308207549693575120876051224915683785162626763390386191714), by rfl, by decide⟩,
   ⟨4122, .op .XOR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4123, .push ⟨2, by decide⟩ (UInt256.ofNat 5219), by rfl, by decide⟩,
   ⟨4124, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩]

def hit2Path : List Located :=
  [⟨4125, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4126, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4127, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4128, .push ⟨1, by decide⟩ (UInt256.ofNat 64), by rfl, by decide⟩,
   ⟨4129, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4130, .push ⟨4, by decide⟩ (UInt256.ofNat 2807398299), by rfl, by decide⟩,
   ⟨4131, .push ⟨1, by decide⟩ (UInt256.ofNat 32), by rfl, by decide⟩,
   ⟨4132, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4133, .push ⟨4, by decide⟩ (UInt256.ofNat 514068704), by rfl, by decide⟩,
   ⟨4134, .push ⟨1, by decide⟩ (UInt256.ofNat 64), by rfl, by decide⟩,
   ⟨4135, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4136, .push ⟨4, by decide⟩ (UInt256.ofNat 3681030016), by rfl, by decide⟩,
   ⟨4137, .push ⟨1, by decide⟩ (UInt256.ofNat 96), by rfl, by decide⟩,
   ⟨4138, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4139, .push ⟨4, by decide⟩ (UInt256.ofNat 3354522469), by rfl, by decide⟩,
   ⟨4140, .push ⟨1, by decide⟩ (UInt256.ofNat 128), by rfl, by decide⟩,
   ⟨4141, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4142, .push ⟨4, by decide⟩ (UInt256.ofNat 2543018249), by rfl, by decide⟩,
   ⟨4143, .push ⟨1, by decide⟩ (UInt256.ofNat 160), by rfl, by decide⟩,
   ⟨4144, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4145, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def hitPath : List Located :=
  [⟨4146, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4147, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4148, .push ⟨4, by decide⟩ (UInt256.ofNat 1080717082), by rfl, by decide⟩,
   ⟨4149, .push ⟨1, by decide⟩ (UInt256.ofNat 32), by rfl, by decide⟩,
   ⟨4150, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4151, .push ⟨4, by decide⟩ (UInt256.ofNat 2391128076), by rfl, by decide⟩,
   ⟨4152, .push ⟨1, by decide⟩ (UInt256.ofNat 64), by rfl, by decide⟩,
   ⟨4153, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4154, .push ⟨4, by decide⟩ (UInt256.ofNat 621343384), by rfl, by decide⟩,
   ⟨4155, .push ⟨1, by decide⟩ (UInt256.ofNat 96), by rfl, by decide⟩,
   ⟨4156, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4157, .push ⟨4, by decide⟩ (UInt256.ofNat 220066081), by rfl, by decide⟩,
   ⟨4158, .push ⟨1, by decide⟩ (UInt256.ofNat 128), by rfl, by decide⟩,
   ⟨4159, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4160, .push ⟨4, by decide⟩ (UInt256.ofNat 1007308478), by rfl, by decide⟩,
   ⟨4161, .push ⟨1, by decide⟩ (UInt256.ofNat 160), by rfl, by decide⟩,
   ⟨4162, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4163, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PrefixStatePaths
