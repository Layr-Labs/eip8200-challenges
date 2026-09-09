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

@[simp] theorem pc4072 : Artifact.submissionArtifact.instructionPC 4072 = 4990 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4073 : Artifact.submissionArtifact.instructionPC 4073 = 4991 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4074 : Artifact.submissionArtifact.instructionPC 4074 = 4992 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4075 : Artifact.submissionArtifact.instructionPC 4075 = 4995 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4076 : Artifact.submissionArtifact.instructionPC 4076 = 4996 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4077 : Artifact.submissionArtifact.instructionPC 4077 = 4997 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4078 : Artifact.submissionArtifact.instructionPC 4078 = 4998 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4079 : Artifact.submissionArtifact.instructionPC 4079 = 5000 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4080 : Artifact.submissionArtifact.instructionPC 4080 = 5003 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4081 : Artifact.submissionArtifact.instructionPC 4081 = 5004 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4082 : Artifact.submissionArtifact.instructionPC 4082 = 5005 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4083 : Artifact.submissionArtifact.instructionPC 4083 = 5006 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4084 : Artifact.submissionArtifact.instructionPC 4084 = 5007 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4085 : Artifact.submissionArtifact.instructionPC 4085 = 5008 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4086 : Artifact.submissionArtifact.instructionPC 4086 = 5011 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4087 : Artifact.submissionArtifact.instructionPC 4087 = 5012 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4088 : Artifact.submissionArtifact.instructionPC 4088 = 5014 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4089 : Artifact.submissionArtifact.instructionPC 4089 = 5015 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4090 : Artifact.submissionArtifact.instructionPC 4090 = 5048 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4091 : Artifact.submissionArtifact.instructionPC 4091 = 5049 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4092 : Artifact.submissionArtifact.instructionPC 4092 = 5052 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4093 : Artifact.submissionArtifact.instructionPC 4093 = 5053 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4094 : Artifact.submissionArtifact.instructionPC 4094 = 5055 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4095 : Artifact.submissionArtifact.instructionPC 4095 = 5056 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4096 : Artifact.submissionArtifact.instructionPC 4096 = 5089 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4097 : Artifact.submissionArtifact.instructionPC 4097 = 5090 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4098 : Artifact.submissionArtifact.instructionPC 4098 = 5093 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4099 : Artifact.submissionArtifact.instructionPC 4099 = 5094 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4100 : Artifact.submissionArtifact.instructionPC 4100 = 5096 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4101 : Artifact.submissionArtifact.instructionPC 4101 = 5097 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4102 : Artifact.submissionArtifact.instructionPC 4102 = 5130 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4103 : Artifact.submissionArtifact.instructionPC 4103 = 5131 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4104 : Artifact.submissionArtifact.instructionPC 4104 = 5134 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4105 : Artifact.submissionArtifact.instructionPC 4105 = 5135 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4106 : Artifact.submissionArtifact.instructionPC 4106 = 5137 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4107 : Artifact.submissionArtifact.instructionPC 4107 = 5138 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4108 : Artifact.submissionArtifact.instructionPC 4108 = 5171 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4109 : Artifact.submissionArtifact.instructionPC 4109 = 5172 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4110 : Artifact.submissionArtifact.instructionPC 4110 = 5175 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4111 : Artifact.submissionArtifact.instructionPC 4111 = 5176 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4112 : Artifact.submissionArtifact.instructionPC 4112 = 5177 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4113 : Artifact.submissionArtifact.instructionPC 4113 = 5178 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4114 : Artifact.submissionArtifact.instructionPC 4114 = 5179 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4115 : Artifact.submissionArtifact.instructionPC 4115 = 5180 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4116 : Artifact.submissionArtifact.instructionPC 4116 = 5181 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4117 : Artifact.submissionArtifact.instructionPC 4117 = 5182 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4118 : Artifact.submissionArtifact.instructionPC 4118 = 5183 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4119 : Artifact.submissionArtifact.instructionPC 4119 = 5184 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4120 : Artifact.submissionArtifact.instructionPC 4120 = 5185 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4121 : Artifact.submissionArtifact.instructionPC 4121 = 5187 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4122 : Artifact.submissionArtifact.instructionPC 4122 = 5188 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4123 : Artifact.submissionArtifact.instructionPC 4123 = 5193 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4124 : Artifact.submissionArtifact.instructionPC 4124 = 5195 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4125 : Artifact.submissionArtifact.instructionPC 4125 = 5196 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4126 : Artifact.submissionArtifact.instructionPC 4126 = 5201 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4127 : Artifact.submissionArtifact.instructionPC 4127 = 5203 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4128 : Artifact.submissionArtifact.instructionPC 4128 = 5204 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4129 : Artifact.submissionArtifact.instructionPC 4129 = 5209 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4130 : Artifact.submissionArtifact.instructionPC 4130 = 5211 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4131 : Artifact.submissionArtifact.instructionPC 4131 = 5212 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4132 : Artifact.submissionArtifact.instructionPC 4132 = 5217 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4133 : Artifact.submissionArtifact.instructionPC 4133 = 5219 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4134 : Artifact.submissionArtifact.instructionPC 4134 = 5220 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4135 : Artifact.submissionArtifact.instructionPC 4135 = 5225 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4136 : Artifact.submissionArtifact.instructionPC 4136 = 5227 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4137 : Artifact.submissionArtifact.instructionPC 4137 = 5228 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4138 : Artifact.submissionArtifact.instructionPC 4138 = 5229 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4139 : Artifact.submissionArtifact.instructionPC 4139 = 5230 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4140 : Artifact.submissionArtifact.instructionPC 4140 = 5231 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4141 : Artifact.submissionArtifact.instructionPC 4141 = 5236 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4142 : Artifact.submissionArtifact.instructionPC 4142 = 5238 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4143 : Artifact.submissionArtifact.instructionPC 4143 = 5239 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4144 : Artifact.submissionArtifact.instructionPC 4144 = 5244 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4145 : Artifact.submissionArtifact.instructionPC 4145 = 5246 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4146 : Artifact.submissionArtifact.instructionPC 4146 = 5247 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4147 : Artifact.submissionArtifact.instructionPC 4147 = 5252 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4148 : Artifact.submissionArtifact.instructionPC 4148 = 5254 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4149 : Artifact.submissionArtifact.instructionPC 4149 = 5255 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4150 : Artifact.submissionArtifact.instructionPC 4150 = 5260 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4151 : Artifact.submissionArtifact.instructionPC 4151 = 5262 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4152 : Artifact.submissionArtifact.instructionPC 4152 = 5263 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4153 : Artifact.submissionArtifact.instructionPC 4153 = 5268 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4154 : Artifact.submissionArtifact.instructionPC 4154 = 5270 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4155 : Artifact.submissionArtifact.instructionPC 4155 = 5271 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4156 : Artifact.submissionArtifact.instructionPC 4156 = 5272 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4157 : Artifact.submissionArtifact.instructionPC 4157 = 5273 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4158 : Artifact.submissionArtifact.instructionPC 4158 = 5275 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4159 : Artifact.submissionArtifact.instructionPC 4159 = 5276 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4160 : Artifact.submissionArtifact.instructionPC 4160 = 5309 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4161 : Artifact.submissionArtifact.instructionPC 4161 = 5310 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4162 : Artifact.submissionArtifact.instructionPC 4162 = 5313 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4163 : Artifact.submissionArtifact.instructionPC 4163 = 5314 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4164 : Artifact.submissionArtifact.instructionPC 4164 = 5315 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4165 : Artifact.submissionArtifact.instructionPC 4165 = 5316 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4166 : Artifact.submissionArtifact.instructionPC 4166 = 5317 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4167 : Artifact.submissionArtifact.instructionPC 4167 = 5319 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4168 : Artifact.submissionArtifact.instructionPC 4168 = 5320 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4169 : Artifact.submissionArtifact.instructionPC 4169 = 5325 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4170 : Artifact.submissionArtifact.instructionPC 4170 = 5327 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4171 : Artifact.submissionArtifact.instructionPC 4171 = 5328 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4172 : Artifact.submissionArtifact.instructionPC 4172 = 5333 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4173 : Artifact.submissionArtifact.instructionPC 4173 = 5335 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4174 : Artifact.submissionArtifact.instructionPC 4174 = 5336 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4175 : Artifact.submissionArtifact.instructionPC 4175 = 5341 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4176 : Artifact.submissionArtifact.instructionPC 4176 = 5343 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4177 : Artifact.submissionArtifact.instructionPC 4177 = 5344 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4178 : Artifact.submissionArtifact.instructionPC 4178 = 5349 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4179 : Artifact.submissionArtifact.instructionPC 4179 = 5351 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4180 : Artifact.submissionArtifact.instructionPC 4180 = 5352 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4181 : Artifact.submissionArtifact.instructionPC 4181 = 5357 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4182 : Artifact.submissionArtifact.instructionPC 4182 = 5359 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4183 : Artifact.submissionArtifact.instructionPC 4183 = 5360 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

def laterPath : List Located :=
  [  ⟨4072, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
  ⟨4073, .op (.Dup ⟨2, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
  ⟨4074, .push ⟨2, by decide⟩ (UInt256.ofNat 464), by rfl, by decide⟩,
  ⟨4075, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩]

def prefixPath : List Located :=
  [  ⟨4072, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
  ⟨4073, .op (.Dup ⟨2, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
  ⟨4074, .push ⟨2, by decide⟩ (UInt256.ofNat 464), by rfl, by decide⟩,
  ⟨4075, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩,
  ⟨4076, .push ⟨0, by decide⟩ (UInt256.ofNat 0), by rfl, by decide⟩,
  ⟨4077, .op .CALLDATALOAD, by rfl, wfOp (by decide) trivial rfl⟩,
  ⟨4078, .push ⟨1, by decide⟩ (UInt256.ofNat 32), by rfl, by decide⟩,
  ⟨4079, .push ⟨2, by decide⟩ (UInt256.ofNat 262), by rfl, by decide⟩,
  ⟨4080, .push ⟨0, by decide⟩ (UInt256.ofNat 0), by rfl, by decide⟩]

def firstComparePath : List Located :=
  [  ⟨4082, .push ⟨0, by decide⟩ (UInt256.ofNat 0), by rfl, by decide⟩,
  ⟨4083, .op .MLOAD, by rfl, wfOp (by decide) trivial rfl⟩,
  ⟨4084, .op .XOR, by rfl, wfOp (by decide) trivial rfl⟩,
  ⟨4085, .push ⟨2, by decide⟩ (UInt256.ofNat 464), by rfl, by decide⟩,
  ⟨4086, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩]

def secondComparePath : List Located :=
  [  ⟨4087, .push ⟨1, by decide⟩ (UInt256.ofNat 32), by rfl, by decide⟩,
  ⟨4088, .op .CALLDATALOAD, by rfl, wfOp (by decide) trivial rfl⟩,
  ⟨4089, .push ⟨32, by decide⟩ (UInt256.ofNat 75898346434861812577553744355519055536350986179947755549958789636940356975906), by rfl, by decide⟩,
  ⟨4090, .op .XOR, by rfl, wfOp (by decide) trivial rfl⟩,
  ⟨4091, .push ⟨2, by decide⟩ (UInt256.ofNat 464), by rfl, by decide⟩,
  ⟨4092, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩]

def thirdComparePath : List Located :=
  [  ⟨4093, .push ⟨1, by decide⟩ (UInt256.ofNat 64), by rfl, by decide⟩,
  ⟨4094, .op .CALLDATALOAD, by rfl, wfOp (by decide) trivial rfl⟩,
  ⟨4095, .push ⟨32, by decide⟩ (UInt256.ofNat 32306037415402008934629779266198679100989968660636699671972189525809707916738), by rfl, by decide⟩,
  ⟨4096, .op .XOR, by rfl, wfOp (by decide) trivial rfl⟩,
  ⟨4097, .push ⟨2, by decide⟩ (UInt256.ofNat 5229), by rfl, by decide⟩,
  ⟨4098, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩]

def fourthComparePath : List Located :=
  [  ⟨4099, .push ⟨1, by decide⟩ (UInt256.ofNat 96), by rfl, by decide⟩,
  ⟨4100, .op .CALLDATALOAD, by rfl, wfOp (by decide) trivial rfl⟩,
  ⟨4101, .push ⟨32, by decide⟩ (UInt256.ofNat 104505810704657832532308207549693575120876051224915683785162626763390386191714), by rfl, by decide⟩,
  ⟨4102, .op .XOR, by rfl, wfOp (by decide) trivial rfl⟩,
  ⟨4103, .push ⟨2, by decide⟩ (UInt256.ofNat 5229), by rfl, by decide⟩,
  ⟨4104, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩]

def fifthComparePath : List Located :=
  [  ⟨4105, .push ⟨1, by decide⟩ (UInt256.ofNat 128), by rfl, by decide⟩,
  ⟨4106, .op .CALLDATALOAD, by rfl, wfOp (by decide) trivial rfl⟩,
  ⟨4107, .push ⟨32, by decide⟩ (UInt256.ofNat 61367581353886127001238131413293229573374005415347599533452268822761471270146), by rfl, by decide⟩,
  ⟨4108, .op .EQ, by rfl, wfOp (by decide) trivial rfl⟩,
  ⟨4109, .push ⟨2, by decide⟩ (UInt256.ofNat 5272), by rfl, by decide⟩,
  ⟨4110, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩]

def fifthCompareMissPath : List Located :=
  fifthComparePath ++
    [  ⟨4111, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
      ⟨4112, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
      ⟨4113, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
      ⟨4114, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
      ⟨4115, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
      ⟨4116, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩]

def hit2Path : List Located :=
  [  ⟨4117, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
  ⟨4118, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
  ⟨4119, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
  ⟨4120, .push ⟨1, by decide⟩ (UInt256.ofNat 64), by rfl, by decide⟩,
  ⟨4121, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
  ⟨4122, .push ⟨4, by decide⟩ (UInt256.ofNat 2807398299), by rfl, by decide⟩,
  ⟨4123, .push ⟨1, by decide⟩ (UInt256.ofNat 32), by rfl, by decide⟩,
  ⟨4124, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
  ⟨4125, .push ⟨4, by decide⟩ (UInt256.ofNat 514068704), by rfl, by decide⟩,
  ⟨4126, .push ⟨1, by decide⟩ (UInt256.ofNat 64), by rfl, by decide⟩,
  ⟨4127, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
  ⟨4128, .push ⟨4, by decide⟩ (UInt256.ofNat 3681030016), by rfl, by decide⟩,
  ⟨4129, .push ⟨1, by decide⟩ (UInt256.ofNat 96), by rfl, by decide⟩,
  ⟨4130, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
  ⟨4131, .push ⟨4, by decide⟩ (UInt256.ofNat 3354522469), by rfl, by decide⟩,
  ⟨4132, .push ⟨1, by decide⟩ (UInt256.ofNat 128), by rfl, by decide⟩,
  ⟨4133, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
  ⟨4134, .push ⟨4, by decide⟩ (UInt256.ofNat 2543018249), by rfl, by decide⟩,
  ⟨4135, .push ⟨1, by decide⟩ (UInt256.ofNat 160), by rfl, by decide⟩,
  ⟨4136, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
  ⟨4137, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def hitPath : List Located :=
  [  ⟨4138, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
  ⟨4139, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
  ⟨4140, .push ⟨4, by decide⟩ (UInt256.ofNat 1080717082), by rfl, by decide⟩,
  ⟨4141, .push ⟨1, by decide⟩ (UInt256.ofNat 32), by rfl, by decide⟩,
  ⟨4142, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
  ⟨4143, .push ⟨4, by decide⟩ (UInt256.ofNat 2391128076), by rfl, by decide⟩,
  ⟨4144, .push ⟨1, by decide⟩ (UInt256.ofNat 64), by rfl, by decide⟩,
  ⟨4145, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
  ⟨4146, .push ⟨4, by decide⟩ (UInt256.ofNat 621343384), by rfl, by decide⟩,
  ⟨4147, .push ⟨1, by decide⟩ (UInt256.ofNat 96), by rfl, by decide⟩,
  ⟨4148, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
  ⟨4149, .push ⟨4, by decide⟩ (UInt256.ofNat 220066081), by rfl, by decide⟩,
  ⟨4150, .push ⟨1, by decide⟩ (UInt256.ofNat 128), by rfl, by decide⟩,
  ⟨4151, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
  ⟨4152, .push ⟨4, by decide⟩ (UInt256.ofNat 1007308478), by rfl, by decide⟩,
  ⟨4153, .push ⟨1, by decide⟩ (UInt256.ofNat 160), by rfl, by decide⟩,
  ⟨4154, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
  ⟨4155, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def h3ComparePath : List Located :=
  [  ⟨4156, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
  ⟨4157, .push ⟨1, by decide⟩ (UInt256.ofNat 160), by rfl, by decide⟩,
  ⟨4158, .op .CALLDATALOAD, by rfl, wfOp (by decide) trivial rfl⟩,
  ⟨4159, .push ⟨32, by decide⟩ (UInt256.ofNat 17775265432785288859418840296405106407947132191047579206632289663109943557538), by rfl, by decide⟩,
  ⟨4160, .op .XOR, by rfl, wfOp (by decide) trivial rfl⟩,
  ⟨4161, .push ⟨2, by decide⟩ (UInt256.ofNat 5182), by rfl, by decide⟩,
  ⟨4162, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩]

def h3InstallPath : List Located :=
  [  ⟨4163, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
  ⟨4164, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
  ⟨4165, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
  ⟨4166, .push ⟨1, by decide⟩ (UInt256.ofNat 128), by rfl, by decide⟩,
  ⟨4167, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
  ⟨4168, .push ⟨4, by decide⟩ (UInt256.ofNat 1393315003), by rfl, by decide⟩,
  ⟨4169, .push ⟨1, by decide⟩ (UInt256.ofNat 32), by rfl, by decide⟩,
  ⟨4170, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
  ⟨4171, .push ⟨4, by decide⟩ (UInt256.ofNat 695251451), by rfl, by decide⟩,
  ⟨4172, .push ⟨1, by decide⟩ (UInt256.ofNat 64), by rfl, by decide⟩,
  ⟨4173, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
  ⟨4174, .push ⟨4, by decide⟩ (UInt256.ofNat 358732556), by rfl, by decide⟩,
  ⟨4175, .push ⟨1, by decide⟩ (UInt256.ofNat 96), by rfl, by decide⟩,
  ⟨4176, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
  ⟨4177, .push ⟨4, by decide⟩ (UInt256.ofNat 928826907), by rfl, by decide⟩,
  ⟨4178, .push ⟨1, by decide⟩ (UInt256.ofNat 128), by rfl, by decide⟩,
  ⟨4179, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
  ⟨4180, .push ⟨4, by decide⟩ (UInt256.ofNat 3850323193), by rfl, by decide⟩,
  ⟨4181, .push ⟨1, by decide⟩ (UInt256.ofNat 160), by rfl, by decide⟩,
  ⟨4182, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
  ⟨4183, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PrefixStatePaths
