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
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc4106 : Artifact.submissionArtifact.instructionPC 4106 = 5138 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc4107 : Artifact.submissionArtifact.instructionPC 4107 = 5139 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc4108 : Artifact.submissionArtifact.instructionPC 4108 = 5140 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc4109 : Artifact.submissionArtifact.instructionPC 4109 = 5141 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc4110 : Artifact.submissionArtifact.instructionPC 4110 = 5146 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc4111 : Artifact.submissionArtifact.instructionPC 4111 = 5148 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc4112 : Artifact.submissionArtifact.instructionPC 4112 = 5149 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc4113 : Artifact.submissionArtifact.instructionPC 4113 = 5154 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc4114 : Artifact.submissionArtifact.instructionPC 4114 = 5156 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc4115 : Artifact.submissionArtifact.instructionPC 4115 = 5157 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc4116 : Artifact.submissionArtifact.instructionPC 4116 = 5162 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc4117 : Artifact.submissionArtifact.instructionPC 4117 = 5164 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc4118 : Artifact.submissionArtifact.instructionPC 4118 = 5165 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc4119 : Artifact.submissionArtifact.instructionPC 4119 = 5170 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc4120 : Artifact.submissionArtifact.instructionPC 4120 = 5172 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc4121 : Artifact.submissionArtifact.instructionPC 4121 = 5173 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc4122 : Artifact.submissionArtifact.instructionPC 4122 = 5178 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc4123 : Artifact.submissionArtifact.instructionPC 4123 = 5180 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc4124 : Artifact.submissionArtifact.instructionPC 4124 = 5181 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc4125 : Artifact.submissionArtifact.instructionPC 4125 = 5182 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc4126 : Artifact.submissionArtifact.instructionPC 4126 = 5183 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc4127 : Artifact.submissionArtifact.instructionPC 4127 = 5184 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc4128 : Artifact.submissionArtifact.instructionPC 4128 = 5189 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc4129 : Artifact.submissionArtifact.instructionPC 4129 = 5191 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc4130 : Artifact.submissionArtifact.instructionPC 4130 = 5192 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc4131 : Artifact.submissionArtifact.instructionPC 4131 = 5197 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc4132 : Artifact.submissionArtifact.instructionPC 4132 = 5199 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc4133 : Artifact.submissionArtifact.instructionPC 4133 = 5200 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc4134 : Artifact.submissionArtifact.instructionPC 4134 = 5205 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc4135 : Artifact.submissionArtifact.instructionPC 4135 = 5207 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc4136 : Artifact.submissionArtifact.instructionPC 4136 = 5208 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc4137 : Artifact.submissionArtifact.instructionPC 4137 = 5213 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc4138 : Artifact.submissionArtifact.instructionPC 4138 = 5215 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc4139 : Artifact.submissionArtifact.instructionPC 4139 = 5216 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc4140 : Artifact.submissionArtifact.instructionPC 4140 = 5221 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc4141 : Artifact.submissionArtifact.instructionPC 4141 = 5223 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc4142 : Artifact.submissionArtifact.instructionPC 4142 = 5224 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc4143 : Artifact.submissionArtifact.instructionPC 4143 = 5225 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc4144 : Artifact.submissionArtifact.instructionPC 4144 = 5226 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc4145 : Artifact.submissionArtifact.instructionPC 4145 = 5227 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc4146 : Artifact.submissionArtifact.instructionPC 4146 = 5228 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc4147 : Artifact.submissionArtifact.instructionPC 4147 = 5229 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc4148 : Artifact.submissionArtifact.instructionPC 4148 = 5231 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc4149 : Artifact.submissionArtifact.instructionPC 4149 = 5232 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc4150 : Artifact.submissionArtifact.instructionPC 4150 = 5237 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc4151 : Artifact.submissionArtifact.instructionPC 4151 = 5239 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc4152 : Artifact.submissionArtifact.instructionPC 4152 = 5240 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc4153 : Artifact.submissionArtifact.instructionPC 4153 = 5245 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc4154 : Artifact.submissionArtifact.instructionPC 4154 = 5247 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc4155 : Artifact.submissionArtifact.instructionPC 4155 = 5248 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc4156 : Artifact.submissionArtifact.instructionPC 4156 = 5253 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc4157 : Artifact.submissionArtifact.instructionPC 4157 = 5255 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc4158 : Artifact.submissionArtifact.instructionPC 4158 = 5256 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc4159 : Artifact.submissionArtifact.instructionPC 4159 = 5261 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc4160 : Artifact.submissionArtifact.instructionPC 4160 = 5263 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc4161 : Artifact.submissionArtifact.instructionPC 4161 = 5264 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc4162 : Artifact.submissionArtifact.instructionPC 4162 = 5269 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc4163 : Artifact.submissionArtifact.instructionPC 4163 = 5271 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc4164 : Artifact.submissionArtifact.instructionPC 4164 = 5272 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc4165 : Artifact.submissionArtifact.instructionPC 4165 = 5273 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc4166 : Artifact.submissionArtifact.instructionPC 4166 = 5274 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc4167 : Artifact.submissionArtifact.instructionPC 4167 = 5276 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc4168 : Artifact.submissionArtifact.instructionPC 4168 = 5277 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc4169 : Artifact.submissionArtifact.instructionPC 4169 = 5310 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc4170 : Artifact.submissionArtifact.instructionPC 4170 = 5311 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc4171 : Artifact.submissionArtifact.instructionPC 4171 = 5314 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc4172 : Artifact.submissionArtifact.instructionPC 4172 = 5315 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc4173 : Artifact.submissionArtifact.instructionPC 4173 = 5317 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc4174 : Artifact.submissionArtifact.instructionPC 4174 = 5318 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc4175 : Artifact.submissionArtifact.instructionPC 4175 = 5351 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc4176 : Artifact.submissionArtifact.instructionPC 4176 = 5352 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc4177 : Artifact.submissionArtifact.instructionPC 4177 = 5355 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc4178 : Artifact.submissionArtifact.instructionPC 4178 = 5356 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc4179 : Artifact.submissionArtifact.instructionPC 4179 = 5357 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc4180 : Artifact.submissionArtifact.instructionPC 4180 = 5358 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc4181 : Artifact.submissionArtifact.instructionPC 4181 = 5359 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc4182 : Artifact.submissionArtifact.instructionPC 4182 = 5361 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc4183 : Artifact.submissionArtifact.instructionPC 4183 = 5362 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc4184 : Artifact.submissionArtifact.instructionPC 4184 = 5367 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc4185 : Artifact.submissionArtifact.instructionPC 4185 = 5369 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc4186 : Artifact.submissionArtifact.instructionPC 4186 = 5370 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc4187 : Artifact.submissionArtifact.instructionPC 4187 = 5375 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc4188 : Artifact.submissionArtifact.instructionPC 4188 = 5377 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc4189 : Artifact.submissionArtifact.instructionPC 4189 = 5378 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc4190 : Artifact.submissionArtifact.instructionPC 4190 = 5383 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc4191 : Artifact.submissionArtifact.instructionPC 4191 = 5385 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc4192 : Artifact.submissionArtifact.instructionPC 4192 = 5386 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc4193 : Artifact.submissionArtifact.instructionPC 4193 = 5391 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc4194 : Artifact.submissionArtifact.instructionPC 4194 = 5393 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc4195 : Artifact.submissionArtifact.instructionPC 4195 = 5394 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc4196 : Artifact.submissionArtifact.instructionPC 4196 = 5399 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc4197 : Artifact.submissionArtifact.instructionPC 4197 = 5401 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc4198 : Artifact.submissionArtifact.instructionPC 4198 = 5402 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl

def laterPath : List Located :=
  [⟨4072, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4073, .op (.Dup ⟨2, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4074, .push ⟨2, by decide⟩ (UInt256.ofNat 464), by rfl, by decide⟩,
   ⟨4075, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩]

def prefixPath : List Located :=
  [⟨4072, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4073, .op (.Dup ⟨2, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4074, .push ⟨2, by decide⟩ (UInt256.ofNat 464), by rfl, by decide⟩,
   ⟨4075, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4076, .push ⟨0, by decide⟩ (UInt256.ofNat 0), by rfl, by decide⟩,
   ⟨4077, .op .CALLDATALOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4078, .push ⟨1, by decide⟩ (UInt256.ofNat 32), by rfl, by decide⟩,
   ⟨4079, .push ⟨2, by decide⟩ (UInt256.ofNat 262), by rfl, by decide⟩,
   ⟨4080, .push ⟨0, by decide⟩ (UInt256.ofNat 0), by rfl, by decide⟩]

def firstComparePath : List Located :=
  [⟨4082, .push ⟨0, by decide⟩ (UInt256.ofNat 0), by rfl, by decide⟩,
   ⟨4083, .op .MLOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4084, .op .XOR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4085, .push ⟨2, by decide⟩ (UInt256.ofNat 464), by rfl, by decide⟩,
   ⟨4086, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩]

def secondComparePath : List Located :=
  [⟨4087, .push ⟨1, by decide⟩ (UInt256.ofNat 32), by rfl, by decide⟩,
   ⟨4088, .op .CALLDATALOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4089, .push ⟨32, by decide⟩ (UInt256.ofNat 75898346434861812577553744355519055536350986179947755549958789636940356975906), by rfl, by decide⟩,
   ⟨4090, .op .XOR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4091, .push ⟨2, by decide⟩ (UInt256.ofNat 464), by rfl, by decide⟩,
   ⟨4092, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩]

def thirdComparePath : List Located :=
  [⟨4093, .push ⟨1, by decide⟩ (UInt256.ofNat 64), by rfl, by decide⟩,
   ⟨4094, .op .CALLDATALOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4095, .push ⟨32, by decide⟩ (UInt256.ofNat 32306037415402008934629779266198679100989968660636699671972189525809707916738), by rfl, by decide⟩,
   ⟨4096, .op .XOR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4097, .push ⟨2, by decide⟩ (UInt256.ofNat 5182), by rfl, by decide⟩,
   ⟨4098, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩]

def fourthComparePath : List Located :=
  [⟨4099, .push ⟨1, by decide⟩ (UInt256.ofNat 96), by rfl, by decide⟩,
   ⟨4100, .op .CALLDATALOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4101, .push ⟨32, by decide⟩ (UInt256.ofNat 104505810704657832532308207549693575120876051224915683785162626763390386191714), by rfl, by decide⟩,
   ⟨4102, .op .XOR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4103, .push ⟨2, by decide⟩ (UInt256.ofNat 5182), by rfl, by decide⟩,
   ⟨4104, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4105, .push ⟨2, by decide⟩ (UInt256.ofNat 5273), by rfl, by decide⟩,
   ⟨4106, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def hit2Path : List Located :=
  [⟨4143, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4144, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4145, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4146, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4147, .push ⟨1, by decide⟩ (UInt256.ofNat 64), by rfl, by decide⟩,
   ⟨4148, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4149, .push ⟨4, by decide⟩ (UInt256.ofNat 2807398299), by rfl, by decide⟩,
   ⟨4150, .push ⟨1, by decide⟩ (UInt256.ofNat 32), by rfl, by decide⟩,
   ⟨4151, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4152, .push ⟨4, by decide⟩ (UInt256.ofNat 514068704), by rfl, by decide⟩,
   ⟨4153, .push ⟨1, by decide⟩ (UInt256.ofNat 64), by rfl, by decide⟩,
   ⟨4154, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4155, .push ⟨4, by decide⟩ (UInt256.ofNat 3681030016), by rfl, by decide⟩,
   ⟨4156, .push ⟨1, by decide⟩ (UInt256.ofNat 96), by rfl, by decide⟩,
   ⟨4157, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4158, .push ⟨4, by decide⟩ (UInt256.ofNat 3354522469), by rfl, by decide⟩,
   ⟨4159, .push ⟨1, by decide⟩ (UInt256.ofNat 128), by rfl, by decide⟩,
   ⟨4160, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4161, .push ⟨4, by decide⟩ (UInt256.ofNat 2543018249), by rfl, by decide⟩,
   ⟨4162, .push ⟨1, by decide⟩ (UInt256.ofNat 160), by rfl, by decide⟩,
   ⟨4163, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4164, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def fifthComparePath : List Located :=
  [⟨4166, .push ⟨1, by decide⟩ (UInt256.ofNat 128), by rfl, by decide⟩,
   ⟨4167, .op .CALLDATALOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4168, .push ⟨32, by decide⟩ (UInt256.ofNat 61367581353886127001238131413293229573374005415347599533452268822761471270146), by rfl, by decide⟩,
   ⟨4169, .op .XOR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4170, .push ⟨2, by decide⟩ (UInt256.ofNat 5225), by rfl, by decide⟩,
   ⟨4171, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩]

def sixthComparePath : List Located :=
  [⟨4172, .push ⟨1, by decide⟩ (UInt256.ofNat 160), by rfl, by decide⟩,
   ⟨4173, .op .CALLDATALOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4174, .push ⟨32, by decide⟩ (UInt256.ofNat 17775265432785288859418840296405106407947132191047579206632289663109943557538), by rfl, by decide⟩,
   ⟨4175, .op .XOR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4176, .push ⟨2, by decide⟩ (UInt256.ofNat 5225), by rfl, by decide⟩,
   ⟨4177, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩]

def hit3Path : List Located :=
  [⟨4178, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4179, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4180, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4181, .push ⟨1, by decide⟩ (UInt256.ofNat 128), by rfl, by decide⟩,
   ⟨4182, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4183, .push ⟨4, by decide⟩ (UInt256.ofNat 1393315003), by rfl, by decide⟩,
   ⟨4184, .push ⟨1, by decide⟩ (UInt256.ofNat 32), by rfl, by decide⟩,
   ⟨4185, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4186, .push ⟨4, by decide⟩ (UInt256.ofNat 695251451), by rfl, by decide⟩,
   ⟨4187, .push ⟨1, by decide⟩ (UInt256.ofNat 64), by rfl, by decide⟩,
   ⟨4188, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4189, .push ⟨4, by decide⟩ (UInt256.ofNat 358732556), by rfl, by decide⟩,
   ⟨4190, .push ⟨1, by decide⟩ (UInt256.ofNat 96), by rfl, by decide⟩,
   ⟨4191, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4192, .push ⟨4, by decide⟩ (UInt256.ofNat 928826907), by rfl, by decide⟩,
   ⟨4193, .push ⟨1, by decide⟩ (UInt256.ofNat 128), by rfl, by decide⟩,
   ⟨4194, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4195, .push ⟨4, by decide⟩ (UInt256.ofNat 3850323193), by rfl, by decide⟩,
   ⟨4196, .push ⟨1, by decide⟩ (UInt256.ofNat 160), by rfl, by decide⟩,
   ⟨4197, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4198, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def hitPath : List Located :=
  [⟨4125, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4126, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4127, .push ⟨4, by decide⟩ (UInt256.ofNat 1080717082), by rfl, by decide⟩,
   ⟨4128, .push ⟨1, by decide⟩ (UInt256.ofNat 32), by rfl, by decide⟩,
   ⟨4129, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4130, .push ⟨4, by decide⟩ (UInt256.ofNat 2391128076), by rfl, by decide⟩,
   ⟨4131, .push ⟨1, by decide⟩ (UInt256.ofNat 64), by rfl, by decide⟩,
   ⟨4132, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4133, .push ⟨4, by decide⟩ (UInt256.ofNat 621343384), by rfl, by decide⟩,
   ⟨4134, .push ⟨1, by decide⟩ (UInt256.ofNat 96), by rfl, by decide⟩,
   ⟨4135, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4136, .push ⟨4, by decide⟩ (UInt256.ofNat 220066081), by rfl, by decide⟩,
   ⟨4137, .push ⟨1, by decide⟩ (UInt256.ofNat 128), by rfl, by decide⟩,
   ⟨4138, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4139, .push ⟨4, by decide⟩ (UInt256.ofNat 1007308478), by rfl, by decide⟩,
   ⟨4140, .push ⟨1, by decide⟩ (UInt256.ofNat 160), by rfl, by decide⟩,
   ⟨4141, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4142, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PrefixStatePaths
