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

@[simp] theorem pc4013 : Artifact.submissionArtifact.instructionPC 4257 = 5208 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4014 : Artifact.submissionArtifact.instructionPC 4258 = 5209 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4015 : Artifact.submissionArtifact.instructionPC 4259 = 5210 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4016 : Artifact.submissionArtifact.instructionPC 4260 = 5213 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4017 : Artifact.submissionArtifact.instructionPC 4261 = 5214 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4018 : Artifact.submissionArtifact.instructionPC 4262 = 5215 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4019 : Artifact.submissionArtifact.instructionPC 4263 = 5216 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4020 : Artifact.submissionArtifact.instructionPC 4264 = 5218 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4021 : Artifact.submissionArtifact.instructionPC 4265 = 5221 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4022 : Artifact.submissionArtifact.instructionPC 4266 = 5222 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4023 : Artifact.submissionArtifact.instructionPC 4267 = 5223 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4024 : Artifact.submissionArtifact.instructionPC 4268 = 5224 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4025 : Artifact.submissionArtifact.instructionPC 4269 = 5225 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4026 : Artifact.submissionArtifact.instructionPC 4270 = 5226 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4027 : Artifact.submissionArtifact.instructionPC 4271 = 5229 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4028 : Artifact.submissionArtifact.instructionPC 4272 = 5230 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4029 : Artifact.submissionArtifact.instructionPC 4273 = 5232 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4030 : Artifact.submissionArtifact.instructionPC 4274 = 5233 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4031 : Artifact.submissionArtifact.instructionPC 4275 = 5266 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4032 : Artifact.submissionArtifact.instructionPC 4276 = 5267 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4033 : Artifact.submissionArtifact.instructionPC 4277 = 5270 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4034 : Artifact.submissionArtifact.instructionPC 4278 = 5271 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4035 : Artifact.submissionArtifact.instructionPC 4279 = 5272 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4036 : Artifact.submissionArtifact.instructionPC 4280 = 5277 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4037 : Artifact.submissionArtifact.instructionPC 4281 = 5279 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4038 : Artifact.submissionArtifact.instructionPC 4282 = 5280 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4039 : Artifact.submissionArtifact.instructionPC 4283 = 5285 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4040 : Artifact.submissionArtifact.instructionPC 4284 = 5287 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4041 : Artifact.submissionArtifact.instructionPC 4285 = 5288 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4042 : Artifact.submissionArtifact.instructionPC 4286 = 5293 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4043 : Artifact.submissionArtifact.instructionPC 4287 = 5295 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4044 : Artifact.submissionArtifact.instructionPC 4288 = 5296 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4045 : Artifact.submissionArtifact.instructionPC 4289 = 5301 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4046 : Artifact.submissionArtifact.instructionPC 4290 = 5303 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4047 : Artifact.submissionArtifact.instructionPC 4291 = 5304 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4048 : Artifact.submissionArtifact.instructionPC 4292 = 5309 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4049 : Artifact.submissionArtifact.instructionPC 4293 = 5311 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4050 : Artifact.submissionArtifact.instructionPC 4294 = 5312 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

def laterPath : List Located :=
  [⟨4257, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4258, .op (.Dup ⟨2, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4259, .push ⟨2, by decide⟩ (UInt256.ofNat 460), by rfl, by decide⟩,
   ⟨4260, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩]

def prefixPath : List Located :=
  [⟨4257, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4258, .op (.Dup ⟨2, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4259, .push ⟨2, by decide⟩ (UInt256.ofNat 460), by rfl, by decide⟩,
   ⟨4260, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4261, .push ⟨0, by decide⟩ (UInt256.ofNat 0), by rfl, by decide⟩,
   ⟨4262, .op .CALLDATALOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4263, .push ⟨1, by decide⟩ (UInt256.ofNat 32), by rfl, by decide⟩,
   ⟨4264, .push ⟨2, by decide⟩ (UInt256.ofNat 260), by rfl, by decide⟩,
   ⟨4265, .push ⟨0, by decide⟩ (UInt256.ofNat 0), by rfl, by decide⟩]

def firstComparePath : List Located :=
  [⟨4267, .push ⟨0, by decide⟩ (UInt256.ofNat 0), by rfl, by decide⟩,
   ⟨4268, .op .MLOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4269, .op .XOR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4270, .push ⟨2, by decide⟩ (UInt256.ofNat 460), by rfl, by decide⟩,
   ⟨4271, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩]

def secondComparePath : List Located :=
  [⟨4272, .push ⟨1, by decide⟩ (UInt256.ofNat 32), by rfl, by decide⟩,
   ⟨4273, .op .CALLDATALOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4274, .push ⟨32, by decide⟩ (UInt256.ofNat 75898346434861812577553744355519055536350986179947755549958789636940356975906), by rfl, by decide⟩,
   ⟨4275, .op .XOR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4276, .push ⟨2, by decide⟩ (UInt256.ofNat 460), by rfl, by decide⟩,
   ⟨4277, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩]

def hitPath : List Located :=
  [⟨4278, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4279, .push ⟨4, by decide⟩ (UInt256.ofNat 1080717082), by rfl, by decide⟩,
   ⟨4280, .push ⟨1, by decide⟩ (UInt256.ofNat 32), by rfl, by decide⟩,
   ⟨4281, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4282, .push ⟨4, by decide⟩ (UInt256.ofNat 2391128076), by rfl, by decide⟩,
   ⟨4283, .push ⟨1, by decide⟩ (UInt256.ofNat 64), by rfl, by decide⟩,
   ⟨4284, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4285, .push ⟨4, by decide⟩ (UInt256.ofNat 621343384), by rfl, by decide⟩,
   ⟨4286, .push ⟨1, by decide⟩ (UInt256.ofNat 96), by rfl, by decide⟩,
   ⟨4287, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4288, .push ⟨4, by decide⟩ (UInt256.ofNat 220066081), by rfl, by decide⟩,
   ⟨4289, .push ⟨1, by decide⟩ (UInt256.ofNat 128), by rfl, by decide⟩,
   ⟨4290, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4291, .push ⟨4, by decide⟩ (UInt256.ofNat 1007308478), by rfl, by decide⟩,
   ⟨4292, .push ⟨1, by decide⟩ (UInt256.ofNat 160), by rfl, by decide⟩,
   ⟨4293, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4294, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PrefixStatePaths
