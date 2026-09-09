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

@[simp] theorem pc4013 : Artifact.submissionArtifact.instructionPC 4255 = 5217 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4014 : Artifact.submissionArtifact.instructionPC 4256 = 5218 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4015 : Artifact.submissionArtifact.instructionPC 4257 = 5219 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4016 : Artifact.submissionArtifact.instructionPC 4258 = 5222 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4017 : Artifact.submissionArtifact.instructionPC 4259 = 5223 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4018 : Artifact.submissionArtifact.instructionPC 4260 = 5224 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4019 : Artifact.submissionArtifact.instructionPC 4261 = 5225 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4020 : Artifact.submissionArtifact.instructionPC 4262 = 5227 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4021 : Artifact.submissionArtifact.instructionPC 4263 = 5230 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4022 : Artifact.submissionArtifact.instructionPC 4264 = 5231 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4023 : Artifact.submissionArtifact.instructionPC 4265 = 5232 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4024 : Artifact.submissionArtifact.instructionPC 4266 = 5233 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4025 : Artifact.submissionArtifact.instructionPC 4267 = 5234 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4026 : Artifact.submissionArtifact.instructionPC 4268 = 5235 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4027 : Artifact.submissionArtifact.instructionPC 4269 = 5238 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4028 : Artifact.submissionArtifact.instructionPC 4270 = 5239 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4029 : Artifact.submissionArtifact.instructionPC 4271 = 5241 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4030 : Artifact.submissionArtifact.instructionPC 4272 = 5242 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4031 : Artifact.submissionArtifact.instructionPC 4273 = 5275 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4032 : Artifact.submissionArtifact.instructionPC 4274 = 5276 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4033 : Artifact.submissionArtifact.instructionPC 4275 = 5279 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4034 : Artifact.submissionArtifact.instructionPC 4276 = 5280 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4035 : Artifact.submissionArtifact.instructionPC 4277 = 5281 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4036 : Artifact.submissionArtifact.instructionPC 4278 = 5286 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4037 : Artifact.submissionArtifact.instructionPC 4279 = 5288 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4038 : Artifact.submissionArtifact.instructionPC 4280 = 5289 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4039 : Artifact.submissionArtifact.instructionPC 4281 = 5294 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4040 : Artifact.submissionArtifact.instructionPC 4282 = 5296 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4041 : Artifact.submissionArtifact.instructionPC 4283 = 5297 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4042 : Artifact.submissionArtifact.instructionPC 4284 = 5302 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4043 : Artifact.submissionArtifact.instructionPC 4285 = 5304 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4044 : Artifact.submissionArtifact.instructionPC 4286 = 5305 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4045 : Artifact.submissionArtifact.instructionPC 4287 = 5310 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4046 : Artifact.submissionArtifact.instructionPC 4288 = 5312 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4047 : Artifact.submissionArtifact.instructionPC 4289 = 5313 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4048 : Artifact.submissionArtifact.instructionPC 4290 = 5318 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4049 : Artifact.submissionArtifact.instructionPC 4291 = 5320 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4050 : Artifact.submissionArtifact.instructionPC 4292 = 5321 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

def laterPath : List Located :=
  [⟨4255, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4256, .op (.Dup ⟨2, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4257, .push ⟨2, by decide⟩ (UInt256.ofNat 460), by rfl, by decide⟩,
   ⟨4258, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩]

def prefixPath : List Located :=
  [⟨4255, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4256, .op (.Dup ⟨2, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4257, .push ⟨2, by decide⟩ (UInt256.ofNat 460), by rfl, by decide⟩,
   ⟨4258, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4259, .push ⟨0, by decide⟩ (UInt256.ofNat 0), by rfl, by decide⟩,
   ⟨4260, .op .CALLDATALOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4261, .push ⟨1, by decide⟩ (UInt256.ofNat 32), by rfl, by decide⟩,
   ⟨4262, .push ⟨2, by decide⟩ (UInt256.ofNat 260), by rfl, by decide⟩,
   ⟨4263, .push ⟨0, by decide⟩ (UInt256.ofNat 0), by rfl, by decide⟩]

def firstComparePath : List Located :=
  [⟨4265, .push ⟨0, by decide⟩ (UInt256.ofNat 0), by rfl, by decide⟩,
   ⟨4266, .op .MLOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4267, .op .XOR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4268, .push ⟨2, by decide⟩ (UInt256.ofNat 460), by rfl, by decide⟩,
   ⟨4269, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩]

def secondComparePath : List Located :=
  [⟨4270, .push ⟨1, by decide⟩ (UInt256.ofNat 32), by rfl, by decide⟩,
   ⟨4271, .op .CALLDATALOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4272, .push ⟨32, by decide⟩ (UInt256.ofNat 75898346434861812577553744355519055536350986179947755549958789636940356975906), by rfl, by decide⟩,
   ⟨4273, .op .XOR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4274, .push ⟨2, by decide⟩ (UInt256.ofNat 460), by rfl, by decide⟩,
   ⟨4275, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩]

def hitPath : List Located :=
  [⟨4276, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4277, .push ⟨4, by decide⟩ (UInt256.ofNat 1080717082), by rfl, by decide⟩,
   ⟨4278, .push ⟨1, by decide⟩ (UInt256.ofNat 32), by rfl, by decide⟩,
   ⟨4279, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4280, .push ⟨4, by decide⟩ (UInt256.ofNat 2391128076), by rfl, by decide⟩,
   ⟨4281, .push ⟨1, by decide⟩ (UInt256.ofNat 64), by rfl, by decide⟩,
   ⟨4282, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4283, .push ⟨4, by decide⟩ (UInt256.ofNat 621343384), by rfl, by decide⟩,
   ⟨4284, .push ⟨1, by decide⟩ (UInt256.ofNat 96), by rfl, by decide⟩,
   ⟨4285, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4286, .push ⟨4, by decide⟩ (UInt256.ofNat 220066081), by rfl, by decide⟩,
   ⟨4287, .push ⟨1, by decide⟩ (UInt256.ofNat 128), by rfl, by decide⟩,
   ⟨4288, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4289, .push ⟨4, by decide⟩ (UInt256.ofNat 1007308478), by rfl, by decide⟩,
   ⟨4290, .push ⟨1, by decide⟩ (UInt256.ofNat 160), by rfl, by decide⟩,
   ⟨4291, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4292, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PrefixStatePaths
