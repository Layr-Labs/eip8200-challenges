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

@[simp] theorem pc4013 : Artifact.submissionArtifact.instructionPC 4270 = 5197 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4014 : Artifact.submissionArtifact.instructionPC 4271 = 5198 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4015 : Artifact.submissionArtifact.instructionPC 4272 = 5199 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4016 : Artifact.submissionArtifact.instructionPC 4273 = 5202 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4017 : Artifact.submissionArtifact.instructionPC 4274 = 5203 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4018 : Artifact.submissionArtifact.instructionPC 4275 = 5204 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4019 : Artifact.submissionArtifact.instructionPC 4276 = 5205 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4020 : Artifact.submissionArtifact.instructionPC 4277 = 5207 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4021 : Artifact.submissionArtifact.instructionPC 4278 = 5210 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4022 : Artifact.submissionArtifact.instructionPC 4279 = 5211 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4023 : Artifact.submissionArtifact.instructionPC 4280 = 5212 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4024 : Artifact.submissionArtifact.instructionPC 4281 = 5213 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4025 : Artifact.submissionArtifact.instructionPC 4282 = 5214 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4026 : Artifact.submissionArtifact.instructionPC 4283 = 5215 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4027 : Artifact.submissionArtifact.instructionPC 4284 = 5218 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4028 : Artifact.submissionArtifact.instructionPC 4285 = 5219 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4029 : Artifact.submissionArtifact.instructionPC 4286 = 5221 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4030 : Artifact.submissionArtifact.instructionPC 4287 = 5222 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4031 : Artifact.submissionArtifact.instructionPC 4288 = 5255 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4032 : Artifact.submissionArtifact.instructionPC 4289 = 5256 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4033 : Artifact.submissionArtifact.instructionPC 4290 = 5259 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4034 : Artifact.submissionArtifact.instructionPC 4291 = 5260 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4035 : Artifact.submissionArtifact.instructionPC 4292 = 5261 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4036 : Artifact.submissionArtifact.instructionPC 4293 = 5266 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4037 : Artifact.submissionArtifact.instructionPC 4294 = 5268 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4038 : Artifact.submissionArtifact.instructionPC 4295 = 5269 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4039 : Artifact.submissionArtifact.instructionPC 4296 = 5274 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4040 : Artifact.submissionArtifact.instructionPC 4297 = 5276 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4041 : Artifact.submissionArtifact.instructionPC 4298 = 5277 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4042 : Artifact.submissionArtifact.instructionPC 4299 = 5282 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4043 : Artifact.submissionArtifact.instructionPC 4300 = 5284 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4044 : Artifact.submissionArtifact.instructionPC 4301 = 5285 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4045 : Artifact.submissionArtifact.instructionPC 4302 = 5290 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4046 : Artifact.submissionArtifact.instructionPC 4303 = 5292 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4047 : Artifact.submissionArtifact.instructionPC 4304 = 5293 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4048 : Artifact.submissionArtifact.instructionPC 4305 = 5298 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4049 : Artifact.submissionArtifact.instructionPC 4306 = 5300 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4050 : Artifact.submissionArtifact.instructionPC 4307 = 5301 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

def laterPath : List Located :=
  [⟨4270, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4271, .op (.Dup ⟨2, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4272, .push ⟨2, by decide⟩ (UInt256.ofNat 464), by rfl, by decide⟩,
   ⟨4273, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩]

def prefixPath : List Located :=
  [⟨4270, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4271, .op (.Dup ⟨2, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4272, .push ⟨2, by decide⟩ (UInt256.ofNat 464), by rfl, by decide⟩,
   ⟨4273, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4274, .push ⟨0, by decide⟩ (UInt256.ofNat 0), by rfl, by decide⟩,
   ⟨4275, .op .CALLDATALOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4276, .push ⟨1, by decide⟩ (UInt256.ofNat 32), by rfl, by decide⟩,
   ⟨4277, .push ⟨2, by decide⟩ (UInt256.ofNat 262), by rfl, by decide⟩,
   ⟨4278, .push ⟨0, by decide⟩ (UInt256.ofNat 0), by rfl, by decide⟩]

def firstComparePath : List Located :=
  [⟨4280, .push ⟨0, by decide⟩ (UInt256.ofNat 0), by rfl, by decide⟩,
   ⟨4281, .op .MLOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4282, .op .XOR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4283, .push ⟨2, by decide⟩ (UInt256.ofNat 464), by rfl, by decide⟩,
   ⟨4284, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩]

def secondComparePath : List Located :=
  [⟨4285, .push ⟨1, by decide⟩ (UInt256.ofNat 32), by rfl, by decide⟩,
   ⟨4286, .op .CALLDATALOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4287, .push ⟨32, by decide⟩ (UInt256.ofNat 75898346434861812577553744355519055536350986179947755549958789636940356975906), by rfl, by decide⟩,
   ⟨4288, .op .XOR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4289, .push ⟨2, by decide⟩ (UInt256.ofNat 464), by rfl, by decide⟩,
   ⟨4290, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩]

def hitPath : List Located :=
  [⟨4291, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4292, .push ⟨4, by decide⟩ (UInt256.ofNat 1080717082), by rfl, by decide⟩,
   ⟨4293, .push ⟨1, by decide⟩ (UInt256.ofNat 32), by rfl, by decide⟩,
   ⟨4294, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4295, .push ⟨4, by decide⟩ (UInt256.ofNat 2391128076), by rfl, by decide⟩,
   ⟨4296, .push ⟨1, by decide⟩ (UInt256.ofNat 64), by rfl, by decide⟩,
   ⟨4297, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4298, .push ⟨4, by decide⟩ (UInt256.ofNat 621343384), by rfl, by decide⟩,
   ⟨4299, .push ⟨1, by decide⟩ (UInt256.ofNat 96), by rfl, by decide⟩,
   ⟨4300, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4301, .push ⟨4, by decide⟩ (UInt256.ofNat 220066081), by rfl, by decide⟩,
   ⟨4302, .push ⟨1, by decide⟩ (UInt256.ofNat 128), by rfl, by decide⟩,
   ⟨4303, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4304, .push ⟨4, by decide⟩ (UInt256.ofNat 1007308478), by rfl, by decide⟩,
   ⟨4305, .push ⟨1, by decide⟩ (UInt256.ofNat 160), by rfl, by decide⟩,
   ⟨4306, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4307, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PrefixStatePaths
