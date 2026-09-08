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

@[simp] theorem pc4013 : Artifact.submissionArtifact.instructionPC 4013 = 5230 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4014 : Artifact.submissionArtifact.instructionPC 4014 = 5231 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4015 : Artifact.submissionArtifact.instructionPC 4015 = 5232 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4016 : Artifact.submissionArtifact.instructionPC 4016 = 5235 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4017 : Artifact.submissionArtifact.instructionPC 4017 = 5236 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4018 : Artifact.submissionArtifact.instructionPC 4018 = 5237 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4019 : Artifact.submissionArtifact.instructionPC 4019 = 5238 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4020 : Artifact.submissionArtifact.instructionPC 4020 = 5240 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4021 : Artifact.submissionArtifact.instructionPC 4021 = 5243 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4022 : Artifact.submissionArtifact.instructionPC 4022 = 5244 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4023 : Artifact.submissionArtifact.instructionPC 4023 = 5245 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4024 : Artifact.submissionArtifact.instructionPC 4024 = 5246 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4025 : Artifact.submissionArtifact.instructionPC 4025 = 5247 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4026 : Artifact.submissionArtifact.instructionPC 4026 = 5248 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4027 : Artifact.submissionArtifact.instructionPC 4027 = 5251 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4028 : Artifact.submissionArtifact.instructionPC 4028 = 5252 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4029 : Artifact.submissionArtifact.instructionPC 4029 = 5254 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4030 : Artifact.submissionArtifact.instructionPC 4030 = 5255 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4031 : Artifact.submissionArtifact.instructionPC 4031 = 5288 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4032 : Artifact.submissionArtifact.instructionPC 4032 = 5289 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4033 : Artifact.submissionArtifact.instructionPC 4033 = 5292 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4034 : Artifact.submissionArtifact.instructionPC 4034 = 5293 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4035 : Artifact.submissionArtifact.instructionPC 4035 = 5294 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4036 : Artifact.submissionArtifact.instructionPC 4036 = 5299 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4037 : Artifact.submissionArtifact.instructionPC 4037 = 5301 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4038 : Artifact.submissionArtifact.instructionPC 4038 = 5302 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4039 : Artifact.submissionArtifact.instructionPC 4039 = 5307 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4040 : Artifact.submissionArtifact.instructionPC 4040 = 5309 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4041 : Artifact.submissionArtifact.instructionPC 4041 = 5310 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4042 : Artifact.submissionArtifact.instructionPC 4042 = 5315 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4043 : Artifact.submissionArtifact.instructionPC 4043 = 5317 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4044 : Artifact.submissionArtifact.instructionPC 4044 = 5318 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4045 : Artifact.submissionArtifact.instructionPC 4045 = 5323 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4046 : Artifact.submissionArtifact.instructionPC 4046 = 5325 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4047 : Artifact.submissionArtifact.instructionPC 4047 = 5326 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4048 : Artifact.submissionArtifact.instructionPC 4048 = 5331 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4049 : Artifact.submissionArtifact.instructionPC 4049 = 5333 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4050 : Artifact.submissionArtifact.instructionPC 4050 = 5334 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

def laterPath : List Located :=
  [⟨4013, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4014, .op (.Dup ⟨2, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4015, .push ⟨2, by decide⟩ (UInt256.ofNat 464), by rfl, by decide⟩,
   ⟨4016, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩]

def prefixPath : List Located :=
  [⟨4013, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4014, .op (.Dup ⟨2, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4015, .push ⟨2, by decide⟩ (UInt256.ofNat 464), by rfl, by decide⟩,
   ⟨4016, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4017, .push ⟨0, by decide⟩ (UInt256.ofNat 0), by rfl, by decide⟩,
   ⟨4018, .op .CALLDATALOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4019, .push ⟨1, by decide⟩ (UInt256.ofNat 32), by rfl, by decide⟩,
   ⟨4020, .push ⟨2, by decide⟩ (UInt256.ofNat 262), by rfl, by decide⟩,
   ⟨4021, .push ⟨0, by decide⟩ (UInt256.ofNat 0), by rfl, by decide⟩]

def firstComparePath : List Located :=
  [⟨4023, .push ⟨0, by decide⟩ (UInt256.ofNat 0), by rfl, by decide⟩,
   ⟨4024, .op .MLOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4025, .op .XOR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4026, .push ⟨2, by decide⟩ (UInt256.ofNat 464), by rfl, by decide⟩,
   ⟨4027, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩]

def secondComparePath : List Located :=
  [⟨4028, .push ⟨1, by decide⟩ (UInt256.ofNat 32), by rfl, by decide⟩,
   ⟨4029, .op .CALLDATALOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4030, .push ⟨32, by decide⟩ (UInt256.ofNat 75898346434861812577553744355519055536350986179947755549958789636940356975906), by rfl, by decide⟩,
   ⟨4031, .op .XOR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4032, .push ⟨2, by decide⟩ (UInt256.ofNat 464), by rfl, by decide⟩,
   ⟨4033, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩]

def hitPath : List Located :=
  [⟨4034, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4035, .push ⟨4, by decide⟩ (UInt256.ofNat 1080717082), by rfl, by decide⟩,
   ⟨4036, .push ⟨1, by decide⟩ (UInt256.ofNat 32), by rfl, by decide⟩,
   ⟨4037, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4038, .push ⟨4, by decide⟩ (UInt256.ofNat 2391128076), by rfl, by decide⟩,
   ⟨4039, .push ⟨1, by decide⟩ (UInt256.ofNat 64), by rfl, by decide⟩,
   ⟨4040, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4041, .push ⟨4, by decide⟩ (UInt256.ofNat 621343384), by rfl, by decide⟩,
   ⟨4042, .push ⟨1, by decide⟩ (UInt256.ofNat 96), by rfl, by decide⟩,
   ⟨4043, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4044, .push ⟨4, by decide⟩ (UInt256.ofNat 220066081), by rfl, by decide⟩,
   ⟨4045, .push ⟨1, by decide⟩ (UInt256.ofNat 128), by rfl, by decide⟩,
   ⟨4046, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4047, .push ⟨4, by decide⟩ (UInt256.ofNat 1007308478), by rfl, by decide⟩,
   ⟨4048, .push ⟨1, by decide⟩ (UInt256.ofNat 160), by rfl, by decide⟩,
   ⟨4049, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4050, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PrefixStatePaths
