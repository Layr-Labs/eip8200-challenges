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

@[simp] theorem pc4013 : Artifact.submissionArtifact.instructionPC 4244 = 0x1455 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4014 : Artifact.submissionArtifact.instructionPC 4245 = 0x1456 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4015 : Artifact.submissionArtifact.instructionPC 4246 = 0x1457 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4016 : Artifact.submissionArtifact.instructionPC 4247 = 0x145a := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4017 : Artifact.submissionArtifact.instructionPC 4248 = 0x145b := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4018 : Artifact.submissionArtifact.instructionPC 4249 = 0x145c := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4019 : Artifact.submissionArtifact.instructionPC 4250 = 0x145d := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4020 : Artifact.submissionArtifact.instructionPC 4251 = 0x145f := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4021 : Artifact.submissionArtifact.instructionPC 4252 = 0x1462 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4022 : Artifact.submissionArtifact.instructionPC 4253 = 0x1463 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4023 : Artifact.submissionArtifact.instructionPC 4254 = 0x1464 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4024 : Artifact.submissionArtifact.instructionPC 4255 = 0x1465 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4025 : Artifact.submissionArtifact.instructionPC 4256 = 0x1466 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4026 : Artifact.submissionArtifact.instructionPC 4257 = 0x1467 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4027 : Artifact.submissionArtifact.instructionPC 4258 = 0x146a := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4028 : Artifact.submissionArtifact.instructionPC 4259 = 0x146b := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4029 : Artifact.submissionArtifact.instructionPC 4260 = 0x146d := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4030 : Artifact.submissionArtifact.instructionPC 4261 = 0x146e := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4031 : Artifact.submissionArtifact.instructionPC 4262 = 0x148f := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4032 : Artifact.submissionArtifact.instructionPC 4263 = 0x1490 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4033 : Artifact.submissionArtifact.instructionPC 4264 = 0x1493 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4034 : Artifact.submissionArtifact.instructionPC 4265 = 0x1494 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4035 : Artifact.submissionArtifact.instructionPC 4266 = 0x1495 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4036 : Artifact.submissionArtifact.instructionPC 4267 = 0x149a := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4037 : Artifact.submissionArtifact.instructionPC 4268 = 0x149c := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4038 : Artifact.submissionArtifact.instructionPC 4269 = 0x149d := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4039 : Artifact.submissionArtifact.instructionPC 4270 = 0x14a2 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4040 : Artifact.submissionArtifact.instructionPC 4271 = 0x14a4 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4041 : Artifact.submissionArtifact.instructionPC 4272 = 0x14a5 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4042 : Artifact.submissionArtifact.instructionPC 4273 = 0x14aa := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4043 : Artifact.submissionArtifact.instructionPC 4274 = 0x14ac := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4044 : Artifact.submissionArtifact.instructionPC 4275 = 0x14ad := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4045 : Artifact.submissionArtifact.instructionPC 4276 = 0x14b2 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4046 : Artifact.submissionArtifact.instructionPC 4277 = 0x14b4 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4047 : Artifact.submissionArtifact.instructionPC 4278 = 0x14b5 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4048 : Artifact.submissionArtifact.instructionPC 4279 = 0x14ba := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4049 : Artifact.submissionArtifact.instructionPC 4280 = 0x14bc := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4050 : Artifact.submissionArtifact.instructionPC 4281 = 0x14bd := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

def laterPath : List Located :=
  [⟨4244, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4245, .op (.Dup ⟨2, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4246, .push ⟨2, by decide⟩ (UInt256.ofNat 448), by rfl, by decide⟩,
   ⟨4247, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩]

def prefixPath : List Located :=
  [⟨4244, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4245, .op (.Dup ⟨2, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4246, .push ⟨2, by decide⟩ (UInt256.ofNat 448), by rfl, by decide⟩,
   ⟨4247, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4248, .push ⟨0, by decide⟩ (UInt256.ofNat 0), by rfl, by decide⟩,
   ⟨4249, .op .CALLDATALOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4250, .push ⟨1, by decide⟩ (UInt256.ofNat 32), by rfl, by decide⟩,
   ⟨4251, .push ⟨2, by decide⟩ (UInt256.ofNat 259), by rfl, by decide⟩,
   ⟨4252, .push ⟨0, by decide⟩ (UInt256.ofNat 0), by rfl, by decide⟩]

def firstComparePath : List Located :=
  [⟨4254, .push ⟨0, by decide⟩ (UInt256.ofNat 0), by rfl, by decide⟩,
   ⟨4255, .op .MLOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4256, .op .XOR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4257, .push ⟨2, by decide⟩ (UInt256.ofNat 448), by rfl, by decide⟩,
   ⟨4258, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩]

def secondComparePath : List Located :=
  [⟨4259, .push ⟨1, by decide⟩ (UInt256.ofNat 32), by rfl, by decide⟩,
   ⟨4260, .op .CALLDATALOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4261, .push ⟨32, by decide⟩ (UInt256.ofNat 75898346434861812577553744355519055536350986179947755549958789636940356975906), by rfl, by decide⟩,
   ⟨4262, .op .XOR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4263, .push ⟨2, by decide⟩ (UInt256.ofNat 448), by rfl, by decide⟩,
   ⟨4264, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩]

def hitPath : List Located :=
  [⟨4265, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4266, .push ⟨4, by decide⟩ (UInt256.ofNat 1080717082), by rfl, by decide⟩,
   ⟨4267, .push ⟨1, by decide⟩ (UInt256.ofNat 32), by rfl, by decide⟩,
   ⟨4268, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4269, .push ⟨4, by decide⟩ (UInt256.ofNat 2391128076), by rfl, by decide⟩,
   ⟨4270, .push ⟨1, by decide⟩ (UInt256.ofNat 64), by rfl, by decide⟩,
   ⟨4271, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4272, .push ⟨4, by decide⟩ (UInt256.ofNat 621343384), by rfl, by decide⟩,
   ⟨4273, .push ⟨1, by decide⟩ (UInt256.ofNat 96), by rfl, by decide⟩,
   ⟨4274, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4275, .push ⟨4, by decide⟩ (UInt256.ofNat 220066081), by rfl, by decide⟩,
   ⟨4276, .push ⟨1, by decide⟩ (UInt256.ofNat 128), by rfl, by decide⟩,
   ⟨4277, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4278, .push ⟨4, by decide⟩ (UInt256.ofNat 1007308478), by rfl, by decide⟩,
   ⟨4279, .push ⟨1, by decide⟩ (UInt256.ofNat 160), by rfl, by decide⟩,
   ⟨4280, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4281, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PrefixStatePaths
