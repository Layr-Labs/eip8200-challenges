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

@[simp] theorem pc4072 : Artifact.submissionArtifact.instructionPC 4073 = 5044 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4073 : Artifact.submissionArtifact.instructionPC 4074 = 5045 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4074 : Artifact.submissionArtifact.instructionPC 4075 = 5046 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4075 : Artifact.submissionArtifact.instructionPC 4076 = 5049 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4076 : Artifact.submissionArtifact.instructionPC 4077 = 5050 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4077 : Artifact.submissionArtifact.instructionPC 4078 = 5051 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4078 : Artifact.submissionArtifact.instructionPC 4079 = 5052 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4079 : Artifact.submissionArtifact.instructionPC 4080 = 5054 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4080 : Artifact.submissionArtifact.instructionPC 4081 = 5057 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4081 : Artifact.submissionArtifact.instructionPC 4082 = 5058 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4082 : Artifact.submissionArtifact.instructionPC 4083 = 5059 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4083 : Artifact.submissionArtifact.instructionPC 4084 = 5060 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4084 : Artifact.submissionArtifact.instructionPC 4085 = 5061 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4085 : Artifact.submissionArtifact.instructionPC 4086 = 5062 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4086 : Artifact.submissionArtifact.instructionPC 4087 = 5065 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4087 : Artifact.submissionArtifact.instructionPC 4088 = 5066 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4088 : Artifact.submissionArtifact.instructionPC 4089 = 5068 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4089 : Artifact.submissionArtifact.instructionPC 4090 = 5069 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4090 : Artifact.submissionArtifact.instructionPC 4091 = 5102 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4091 : Artifact.submissionArtifact.instructionPC 4092 = 5103 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4092 : Artifact.submissionArtifact.instructionPC 4093 = 5106 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4093 : Artifact.submissionArtifact.instructionPC 4094 = 5107 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4094 : Artifact.submissionArtifact.instructionPC 4095 = 5109 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4095 : Artifact.submissionArtifact.instructionPC 4096 = 5110 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4096 : Artifact.submissionArtifact.instructionPC 4097 = 5143 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4097 : Artifact.submissionArtifact.instructionPC 4098 = 5144 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4098 : Artifact.submissionArtifact.instructionPC 4099 = 5147 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4099 : Artifact.submissionArtifact.instructionPC 4100 = 5148 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4100 : Artifact.submissionArtifact.instructionPC 4101 = 5150 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4101 : Artifact.submissionArtifact.instructionPC 4102 = 5151 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4102 : Artifact.submissionArtifact.instructionPC 4103 = 5184 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4103 : Artifact.submissionArtifact.instructionPC 4104 = 5185 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4104 : Artifact.submissionArtifact.instructionPC 4105 = 5188 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4105 : Artifact.submissionArtifact.instructionPC 4106 = 5189 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4106 : Artifact.submissionArtifact.instructionPC 4107 = 5190 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4107 : Artifact.submissionArtifact.instructionPC 4108 = 5191 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4108 : Artifact.submissionArtifact.instructionPC 4109 = 5192 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4109 : Artifact.submissionArtifact.instructionPC 4110 = 5194 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4110 : Artifact.submissionArtifact.instructionPC 4111 = 5195 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4111 : Artifact.submissionArtifact.instructionPC 4112 = 5200 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4112 : Artifact.submissionArtifact.instructionPC 4113 = 5202 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4113 : Artifact.submissionArtifact.instructionPC 4114 = 5203 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4114 : Artifact.submissionArtifact.instructionPC 4115 = 5208 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4115 : Artifact.submissionArtifact.instructionPC 4116 = 5210 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4116 : Artifact.submissionArtifact.instructionPC 4117 = 5211 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4117 : Artifact.submissionArtifact.instructionPC 4118 = 5216 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4118 : Artifact.submissionArtifact.instructionPC 4119 = 5218 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4119 : Artifact.submissionArtifact.instructionPC 4120 = 5219 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4120 : Artifact.submissionArtifact.instructionPC 4121 = 5224 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4121 : Artifact.submissionArtifact.instructionPC 4122 = 5226 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4122 : Artifact.submissionArtifact.instructionPC 4123 = 5227 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4123 : Artifact.submissionArtifact.instructionPC 4124 = 5232 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4124 : Artifact.submissionArtifact.instructionPC 4125 = 5234 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4125 : Artifact.submissionArtifact.instructionPC 4126 = 5235 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4126 : Artifact.submissionArtifact.instructionPC 4127 = 5236 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4127 : Artifact.submissionArtifact.instructionPC 4128 = 5237 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4128 : Artifact.submissionArtifact.instructionPC 4129 = 5238 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4129 : Artifact.submissionArtifact.instructionPC 4130 = 5243 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4130 : Artifact.submissionArtifact.instructionPC 4131 = 5245 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4131 : Artifact.submissionArtifact.instructionPC 4132 = 5246 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4132 : Artifact.submissionArtifact.instructionPC 4133 = 5251 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4133 : Artifact.submissionArtifact.instructionPC 4134 = 5253 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4134 : Artifact.submissionArtifact.instructionPC 4135 = 5254 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4135 : Artifact.submissionArtifact.instructionPC 4136 = 5259 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4136 : Artifact.submissionArtifact.instructionPC 4137 = 5261 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4137 : Artifact.submissionArtifact.instructionPC 4138 = 5262 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4138 : Artifact.submissionArtifact.instructionPC 4139 = 5267 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4139 : Artifact.submissionArtifact.instructionPC 4140 = 5269 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4140 : Artifact.submissionArtifact.instructionPC 4141 = 5270 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4141 : Artifact.submissionArtifact.instructionPC 4142 = 5275 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4142 : Artifact.submissionArtifact.instructionPC 4143 = 5277 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4143 : Artifact.submissionArtifact.instructionPC 4144 = 5278 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

def laterPath : List Located :=
  [⟨4073, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4074, .op (.Dup ⟨2, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4075, .push ⟨2, by decide⟩ (UInt256.ofNat 494), by rfl, by decide⟩,
   ⟨4076, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩]

def prefixPath : List Located :=
  [⟨4073, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4074, .op (.Dup ⟨2, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4075, .push ⟨2, by decide⟩ (UInt256.ofNat 494), by rfl, by decide⟩,
   ⟨4076, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4077, .push ⟨0, by decide⟩ (UInt256.ofNat 0), by rfl, by decide⟩,
   ⟨4078, .op .CALLDATALOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4079, .push ⟨1, by decide⟩ (UInt256.ofNat 32), by rfl, by decide⟩,
   ⟨4080, .push ⟨2, by decide⟩ (UInt256.ofNat 276), by rfl, by decide⟩,
   ⟨4081, .push ⟨0, by decide⟩ (UInt256.ofNat 0), by rfl, by decide⟩]

def firstComparePath : List Located :=
  [⟨4083, .push ⟨0, by decide⟩ (UInt256.ofNat 0), by rfl, by decide⟩,
   ⟨4084, .op .MLOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4085, .op .XOR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4086, .push ⟨2, by decide⟩ (UInt256.ofNat 494), by rfl, by decide⟩,
   ⟨4087, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩]

def secondComparePath : List Located :=
  [⟨4088, .push ⟨1, by decide⟩ (UInt256.ofNat 32), by rfl, by decide⟩,
   ⟨4089, .op .CALLDATALOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4090, .push ⟨32, by decide⟩ (UInt256.ofNat 75898346434861812577553744355519055536350986179947755549958789636940356975906), by rfl, by decide⟩,
   ⟨4091, .op .XOR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4092, .push ⟨2, by decide⟩ (UInt256.ofNat 494), by rfl, by decide⟩,
   ⟨4093, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩]

def thirdComparePath : List Located :=
  [⟨4094, .push ⟨1, by decide⟩ (UInt256.ofNat 64), by rfl, by decide⟩,
   ⟨4095, .op .CALLDATALOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4096, .push ⟨32, by decide⟩ (UInt256.ofNat 32306037415402008934629779266198679100989968660636699671972189525809707916738), by rfl, by decide⟩,
   ⟨4097, .op .XOR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4098, .push ⟨2, by decide⟩ (UInt256.ofNat 5236), by rfl, by decide⟩,
   ⟨4099, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩]

def fourthComparePath : List Located :=
  [⟨4100, .push ⟨1, by decide⟩ (UInt256.ofNat 96), by rfl, by decide⟩,
   ⟨4101, .op .CALLDATALOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4102, .push ⟨32, by decide⟩ (UInt256.ofNat 104505810704657832532308207549693575120876051224915683785162626763390386191714), by rfl, by decide⟩,
   ⟨4103, .op .XOR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4104, .push ⟨2, by decide⟩ (UInt256.ofNat 5236), by rfl, by decide⟩,
   ⟨4105, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩]

def hit2Path : List Located :=
  [⟨4106, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4107, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4108, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4109, .push ⟨1, by decide⟩ (UInt256.ofNat 64), by rfl, by decide⟩,
   ⟨4110, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4111, .push ⟨4, by decide⟩ (UInt256.ofNat 2807398299), by rfl, by decide⟩,
   ⟨4112, .push ⟨1, by decide⟩ (UInt256.ofNat 32), by rfl, by decide⟩,
   ⟨4113, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4114, .push ⟨4, by decide⟩ (UInt256.ofNat 514068704), by rfl, by decide⟩,
   ⟨4115, .push ⟨1, by decide⟩ (UInt256.ofNat 64), by rfl, by decide⟩,
   ⟨4116, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4117, .push ⟨4, by decide⟩ (UInt256.ofNat 3681030016), by rfl, by decide⟩,
   ⟨4118, .push ⟨1, by decide⟩ (UInt256.ofNat 96), by rfl, by decide⟩,
   ⟨4119, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4120, .push ⟨4, by decide⟩ (UInt256.ofNat 3354522469), by rfl, by decide⟩,
   ⟨4121, .push ⟨1, by decide⟩ (UInt256.ofNat 128), by rfl, by decide⟩,
   ⟨4122, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4123, .push ⟨4, by decide⟩ (UInt256.ofNat 2543018249), by rfl, by decide⟩,
   ⟨4124, .push ⟨1, by decide⟩ (UInt256.ofNat 160), by rfl, by decide⟩,
   ⟨4125, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4126, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def hitPath : List Located :=
  [⟨4127, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4128, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4129, .push ⟨4, by decide⟩ (UInt256.ofNat 1080717082), by rfl, by decide⟩,
   ⟨4130, .push ⟨1, by decide⟩ (UInt256.ofNat 32), by rfl, by decide⟩,
   ⟨4131, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4132, .push ⟨4, by decide⟩ (UInt256.ofNat 2391128076), by rfl, by decide⟩,
   ⟨4133, .push ⟨1, by decide⟩ (UInt256.ofNat 64), by rfl, by decide⟩,
   ⟨4134, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4135, .push ⟨4, by decide⟩ (UInt256.ofNat 621343384), by rfl, by decide⟩,
   ⟨4136, .push ⟨1, by decide⟩ (UInt256.ofNat 96), by rfl, by decide⟩,
   ⟨4137, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4138, .push ⟨4, by decide⟩ (UInt256.ofNat 220066081), by rfl, by decide⟩,
   ⟨4139, .push ⟨1, by decide⟩ (UInt256.ofNat 128), by rfl, by decide⟩,
   ⟨4140, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4141, .push ⟨4, by decide⟩ (UInt256.ofNat 1007308478), by rfl, by decide⟩,
   ⟨4142, .push ⟨1, by decide⟩ (UInt256.ofNat 160), by rfl, by decide⟩,
   ⟨4143, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4144, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PrefixStatePaths
