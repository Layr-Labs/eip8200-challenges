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

@[simp] theorem pc4105 : Artifact.submissionArtifact.instructionPC 4129 = 5299 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4106 : Artifact.submissionArtifact.instructionPC 4130 = 5300 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4107 : Artifact.submissionArtifact.instructionPC 4131 = 5301 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4108 : Artifact.submissionArtifact.instructionPC 4132 = 5302 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4109 : Artifact.submissionArtifact.instructionPC 4133 = 5304 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4110 : Artifact.submissionArtifact.instructionPC 4134 = 5305 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4111 : Artifact.submissionArtifact.instructionPC 4135 = 5310 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4112 : Artifact.submissionArtifact.instructionPC 4136 = 5312 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4113 : Artifact.submissionArtifact.instructionPC 4137 = 5313 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4114 : Artifact.submissionArtifact.instructionPC 4138 = 5318 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4115 : Artifact.submissionArtifact.instructionPC 4139 = 5320 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4116 : Artifact.submissionArtifact.instructionPC 4140 = 5321 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4117 : Artifact.submissionArtifact.instructionPC 4141 = 5326 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4118 : Artifact.submissionArtifact.instructionPC 4142 = 5328 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4119 : Artifact.submissionArtifact.instructionPC 4143 = 5329 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4120 : Artifact.submissionArtifact.instructionPC 4144 = 5334 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4121 : Artifact.submissionArtifact.instructionPC 4145 = 5336 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4122 : Artifact.submissionArtifact.instructionPC 4146 = 5337 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4123 : Artifact.submissionArtifact.instructionPC 4147 = 5342 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4124 : Artifact.submissionArtifact.instructionPC 4148 = 5344 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4125 : Artifact.submissionArtifact.instructionPC 4149 = 5345 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4126 : Artifact.submissionArtifact.instructionPC 4150 = 5346 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4127 : Artifact.submissionArtifact.instructionPC 4151 = 5347 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4128 : Artifact.submissionArtifact.instructionPC 4152 = 5348 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4129 : Artifact.submissionArtifact.instructionPC 4153 = 5353 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4130 : Artifact.submissionArtifact.instructionPC 4154 = 5355 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4131 : Artifact.submissionArtifact.instructionPC 4155 = 5356 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4132 : Artifact.submissionArtifact.instructionPC 4156 = 5361 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4133 : Artifact.submissionArtifact.instructionPC 4157 = 5363 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4134 : Artifact.submissionArtifact.instructionPC 4158 = 5364 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4135 : Artifact.submissionArtifact.instructionPC 4159 = 5369 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4136 : Artifact.submissionArtifact.instructionPC 4160 = 5371 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4137 : Artifact.submissionArtifact.instructionPC 4161 = 5372 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4138 : Artifact.submissionArtifact.instructionPC 4162 = 5377 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4139 : Artifact.submissionArtifact.instructionPC 4163 = 5379 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4140 : Artifact.submissionArtifact.instructionPC 4164 = 5380 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4141 : Artifact.submissionArtifact.instructionPC 4165 = 5385 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4142 : Artifact.submissionArtifact.instructionPC 4166 = 5387 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc4143 : Artifact.submissionArtifact.instructionPC 4167 = 5388 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

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
   ⟨4097, .push ⟨2, by decide⟩ (UInt256.ofNat 5346), by rfl, by decide⟩,
   ⟨4098, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩]

def fourthComparePath : List Located :=
  [⟨4099, .push ⟨1, by decide⟩ (UInt256.ofNat 96), by rfl, by decide⟩,
   ⟨4100, .op .CALLDATALOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4101, .push ⟨32, by decide⟩ (UInt256.ofNat 104505810704657832532308207549693575120876051224915683785162626763390386191714), by rfl, by decide⟩,
   ⟨4102, .op .XOR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4103, .push ⟨2, by decide⟩ (UInt256.ofNat 5346), by rfl, by decide⟩,
   ⟨4104, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩]

@[simp] theorem widePc4105 : Artifact.submissionArtifact.instructionPC 4105 = 5135 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem widePc4106 : Artifact.submissionArtifact.instructionPC 4106 = 5137 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem widePc4107 : Artifact.submissionArtifact.instructionPC 4107 = 5138 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem widePc4108 : Artifact.submissionArtifact.instructionPC 4108 = 5171 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem widePc4109 : Artifact.submissionArtifact.instructionPC 4109 = 5172 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem widePc4110 : Artifact.submissionArtifact.instructionPC 4110 = 5175 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

def word4ComparePath : List Located :=
  [⟨4105, .push ⟨1, by decide⟩ (UInt256.ofNat 128), by rfl, by decide⟩,
   ⟨4106, .op .CALLDATALOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4107, .push ⟨32, by decide⟩ (UInt256.ofNat 61367581353886127001238131413293229573374005415347599533452268822761471270146), by rfl, by decide⟩,
   ⟨4108, .op .XOR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4109, .push ⟨2, by decide⟩ (UInt256.ofNat 5346), by rfl, by decide⟩,
   ⟨4110, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩]

@[simp] theorem widePc4111 : Artifact.submissionArtifact.instructionPC 4111 = 5176 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem widePc4112 : Artifact.submissionArtifact.instructionPC 4112 = 5178 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem widePc4113 : Artifact.submissionArtifact.instructionPC 4113 = 5179 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem widePc4114 : Artifact.submissionArtifact.instructionPC 4114 = 5212 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem widePc4115 : Artifact.submissionArtifact.instructionPC 4115 = 5213 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem widePc4116 : Artifact.submissionArtifact.instructionPC 4116 = 5216 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

def word5ComparePath : List Located :=
  [⟨4111, .push ⟨1, by decide⟩ (UInt256.ofNat 160), by rfl, by decide⟩,
   ⟨4112, .op .CALLDATALOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4113, .push ⟨32, by decide⟩ (UInt256.ofNat 17775265432785288859418840296405106407947132191047579206632289663109943557538), by rfl, by decide⟩,
   ⟨4114, .op .XOR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4115, .push ⟨2, by decide⟩ (UInt256.ofNat 5346), by rfl, by decide⟩,
   ⟨4116, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩]

@[simp] theorem widePc4117 : Artifact.submissionArtifact.instructionPC 4117 = 5217 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem widePc4118 : Artifact.submissionArtifact.instructionPC 4118 = 5219 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem widePc4119 : Artifact.submissionArtifact.instructionPC 4119 = 5220 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem widePc4120 : Artifact.submissionArtifact.instructionPC 4120 = 5253 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem widePc4121 : Artifact.submissionArtifact.instructionPC 4121 = 5254 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem widePc4122 : Artifact.submissionArtifact.instructionPC 4122 = 5257 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

def word6ComparePath : List Located :=
  [⟨4117, .push ⟨1, by decide⟩ (UInt256.ofNat 192), by rfl, by decide⟩,
   ⟨4118, .op .CALLDATALOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4119, .push ⟨32, by decide⟩ (UInt256.ofNat 90427351570519066560079137287317450753818552617089646512985429813514949107010), by rfl, by decide⟩,
   ⟨4120, .op .XOR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4121, .push ⟨2, by decide⟩ (UInt256.ofNat 5346), by rfl, by decide⟩,
   ⟨4122, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩]

@[simp] theorem widePc4123 : Artifact.submissionArtifact.instructionPC 4123 = 5258 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem widePc4124 : Artifact.submissionArtifact.instructionPC 4124 = 5260 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem widePc4125 : Artifact.submissionArtifact.instructionPC 4125 = 5261 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem widePc4126 : Artifact.submissionArtifact.instructionPC 4126 = 5294 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem widePc4127 : Artifact.submissionArtifact.instructionPC 4127 = 5295 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem widePc4128 : Artifact.submissionArtifact.instructionPC 4128 = 5298 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

def word7ComparePath : List Located :=
  [⟨4123, .push ⟨1, by decide⟩ (UInt256.ofNat 224), by rfl, by decide⟩,
   ⟨4124, .op .CALLDATALOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4125, .push ⟨32, by decide⟩ (UInt256.ofNat 46836809398124041301509275424151671459047373308733951134252891636799006558445), by rfl, by decide⟩,
   ⟨4126, .op .XOR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4127, .push ⟨2, by decide⟩ (UInt256.ofNat 5346), by rfl, by decide⟩,
   ⟨4128, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩]

def hit2Path : List Located :=
  [⟨4129, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4130, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4131, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4132, .push ⟨1, by decide⟩ (UInt256.ofNat 192), by rfl, by decide⟩,
   ⟨4133, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4134, .push ⟨4, by decide⟩ (UInt256.ofNat 4072035125), by rfl, by decide⟩,
   ⟨4135, .push ⟨1, by decide⟩ (UInt256.ofNat 32), by rfl, by decide⟩,
   ⟨4136, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4137, .push ⟨4, by decide⟩ (UInt256.ofNat 1663407839), by rfl, by decide⟩,
   ⟨4138, .push ⟨1, by decide⟩ (UInt256.ofNat 64), by rfl, by decide⟩,
   ⟨4139, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4140, .push ⟨4, by decide⟩ (UInt256.ofNat 3044672391), by rfl, by decide⟩,
   ⟨4141, .push ⟨1, by decide⟩ (UInt256.ofNat 96), by rfl, by decide⟩,
   ⟨4142, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4143, .push ⟨4, by decide⟩ (UInt256.ofNat 4264519132), by rfl, by decide⟩,
   ⟨4144, .push ⟨1, by decide⟩ (UInt256.ofNat 128), by rfl, by decide⟩,
   ⟨4145, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4146, .push ⟨4, by decide⟩ (UInt256.ofNat 737150935), by rfl, by decide⟩,
   ⟨4147, .push ⟨1, by decide⟩ (UInt256.ofNat 160), by rfl, by decide⟩,
   ⟨4148, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4149, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def hitPath : List Located :=
  [⟨4150, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4151, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4152, .push ⟨4, by decide⟩ (UInt256.ofNat 1080717082), by rfl, by decide⟩,
   ⟨4153, .push ⟨1, by decide⟩ (UInt256.ofNat 32), by rfl, by decide⟩,
   ⟨4154, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4155, .push ⟨4, by decide⟩ (UInt256.ofNat 2391128076), by rfl, by decide⟩,
   ⟨4156, .push ⟨1, by decide⟩ (UInt256.ofNat 64), by rfl, by decide⟩,
   ⟨4157, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4158, .push ⟨4, by decide⟩ (UInt256.ofNat 621343384), by rfl, by decide⟩,
   ⟨4159, .push ⟨1, by decide⟩ (UInt256.ofNat 96), by rfl, by decide⟩,
   ⟨4160, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4161, .push ⟨4, by decide⟩ (UInt256.ofNat 220066081), by rfl, by decide⟩,
   ⟨4162, .push ⟨1, by decide⟩ (UInt256.ofNat 128), by rfl, by decide⟩,
   ⟨4163, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4164, .push ⟨4, by decide⟩ (UInt256.ofNat 1007308478), by rfl, by decide⟩,
   ⟨4165, .push ⟨1, by decide⟩ (UInt256.ofNat 160), by rfl, by decide⟩,
   ⟨4166, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4167, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PrefixStatePaths
