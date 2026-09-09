import Batteries.Tactic.OpenPrivate
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Artifact
set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000

/-!
# Located paths of the depth-3 patterned-prefix ladder (instructions 4059..4251)

The ladder occupies the trailing 297 bytes (pc 5040..5336).  Its PC and
instruction lemmas are derived from a split of the instruction list at index
4059 so every `rfl` evaluates only the 193-instruction ladder segment.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PrefixStatePaths

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM

open private
  submissionInstructionsChunk0
  submissionInstructionsChunk1
  submissionInstructionsChunk2
  submissionInstructionsChunk3
  submissionInstructionsChunk4
  submissionInstructionsChunk5
  submissionInstructionsChunk6
  submissionInstructionsChunk7
  submissionInstructionsChunk8
  submissionInstructionsChunk9
  submissionInstructionsChunk10
  submissionInstructionsChunk11
  submissionInstructionsChunk12
  submissionInstructionsChunk13
  submissionInstructionsChunk14
  submissionInstructionsChunk15
  submissionInstructionsChunk16
  submissionInstructionsChunk17
  submissionInstructionsChunk18
  submissionInstructionsChunk19
  submissionInstructionsChunk20
  submissionInstructionsChunk21
  submissionInstructionsChunk0_length
  submissionInstructionsChunk1_length
  submissionInstructionsChunk2_length
  submissionInstructionsChunk3_length
  submissionInstructionsChunk4_length
  submissionInstructionsChunk5_length
  submissionInstructionsChunk6_length
  submissionInstructionsChunk7_length
  submissionInstructionsChunk8_length
  submissionInstructionsChunk9_length
  submissionInstructionsChunk10_length
  submissionInstructionsChunk11_length
  submissionInstructionsChunk12_length
  submissionInstructionsChunk13_length
  submissionInstructionsChunk14_length
  submissionInstructionsChunk15_length
  submissionInstructionsChunk16_length
  submissionInstructionsChunk17_length
  submissionInstructionsChunk18_length
  submissionInstructionsChunk19_length
  submissionInstructionsChunk20_length
  submissionInstructionsChunk21_length
  from Challenge.Ripemd160.Submission.Proofs.Bytecode.Artifact

private def wfOp {op : Operation}
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op)
    (hplain : YulEvmCompiler.plainOp op)
    (havailable : op.availableInFork .Osaka = true) :
    Stepper.WellFormed .Osaka (.op op) := ⟨hopcode,hplain,havailable⟩

abbrev Located := Stepper.Located Artifact.submissionArtifact .Osaka

/-! ## Ladder segment -/

private def ladderBefore : List YulEvmCompiler.Instr :=
  submissionInstructionsChunk0 ++ submissionInstructionsChunk1 ++ submissionInstructionsChunk2 ++ submissionInstructionsChunk3 ++ submissionInstructionsChunk4 ++ submissionInstructionsChunk5 ++ submissionInstructionsChunk6 ++ submissionInstructionsChunk7 ++ submissionInstructionsChunk8 ++ submissionInstructionsChunk9 ++ submissionInstructionsChunk10 ++ submissionInstructionsChunk11 ++ submissionInstructionsChunk12 ++ submissionInstructionsChunk13 ++ submissionInstructionsChunk14 ++ submissionInstructionsChunk15 ++ submissionInstructionsChunk16 ++ submissionInstructionsChunk17 ++ submissionInstructionsChunk18 ++ submissionInstructionsChunk19 ++ submissionInstructionsChunk20.take 72

private def ladderSegment : List YulEvmCompiler.Instr :=
  submissionInstructionsChunk20.drop 72 ++ submissionInstructionsChunk21

private theorem ladderBefore_length : ladderBefore.length = 4059 := by
  simp [ladderBefore]

private theorem ladderSegment_length : ladderSegment.length = 193 := by
  simp [ladderSegment]

private theorem artifact_ladder_split :
    Artifact.submissionArtifact.instructions = ladderBefore ++ ladderSegment ++ [] := by
  change Artifact.submissionInstructions = _
  have hprefix : Artifact.submissionInstructions =
      submissionInstructionsChunk0 ++
      submissionInstructionsChunk1 ++
      submissionInstructionsChunk2 ++
      submissionInstructionsChunk3 ++
      submissionInstructionsChunk4 ++
      submissionInstructionsChunk5 ++
      submissionInstructionsChunk6 ++
      submissionInstructionsChunk7 ++
      submissionInstructionsChunk8 ++
      submissionInstructionsChunk9 ++
      submissionInstructionsChunk10 ++
      submissionInstructionsChunk11 ++
      submissionInstructionsChunk12 ++
      submissionInstructionsChunk13 ++
      submissionInstructionsChunk14 ++
      submissionInstructionsChunk15 ++
      submissionInstructionsChunk16 ++
      submissionInstructionsChunk17 ++
      submissionInstructionsChunk18 ++
      submissionInstructionsChunk19 ++
      submissionInstructionsChunk20 ++
      submissionInstructionsChunk21 := by
    simp only [Artifact.submissionInstructions, List.append_assoc]
  have hchunk : submissionInstructionsChunk20 =
      submissionInstructionsChunk20.take 72 ++ submissionInstructionsChunk20.drop 72 :=
    (List.take_append_drop 72 submissionInstructionsChunk20).symm
  rw [hprefix]
  conv_lhs => rw [hchunk]
  simp only [ladderBefore, ladderSegment, List.append_assoc, List.append_nil]

private theorem ladderBefore_pc :
    (YulEvmCompiler.assembleBytes ladderBefore).length = 5040 := by
  rw [← ArtifactByteLength.byteLength_eq_assemble]
  rfl

private theorem ladder_pc (i : Nat) (hi : i ≤ 193) :
    Artifact.submissionArtifact.instructionPC (4059 + i) =
      5040 + ArtifactByteLength.byteLength (ladderSegment.take i) := by
  rw [ArtifactByteLength.byteLength_eq_assemble]
  exact ArtifactSegment.instructionPC_segment_of_bounds Artifact.submissionArtifact
    ladderBefore ladderSegment [] 4059 5040 artifact_ladder_split ladderBefore_length
    ladderBefore_pc i (by rw [ladderSegment_length]; exact hi)

private theorem ladder_at (i : Nat) (hi : i < 193) :
    Artifact.submissionArtifact.instructions[4059 + i]? = ladderSegment[i]? := by
  have h := ArtifactSegment.getElem?_segment Artifact.submissionArtifact
    ladderBefore ladderSegment [] artifact_ladder_split i (by rw [ladderSegment_length]; exact hi)
  rwa [ladderBefore_length] at h

/-! ## Instruction PCs -/

@[simp] theorem pc4072 : Artifact.submissionArtifact.instructionPC 4059 = 5040 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 0) = 5040
  rw [ladder_pc 0 (by decide)]
  rfl

@[simp] theorem pc4073 : Artifact.submissionArtifact.instructionPC 4060 = 5041 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 1) = 5041
  rw [ladder_pc 1 (by decide)]
  rfl

@[simp] theorem pc4074 : Artifact.submissionArtifact.instructionPC 4061 = 5042 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 2) = 5042
  rw [ladder_pc 2 (by decide)]
  rfl

@[simp] theorem pc4075 : Artifact.submissionArtifact.instructionPC 4062 = 5045 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 3) = 5045
  rw [ladder_pc 3 (by decide)]
  rfl

@[simp] theorem pc4076 : Artifact.submissionArtifact.instructionPC 4063 = 5046 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 4) = 5046
  rw [ladder_pc 4 (by decide)]
  rfl

@[simp] theorem pc4077 : Artifact.submissionArtifact.instructionPC 4064 = 5048 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 5) = 5048
  rw [ladder_pc 5 (by decide)]
  rfl

@[simp] theorem pc4078 : Artifact.submissionArtifact.instructionPC 4065 = 5051 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 6) = 5051
  rw [ladder_pc 6 (by decide)]
  rfl

@[simp] theorem pc4079 : Artifact.submissionArtifact.instructionPC 4066 = 5052 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 7) = 5052
  rw [ladder_pc 7 (by decide)]
  rfl

@[simp] theorem pc4080 : Artifact.submissionArtifact.instructionPC 4067 = 5053 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 8) = 5053
  rw [ladder_pc 8 (by decide)]
  rfl

@[simp] theorem pc4081 : Artifact.submissionArtifact.instructionPC 4068 = 5054 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 9) = 5054
  rw [ladder_pc 9 (by decide)]
  rfl

@[simp] theorem pc4082 : Artifact.submissionArtifact.instructionPC 4069 = 5055 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 10) = 5055
  rw [ladder_pc 10 (by decide)]
  rfl

@[simp] theorem pc4083 : Artifact.submissionArtifact.instructionPC 4070 = 5056 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 11) = 5056
  rw [ladder_pc 11 (by decide)]
  rfl

@[simp] theorem pc4084 : Artifact.submissionArtifact.instructionPC 4071 = 5057 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 12) = 5057
  rw [ladder_pc 12 (by decide)]
  rfl

@[simp] theorem pc4085 : Artifact.submissionArtifact.instructionPC 4072 = 5058 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 13) = 5058
  rw [ladder_pc 13 (by decide)]
  rfl

@[simp] theorem pc4086 : Artifact.submissionArtifact.instructionPC 4073 = 5061 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 14) = 5061
  rw [ladder_pc 14 (by decide)]
  rfl

@[simp] theorem pc4087 : Artifact.submissionArtifact.instructionPC 4074 = 5062 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 15) = 5062
  rw [ladder_pc 15 (by decide)]
  rfl

@[simp] theorem pc4088 : Artifact.submissionArtifact.instructionPC 4075 = 5064 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 16) = 5064
  rw [ladder_pc 16 (by decide)]
  rfl

@[simp] theorem pc4089 : Artifact.submissionArtifact.instructionPC 4076 = 5065 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 17) = 5065
  rw [ladder_pc 17 (by decide)]
  rfl

@[simp] theorem pc4090 : Artifact.submissionArtifact.instructionPC 4077 = 5066 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 18) = 5066
  rw [ladder_pc 18 (by decide)]
  rfl

@[simp] theorem pc4091 : Artifact.submissionArtifact.instructionPC 4078 = 5067 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 19) = 5067
  rw [ladder_pc 19 (by decide)]
  rfl

@[simp] theorem pc4092 : Artifact.submissionArtifact.instructionPC 4079 = 5069 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 20) = 5069
  rw [ladder_pc 20 (by decide)]
  rfl

@[simp] theorem pc4093 : Artifact.submissionArtifact.instructionPC 4080 = 5070 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 21) = 5070
  rw [ladder_pc 21 (by decide)]
  rfl

@[simp] theorem pc4094 : Artifact.submissionArtifact.instructionPC 4081 = 5071 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 22) = 5071
  rw [ladder_pc 22 (by decide)]
  rfl

@[simp] theorem pc4095 : Artifact.submissionArtifact.instructionPC 4082 = 5072 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 23) = 5072
  rw [ladder_pc 23 (by decide)]
  rfl

@[simp] theorem pc4096 : Artifact.submissionArtifact.instructionPC 4083 = 5073 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 24) = 5073
  rw [ladder_pc 24 (by decide)]
  rfl

@[simp] theorem pc4097 : Artifact.submissionArtifact.instructionPC 4084 = 5075 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 25) = 5075
  rw [ladder_pc 25 (by decide)]
  rfl

@[simp] theorem pc4098 : Artifact.submissionArtifact.instructionPC 4085 = 5076 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 26) = 5076
  rw [ladder_pc 26 (by decide)]
  rfl

@[simp] theorem pc4099 : Artifact.submissionArtifact.instructionPC 4086 = 5077 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 27) = 5077
  rw [ladder_pc 27 (by decide)]
  rfl

@[simp] theorem pc4100 : Artifact.submissionArtifact.instructionPC 4087 = 5078 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 28) = 5078
  rw [ladder_pc 28 (by decide)]
  rfl

@[simp] theorem pc4101 : Artifact.submissionArtifact.instructionPC 4088 = 5079 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 29) = 5079
  rw [ladder_pc 29 (by decide)]
  rfl

@[simp] theorem pc4102 : Artifact.submissionArtifact.instructionPC 4089 = 5080 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 30) = 5080
  rw [ladder_pc 30 (by decide)]
  rfl

@[simp] theorem pc4103 : Artifact.submissionArtifact.instructionPC 4090 = 5081 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 31) = 5081
  rw [ladder_pc 31 (by decide)]
  rfl

@[simp] theorem pc4104 : Artifact.submissionArtifact.instructionPC 4091 = 5082 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 32) = 5082
  rw [ladder_pc 32 (by decide)]
  rfl

@[simp] theorem pc4105 : Artifact.submissionArtifact.instructionPC 4092 = 5083 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 33) = 5083
  rw [ladder_pc 33 (by decide)]
  rfl

@[simp] theorem pc4106 : Artifact.submissionArtifact.instructionPC 4093 = 5084 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 34) = 5084
  rw [ladder_pc 34 (by decide)]
  rfl

@[simp] theorem pc4107 : Artifact.submissionArtifact.instructionPC 4094 = 5085 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 35) = 5085
  rw [ladder_pc 35 (by decide)]
  rfl

@[simp] theorem pc4108 : Artifact.submissionArtifact.instructionPC 4095 = 5086 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 36) = 5086
  rw [ladder_pc 36 (by decide)]
  rfl

@[simp] theorem pc4109 : Artifact.submissionArtifact.instructionPC 4096 = 5087 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 37) = 5087
  rw [ladder_pc 37 (by decide)]
  rfl

@[simp] theorem pc4110 : Artifact.submissionArtifact.instructionPC 4097 = 5088 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 38) = 5088
  rw [ladder_pc 38 (by decide)]
  rfl

@[simp] theorem pc4111 : Artifact.submissionArtifact.instructionPC 4098 = 5089 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 39) = 5089
  rw [ladder_pc 39 (by decide)]
  rfl

@[simp] theorem pc4112 : Artifact.submissionArtifact.instructionPC 4099 = 5090 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 40) = 5090
  rw [ladder_pc 40 (by decide)]
  rfl

@[simp] theorem pc4113 : Artifact.submissionArtifact.instructionPC 4100 = 5092 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 41) = 5092
  rw [ladder_pc 41 (by decide)]
  rfl

@[simp] theorem pc4114 : Artifact.submissionArtifact.instructionPC 4101 = 5093 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 42) = 5093
  rw [ladder_pc 42 (by decide)]
  rfl

@[simp] theorem pc4115 : Artifact.submissionArtifact.instructionPC 4102 = 5094 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 43) = 5094
  rw [ladder_pc 43 (by decide)]
  rfl

@[simp] theorem pc4116 : Artifact.submissionArtifact.instructionPC 4103 = 5097 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 44) = 5097
  rw [ladder_pc 44 (by decide)]
  rfl

@[simp] theorem pc4117 : Artifact.submissionArtifact.instructionPC 4104 = 5098 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 45) = 5098
  rw [ladder_pc 45 (by decide)]
  rfl

@[simp] theorem pc4118 : Artifact.submissionArtifact.instructionPC 4105 = 5099 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 46) = 5099
  rw [ladder_pc 46 (by decide)]
  rfl

@[simp] theorem pc4119 : Artifact.submissionArtifact.instructionPC 4106 = 5100 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 47) = 5100
  rw [ladder_pc 47 (by decide)]
  rfl

@[simp] theorem pc4120 : Artifact.submissionArtifact.instructionPC 4107 = 5101 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 48) = 5101
  rw [ladder_pc 48 (by decide)]
  rfl

@[simp] theorem pc4121 : Artifact.submissionArtifact.instructionPC 4108 = 5102 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 49) = 5102
  rw [ladder_pc 49 (by decide)]
  rfl

@[simp] theorem pc4122 : Artifact.submissionArtifact.instructionPC 4109 = 5103 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 50) = 5103
  rw [ladder_pc 50 (by decide)]
  rfl

@[simp] theorem pc4123 : Artifact.submissionArtifact.instructionPC 4110 = 5104 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 51) = 5104
  rw [ladder_pc 51 (by decide)]
  rfl

@[simp] theorem pc4124 : Artifact.submissionArtifact.instructionPC 4111 = 5105 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 52) = 5105
  rw [ladder_pc 52 (by decide)]
  rfl

@[simp] theorem pc4125 : Artifact.submissionArtifact.instructionPC 4112 = 5106 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 53) = 5106
  rw [ladder_pc 53 (by decide)]
  rfl

@[simp] theorem pc4126 : Artifact.submissionArtifact.instructionPC 4113 = 5107 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 54) = 5107
  rw [ladder_pc 54 (by decide)]
  rfl

@[simp] theorem pc4127 : Artifact.submissionArtifact.instructionPC 4114 = 5108 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 55) = 5108
  rw [ladder_pc 55 (by decide)]
  rfl

@[simp] theorem pc4128 : Artifact.submissionArtifact.instructionPC 4115 = 5109 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 56) = 5109
  rw [ladder_pc 56 (by decide)]
  rfl

@[simp] theorem pc4129 : Artifact.submissionArtifact.instructionPC 4116 = 5110 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 57) = 5110
  rw [ladder_pc 57 (by decide)]
  rfl

@[simp] theorem pc4130 : Artifact.submissionArtifact.instructionPC 4117 = 5112 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 58) = 5112
  rw [ladder_pc 58 (by decide)]
  rfl

@[simp] theorem pc4131 : Artifact.submissionArtifact.instructionPC 4118 = 5113 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 59) = 5113
  rw [ladder_pc 59 (by decide)]
  rfl

@[simp] theorem pc4132 : Artifact.submissionArtifact.instructionPC 4119 = 5114 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 60) = 5114
  rw [ladder_pc 60 (by decide)]
  rfl

@[simp] theorem pc4133 : Artifact.submissionArtifact.instructionPC 4120 = 5117 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 61) = 5117
  rw [ladder_pc 61 (by decide)]
  rfl

@[simp] theorem pc4134 : Artifact.submissionArtifact.instructionPC 4121 = 5118 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 62) = 5118
  rw [ladder_pc 62 (by decide)]
  rfl

@[simp] theorem pc4135 : Artifact.submissionArtifact.instructionPC 4122 = 5119 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 63) = 5119
  rw [ladder_pc 63 (by decide)]
  rfl

@[simp] theorem pc4136 : Artifact.submissionArtifact.instructionPC 4123 = 5120 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 64) = 5120
  rw [ladder_pc 64 (by decide)]
  rfl

@[simp] theorem pc4137 : Artifact.submissionArtifact.instructionPC 4124 = 5121 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 65) = 5121
  rw [ladder_pc 65 (by decide)]
  rfl

@[simp] theorem pc4138 : Artifact.submissionArtifact.instructionPC 4125 = 5122 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 66) = 5122
  rw [ladder_pc 66 (by decide)]
  rfl

@[simp] theorem pc4139 : Artifact.submissionArtifact.instructionPC 4126 = 5123 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 67) = 5123
  rw [ladder_pc 67 (by decide)]
  rfl

@[simp] theorem pc4140 : Artifact.submissionArtifact.instructionPC 4127 = 5124 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 68) = 5124
  rw [ladder_pc 68 (by decide)]
  rfl

@[simp] theorem pc4141 : Artifact.submissionArtifact.instructionPC 4128 = 5125 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 69) = 5125
  rw [ladder_pc 69 (by decide)]
  rfl

@[simp] theorem pc4142 : Artifact.submissionArtifact.instructionPC 4129 = 5126 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 70) = 5126
  rw [ladder_pc 70 (by decide)]
  rfl

@[simp] theorem pc4143 : Artifact.submissionArtifact.instructionPC 4130 = 5127 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 71) = 5127
  rw [ladder_pc 71 (by decide)]
  rfl

@[simp] theorem pc4144 : Artifact.submissionArtifact.instructionPC 4131 = 5128 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 72) = 5128
  rw [ladder_pc 72 (by decide)]
  rfl

@[simp] theorem pc4145 : Artifact.submissionArtifact.instructionPC 4132 = 5129 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 73) = 5129
  rw [ladder_pc 73 (by decide)]
  rfl

@[simp] theorem pc4146 : Artifact.submissionArtifact.instructionPC 4133 = 5130 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 74) = 5130
  rw [ladder_pc 74 (by decide)]
  rfl

@[simp] theorem pc4147 : Artifact.submissionArtifact.instructionPC 4134 = 5132 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 75) = 5132
  rw [ladder_pc 75 (by decide)]
  rfl

@[simp] theorem pc4148 : Artifact.submissionArtifact.instructionPC 4135 = 5133 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 76) = 5133
  rw [ladder_pc 76 (by decide)]
  rfl

@[simp] theorem pc4149 : Artifact.submissionArtifact.instructionPC 4136 = 5134 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 77) = 5134
  rw [ladder_pc 77 (by decide)]
  rfl

@[simp] theorem pc4150 : Artifact.submissionArtifact.instructionPC 4137 = 5137 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 78) = 5137
  rw [ladder_pc 78 (by decide)]
  rfl

@[simp] theorem pc4151 : Artifact.submissionArtifact.instructionPC 4138 = 5138 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 79) = 5138
  rw [ladder_pc 79 (by decide)]
  rfl

@[simp] theorem pc4152 : Artifact.submissionArtifact.instructionPC 4139 = 5139 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 80) = 5139
  rw [ladder_pc 80 (by decide)]
  rfl

@[simp] theorem pc4153 : Artifact.submissionArtifact.instructionPC 4140 = 5140 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 81) = 5140
  rw [ladder_pc 81 (by decide)]
  rfl

@[simp] theorem pc4154 : Artifact.submissionArtifact.instructionPC 4141 = 5141 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 82) = 5141
  rw [ladder_pc 82 (by decide)]
  rfl

@[simp] theorem pc4155 : Artifact.submissionArtifact.instructionPC 4142 = 5142 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 83) = 5142
  rw [ladder_pc 83 (by decide)]
  rfl

@[simp] theorem pc4156 : Artifact.submissionArtifact.instructionPC 4143 = 5143 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 84) = 5143
  rw [ladder_pc 84 (by decide)]
  rfl

@[simp] theorem pc4157 : Artifact.submissionArtifact.instructionPC 4144 = 5144 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 85) = 5144
  rw [ladder_pc 85 (by decide)]
  rfl

@[simp] theorem pc4158 : Artifact.submissionArtifact.instructionPC 4145 = 5145 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 86) = 5145
  rw [ladder_pc 86 (by decide)]
  rfl

@[simp] theorem pc4159 : Artifact.submissionArtifact.instructionPC 4146 = 5146 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 87) = 5146
  rw [ladder_pc 87 (by decide)]
  rfl

@[simp] theorem pc4160 : Artifact.submissionArtifact.instructionPC 4147 = 5147 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 88) = 5147
  rw [ladder_pc 88 (by decide)]
  rfl

@[simp] theorem pc4161 : Artifact.submissionArtifact.instructionPC 4148 = 5148 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 89) = 5148
  rw [ladder_pc 89 (by decide)]
  rfl

@[simp] theorem pc4162 : Artifact.submissionArtifact.instructionPC 4149 = 5149 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 90) = 5149
  rw [ladder_pc 90 (by decide)]
  rfl

@[simp] theorem pc4163 : Artifact.submissionArtifact.instructionPC 4150 = 5150 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 91) = 5150
  rw [ladder_pc 91 (by decide)]
  rfl

@[simp] theorem pc4164 : Artifact.submissionArtifact.instructionPC 4151 = 5152 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 92) = 5152
  rw [ladder_pc 92 (by decide)]
  rfl

@[simp] theorem pc4165 : Artifact.submissionArtifact.instructionPC 4152 = 5153 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 93) = 5153
  rw [ladder_pc 93 (by decide)]
  rfl

@[simp] theorem pc4166 : Artifact.submissionArtifact.instructionPC 4153 = 5154 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 94) = 5154
  rw [ladder_pc 94 (by decide)]
  rfl

@[simp] theorem pc4167 : Artifact.submissionArtifact.instructionPC 4154 = 5157 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 95) = 5157
  rw [ladder_pc 95 (by decide)]
  rfl

@[simp] theorem pc4168 : Artifact.submissionArtifact.instructionPC 4155 = 5158 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 96) = 5158
  rw [ladder_pc 96 (by decide)]
  rfl

@[simp] theorem pc4169 : Artifact.submissionArtifact.instructionPC 4156 = 5159 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 97) = 5159
  rw [ladder_pc 97 (by decide)]
  rfl

@[simp] theorem pc4170 : Artifact.submissionArtifact.instructionPC 4157 = 5160 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 98) = 5160
  rw [ladder_pc 98 (by decide)]
  rfl

@[simp] theorem pc4171 : Artifact.submissionArtifact.instructionPC 4158 = 5161 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 99) = 5161
  rw [ladder_pc 99 (by decide)]
  rfl

@[simp] theorem pc4172 : Artifact.submissionArtifact.instructionPC 4159 = 5162 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 100) = 5162
  rw [ladder_pc 100 (by decide)]
  rfl

@[simp] theorem pc4173 : Artifact.submissionArtifact.instructionPC 4160 = 5163 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 101) = 5163
  rw [ladder_pc 101 (by decide)]
  rfl

@[simp] theorem pc4174 : Artifact.submissionArtifact.instructionPC 4161 = 5164 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 102) = 5164
  rw [ladder_pc 102 (by decide)]
  rfl

@[simp] theorem pc4175 : Artifact.submissionArtifact.instructionPC 4162 = 5165 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 103) = 5165
  rw [ladder_pc 103 (by decide)]
  rfl

@[simp] theorem pc4176 : Artifact.submissionArtifact.instructionPC 4163 = 5166 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 104) = 5166
  rw [ladder_pc 104 (by decide)]
  rfl

@[simp] theorem pc4177 : Artifact.submissionArtifact.instructionPC 4164 = 5167 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 105) = 5167
  rw [ladder_pc 105 (by decide)]
  rfl

@[simp] theorem pc4178 : Artifact.submissionArtifact.instructionPC 4165 = 5168 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 106) = 5168
  rw [ladder_pc 106 (by decide)]
  rfl

@[simp] theorem pc4179 : Artifact.submissionArtifact.instructionPC 4166 = 5169 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 107) = 5169
  rw [ladder_pc 107 (by decide)]
  rfl

@[simp] theorem pc4180 : Artifact.submissionArtifact.instructionPC 4167 = 5170 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 108) = 5170
  rw [ladder_pc 108 (by decide)]
  rfl

@[simp] theorem pc4181 : Artifact.submissionArtifact.instructionPC 4168 = 5172 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 109) = 5172
  rw [ladder_pc 109 (by decide)]
  rfl

@[simp] theorem pc4182 : Artifact.submissionArtifact.instructionPC 4169 = 5173 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 110) = 5173
  rw [ladder_pc 110 (by decide)]
  rfl

@[simp] theorem pc4183 : Artifact.submissionArtifact.instructionPC 4170 = 5174 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 111) = 5174
  rw [ladder_pc 111 (by decide)]
  rfl

@[simp] theorem pc4184 : Artifact.submissionArtifact.instructionPC 4171 = 5177 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 112) = 5177
  rw [ladder_pc 112 (by decide)]
  rfl

@[simp] theorem pc4185 : Artifact.submissionArtifact.instructionPC 4172 = 5178 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 113) = 5178
  rw [ladder_pc 113 (by decide)]
  rfl

@[simp] theorem pc4186 : Artifact.submissionArtifact.instructionPC 4173 = 5179 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 114) = 5179
  rw [ladder_pc 114 (by decide)]
  rfl

@[simp] theorem pc4187 : Artifact.submissionArtifact.instructionPC 4174 = 5180 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 115) = 5180
  rw [ladder_pc 115 (by decide)]
  rfl

@[simp] theorem pc4188 : Artifact.submissionArtifact.instructionPC 4175 = 5181 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 116) = 5181
  rw [ladder_pc 116 (by decide)]
  rfl

@[simp] theorem pc4189 : Artifact.submissionArtifact.instructionPC 4176 = 5182 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 117) = 5182
  rw [ladder_pc 117 (by decide)]
  rfl

@[simp] theorem pc4190 : Artifact.submissionArtifact.instructionPC 4177 = 5183 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 118) = 5183
  rw [ladder_pc 118 (by decide)]
  rfl

@[simp] theorem pc4191 : Artifact.submissionArtifact.instructionPC 4178 = 5184 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 119) = 5184
  rw [ladder_pc 119 (by decide)]
  rfl

@[simp] theorem pc4192 : Artifact.submissionArtifact.instructionPC 4179 = 5185 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 120) = 5185
  rw [ladder_pc 120 (by decide)]
  rfl

@[simp] theorem pc4193 : Artifact.submissionArtifact.instructionPC 4180 = 5187 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 121) = 5187
  rw [ladder_pc 121 (by decide)]
  rfl

@[simp] theorem pc4194 : Artifact.submissionArtifact.instructionPC 4181 = 5188 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 122) = 5188
  rw [ladder_pc 122 (by decide)]
  rfl

@[simp] theorem pc4195 : Artifact.submissionArtifact.instructionPC 4182 = 5193 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 123) = 5193
  rw [ladder_pc 123 (by decide)]
  rfl

@[simp] theorem pc4196 : Artifact.submissionArtifact.instructionPC 4183 = 5195 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 124) = 5195
  rw [ladder_pc 124 (by decide)]
  rfl

@[simp] theorem pc4197 : Artifact.submissionArtifact.instructionPC 4184 = 5196 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 125) = 5196
  rw [ladder_pc 125 (by decide)]
  rfl

@[simp] theorem pc4198 : Artifact.submissionArtifact.instructionPC 4185 = 5201 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 126) = 5201
  rw [ladder_pc 126 (by decide)]
  rfl

@[simp] theorem pc4199 : Artifact.submissionArtifact.instructionPC 4186 = 5203 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 127) = 5203
  rw [ladder_pc 127 (by decide)]
  rfl

@[simp] theorem pc4200 : Artifact.submissionArtifact.instructionPC 4187 = 5204 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 128) = 5204
  rw [ladder_pc 128 (by decide)]
  rfl

@[simp] theorem pc4201 : Artifact.submissionArtifact.instructionPC 4188 = 5209 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 129) = 5209
  rw [ladder_pc 129 (by decide)]
  rfl

@[simp] theorem pc4202 : Artifact.submissionArtifact.instructionPC 4189 = 5211 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 130) = 5211
  rw [ladder_pc 130 (by decide)]
  rfl

@[simp] theorem pc4203 : Artifact.submissionArtifact.instructionPC 4190 = 5212 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 131) = 5212
  rw [ladder_pc 131 (by decide)]
  rfl

@[simp] theorem pc4204 : Artifact.submissionArtifact.instructionPC 4191 = 5217 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 132) = 5217
  rw [ladder_pc 132 (by decide)]
  rfl

@[simp] theorem pc4205 : Artifact.submissionArtifact.instructionPC 4192 = 5219 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 133) = 5219
  rw [ladder_pc 133 (by decide)]
  rfl

@[simp] theorem pc4206 : Artifact.submissionArtifact.instructionPC 4193 = 5220 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 134) = 5220
  rw [ladder_pc 134 (by decide)]
  rfl

@[simp] theorem pc4207 : Artifact.submissionArtifact.instructionPC 4194 = 5225 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 135) = 5225
  rw [ladder_pc 135 (by decide)]
  rfl

@[simp] theorem pc4208 : Artifact.submissionArtifact.instructionPC 4195 = 5227 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 136) = 5227
  rw [ladder_pc 136 (by decide)]
  rfl

@[simp] theorem pc4209 : Artifact.submissionArtifact.instructionPC 4196 = 5228 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 137) = 5228
  rw [ladder_pc 137 (by decide)]
  rfl

@[simp] theorem pc4210 : Artifact.submissionArtifact.instructionPC 4197 = 5229 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 138) = 5229
  rw [ladder_pc 138 (by decide)]
  rfl

@[simp] theorem pc4211 : Artifact.submissionArtifact.instructionPC 4198 = 5230 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 139) = 5230
  rw [ladder_pc 139 (by decide)]
  rfl

@[simp] theorem pc4212 : Artifact.submissionArtifact.instructionPC 4199 = 5231 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 140) = 5231
  rw [ladder_pc 140 (by decide)]
  rfl

@[simp] theorem pc4213 : Artifact.submissionArtifact.instructionPC 4200 = 5232 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 141) = 5232
  rw [ladder_pc 141 (by decide)]
  rfl

@[simp] theorem pc4214 : Artifact.submissionArtifact.instructionPC 4201 = 5233 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 142) = 5233
  rw [ladder_pc 142 (by decide)]
  rfl

@[simp] theorem pc4215 : Artifact.submissionArtifact.instructionPC 4202 = 5234 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 143) = 5234
  rw [ladder_pc 143 (by decide)]
  rfl

@[simp] theorem pc4216 : Artifact.submissionArtifact.instructionPC 4203 = 5235 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 144) = 5235
  rw [ladder_pc 144 (by decide)]
  rfl

@[simp] theorem pc4217 : Artifact.submissionArtifact.instructionPC 4204 = 5236 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 145) = 5236
  rw [ladder_pc 145 (by decide)]
  rfl

@[simp] theorem pc4218 : Artifact.submissionArtifact.instructionPC 4205 = 5237 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 146) = 5237
  rw [ladder_pc 146 (by decide)]
  rfl

@[simp] theorem pc4219 : Artifact.submissionArtifact.instructionPC 4206 = 5239 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 147) = 5239
  rw [ladder_pc 147 (by decide)]
  rfl

@[simp] theorem pc4220 : Artifact.submissionArtifact.instructionPC 4207 = 5240 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 148) = 5240
  rw [ladder_pc 148 (by decide)]
  rfl

@[simp] theorem pc4221 : Artifact.submissionArtifact.instructionPC 4208 = 5245 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 149) = 5245
  rw [ladder_pc 149 (by decide)]
  rfl

@[simp] theorem pc4222 : Artifact.submissionArtifact.instructionPC 4209 = 5247 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 150) = 5247
  rw [ladder_pc 150 (by decide)]
  rfl

@[simp] theorem pc4223 : Artifact.submissionArtifact.instructionPC 4210 = 5248 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 151) = 5248
  rw [ladder_pc 151 (by decide)]
  rfl

@[simp] theorem pc4224 : Artifact.submissionArtifact.instructionPC 4211 = 5253 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 152) = 5253
  rw [ladder_pc 152 (by decide)]
  rfl

@[simp] theorem pc4225 : Artifact.submissionArtifact.instructionPC 4212 = 5255 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 153) = 5255
  rw [ladder_pc 153 (by decide)]
  rfl

@[simp] theorem pc4226 : Artifact.submissionArtifact.instructionPC 4213 = 5256 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 154) = 5256
  rw [ladder_pc 154 (by decide)]
  rfl

@[simp] theorem pc4227 : Artifact.submissionArtifact.instructionPC 4214 = 5261 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 155) = 5261
  rw [ladder_pc 155 (by decide)]
  rfl

@[simp] theorem pc4228 : Artifact.submissionArtifact.instructionPC 4215 = 5263 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 156) = 5263
  rw [ladder_pc 156 (by decide)]
  rfl

@[simp] theorem pc4229 : Artifact.submissionArtifact.instructionPC 4216 = 5264 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 157) = 5264
  rw [ladder_pc 157 (by decide)]
  rfl

@[simp] theorem pc4230 : Artifact.submissionArtifact.instructionPC 4217 = 5269 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 158) = 5269
  rw [ladder_pc 158 (by decide)]
  rfl

@[simp] theorem pc4231 : Artifact.submissionArtifact.instructionPC 4218 = 5271 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 159) = 5271
  rw [ladder_pc 159 (by decide)]
  rfl

@[simp] theorem pc4232 : Artifact.submissionArtifact.instructionPC 4219 = 5272 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 160) = 5272
  rw [ladder_pc 160 (by decide)]
  rfl

@[simp] theorem pc4233 : Artifact.submissionArtifact.instructionPC 4220 = 5277 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 161) = 5277
  rw [ladder_pc 161 (by decide)]
  rfl

@[simp] theorem pc4234 : Artifact.submissionArtifact.instructionPC 4221 = 5279 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 162) = 5279
  rw [ladder_pc 162 (by decide)]
  rfl

@[simp] theorem pc4235 : Artifact.submissionArtifact.instructionPC 4222 = 5280 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 163) = 5280
  rw [ladder_pc 163 (by decide)]
  rfl

@[simp] theorem pc4236 : Artifact.submissionArtifact.instructionPC 4223 = 5281 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 164) = 5281
  rw [ladder_pc 164 (by decide)]
  rfl

@[simp] theorem pc4237 : Artifact.submissionArtifact.instructionPC 4224 = 5282 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 165) = 5282
  rw [ladder_pc 165 (by decide)]
  rfl

@[simp] theorem pc4238 : Artifact.submissionArtifact.instructionPC 4225 = 5283 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 166) = 5283
  rw [ladder_pc 166 (by decide)]
  rfl

@[simp] theorem pc4239 : Artifact.submissionArtifact.instructionPC 4226 = 5284 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 167) = 5284
  rw [ladder_pc 167 (by decide)]
  rfl

@[simp] theorem pc4240 : Artifact.submissionArtifact.instructionPC 4227 = 5285 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 168) = 5285
  rw [ladder_pc 168 (by decide)]
  rfl

@[simp] theorem pc4241 : Artifact.submissionArtifact.instructionPC 4228 = 5286 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 169) = 5286
  rw [ladder_pc 169 (by decide)]
  rfl

@[simp] theorem pc4242 : Artifact.submissionArtifact.instructionPC 4229 = 5287 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 170) = 5287
  rw [ladder_pc 170 (by decide)]
  rfl

@[simp] theorem pc4243 : Artifact.submissionArtifact.instructionPC 4230 = 5292 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 171) = 5292
  rw [ladder_pc 171 (by decide)]
  rfl

@[simp] theorem pc4244 : Artifact.submissionArtifact.instructionPC 4231 = 5294 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 172) = 5294
  rw [ladder_pc 172 (by decide)]
  rfl

@[simp] theorem pc4245 : Artifact.submissionArtifact.instructionPC 4232 = 5295 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 173) = 5295
  rw [ladder_pc 173 (by decide)]
  rfl

@[simp] theorem pc4246 : Artifact.submissionArtifact.instructionPC 4233 = 5300 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 174) = 5300
  rw [ladder_pc 174 (by decide)]
  rfl

@[simp] theorem pc4247 : Artifact.submissionArtifact.instructionPC 4234 = 5302 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 175) = 5302
  rw [ladder_pc 175 (by decide)]
  rfl

@[simp] theorem pc4248 : Artifact.submissionArtifact.instructionPC 4235 = 5303 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 176) = 5303
  rw [ladder_pc 176 (by decide)]
  rfl

@[simp] theorem pc4249 : Artifact.submissionArtifact.instructionPC 4236 = 5308 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 177) = 5308
  rw [ladder_pc 177 (by decide)]
  rfl

@[simp] theorem pc4250 : Artifact.submissionArtifact.instructionPC 4237 = 5310 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 178) = 5310
  rw [ladder_pc 178 (by decide)]
  rfl

@[simp] theorem pc4251 : Artifact.submissionArtifact.instructionPC 4238 = 5311 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 179) = 5311
  rw [ladder_pc 179 (by decide)]
  rfl

@[simp] theorem pc4252 : Artifact.submissionArtifact.instructionPC 4239 = 5316 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 180) = 5316
  rw [ladder_pc 180 (by decide)]
  rfl

@[simp] theorem pc4253 : Artifact.submissionArtifact.instructionPC 4240 = 5318 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 181) = 5318
  rw [ladder_pc 181 (by decide)]
  rfl

@[simp] theorem pc4254 : Artifact.submissionArtifact.instructionPC 4241 = 5319 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 182) = 5319
  rw [ladder_pc 182 (by decide)]
  rfl

@[simp] theorem pc4255 : Artifact.submissionArtifact.instructionPC 4242 = 5324 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 183) = 5324
  rw [ladder_pc 183 (by decide)]
  rfl

@[simp] theorem pc4256 : Artifact.submissionArtifact.instructionPC 4243 = 5326 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 184) = 5326
  rw [ladder_pc 184 (by decide)]
  rfl

@[simp] theorem pc4257 : Artifact.submissionArtifact.instructionPC 4244 = 5327 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 185) = 5327
  rw [ladder_pc 185 (by decide)]
  rfl

@[simp] theorem pc4258 : Artifact.submissionArtifact.instructionPC 4245 = 5328 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 186) = 5328
  rw [ladder_pc 186 (by decide)]
  rfl

@[simp] theorem pc4259 : Artifact.submissionArtifact.instructionPC 4246 = 5329 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 187) = 5329
  rw [ladder_pc 187 (by decide)]
  rfl

@[simp] theorem pc4260 : Artifact.submissionArtifact.instructionPC 4247 = 5330 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 188) = 5330
  rw [ladder_pc 188 (by decide)]
  rfl

@[simp] theorem pc4261 : Artifact.submissionArtifact.instructionPC 4248 = 5331 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 189) = 5331
  rw [ladder_pc 189 (by decide)]
  rfl

@[simp] theorem pc4262 : Artifact.submissionArtifact.instructionPC 4249 = 5332 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 190) = 5332
  rw [ladder_pc 190 (by decide)]
  rfl

@[simp] theorem pc4263 : Artifact.submissionArtifact.instructionPC 4250 = 5333 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 191) = 5333
  rw [ladder_pc 191 (by decide)]
  rfl

@[simp] theorem pc4264 : Artifact.submissionArtifact.instructionPC 4251 = 5336 := by
  show Artifact.submissionArtifact.instructionPC (4059 + 192) = 5336
  rw [ladder_pc 192 (by decide)]
  rfl

/-! ## Paths -/

def laterPath : List Located :=
  [⟨4059, .op .JUMPDEST, (ladder_at 0 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4060, .op (.Dup ⟨2, by decide⟩), (ladder_at 1 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4061, .push ⟨2, by decide⟩ (UInt256.ofNat 464), (ladder_at 2 (by decide)).trans rfl, by decide⟩,
   ⟨4062, .op .JUMPI, (ladder_at 3 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩]

def prefixPath : List Located :=
  [⟨4059, .op .JUMPDEST, (ladder_at 0 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4060, .op (.Dup ⟨2, by decide⟩), (ladder_at 1 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4061, .push ⟨2, by decide⟩ (UInt256.ofNat 464), (ladder_at 2 (by decide)).trans rfl, by decide⟩,
   ⟨4062, .op .JUMPI, (ladder_at 3 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4063, .push ⟨1, by decide⟩ (UInt256.ofNat 32), (ladder_at 4 (by decide)).trans rfl, by decide⟩,
   ⟨4064, .push ⟨2, by decide⟩ (UInt256.ofNat 262), (ladder_at 5 (by decide)).trans rfl, by decide⟩,
   ⟨4065, .push ⟨0, by decide⟩ (UInt256.ofNat 0), (ladder_at 6 (by decide)).trans rfl, by decide⟩]

def firstComparePath : List Located :=
  [⟨4067, .push ⟨0, by decide⟩ (UInt256.ofNat 0), (ladder_at 8 (by decide)).trans rfl, by decide⟩,
   ⟨4068, .op .MLOAD, (ladder_at 9 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4069, .push ⟨0, by decide⟩ (UInt256.ofNat 0), (ladder_at 10 (by decide)).trans rfl, by decide⟩,
   ⟨4070, .op .CALLDATALOAD, (ladder_at 11 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4071, .op .XOR, (ladder_at 12 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4072, .push ⟨2, by decide⟩ (UInt256.ofNat 464), (ladder_at 13 (by decide)).trans rfl, by decide⟩,
   ⟨4073, .op .JUMPI, (ladder_at 14 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩]

def setupPath : List Located :=
  [⟨4074, .push ⟨1, by decide⟩ (UInt256.ofNat 255), (ladder_at 15 (by decide)).trans rfl, by decide⟩,
   ⟨4075, .push ⟨0, by decide⟩ (UInt256.ofNat 0), (ladder_at 16 (by decide)).trans rfl, by decide⟩,
   ⟨4076, .op .NOT, (ladder_at 17 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4077, .op .DIV, (ladder_at 18 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4078, .push ⟨1, by decide⟩ (UInt256.ofNat 127), (ladder_at 19 (by decide)).trans rfl, by decide⟩,
   ⟨4079, .op .MUL, (ladder_at 20 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4080, .op (.Dup ⟨0, by decide⟩), (ladder_at 21 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4081, .op .NOT, (ladder_at 22 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4082, .op (.Dup ⟨0, by decide⟩), (ladder_at 23 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4083, .push ⟨1, by decide⟩ (UInt256.ofNat 2), (ladder_at 24 (by decide)).trans rfl, by decide⟩,
   ⟨4084, .op .SHR, (ladder_at 25 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4085, .push ⟨0, by decide⟩ (UInt256.ofNat 0), (ladder_at 26 (by decide)).trans rfl, by decide⟩,
   ⟨4086, .op .MLOAD, (ladder_at 27 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩]

def rung1Path : List Located :=
  [⟨4087, .op (.Dup ⟨0, by decide⟩), (ladder_at 28 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4088, .op (.Dup ⟨4, by decide⟩), (ladder_at 29 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4089, .op .AND, (ladder_at 30 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4090, .op (.Dup ⟨2, by decide⟩), (ladder_at 31 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4091, .op .ADD, (ladder_at 32 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4092, .op (.Swap ⟨0, by decide⟩), (ladder_at 33 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4093, .op (.Dup ⟨3, by decide⟩), (ladder_at 34 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4094, .op .AND, (ladder_at 35 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4095, .op .XOR, (ladder_at 36 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4096, .op (.Dup ⟨2, by decide⟩), (ladder_at 37 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4097, .op .XOR, (ladder_at 38 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4098, .op (.Dup ⟨0, by decide⟩), (ladder_at 39 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4099, .push ⟨1, by decide⟩ (UInt256.ofNat 32), (ladder_at 40 (by decide)).trans rfl, by decide⟩,
   ⟨4100, .op .CALLDATALOAD, (ladder_at 41 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4101, .op .XOR, (ladder_at 42 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4102, .push ⟨2, by decide⟩ (UInt256.ofNat 5328), (ladder_at 43 (by decide)).trans rfl, by decide⟩,
   ⟨4103, .op .JUMPI, (ladder_at 44 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩]

def rung2Path : List Located :=
  [⟨4104, .op (.Dup ⟨0, by decide⟩), (ladder_at 45 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4105, .op (.Dup ⟨4, by decide⟩), (ladder_at 46 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4106, .op .AND, (ladder_at 47 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4107, .op (.Dup ⟨2, by decide⟩), (ladder_at 48 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4108, .op .ADD, (ladder_at 49 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4109, .op (.Swap ⟨0, by decide⟩), (ladder_at 50 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4110, .op (.Dup ⟨3, by decide⟩), (ladder_at 51 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4111, .op .AND, (ladder_at 52 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4112, .op .XOR, (ladder_at 53 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4113, .op (.Dup ⟨2, by decide⟩), (ladder_at 54 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4114, .op .XOR, (ladder_at 55 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4115, .op (.Dup ⟨0, by decide⟩), (ladder_at 56 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4116, .push ⟨1, by decide⟩ (UInt256.ofNat 64), (ladder_at 57 (by decide)).trans rfl, by decide⟩,
   ⟨4117, .op .CALLDATALOAD, (ladder_at 58 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4118, .op .XOR, (ladder_at 59 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4119, .push ⟨2, by decide⟩ (UInt256.ofNat 5281), (ladder_at 60 (by decide)).trans rfl, by decide⟩,
   ⟨4120, .op .JUMPI, (ladder_at 61 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩]

def rung3Path : List Located :=
  [⟨4121, .op (.Dup ⟨0, by decide⟩), (ladder_at 62 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4122, .op (.Dup ⟨4, by decide⟩), (ladder_at 63 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4123, .op .AND, (ladder_at 64 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4124, .op (.Dup ⟨2, by decide⟩), (ladder_at 65 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4125, .op .ADD, (ladder_at 66 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4126, .op (.Swap ⟨0, by decide⟩), (ladder_at 67 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4127, .op (.Dup ⟨3, by decide⟩), (ladder_at 68 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4128, .op .AND, (ladder_at 69 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4129, .op .XOR, (ladder_at 70 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4130, .op (.Dup ⟨2, by decide⟩), (ladder_at 71 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4131, .op .XOR, (ladder_at 72 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4132, .op (.Dup ⟨0, by decide⟩), (ladder_at 73 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4133, .push ⟨1, by decide⟩ (UInt256.ofNat 96), (ladder_at 74 (by decide)).trans rfl, by decide⟩,
   ⟨4134, .op .CALLDATALOAD, (ladder_at 75 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4135, .op .XOR, (ladder_at 76 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4136, .push ⟨2, by decide⟩ (UInt256.ofNat 5281), (ladder_at 77 (by decide)).trans rfl, by decide⟩,
   ⟨4137, .op .JUMPI, (ladder_at 78 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩]

def rung4Path : List Located :=
  [⟨4138, .op (.Dup ⟨0, by decide⟩), (ladder_at 79 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4139, .op (.Dup ⟨4, by decide⟩), (ladder_at 80 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4140, .op .AND, (ladder_at 81 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4141, .op (.Dup ⟨2, by decide⟩), (ladder_at 82 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4142, .op .ADD, (ladder_at 83 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4143, .op (.Swap ⟨0, by decide⟩), (ladder_at 84 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4144, .op (.Dup ⟨3, by decide⟩), (ladder_at 85 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4145, .op .AND, (ladder_at 86 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4146, .op .XOR, (ladder_at 87 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4147, .op (.Dup ⟨2, by decide⟩), (ladder_at 88 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4148, .op .XOR, (ladder_at 89 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4149, .op (.Dup ⟨0, by decide⟩), (ladder_at 90 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4150, .push ⟨1, by decide⟩ (UInt256.ofNat 128), (ladder_at 91 (by decide)).trans rfl, by decide⟩,
   ⟨4151, .op .CALLDATALOAD, (ladder_at 92 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4152, .op .XOR, (ladder_at 93 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4153, .push ⟨2, by decide⟩ (UInt256.ofNat 5229), (ladder_at 94 (by decide)).trans rfl, by decide⟩,
   ⟨4154, .op .JUMPI, (ladder_at 95 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩]

def rung5Path : List Located :=
  [⟨4155, .op (.Dup ⟨0, by decide⟩), (ladder_at 96 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4156, .op (.Dup ⟨4, by decide⟩), (ladder_at 97 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4157, .op .AND, (ladder_at 98 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4158, .op (.Dup ⟨2, by decide⟩), (ladder_at 99 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4159, .op .ADD, (ladder_at 100 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4160, .op (.Swap ⟨0, by decide⟩), (ladder_at 101 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4161, .op (.Dup ⟨3, by decide⟩), (ladder_at 102 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4162, .op .AND, (ladder_at 103 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4163, .op .XOR, (ladder_at 104 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4164, .op (.Dup ⟨2, by decide⟩), (ladder_at 105 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4165, .op .XOR, (ladder_at 106 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4166, .op (.Dup ⟨0, by decide⟩), (ladder_at 107 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4167, .push ⟨1, by decide⟩ (UInt256.ofNat 160), (ladder_at 108 (by decide)).trans rfl, by decide⟩,
   ⟨4168, .op .CALLDATALOAD, (ladder_at 109 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4169, .op .XOR, (ladder_at 110 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4170, .push ⟨2, by decide⟩ (UInt256.ofNat 5229), (ladder_at 111 (by decide)).trans rfl, by decide⟩,
   ⟨4171, .op .JUMPI, (ladder_at 112 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩]

def hit3Path : List Located :=
  [⟨4172, .op .POP, (ladder_at 113 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4173, .op .POP, (ladder_at 114 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4174, .op .POP, (ladder_at 115 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4175, .op .POP, (ladder_at 116 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4176, .op .POP, (ladder_at 117 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4177, .op (.Swap ⟨0, by decide⟩), (ladder_at 118 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4178, .op .POP, (ladder_at 119 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4179, .push ⟨1, by decide⟩ (UInt256.ofNat 128), (ladder_at 120 (by decide)).trans rfl, by decide⟩,
   ⟨4180, .op (.Swap ⟨0, by decide⟩), (ladder_at 121 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4181, .push ⟨4, by decide⟩ (UInt256.ofNat 1393315003), (ladder_at 122 (by decide)).trans rfl, by decide⟩,
   ⟨4182, .push ⟨1, by decide⟩ (UInt256.ofNat 32), (ladder_at 123 (by decide)).trans rfl, by decide⟩,
   ⟨4183, .op .MSTORE, (ladder_at 124 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4184, .push ⟨4, by decide⟩ (UInt256.ofNat 695251451), (ladder_at 125 (by decide)).trans rfl, by decide⟩,
   ⟨4185, .push ⟨1, by decide⟩ (UInt256.ofNat 64), (ladder_at 126 (by decide)).trans rfl, by decide⟩,
   ⟨4186, .op .MSTORE, (ladder_at 127 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4187, .push ⟨4, by decide⟩ (UInt256.ofNat 358732556), (ladder_at 128 (by decide)).trans rfl, by decide⟩,
   ⟨4188, .push ⟨1, by decide⟩ (UInt256.ofNat 96), (ladder_at 129 (by decide)).trans rfl, by decide⟩,
   ⟨4189, .op .MSTORE, (ladder_at 130 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4190, .push ⟨4, by decide⟩ (UInt256.ofNat 928826907), (ladder_at 131 (by decide)).trans rfl, by decide⟩,
   ⟨4191, .push ⟨1, by decide⟩ (UInt256.ofNat 128), (ladder_at 132 (by decide)).trans rfl, by decide⟩,
   ⟨4192, .op .MSTORE, (ladder_at 133 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4193, .push ⟨4, by decide⟩ (UInt256.ofNat 3850323193), (ladder_at 134 (by decide)).trans rfl, by decide⟩,
   ⟨4194, .push ⟨1, by decide⟩ (UInt256.ofNat 160), (ladder_at 135 (by decide)).trans rfl, by decide⟩,
   ⟨4195, .op .MSTORE, (ladder_at 136 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4196, .op .JUMP, (ladder_at 137 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩]

def hit2Path : List Located :=
  [⟨4197, .op .JUMPDEST, (ladder_at 138 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4198, .op .POP, (ladder_at 139 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4199, .op .POP, (ladder_at 140 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4200, .op .POP, (ladder_at 141 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4201, .op .POP, (ladder_at 142 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4202, .op .POP, (ladder_at 143 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4203, .op (.Swap ⟨0, by decide⟩), (ladder_at 144 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4204, .op .POP, (ladder_at 145 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4205, .push ⟨1, by decide⟩ (UInt256.ofNat 64), (ladder_at 146 (by decide)).trans rfl, by decide⟩,
   ⟨4206, .op (.Swap ⟨0, by decide⟩), (ladder_at 147 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4207, .push ⟨4, by decide⟩ (UInt256.ofNat 2807398299), (ladder_at 148 (by decide)).trans rfl, by decide⟩,
   ⟨4208, .push ⟨1, by decide⟩ (UInt256.ofNat 32), (ladder_at 149 (by decide)).trans rfl, by decide⟩,
   ⟨4209, .op .MSTORE, (ladder_at 150 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4210, .push ⟨4, by decide⟩ (UInt256.ofNat 514068704), (ladder_at 151 (by decide)).trans rfl, by decide⟩,
   ⟨4211, .push ⟨1, by decide⟩ (UInt256.ofNat 64), (ladder_at 152 (by decide)).trans rfl, by decide⟩,
   ⟨4212, .op .MSTORE, (ladder_at 153 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4213, .push ⟨4, by decide⟩ (UInt256.ofNat 3681030016), (ladder_at 154 (by decide)).trans rfl, by decide⟩,
   ⟨4214, .push ⟨1, by decide⟩ (UInt256.ofNat 96), (ladder_at 155 (by decide)).trans rfl, by decide⟩,
   ⟨4215, .op .MSTORE, (ladder_at 156 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4216, .push ⟨4, by decide⟩ (UInt256.ofNat 3354522469), (ladder_at 157 (by decide)).trans rfl, by decide⟩,
   ⟨4217, .push ⟨1, by decide⟩ (UInt256.ofNat 128), (ladder_at 158 (by decide)).trans rfl, by decide⟩,
   ⟨4218, .op .MSTORE, (ladder_at 159 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4219, .push ⟨4, by decide⟩ (UInt256.ofNat 2543018249), (ladder_at 160 (by decide)).trans rfl, by decide⟩,
   ⟨4220, .push ⟨1, by decide⟩ (UInt256.ofNat 160), (ladder_at 161 (by decide)).trans rfl, by decide⟩,
   ⟨4221, .op .MSTORE, (ladder_at 162 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4222, .op .JUMP, (ladder_at 163 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩]

def hit1Path : List Located :=
  [⟨4223, .op .JUMPDEST, (ladder_at 164 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4224, .op .POP, (ladder_at 165 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4225, .op .POP, (ladder_at 166 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4226, .op .POP, (ladder_at 167 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4227, .op .POP, (ladder_at 168 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4228, .op .POP, (ladder_at 169 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4229, .push ⟨4, by decide⟩ (UInt256.ofNat 1080717082), (ladder_at 170 (by decide)).trans rfl, by decide⟩,
   ⟨4230, .push ⟨1, by decide⟩ (UInt256.ofNat 32), (ladder_at 171 (by decide)).trans rfl, by decide⟩,
   ⟨4231, .op .MSTORE, (ladder_at 172 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4232, .push ⟨4, by decide⟩ (UInt256.ofNat 2391128076), (ladder_at 173 (by decide)).trans rfl, by decide⟩,
   ⟨4233, .push ⟨1, by decide⟩ (UInt256.ofNat 64), (ladder_at 174 (by decide)).trans rfl, by decide⟩,
   ⟨4234, .op .MSTORE, (ladder_at 175 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4235, .push ⟨4, by decide⟩ (UInt256.ofNat 621343384), (ladder_at 176 (by decide)).trans rfl, by decide⟩,
   ⟨4236, .push ⟨1, by decide⟩ (UInt256.ofNat 96), (ladder_at 177 (by decide)).trans rfl, by decide⟩,
   ⟨4237, .op .MSTORE, (ladder_at 178 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4238, .push ⟨4, by decide⟩ (UInt256.ofNat 220066081), (ladder_at 179 (by decide)).trans rfl, by decide⟩,
   ⟨4239, .push ⟨1, by decide⟩ (UInt256.ofNat 128), (ladder_at 180 (by decide)).trans rfl, by decide⟩,
   ⟨4240, .op .MSTORE, (ladder_at 181 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4241, .push ⟨4, by decide⟩ (UInt256.ofNat 1007308478), (ladder_at 182 (by decide)).trans rfl, by decide⟩,
   ⟨4242, .push ⟨1, by decide⟩ (UInt256.ofNat 160), (ladder_at 183 (by decide)).trans rfl, by decide⟩,
   ⟨4243, .op .MSTORE, (ladder_at 184 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4244, .op .JUMP, (ladder_at 185 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩]

def bailPath : List Located :=
  [⟨4245, .op .JUMPDEST, (ladder_at 186 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4246, .op .POP, (ladder_at 187 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4247, .op .POP, (ladder_at 188 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4248, .op .POP, (ladder_at 189 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4249, .op .POP, (ladder_at 190 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4250, .push ⟨2, by decide⟩ (UInt256.ofNat 464), (ladder_at 191 (by decide)).trans rfl, by decide⟩,
   ⟨4251, .op .JUMP, (ladder_at 192 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PrefixStatePaths
