import Batteries.Tactic.OpenPrivate
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Artifact
set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000

/-!
# Located paths of the depth-3 patterned-prefix ladder (instructions 4065..4257)

The ladder occupies the trailing 390 bytes (pc 4990..5379).  Its PC and
instruction lemmas are derived from a split of the instruction list at index
4065 so every `rfl` evaluates only the 193-instruction ladder segment.
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

private theorem ladderBefore_length : ladderBefore.length = 4065 := by
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
    (YulEvmCompiler.assembleBytes ladderBefore).length = 4990 := by
  rw [← ArtifactByteLength.byteLength_eq_assemble]
  rfl

private theorem ladder_pc (i : Nat) (hi : i ≤ 193) :
    Artifact.submissionArtifact.instructionPC (4065 + i) =
      4990 + ArtifactByteLength.byteLength (ladderSegment.take i) := by
  rw [ArtifactByteLength.byteLength_eq_assemble]
  exact ArtifactSegment.instructionPC_segment_of_bounds Artifact.submissionArtifact
    ladderBefore ladderSegment [] 4065 4990 artifact_ladder_split ladderBefore_length
    ladderBefore_pc i (by rw [ladderSegment_length]; exact hi)

private theorem ladder_at (i : Nat) (hi : i < 193) :
    Artifact.submissionArtifact.instructions[4065 + i]? = ladderSegment[i]? := by
  have h := ArtifactSegment.getElem?_segment Artifact.submissionArtifact
    ladderBefore ladderSegment [] artifact_ladder_split i (by rw [ladderSegment_length]; exact hi)
  rwa [ladderBefore_length] at h

/-! ## Instruction PCs -/

@[simp] theorem pc4072 : Artifact.submissionArtifact.instructionPC 4065 = 4990 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 0) = 4990
  rw [ladder_pc 0 (by decide)]
  rfl

@[simp] theorem pc4073 : Artifact.submissionArtifact.instructionPC 4066 = 4991 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 1) = 4991
  rw [ladder_pc 1 (by decide)]
  rfl

@[simp] theorem pc4074 : Artifact.submissionArtifact.instructionPC 4067 = 4992 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 2) = 4992
  rw [ladder_pc 2 (by decide)]
  rfl

@[simp] theorem pc4075 : Artifact.submissionArtifact.instructionPC 4068 = 4995 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 3) = 4995
  rw [ladder_pc 3 (by decide)]
  rfl

@[simp] theorem pc4076 : Artifact.submissionArtifact.instructionPC 4069 = 4996 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 4) = 4996
  rw [ladder_pc 4 (by decide)]
  rfl

@[simp] theorem pc4077 : Artifact.submissionArtifact.instructionPC 4070 = 4998 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 5) = 4998
  rw [ladder_pc 5 (by decide)]
  rfl

@[simp] theorem pc4078 : Artifact.submissionArtifact.instructionPC 4071 = 5001 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 6) = 5001
  rw [ladder_pc 6 (by decide)]
  rfl

@[simp] theorem pc4079 : Artifact.submissionArtifact.instructionPC 4072 = 5002 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 7) = 5002
  rw [ladder_pc 7 (by decide)]
  rfl

@[simp] theorem pc4080 : Artifact.submissionArtifact.instructionPC 4073 = 5003 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 8) = 5003
  rw [ladder_pc 8 (by decide)]
  rfl

@[simp] theorem pc4081 : Artifact.submissionArtifact.instructionPC 4074 = 5004 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 9) = 5004
  rw [ladder_pc 9 (by decide)]
  rfl

@[simp] theorem pc4082 : Artifact.submissionArtifact.instructionPC 4075 = 5005 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 10) = 5005
  rw [ladder_pc 10 (by decide)]
  rfl

@[simp] theorem pc4083 : Artifact.submissionArtifact.instructionPC 4076 = 5006 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 11) = 5006
  rw [ladder_pc 11 (by decide)]
  rfl

@[simp] theorem pc4084 : Artifact.submissionArtifact.instructionPC 4077 = 5007 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 12) = 5007
  rw [ladder_pc 12 (by decide)]
  rfl

@[simp] theorem pc4085 : Artifact.submissionArtifact.instructionPC 4078 = 5008 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 13) = 5008
  rw [ladder_pc 13 (by decide)]
  rfl

@[simp] theorem pc4086 : Artifact.submissionArtifact.instructionPC 4079 = 5011 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 14) = 5011
  rw [ladder_pc 14 (by decide)]
  rfl

@[simp] theorem pc4087 : Artifact.submissionArtifact.instructionPC 4080 = 5012 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 15) = 5012
  rw [ladder_pc 15 (by decide)]
  rfl

@[simp] theorem pc4088 : Artifact.submissionArtifact.instructionPC 4081 = 5045 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 16) = 5045
  rw [ladder_pc 16 (by decide)]
  rfl

@[simp] theorem pc4089 : Artifact.submissionArtifact.instructionPC 4082 = 5078 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 17) = 5078
  rw [ladder_pc 17 (by decide)]
  rfl

@[simp] theorem pc4090 : Artifact.submissionArtifact.instructionPC 4083 = 5111 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 18) = 5111
  rw [ladder_pc 18 (by decide)]
  rfl

@[simp] theorem pc4091 : Artifact.submissionArtifact.instructionPC 4084 = 5112 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 19) = 5112
  rw [ladder_pc 19 (by decide)]
  rfl

@[simp] theorem pc4092 : Artifact.submissionArtifact.instructionPC 4085 = 5113 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 20) = 5113
  rw [ladder_pc 20 (by decide)]
  rfl

@[simp] theorem pc4093 : Artifact.submissionArtifact.instructionPC 4086 = 5114 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 21) = 5114
  rw [ladder_pc 21 (by decide)]
  rfl

@[simp] theorem pc4094 : Artifact.submissionArtifact.instructionPC 4087 = 5115 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 22) = 5115
  rw [ladder_pc 22 (by decide)]
  rfl

@[simp] theorem pc4095 : Artifact.submissionArtifact.instructionPC 4088 = 5116 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 23) = 5116
  rw [ladder_pc 23 (by decide)]
  rfl

@[simp] theorem pc4096 : Artifact.submissionArtifact.instructionPC 4089 = 5117 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 24) = 5117
  rw [ladder_pc 24 (by decide)]
  rfl

@[simp] theorem pc4097 : Artifact.submissionArtifact.instructionPC 4090 = 5118 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 25) = 5118
  rw [ladder_pc 25 (by decide)]
  rfl

@[simp] theorem pc4098 : Artifact.submissionArtifact.instructionPC 4091 = 5119 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 26) = 5119
  rw [ladder_pc 26 (by decide)]
  rfl

@[simp] theorem pc4099 : Artifact.submissionArtifact.instructionPC 4092 = 5120 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 27) = 5120
  rw [ladder_pc 27 (by decide)]
  rfl

@[simp] theorem pc4100 : Artifact.submissionArtifact.instructionPC 4093 = 5121 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 28) = 5121
  rw [ladder_pc 28 (by decide)]
  rfl

@[simp] theorem pc4101 : Artifact.submissionArtifact.instructionPC 4094 = 5122 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 29) = 5122
  rw [ladder_pc 29 (by decide)]
  rfl

@[simp] theorem pc4102 : Artifact.submissionArtifact.instructionPC 4095 = 5123 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 30) = 5123
  rw [ladder_pc 30 (by decide)]
  rfl

@[simp] theorem pc4103 : Artifact.submissionArtifact.instructionPC 4096 = 5124 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 31) = 5124
  rw [ladder_pc 31 (by decide)]
  rfl

@[simp] theorem pc4104 : Artifact.submissionArtifact.instructionPC 4097 = 5125 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 32) = 5125
  rw [ladder_pc 32 (by decide)]
  rfl

@[simp] theorem pc4105 : Artifact.submissionArtifact.instructionPC 4098 = 5126 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 33) = 5126
  rw [ladder_pc 33 (by decide)]
  rfl

@[simp] theorem pc4106 : Artifact.submissionArtifact.instructionPC 4099 = 5127 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 34) = 5127
  rw [ladder_pc 34 (by decide)]
  rfl

@[simp] theorem pc4107 : Artifact.submissionArtifact.instructionPC 4100 = 5128 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 35) = 5128
  rw [ladder_pc 35 (by decide)]
  rfl

@[simp] theorem pc4108 : Artifact.submissionArtifact.instructionPC 4101 = 5129 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 36) = 5129
  rw [ladder_pc 36 (by decide)]
  rfl

@[simp] theorem pc4109 : Artifact.submissionArtifact.instructionPC 4102 = 5130 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 37) = 5130
  rw [ladder_pc 37 (by decide)]
  rfl

@[simp] theorem pc4110 : Artifact.submissionArtifact.instructionPC 4103 = 5131 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 38) = 5131
  rw [ladder_pc 38 (by decide)]
  rfl

@[simp] theorem pc4111 : Artifact.submissionArtifact.instructionPC 4104 = 5132 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 39) = 5132
  rw [ladder_pc 39 (by decide)]
  rfl

@[simp] theorem pc4112 : Artifact.submissionArtifact.instructionPC 4105 = 5133 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 40) = 5133
  rw [ladder_pc 40 (by decide)]
  rfl

@[simp] theorem pc4113 : Artifact.submissionArtifact.instructionPC 4106 = 5135 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 41) = 5135
  rw [ladder_pc 41 (by decide)]
  rfl

@[simp] theorem pc4114 : Artifact.submissionArtifact.instructionPC 4107 = 5136 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 42) = 5136
  rw [ladder_pc 42 (by decide)]
  rfl

@[simp] theorem pc4115 : Artifact.submissionArtifact.instructionPC 4108 = 5137 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 43) = 5137
  rw [ladder_pc 43 (by decide)]
  rfl

@[simp] theorem pc4116 : Artifact.submissionArtifact.instructionPC 4109 = 5140 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 44) = 5140
  rw [ladder_pc 44 (by decide)]
  rfl

@[simp] theorem pc4117 : Artifact.submissionArtifact.instructionPC 4110 = 5141 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 45) = 5141
  rw [ladder_pc 45 (by decide)]
  rfl

@[simp] theorem pc4118 : Artifact.submissionArtifact.instructionPC 4111 = 5142 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 46) = 5142
  rw [ladder_pc 46 (by decide)]
  rfl

@[simp] theorem pc4119 : Artifact.submissionArtifact.instructionPC 4112 = 5143 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 47) = 5143
  rw [ladder_pc 47 (by decide)]
  rfl

@[simp] theorem pc4120 : Artifact.submissionArtifact.instructionPC 4113 = 5144 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 48) = 5144
  rw [ladder_pc 48 (by decide)]
  rfl

@[simp] theorem pc4121 : Artifact.submissionArtifact.instructionPC 4114 = 5145 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 49) = 5145
  rw [ladder_pc 49 (by decide)]
  rfl

@[simp] theorem pc4122 : Artifact.submissionArtifact.instructionPC 4115 = 5146 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 50) = 5146
  rw [ladder_pc 50 (by decide)]
  rfl

@[simp] theorem pc4123 : Artifact.submissionArtifact.instructionPC 4116 = 5147 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 51) = 5147
  rw [ladder_pc 51 (by decide)]
  rfl

@[simp] theorem pc4124 : Artifact.submissionArtifact.instructionPC 4117 = 5148 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 52) = 5148
  rw [ladder_pc 52 (by decide)]
  rfl

@[simp] theorem pc4125 : Artifact.submissionArtifact.instructionPC 4118 = 5149 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 53) = 5149
  rw [ladder_pc 53 (by decide)]
  rfl

@[simp] theorem pc4126 : Artifact.submissionArtifact.instructionPC 4119 = 5150 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 54) = 5150
  rw [ladder_pc 54 (by decide)]
  rfl

@[simp] theorem pc4127 : Artifact.submissionArtifact.instructionPC 4120 = 5151 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 55) = 5151
  rw [ladder_pc 55 (by decide)]
  rfl

@[simp] theorem pc4128 : Artifact.submissionArtifact.instructionPC 4121 = 5152 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 56) = 5152
  rw [ladder_pc 56 (by decide)]
  rfl

@[simp] theorem pc4129 : Artifact.submissionArtifact.instructionPC 4122 = 5153 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 57) = 5153
  rw [ladder_pc 57 (by decide)]
  rfl

@[simp] theorem pc4130 : Artifact.submissionArtifact.instructionPC 4123 = 5155 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 58) = 5155
  rw [ladder_pc 58 (by decide)]
  rfl

@[simp] theorem pc4131 : Artifact.submissionArtifact.instructionPC 4124 = 5156 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 59) = 5156
  rw [ladder_pc 59 (by decide)]
  rfl

@[simp] theorem pc4132 : Artifact.submissionArtifact.instructionPC 4125 = 5157 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 60) = 5157
  rw [ladder_pc 60 (by decide)]
  rfl

@[simp] theorem pc4133 : Artifact.submissionArtifact.instructionPC 4126 = 5160 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 61) = 5160
  rw [ladder_pc 61 (by decide)]
  rfl

@[simp] theorem pc4134 : Artifact.submissionArtifact.instructionPC 4127 = 5161 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 62) = 5161
  rw [ladder_pc 62 (by decide)]
  rfl

@[simp] theorem pc4135 : Artifact.submissionArtifact.instructionPC 4128 = 5162 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 63) = 5162
  rw [ladder_pc 63 (by decide)]
  rfl

@[simp] theorem pc4136 : Artifact.submissionArtifact.instructionPC 4129 = 5163 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 64) = 5163
  rw [ladder_pc 64 (by decide)]
  rfl

@[simp] theorem pc4137 : Artifact.submissionArtifact.instructionPC 4130 = 5164 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 65) = 5164
  rw [ladder_pc 65 (by decide)]
  rfl

@[simp] theorem pc4138 : Artifact.submissionArtifact.instructionPC 4131 = 5165 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 66) = 5165
  rw [ladder_pc 66 (by decide)]
  rfl

@[simp] theorem pc4139 : Artifact.submissionArtifact.instructionPC 4132 = 5166 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 67) = 5166
  rw [ladder_pc 67 (by decide)]
  rfl

@[simp] theorem pc4140 : Artifact.submissionArtifact.instructionPC 4133 = 5167 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 68) = 5167
  rw [ladder_pc 68 (by decide)]
  rfl

@[simp] theorem pc4141 : Artifact.submissionArtifact.instructionPC 4134 = 5168 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 69) = 5168
  rw [ladder_pc 69 (by decide)]
  rfl

@[simp] theorem pc4142 : Artifact.submissionArtifact.instructionPC 4135 = 5169 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 70) = 5169
  rw [ladder_pc 70 (by decide)]
  rfl

@[simp] theorem pc4143 : Artifact.submissionArtifact.instructionPC 4136 = 5170 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 71) = 5170
  rw [ladder_pc 71 (by decide)]
  rfl

@[simp] theorem pc4144 : Artifact.submissionArtifact.instructionPC 4137 = 5171 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 72) = 5171
  rw [ladder_pc 72 (by decide)]
  rfl

@[simp] theorem pc4145 : Artifact.submissionArtifact.instructionPC 4138 = 5172 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 73) = 5172
  rw [ladder_pc 73 (by decide)]
  rfl

@[simp] theorem pc4146 : Artifact.submissionArtifact.instructionPC 4139 = 5173 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 74) = 5173
  rw [ladder_pc 74 (by decide)]
  rfl

@[simp] theorem pc4147 : Artifact.submissionArtifact.instructionPC 4140 = 5175 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 75) = 5175
  rw [ladder_pc 75 (by decide)]
  rfl

@[simp] theorem pc4148 : Artifact.submissionArtifact.instructionPC 4141 = 5176 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 76) = 5176
  rw [ladder_pc 76 (by decide)]
  rfl

@[simp] theorem pc4149 : Artifact.submissionArtifact.instructionPC 4142 = 5177 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 77) = 5177
  rw [ladder_pc 77 (by decide)]
  rfl

@[simp] theorem pc4150 : Artifact.submissionArtifact.instructionPC 4143 = 5180 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 78) = 5180
  rw [ladder_pc 78 (by decide)]
  rfl

@[simp] theorem pc4151 : Artifact.submissionArtifact.instructionPC 4144 = 5181 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 79) = 5181
  rw [ladder_pc 79 (by decide)]
  rfl

@[simp] theorem pc4152 : Artifact.submissionArtifact.instructionPC 4145 = 5182 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 80) = 5182
  rw [ladder_pc 80 (by decide)]
  rfl

@[simp] theorem pc4153 : Artifact.submissionArtifact.instructionPC 4146 = 5183 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 81) = 5183
  rw [ladder_pc 81 (by decide)]
  rfl

@[simp] theorem pc4154 : Artifact.submissionArtifact.instructionPC 4147 = 5184 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 82) = 5184
  rw [ladder_pc 82 (by decide)]
  rfl

@[simp] theorem pc4155 : Artifact.submissionArtifact.instructionPC 4148 = 5185 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 83) = 5185
  rw [ladder_pc 83 (by decide)]
  rfl

@[simp] theorem pc4156 : Artifact.submissionArtifact.instructionPC 4149 = 5186 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 84) = 5186
  rw [ladder_pc 84 (by decide)]
  rfl

@[simp] theorem pc4157 : Artifact.submissionArtifact.instructionPC 4150 = 5187 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 85) = 5187
  rw [ladder_pc 85 (by decide)]
  rfl

@[simp] theorem pc4158 : Artifact.submissionArtifact.instructionPC 4151 = 5188 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 86) = 5188
  rw [ladder_pc 86 (by decide)]
  rfl

@[simp] theorem pc4159 : Artifact.submissionArtifact.instructionPC 4152 = 5189 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 87) = 5189
  rw [ladder_pc 87 (by decide)]
  rfl

@[simp] theorem pc4160 : Artifact.submissionArtifact.instructionPC 4153 = 5190 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 88) = 5190
  rw [ladder_pc 88 (by decide)]
  rfl

@[simp] theorem pc4161 : Artifact.submissionArtifact.instructionPC 4154 = 5191 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 89) = 5191
  rw [ladder_pc 89 (by decide)]
  rfl

@[simp] theorem pc4162 : Artifact.submissionArtifact.instructionPC 4155 = 5192 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 90) = 5192
  rw [ladder_pc 90 (by decide)]
  rfl

@[simp] theorem pc4163 : Artifact.submissionArtifact.instructionPC 4156 = 5193 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 91) = 5193
  rw [ladder_pc 91 (by decide)]
  rfl

@[simp] theorem pc4164 : Artifact.submissionArtifact.instructionPC 4157 = 5195 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 92) = 5195
  rw [ladder_pc 92 (by decide)]
  rfl

@[simp] theorem pc4165 : Artifact.submissionArtifact.instructionPC 4158 = 5196 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 93) = 5196
  rw [ladder_pc 93 (by decide)]
  rfl

@[simp] theorem pc4166 : Artifact.submissionArtifact.instructionPC 4159 = 5197 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 94) = 5197
  rw [ladder_pc 94 (by decide)]
  rfl

@[simp] theorem pc4167 : Artifact.submissionArtifact.instructionPC 4160 = 5200 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 95) = 5200
  rw [ladder_pc 95 (by decide)]
  rfl

@[simp] theorem pc4168 : Artifact.submissionArtifact.instructionPC 4161 = 5201 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 96) = 5201
  rw [ladder_pc 96 (by decide)]
  rfl

@[simp] theorem pc4169 : Artifact.submissionArtifact.instructionPC 4162 = 5202 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 97) = 5202
  rw [ladder_pc 97 (by decide)]
  rfl

@[simp] theorem pc4170 : Artifact.submissionArtifact.instructionPC 4163 = 5203 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 98) = 5203
  rw [ladder_pc 98 (by decide)]
  rfl

@[simp] theorem pc4171 : Artifact.submissionArtifact.instructionPC 4164 = 5204 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 99) = 5204
  rw [ladder_pc 99 (by decide)]
  rfl

@[simp] theorem pc4172 : Artifact.submissionArtifact.instructionPC 4165 = 5205 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 100) = 5205
  rw [ladder_pc 100 (by decide)]
  rfl

@[simp] theorem pc4173 : Artifact.submissionArtifact.instructionPC 4166 = 5206 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 101) = 5206
  rw [ladder_pc 101 (by decide)]
  rfl

@[simp] theorem pc4174 : Artifact.submissionArtifact.instructionPC 4167 = 5207 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 102) = 5207
  rw [ladder_pc 102 (by decide)]
  rfl

@[simp] theorem pc4175 : Artifact.submissionArtifact.instructionPC 4168 = 5208 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 103) = 5208
  rw [ladder_pc 103 (by decide)]
  rfl

@[simp] theorem pc4176 : Artifact.submissionArtifact.instructionPC 4169 = 5209 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 104) = 5209
  rw [ladder_pc 104 (by decide)]
  rfl

@[simp] theorem pc4177 : Artifact.submissionArtifact.instructionPC 4170 = 5210 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 105) = 5210
  rw [ladder_pc 105 (by decide)]
  rfl

@[simp] theorem pc4178 : Artifact.submissionArtifact.instructionPC 4171 = 5211 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 106) = 5211
  rw [ladder_pc 106 (by decide)]
  rfl

@[simp] theorem pc4179 : Artifact.submissionArtifact.instructionPC 4172 = 5212 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 107) = 5212
  rw [ladder_pc 107 (by decide)]
  rfl

@[simp] theorem pc4180 : Artifact.submissionArtifact.instructionPC 4173 = 5213 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 108) = 5213
  rw [ladder_pc 108 (by decide)]
  rfl

@[simp] theorem pc4181 : Artifact.submissionArtifact.instructionPC 4174 = 5215 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 109) = 5215
  rw [ladder_pc 109 (by decide)]
  rfl

@[simp] theorem pc4182 : Artifact.submissionArtifact.instructionPC 4175 = 5216 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 110) = 5216
  rw [ladder_pc 110 (by decide)]
  rfl

@[simp] theorem pc4183 : Artifact.submissionArtifact.instructionPC 4176 = 5217 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 111) = 5217
  rw [ladder_pc 111 (by decide)]
  rfl

@[simp] theorem pc4184 : Artifact.submissionArtifact.instructionPC 4177 = 5220 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 112) = 5220
  rw [ladder_pc 112 (by decide)]
  rfl

@[simp] theorem pc4185 : Artifact.submissionArtifact.instructionPC 4178 = 5221 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 113) = 5221
  rw [ladder_pc 113 (by decide)]
  rfl

@[simp] theorem pc4186 : Artifact.submissionArtifact.instructionPC 4179 = 5222 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 114) = 5222
  rw [ladder_pc 114 (by decide)]
  rfl

@[simp] theorem pc4187 : Artifact.submissionArtifact.instructionPC 4180 = 5223 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 115) = 5223
  rw [ladder_pc 115 (by decide)]
  rfl

@[simp] theorem pc4188 : Artifact.submissionArtifact.instructionPC 4181 = 5224 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 116) = 5224
  rw [ladder_pc 116 (by decide)]
  rfl

@[simp] theorem pc4189 : Artifact.submissionArtifact.instructionPC 4182 = 5225 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 117) = 5225
  rw [ladder_pc 117 (by decide)]
  rfl

@[simp] theorem pc4190 : Artifact.submissionArtifact.instructionPC 4183 = 5226 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 118) = 5226
  rw [ladder_pc 118 (by decide)]
  rfl

@[simp] theorem pc4191 : Artifact.submissionArtifact.instructionPC 4184 = 5227 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 119) = 5227
  rw [ladder_pc 119 (by decide)]
  rfl

@[simp] theorem pc4192 : Artifact.submissionArtifact.instructionPC 4185 = 5228 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 120) = 5228
  rw [ladder_pc 120 (by decide)]
  rfl

@[simp] theorem pc4193 : Artifact.submissionArtifact.instructionPC 4186 = 5230 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 121) = 5230
  rw [ladder_pc 121 (by decide)]
  rfl

@[simp] theorem pc4194 : Artifact.submissionArtifact.instructionPC 4187 = 5231 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 122) = 5231
  rw [ladder_pc 122 (by decide)]
  rfl

@[simp] theorem pc4195 : Artifact.submissionArtifact.instructionPC 4188 = 5236 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 123) = 5236
  rw [ladder_pc 123 (by decide)]
  rfl

@[simp] theorem pc4196 : Artifact.submissionArtifact.instructionPC 4189 = 5238 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 124) = 5238
  rw [ladder_pc 124 (by decide)]
  rfl

@[simp] theorem pc4197 : Artifact.submissionArtifact.instructionPC 4190 = 5239 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 125) = 5239
  rw [ladder_pc 125 (by decide)]
  rfl

@[simp] theorem pc4198 : Artifact.submissionArtifact.instructionPC 4191 = 5244 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 126) = 5244
  rw [ladder_pc 126 (by decide)]
  rfl

@[simp] theorem pc4199 : Artifact.submissionArtifact.instructionPC 4192 = 5246 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 127) = 5246
  rw [ladder_pc 127 (by decide)]
  rfl

@[simp] theorem pc4200 : Artifact.submissionArtifact.instructionPC 4193 = 5247 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 128) = 5247
  rw [ladder_pc 128 (by decide)]
  rfl

@[simp] theorem pc4201 : Artifact.submissionArtifact.instructionPC 4194 = 5252 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 129) = 5252
  rw [ladder_pc 129 (by decide)]
  rfl

@[simp] theorem pc4202 : Artifact.submissionArtifact.instructionPC 4195 = 5254 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 130) = 5254
  rw [ladder_pc 130 (by decide)]
  rfl

@[simp] theorem pc4203 : Artifact.submissionArtifact.instructionPC 4196 = 5255 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 131) = 5255
  rw [ladder_pc 131 (by decide)]
  rfl

@[simp] theorem pc4204 : Artifact.submissionArtifact.instructionPC 4197 = 5260 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 132) = 5260
  rw [ladder_pc 132 (by decide)]
  rfl

@[simp] theorem pc4205 : Artifact.submissionArtifact.instructionPC 4198 = 5262 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 133) = 5262
  rw [ladder_pc 133 (by decide)]
  rfl

@[simp] theorem pc4206 : Artifact.submissionArtifact.instructionPC 4199 = 5263 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 134) = 5263
  rw [ladder_pc 134 (by decide)]
  rfl

@[simp] theorem pc4207 : Artifact.submissionArtifact.instructionPC 4200 = 5268 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 135) = 5268
  rw [ladder_pc 135 (by decide)]
  rfl

@[simp] theorem pc4208 : Artifact.submissionArtifact.instructionPC 4201 = 5270 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 136) = 5270
  rw [ladder_pc 136 (by decide)]
  rfl

@[simp] theorem pc4209 : Artifact.submissionArtifact.instructionPC 4202 = 5271 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 137) = 5271
  rw [ladder_pc 137 (by decide)]
  rfl

@[simp] theorem pc4210 : Artifact.submissionArtifact.instructionPC 4203 = 5272 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 138) = 5272
  rw [ladder_pc 138 (by decide)]
  rfl

@[simp] theorem pc4211 : Artifact.submissionArtifact.instructionPC 4204 = 5273 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 139) = 5273
  rw [ladder_pc 139 (by decide)]
  rfl

@[simp] theorem pc4212 : Artifact.submissionArtifact.instructionPC 4205 = 5274 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 140) = 5274
  rw [ladder_pc 140 (by decide)]
  rfl

@[simp] theorem pc4213 : Artifact.submissionArtifact.instructionPC 4206 = 5275 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 141) = 5275
  rw [ladder_pc 141 (by decide)]
  rfl

@[simp] theorem pc4214 : Artifact.submissionArtifact.instructionPC 4207 = 5276 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 142) = 5276
  rw [ladder_pc 142 (by decide)]
  rfl

@[simp] theorem pc4215 : Artifact.submissionArtifact.instructionPC 4208 = 5277 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 143) = 5277
  rw [ladder_pc 143 (by decide)]
  rfl

@[simp] theorem pc4216 : Artifact.submissionArtifact.instructionPC 4209 = 5278 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 144) = 5278
  rw [ladder_pc 144 (by decide)]
  rfl

@[simp] theorem pc4217 : Artifact.submissionArtifact.instructionPC 4210 = 5279 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 145) = 5279
  rw [ladder_pc 145 (by decide)]
  rfl

@[simp] theorem pc4218 : Artifact.submissionArtifact.instructionPC 4211 = 5280 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 146) = 5280
  rw [ladder_pc 146 (by decide)]
  rfl

@[simp] theorem pc4219 : Artifact.submissionArtifact.instructionPC 4212 = 5282 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 147) = 5282
  rw [ladder_pc 147 (by decide)]
  rfl

@[simp] theorem pc4220 : Artifact.submissionArtifact.instructionPC 4213 = 5283 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 148) = 5283
  rw [ladder_pc 148 (by decide)]
  rfl

@[simp] theorem pc4221 : Artifact.submissionArtifact.instructionPC 4214 = 5288 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 149) = 5288
  rw [ladder_pc 149 (by decide)]
  rfl

@[simp] theorem pc4222 : Artifact.submissionArtifact.instructionPC 4215 = 5290 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 150) = 5290
  rw [ladder_pc 150 (by decide)]
  rfl

@[simp] theorem pc4223 : Artifact.submissionArtifact.instructionPC 4216 = 5291 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 151) = 5291
  rw [ladder_pc 151 (by decide)]
  rfl

@[simp] theorem pc4224 : Artifact.submissionArtifact.instructionPC 4217 = 5296 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 152) = 5296
  rw [ladder_pc 152 (by decide)]
  rfl

@[simp] theorem pc4225 : Artifact.submissionArtifact.instructionPC 4218 = 5298 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 153) = 5298
  rw [ladder_pc 153 (by decide)]
  rfl

@[simp] theorem pc4226 : Artifact.submissionArtifact.instructionPC 4219 = 5299 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 154) = 5299
  rw [ladder_pc 154 (by decide)]
  rfl

@[simp] theorem pc4227 : Artifact.submissionArtifact.instructionPC 4220 = 5304 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 155) = 5304
  rw [ladder_pc 155 (by decide)]
  rfl

@[simp] theorem pc4228 : Artifact.submissionArtifact.instructionPC 4221 = 5306 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 156) = 5306
  rw [ladder_pc 156 (by decide)]
  rfl

@[simp] theorem pc4229 : Artifact.submissionArtifact.instructionPC 4222 = 5307 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 157) = 5307
  rw [ladder_pc 157 (by decide)]
  rfl

@[simp] theorem pc4230 : Artifact.submissionArtifact.instructionPC 4223 = 5312 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 158) = 5312
  rw [ladder_pc 158 (by decide)]
  rfl

@[simp] theorem pc4231 : Artifact.submissionArtifact.instructionPC 4224 = 5314 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 159) = 5314
  rw [ladder_pc 159 (by decide)]
  rfl

@[simp] theorem pc4232 : Artifact.submissionArtifact.instructionPC 4225 = 5315 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 160) = 5315
  rw [ladder_pc 160 (by decide)]
  rfl

@[simp] theorem pc4233 : Artifact.submissionArtifact.instructionPC 4226 = 5320 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 161) = 5320
  rw [ladder_pc 161 (by decide)]
  rfl

@[simp] theorem pc4234 : Artifact.submissionArtifact.instructionPC 4227 = 5322 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 162) = 5322
  rw [ladder_pc 162 (by decide)]
  rfl

@[simp] theorem pc4235 : Artifact.submissionArtifact.instructionPC 4228 = 5323 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 163) = 5323
  rw [ladder_pc 163 (by decide)]
  rfl

@[simp] theorem pc4236 : Artifact.submissionArtifact.instructionPC 4229 = 5324 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 164) = 5324
  rw [ladder_pc 164 (by decide)]
  rfl

@[simp] theorem pc4237 : Artifact.submissionArtifact.instructionPC 4230 = 5325 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 165) = 5325
  rw [ladder_pc 165 (by decide)]
  rfl

@[simp] theorem pc4238 : Artifact.submissionArtifact.instructionPC 4231 = 5326 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 166) = 5326
  rw [ladder_pc 166 (by decide)]
  rfl

@[simp] theorem pc4239 : Artifact.submissionArtifact.instructionPC 4232 = 5327 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 167) = 5327
  rw [ladder_pc 167 (by decide)]
  rfl

@[simp] theorem pc4240 : Artifact.submissionArtifact.instructionPC 4233 = 5328 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 168) = 5328
  rw [ladder_pc 168 (by decide)]
  rfl

@[simp] theorem pc4241 : Artifact.submissionArtifact.instructionPC 4234 = 5329 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 169) = 5329
  rw [ladder_pc 169 (by decide)]
  rfl

@[simp] theorem pc4242 : Artifact.submissionArtifact.instructionPC 4235 = 5330 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 170) = 5330
  rw [ladder_pc 170 (by decide)]
  rfl

@[simp] theorem pc4243 : Artifact.submissionArtifact.instructionPC 4236 = 5335 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 171) = 5335
  rw [ladder_pc 171 (by decide)]
  rfl

@[simp] theorem pc4244 : Artifact.submissionArtifact.instructionPC 4237 = 5337 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 172) = 5337
  rw [ladder_pc 172 (by decide)]
  rfl

@[simp] theorem pc4245 : Artifact.submissionArtifact.instructionPC 4238 = 5338 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 173) = 5338
  rw [ladder_pc 173 (by decide)]
  rfl

@[simp] theorem pc4246 : Artifact.submissionArtifact.instructionPC 4239 = 5343 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 174) = 5343
  rw [ladder_pc 174 (by decide)]
  rfl

@[simp] theorem pc4247 : Artifact.submissionArtifact.instructionPC 4240 = 5345 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 175) = 5345
  rw [ladder_pc 175 (by decide)]
  rfl

@[simp] theorem pc4248 : Artifact.submissionArtifact.instructionPC 4241 = 5346 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 176) = 5346
  rw [ladder_pc 176 (by decide)]
  rfl

@[simp] theorem pc4249 : Artifact.submissionArtifact.instructionPC 4242 = 5351 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 177) = 5351
  rw [ladder_pc 177 (by decide)]
  rfl

@[simp] theorem pc4250 : Artifact.submissionArtifact.instructionPC 4243 = 5353 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 178) = 5353
  rw [ladder_pc 178 (by decide)]
  rfl

@[simp] theorem pc4251 : Artifact.submissionArtifact.instructionPC 4244 = 5354 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 179) = 5354
  rw [ladder_pc 179 (by decide)]
  rfl

@[simp] theorem pc4252 : Artifact.submissionArtifact.instructionPC 4245 = 5359 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 180) = 5359
  rw [ladder_pc 180 (by decide)]
  rfl

@[simp] theorem pc4253 : Artifact.submissionArtifact.instructionPC 4246 = 5361 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 181) = 5361
  rw [ladder_pc 181 (by decide)]
  rfl

@[simp] theorem pc4254 : Artifact.submissionArtifact.instructionPC 4247 = 5362 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 182) = 5362
  rw [ladder_pc 182 (by decide)]
  rfl

@[simp] theorem pc4255 : Artifact.submissionArtifact.instructionPC 4248 = 5367 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 183) = 5367
  rw [ladder_pc 183 (by decide)]
  rfl

@[simp] theorem pc4256 : Artifact.submissionArtifact.instructionPC 4249 = 5369 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 184) = 5369
  rw [ladder_pc 184 (by decide)]
  rfl

@[simp] theorem pc4257 : Artifact.submissionArtifact.instructionPC 4250 = 5370 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 185) = 5370
  rw [ladder_pc 185 (by decide)]
  rfl

@[simp] theorem pc4258 : Artifact.submissionArtifact.instructionPC 4251 = 5371 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 186) = 5371
  rw [ladder_pc 186 (by decide)]
  rfl

@[simp] theorem pc4259 : Artifact.submissionArtifact.instructionPC 4252 = 5372 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 187) = 5372
  rw [ladder_pc 187 (by decide)]
  rfl

@[simp] theorem pc4260 : Artifact.submissionArtifact.instructionPC 4253 = 5373 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 188) = 5373
  rw [ladder_pc 188 (by decide)]
  rfl

@[simp] theorem pc4261 : Artifact.submissionArtifact.instructionPC 4254 = 5374 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 189) = 5374
  rw [ladder_pc 189 (by decide)]
  rfl

@[simp] theorem pc4262 : Artifact.submissionArtifact.instructionPC 4255 = 5375 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 190) = 5375
  rw [ladder_pc 190 (by decide)]
  rfl

@[simp] theorem pc4263 : Artifact.submissionArtifact.instructionPC 4256 = 5376 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 191) = 5376
  rw [ladder_pc 191 (by decide)]
  rfl

@[simp] theorem pc4264 : Artifact.submissionArtifact.instructionPC 4257 = 5379 := by
  show Artifact.submissionArtifact.instructionPC (4065 + 192) = 5379
  rw [ladder_pc 192 (by decide)]
  rfl

/-! ## Paths -/

def laterPath : List Located :=
  [⟨4065, .op .JUMPDEST, (ladder_at 0 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4066, .op (.Dup ⟨2, by decide⟩), (ladder_at 1 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4067, .push ⟨2, by decide⟩ (UInt256.ofNat 464), (ladder_at 2 (by decide)).trans rfl, by decide⟩,
   ⟨4068, .op .JUMPI, (ladder_at 3 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩]

def prefixPath : List Located :=
  [⟨4065, .op .JUMPDEST, (ladder_at 0 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4066, .op (.Dup ⟨2, by decide⟩), (ladder_at 1 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4067, .push ⟨2, by decide⟩ (UInt256.ofNat 464), (ladder_at 2 (by decide)).trans rfl, by decide⟩,
   ⟨4068, .op .JUMPI, (ladder_at 3 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4069, .push ⟨1, by decide⟩ (UInt256.ofNat 32), (ladder_at 4 (by decide)).trans rfl, by decide⟩,
   ⟨4070, .push ⟨2, by decide⟩ (UInt256.ofNat 262), (ladder_at 5 (by decide)).trans rfl, by decide⟩,
   ⟨4071, .push ⟨0, by decide⟩ (UInt256.ofNat 0), (ladder_at 6 (by decide)).trans rfl, by decide⟩]

def firstComparePath : List Located :=
  [⟨4073, .push ⟨0, by decide⟩ (UInt256.ofNat 0), (ladder_at 8 (by decide)).trans rfl, by decide⟩,
   ⟨4074, .op .MLOAD, (ladder_at 9 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4075, .push ⟨0, by decide⟩ (UInt256.ofNat 0), (ladder_at 10 (by decide)).trans rfl, by decide⟩,
   ⟨4076, .op .CALLDATALOAD, (ladder_at 11 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4077, .op .XOR, (ladder_at 12 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4078, .push ⟨2, by decide⟩ (UInt256.ofNat 464), (ladder_at 13 (by decide)).trans rfl, by decide⟩,
   ⟨4079, .op .JUMPI, (ladder_at 14 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩]

def setupPath : List Located :=
  [⟨4080, .push ⟨32, by decide⟩
      (UInt256.ofNat 0x7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f),
      (ladder_at 15 (by decide)).trans rfl, by decide⟩,
   ⟨4081, .push ⟨32, by decide⟩
      (UInt256.ofNat 0x8080808080808080808080808080808080808080808080808080808080808080),
      (ladder_at 16 (by decide)).trans rfl, by decide⟩,
   ⟨4082, .push ⟨32, by decide⟩
      (UInt256.ofNat 0x2020202020202020202020202020202020202020202020202020202020202020),
      (ladder_at 17 (by decide)).trans rfl, by decide⟩,
   ⟨4083, .push ⟨0, by decide⟩ (UInt256.ofNat 0),
      (ladder_at 18 (by decide)).trans rfl, by decide⟩,
   ⟨4084, .op .MLOAD, (ladder_at 19 (by decide)).trans rfl,
      wfOp (by decide) trivial rfl⟩,
   ⟨4085, .op .JUMPDEST, (ladder_at 20 (by decide)).trans rfl,
      wfOp (by decide) trivial rfl⟩,
   ⟨4086, .op .JUMPDEST, (ladder_at 21 (by decide)).trans rfl,
      wfOp (by decide) trivial rfl⟩,
   ⟨4087, .op .JUMPDEST, (ladder_at 22 (by decide)).trans rfl,
      wfOp (by decide) trivial rfl⟩,
   ⟨4088, .op .JUMPDEST, (ladder_at 23 (by decide)).trans rfl,
      wfOp (by decide) trivial rfl⟩,
   ⟨4089, .op .JUMPDEST, (ladder_at 24 (by decide)).trans rfl,
      wfOp (by decide) trivial rfl⟩,
   ⟨4090, .op .JUMPDEST, (ladder_at 25 (by decide)).trans rfl,
      wfOp (by decide) trivial rfl⟩,
   ⟨4091, .op .JUMPDEST, (ladder_at 26 (by decide)).trans rfl,
      wfOp (by decide) trivial rfl⟩,
   ⟨4092, .op .JUMPDEST, (ladder_at 27 (by decide)).trans rfl,
      wfOp (by decide) trivial rfl⟩]

def rung1Path : List Located :=
  [⟨4093, .op (.Dup ⟨0, by decide⟩), (ladder_at 28 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4094, .op (.Dup ⟨4, by decide⟩), (ladder_at 29 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4095, .op .AND, (ladder_at 30 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4096, .op (.Dup ⟨2, by decide⟩), (ladder_at 31 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4097, .op .ADD, (ladder_at 32 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4098, .op (.Swap ⟨0, by decide⟩), (ladder_at 33 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4099, .op (.Dup ⟨3, by decide⟩), (ladder_at 34 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4100, .op .AND, (ladder_at 35 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4101, .op .XOR, (ladder_at 36 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4102, .op (.Dup ⟨2, by decide⟩), (ladder_at 37 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4103, .op .XOR, (ladder_at 38 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4104, .op (.Dup ⟨0, by decide⟩), (ladder_at 39 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4105, .push ⟨1, by decide⟩ (UInt256.ofNat 32), (ladder_at 40 (by decide)).trans rfl, by decide⟩,
   ⟨4106, .op .CALLDATALOAD, (ladder_at 41 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4107, .op .XOR, (ladder_at 42 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4108, .push ⟨2, by decide⟩ (UInt256.ofNat 5371), (ladder_at 43 (by decide)).trans rfl, by decide⟩,
   ⟨4109, .op .JUMPI, (ladder_at 44 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩]

def rung2Path : List Located :=
  [⟨4110, .op (.Dup ⟨0, by decide⟩), (ladder_at 45 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4111, .op (.Dup ⟨4, by decide⟩), (ladder_at 46 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4112, .op .AND, (ladder_at 47 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4113, .op (.Dup ⟨2, by decide⟩), (ladder_at 48 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4114, .op .ADD, (ladder_at 49 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4115, .op (.Swap ⟨0, by decide⟩), (ladder_at 50 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4116, .op (.Dup ⟨3, by decide⟩), (ladder_at 51 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4117, .op .AND, (ladder_at 52 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4118, .op .XOR, (ladder_at 53 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4119, .op (.Dup ⟨2, by decide⟩), (ladder_at 54 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4120, .op .XOR, (ladder_at 55 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4121, .op (.Dup ⟨0, by decide⟩), (ladder_at 56 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4122, .push ⟨1, by decide⟩ (UInt256.ofNat 64), (ladder_at 57 (by decide)).trans rfl, by decide⟩,
   ⟨4123, .op .CALLDATALOAD, (ladder_at 58 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4124, .op .XOR, (ladder_at 59 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4125, .push ⟨2, by decide⟩ (UInt256.ofNat 5324), (ladder_at 60 (by decide)).trans rfl, by decide⟩,
   ⟨4126, .op .JUMPI, (ladder_at 61 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩]

def rung3Path : List Located :=
  [⟨4127, .op (.Dup ⟨0, by decide⟩), (ladder_at 62 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4128, .op (.Dup ⟨4, by decide⟩), (ladder_at 63 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4129, .op .AND, (ladder_at 64 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4130, .op (.Dup ⟨2, by decide⟩), (ladder_at 65 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4131, .op .ADD, (ladder_at 66 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4132, .op (.Swap ⟨0, by decide⟩), (ladder_at 67 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4133, .op (.Dup ⟨3, by decide⟩), (ladder_at 68 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4134, .op .AND, (ladder_at 69 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4135, .op .XOR, (ladder_at 70 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4136, .op (.Dup ⟨2, by decide⟩), (ladder_at 71 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4137, .op .XOR, (ladder_at 72 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4138, .op (.Dup ⟨0, by decide⟩), (ladder_at 73 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4139, .push ⟨1, by decide⟩ (UInt256.ofNat 96), (ladder_at 74 (by decide)).trans rfl, by decide⟩,
   ⟨4140, .op .CALLDATALOAD, (ladder_at 75 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4141, .op .XOR, (ladder_at 76 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4142, .push ⟨2, by decide⟩ (UInt256.ofNat 5324), (ladder_at 77 (by decide)).trans rfl, by decide⟩,
   ⟨4143, .op .JUMPI, (ladder_at 78 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩]

def rung4Path : List Located :=
  [⟨4144, .op (.Dup ⟨0, by decide⟩), (ladder_at 79 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4145, .op (.Dup ⟨4, by decide⟩), (ladder_at 80 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4146, .op .AND, (ladder_at 81 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4147, .op (.Dup ⟨2, by decide⟩), (ladder_at 82 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4148, .op .ADD, (ladder_at 83 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4149, .op (.Swap ⟨0, by decide⟩), (ladder_at 84 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4150, .op (.Dup ⟨3, by decide⟩), (ladder_at 85 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4151, .op .AND, (ladder_at 86 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4152, .op .XOR, (ladder_at 87 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4153, .op (.Dup ⟨2, by decide⟩), (ladder_at 88 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4154, .op .XOR, (ladder_at 89 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4155, .op (.Dup ⟨0, by decide⟩), (ladder_at 90 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4156, .push ⟨1, by decide⟩ (UInt256.ofNat 128), (ladder_at 91 (by decide)).trans rfl, by decide⟩,
   ⟨4157, .op .CALLDATALOAD, (ladder_at 92 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4158, .op .XOR, (ladder_at 93 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4159, .push ⟨2, by decide⟩ (UInt256.ofNat 5272), (ladder_at 94 (by decide)).trans rfl, by decide⟩,
   ⟨4160, .op .JUMPI, (ladder_at 95 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩]

def rung5Path : List Located :=
  [⟨4161, .op (.Dup ⟨0, by decide⟩), (ladder_at 96 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4162, .op (.Dup ⟨4, by decide⟩), (ladder_at 97 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4163, .op .AND, (ladder_at 98 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4164, .op (.Dup ⟨2, by decide⟩), (ladder_at 99 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4165, .op .ADD, (ladder_at 100 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4166, .op (.Swap ⟨0, by decide⟩), (ladder_at 101 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4167, .op (.Dup ⟨3, by decide⟩), (ladder_at 102 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4168, .op .AND, (ladder_at 103 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4169, .op .XOR, (ladder_at 104 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4170, .op (.Dup ⟨2, by decide⟩), (ladder_at 105 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4171, .op .XOR, (ladder_at 106 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4172, .op (.Dup ⟨0, by decide⟩), (ladder_at 107 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4173, .push ⟨1, by decide⟩ (UInt256.ofNat 160), (ladder_at 108 (by decide)).trans rfl, by decide⟩,
   ⟨4174, .op .CALLDATALOAD, (ladder_at 109 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4175, .op .XOR, (ladder_at 110 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4176, .push ⟨2, by decide⟩ (UInt256.ofNat 5272), (ladder_at 111 (by decide)).trans rfl, by decide⟩,
   ⟨4177, .op .JUMPI, (ladder_at 112 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩]

def hit3Path : List Located :=
  [⟨4178, .op .POP, (ladder_at 113 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4179, .op .POP, (ladder_at 114 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4180, .op .POP, (ladder_at 115 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4181, .op .POP, (ladder_at 116 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4182, .op .POP, (ladder_at 117 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4183, .op (.Swap ⟨0, by decide⟩), (ladder_at 118 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4184, .op .POP, (ladder_at 119 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4185, .push ⟨1, by decide⟩ (UInt256.ofNat 128), (ladder_at 120 (by decide)).trans rfl, by decide⟩,
   ⟨4186, .op (.Swap ⟨0, by decide⟩), (ladder_at 121 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4187, .push ⟨4, by decide⟩ (UInt256.ofNat 1393315003), (ladder_at 122 (by decide)).trans rfl, by decide⟩,
   ⟨4188, .push ⟨1, by decide⟩ (UInt256.ofNat 32), (ladder_at 123 (by decide)).trans rfl, by decide⟩,
   ⟨4189, .op .MSTORE, (ladder_at 124 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4190, .push ⟨4, by decide⟩ (UInt256.ofNat 695251451), (ladder_at 125 (by decide)).trans rfl, by decide⟩,
   ⟨4191, .push ⟨1, by decide⟩ (UInt256.ofNat 64), (ladder_at 126 (by decide)).trans rfl, by decide⟩,
   ⟨4192, .op .MSTORE, (ladder_at 127 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4193, .push ⟨4, by decide⟩ (UInt256.ofNat 358732556), (ladder_at 128 (by decide)).trans rfl, by decide⟩,
   ⟨4194, .push ⟨1, by decide⟩ (UInt256.ofNat 96), (ladder_at 129 (by decide)).trans rfl, by decide⟩,
   ⟨4195, .op .MSTORE, (ladder_at 130 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4196, .push ⟨4, by decide⟩ (UInt256.ofNat 928826907), (ladder_at 131 (by decide)).trans rfl, by decide⟩,
   ⟨4197, .push ⟨1, by decide⟩ (UInt256.ofNat 128), (ladder_at 132 (by decide)).trans rfl, by decide⟩,
   ⟨4198, .op .MSTORE, (ladder_at 133 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4199, .push ⟨4, by decide⟩ (UInt256.ofNat 3850323193), (ladder_at 134 (by decide)).trans rfl, by decide⟩,
   ⟨4200, .push ⟨1, by decide⟩ (UInt256.ofNat 160), (ladder_at 135 (by decide)).trans rfl, by decide⟩,
   ⟨4201, .op .MSTORE, (ladder_at 136 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4202, .op .JUMP, (ladder_at 137 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩]

def hit2Path : List Located :=
  [⟨4203, .op .JUMPDEST, (ladder_at 138 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4204, .op .POP, (ladder_at 139 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4205, .op .POP, (ladder_at 140 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4206, .op .POP, (ladder_at 141 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4207, .op .POP, (ladder_at 142 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4208, .op .POP, (ladder_at 143 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4209, .op (.Swap ⟨0, by decide⟩), (ladder_at 144 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4210, .op .POP, (ladder_at 145 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4211, .push ⟨1, by decide⟩ (UInt256.ofNat 64), (ladder_at 146 (by decide)).trans rfl, by decide⟩,
   ⟨4212, .op (.Swap ⟨0, by decide⟩), (ladder_at 147 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4213, .push ⟨4, by decide⟩ (UInt256.ofNat 2807398299), (ladder_at 148 (by decide)).trans rfl, by decide⟩,
   ⟨4214, .push ⟨1, by decide⟩ (UInt256.ofNat 32), (ladder_at 149 (by decide)).trans rfl, by decide⟩,
   ⟨4215, .op .MSTORE, (ladder_at 150 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4216, .push ⟨4, by decide⟩ (UInt256.ofNat 514068704), (ladder_at 151 (by decide)).trans rfl, by decide⟩,
   ⟨4217, .push ⟨1, by decide⟩ (UInt256.ofNat 64), (ladder_at 152 (by decide)).trans rfl, by decide⟩,
   ⟨4218, .op .MSTORE, (ladder_at 153 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4219, .push ⟨4, by decide⟩ (UInt256.ofNat 3681030016), (ladder_at 154 (by decide)).trans rfl, by decide⟩,
   ⟨4220, .push ⟨1, by decide⟩ (UInt256.ofNat 96), (ladder_at 155 (by decide)).trans rfl, by decide⟩,
   ⟨4221, .op .MSTORE, (ladder_at 156 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4222, .push ⟨4, by decide⟩ (UInt256.ofNat 3354522469), (ladder_at 157 (by decide)).trans rfl, by decide⟩,
   ⟨4223, .push ⟨1, by decide⟩ (UInt256.ofNat 128), (ladder_at 158 (by decide)).trans rfl, by decide⟩,
   ⟨4224, .op .MSTORE, (ladder_at 159 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4225, .push ⟨4, by decide⟩ (UInt256.ofNat 2543018249), (ladder_at 160 (by decide)).trans rfl, by decide⟩,
   ⟨4226, .push ⟨1, by decide⟩ (UInt256.ofNat 160), (ladder_at 161 (by decide)).trans rfl, by decide⟩,
   ⟨4227, .op .MSTORE, (ladder_at 162 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4228, .op .JUMP, (ladder_at 163 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩]

def hit1Path : List Located :=
  [⟨4229, .op .JUMPDEST, (ladder_at 164 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4230, .op .POP, (ladder_at 165 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4231, .op .POP, (ladder_at 166 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4232, .op .POP, (ladder_at 167 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4233, .op .POP, (ladder_at 168 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4234, .op .POP, (ladder_at 169 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4235, .push ⟨4, by decide⟩ (UInt256.ofNat 1080717082), (ladder_at 170 (by decide)).trans rfl, by decide⟩,
   ⟨4236, .push ⟨1, by decide⟩ (UInt256.ofNat 32), (ladder_at 171 (by decide)).trans rfl, by decide⟩,
   ⟨4237, .op .MSTORE, (ladder_at 172 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4238, .push ⟨4, by decide⟩ (UInt256.ofNat 2391128076), (ladder_at 173 (by decide)).trans rfl, by decide⟩,
   ⟨4239, .push ⟨1, by decide⟩ (UInt256.ofNat 64), (ladder_at 174 (by decide)).trans rfl, by decide⟩,
   ⟨4240, .op .MSTORE, (ladder_at 175 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4241, .push ⟨4, by decide⟩ (UInt256.ofNat 621343384), (ladder_at 176 (by decide)).trans rfl, by decide⟩,
   ⟨4242, .push ⟨1, by decide⟩ (UInt256.ofNat 96), (ladder_at 177 (by decide)).trans rfl, by decide⟩,
   ⟨4243, .op .MSTORE, (ladder_at 178 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4244, .push ⟨4, by decide⟩ (UInt256.ofNat 220066081), (ladder_at 179 (by decide)).trans rfl, by decide⟩,
   ⟨4245, .push ⟨1, by decide⟩ (UInt256.ofNat 128), (ladder_at 180 (by decide)).trans rfl, by decide⟩,
   ⟨4246, .op .MSTORE, (ladder_at 181 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4247, .push ⟨4, by decide⟩ (UInt256.ofNat 1007308478), (ladder_at 182 (by decide)).trans rfl, by decide⟩,
   ⟨4248, .push ⟨1, by decide⟩ (UInt256.ofNat 160), (ladder_at 183 (by decide)).trans rfl, by decide⟩,
   ⟨4249, .op .MSTORE, (ladder_at 184 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4250, .op .JUMP, (ladder_at 185 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩]

def bailPath : List Located :=
  [⟨4251, .op .JUMPDEST, (ladder_at 186 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4252, .op .POP, (ladder_at 187 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4253, .op .POP, (ladder_at 188 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4254, .op .POP, (ladder_at 189 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4255, .op .POP, (ladder_at 190 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4256, .push ⟨2, by decide⟩ (UInt256.ofNat 464), (ladder_at 191 (by decide)).trans rfl, by decide⟩,
   ⟨4257, .op .JUMP, (ladder_at 192 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PrefixStatePaths
