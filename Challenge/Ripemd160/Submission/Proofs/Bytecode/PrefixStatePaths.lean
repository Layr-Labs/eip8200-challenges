import Batteries.Tactic.OpenPrivate
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Artifact
set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000

/-!
# Located paths of the depth-3 patterned-prefix ladder (instructions 4061..4257)

The ladder occupies the trailing 297 bytes (pc 4997..5293).  Its PC and
instruction lemmas are derived from a split of the instruction list at index
4061 so every `rfl` evaluates only the 163-instruction ladder segment.
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

private theorem ladderBefore_length : ladderBefore.length = 4061 := by
  simp [ladderBefore]

private theorem ladderSegment_length : ladderSegment.length = 163 := by
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
    (YulEvmCompiler.assembleBytes ladderBefore).length = 4997 := by
  rw [← ArtifactByteLength.byteLength_eq_assemble]
  rfl

private theorem ladder_pc (i : Nat) (hi : i ≤ 163) :
    Artifact.submissionArtifact.instructionPC (4061 + i) =
      4997 + ArtifactByteLength.byteLength (ladderSegment.take i) := by
  rw [ArtifactByteLength.byteLength_eq_assemble]
  exact ArtifactSegment.instructionPC_segment_of_bounds Artifact.submissionArtifact
    ladderBefore ladderSegment [] 4061 4997 artifact_ladder_split ladderBefore_length
    ladderBefore_pc i (by rw [ladderSegment_length]; exact hi)

private theorem ladder_at (i : Nat) (hi : i < 163) :
    Artifact.submissionArtifact.instructions[4061 + i]? = ladderSegment[i]? := by
  have h := ArtifactSegment.getElem?_segment Artifact.submissionArtifact
    ladderBefore ladderSegment [] artifact_ladder_split i (by rw [ladderSegment_length]; exact hi)
  rwa [ladderBefore_length] at h

@[simp] theorem pc4072 : Artifact.submissionArtifact.instructionPC 4061 = 4997 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 0) = 4997
  rw [ladder_pc 0 (by decide)]
  rfl

@[simp] theorem pc4073 : Artifact.submissionArtifact.instructionPC 4062 = 4998 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 1) = 4998
  rw [ladder_pc 1 (by decide)]
  rfl

@[simp] theorem pc4074 : Artifact.submissionArtifact.instructionPC 4063 = 4999 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 2) = 4999
  rw [ladder_pc 2 (by decide)]
  rfl

@[simp] theorem pc4075 : Artifact.submissionArtifact.instructionPC 4064 = 5002 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 3) = 5002
  rw [ladder_pc 3 (by decide)]
  rfl

@[simp] theorem pc4076 : Artifact.submissionArtifact.instructionPC 4065 = 5003 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 4) = 5003
  rw [ladder_pc 4 (by decide)]
  rfl

@[simp] theorem pc4077 : Artifact.submissionArtifact.instructionPC 4066 = 5005 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 5) = 5005
  rw [ladder_pc 5 (by decide)]
  rfl

@[simp] theorem pc4078 : Artifact.submissionArtifact.instructionPC 4067 = 5008 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 6) = 5008
  rw [ladder_pc 6 (by decide)]
  rfl

@[simp] theorem pc4079 : Artifact.submissionArtifact.instructionPC 4068 = 5009 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 7) = 5009
  rw [ladder_pc 7 (by decide)]
  rfl

@[simp] theorem pc4080 : Artifact.submissionArtifact.instructionPC 4069 = 5010 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 8) = 5010
  rw [ladder_pc 8 (by decide)]
  rfl

@[simp] theorem pc4081 : Artifact.submissionArtifact.instructionPC 4070 = 5011 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 9) = 5011
  rw [ladder_pc 9 (by decide)]
  rfl

@[simp] theorem pc4082 : Artifact.submissionArtifact.instructionPC 4071 = 5012 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 10) = 5012
  rw [ladder_pc 10 (by decide)]
  rfl

@[simp] theorem pc4083 : Artifact.submissionArtifact.instructionPC 4072 = 5013 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 11) = 5013
  rw [ladder_pc 11 (by decide)]
  rfl

@[simp] theorem pc4084 : Artifact.submissionArtifact.instructionPC 4073 = 5014 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 12) = 5014
  rw [ladder_pc 12 (by decide)]
  rfl

@[simp] theorem pc4085 : Artifact.submissionArtifact.instructionPC 4074 = 5015 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 13) = 5015
  rw [ladder_pc 13 (by decide)]
  rfl

@[simp] theorem pc4086 : Artifact.submissionArtifact.instructionPC 4075 = 5018 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 14) = 5018
  rw [ladder_pc 14 (by decide)]
  rfl

@[simp] theorem compactPc4080 : Artifact.submissionArtifact.instructionPC 4076 = 5019 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 15) = 5019
  rw [ladder_pc 15 (by decide)]
  rfl

@[simp] theorem compactPc4081 : Artifact.submissionArtifact.instructionPC 4077 = 5020 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 16) = 5020
  rw [ladder_pc 16 (by decide)]
  rfl

@[simp] theorem compactPc4082 : Artifact.submissionArtifact.instructionPC 4078 = 5022 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 17) = 5022
  rw [ladder_pc 17 (by decide)]
  rfl

@[simp] theorem compactPc4083 : Artifact.submissionArtifact.instructionPC 4079 = 5023 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 18) = 5023
  rw [ladder_pc 18 (by decide)]
  rfl

@[simp] theorem compactPc4084 : Artifact.submissionArtifact.instructionPC 4080 = 5024 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 19) = 5024
  rw [ladder_pc 19 (by decide)]
  rfl

@[simp] theorem compactPc4085 : Artifact.submissionArtifact.instructionPC 4081 = 5025 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 20) = 5025
  rw [ladder_pc 20 (by decide)]
  rfl

@[simp] theorem compactPc4086 : Artifact.submissionArtifact.instructionPC 4082 = 5027 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 21) = 5027
  rw [ladder_pc 21 (by decide)]
  rfl

@[simp] theorem compactPc4087 : Artifact.submissionArtifact.instructionPC 4083 = 5028 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 22) = 5028
  rw [ladder_pc 22 (by decide)]
  rfl

@[simp] theorem compactPc4088 : Artifact.submissionArtifact.instructionPC 4084 = 5061 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 23) = 5061
  rw [ladder_pc 23 (by decide)]
  rfl

@[simp] theorem compactPc4089 : Artifact.submissionArtifact.instructionPC 4085 = 5063 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 24) = 5063
  rw [ladder_pc 24 (by decide)]
  rfl

@[simp] theorem compactPc4090 : Artifact.submissionArtifact.instructionPC 4086 = 5064 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 25) = 5064
  rw [ladder_pc 25 (by decide)]
  rfl

@[simp] theorem compactPc4091 : Artifact.submissionArtifact.instructionPC 4087 = 5065 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 26) = 5065
  rw [ladder_pc 26 (by decide)]
  rfl

@[simp] theorem compactPc4092 : Artifact.submissionArtifact.instructionPC 4088 = 5068 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 27) = 5068
  rw [ladder_pc 27 (by decide)]
  rfl

@[simp] theorem compactPc4093 : Artifact.submissionArtifact.instructionPC 4089 = 5069 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 28) = 5069
  rw [ladder_pc 28 (by decide)]
  rfl

@[simp] theorem compactPc4094 : Artifact.submissionArtifact.instructionPC 4090 = 5070 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 29) = 5070
  rw [ladder_pc 29 (by decide)]
  rfl

@[simp] theorem compactPc4095 : Artifact.submissionArtifact.instructionPC 4091 = 5071 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 30) = 5071
  rw [ladder_pc 30 (by decide)]
  rfl

@[simp] theorem compactPc4096 : Artifact.submissionArtifact.instructionPC 4092 = 5072 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 31) = 5072
  rw [ladder_pc 31 (by decide)]
  rfl

@[simp] theorem compactPc4097 : Artifact.submissionArtifact.instructionPC 4093 = 5073 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 32) = 5073
  rw [ladder_pc 32 (by decide)]
  rfl

@[simp] theorem compactPc4098 : Artifact.submissionArtifact.instructionPC 4094 = 5074 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 33) = 5074
  rw [ladder_pc 33 (by decide)]
  rfl

@[simp] theorem compactPc4099 : Artifact.submissionArtifact.instructionPC 4095 = 5075 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 34) = 5075
  rw [ladder_pc 34 (by decide)]
  rfl

@[simp] theorem compactPc4100 : Artifact.submissionArtifact.instructionPC 4096 = 5076 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 35) = 5076
  rw [ladder_pc 35 (by decide)]
  rfl

@[simp] theorem compactPc4101 : Artifact.submissionArtifact.instructionPC 4097 = 5077 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 36) = 5077
  rw [ladder_pc 36 (by decide)]
  rfl

@[simp] theorem compactPc4102 : Artifact.submissionArtifact.instructionPC 4098 = 5078 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 37) = 5078
  rw [ladder_pc 37 (by decide)]
  rfl

@[simp] theorem compactPc4103 : Artifact.submissionArtifact.instructionPC 4099 = 5079 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 38) = 5079
  rw [ladder_pc 38 (by decide)]
  rfl

@[simp] theorem compactPc4104 : Artifact.submissionArtifact.instructionPC 4100 = 5081 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 39) = 5081
  rw [ladder_pc 39 (by decide)]
  rfl

@[simp] theorem compactPc4105 : Artifact.submissionArtifact.instructionPC 4101 = 5082 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 40) = 5082
  rw [ladder_pc 40 (by decide)]
  rfl

@[simp] theorem compactPc4106 : Artifact.submissionArtifact.instructionPC 4102 = 5083 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 41) = 5083
  rw [ladder_pc 41 (by decide)]
  rfl

@[simp] theorem compactPc4107 : Artifact.submissionArtifact.instructionPC 4103 = 5086 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 42) = 5086
  rw [ladder_pc 42 (by decide)]
  rfl

@[simp] theorem compactPc4108 : Artifact.submissionArtifact.instructionPC 4104 = 5087 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 43) = 5087
  rw [ladder_pc 43 (by decide)]
  rfl

@[simp] theorem compactPc4109 : Artifact.submissionArtifact.instructionPC 4105 = 5089 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 44) = 5089
  rw [ladder_pc 44 (by decide)]
  rfl

@[simp] theorem compactPc4110 : Artifact.submissionArtifact.instructionPC 4106 = 5090 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 45) = 5090
  rw [ladder_pc 45 (by decide)]
  rfl

@[simp] theorem compactPc4111 : Artifact.submissionArtifact.instructionPC 4107 = 5091 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 46) = 5091
  rw [ladder_pc 46 (by decide)]
  rfl

@[simp] theorem compactPc4112 : Artifact.submissionArtifact.instructionPC 4108 = 5092 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 47) = 5092
  rw [ladder_pc 47 (by decide)]
  rfl

@[simp] theorem compactPc4113 : Artifact.submissionArtifact.instructionPC 4109 = 5093 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 48) = 5093
  rw [ladder_pc 48 (by decide)]
  rfl

@[simp] theorem compactPc4114 : Artifact.submissionArtifact.instructionPC 4110 = 5094 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 49) = 5094
  rw [ladder_pc 49 (by decide)]
  rfl

@[simp] theorem compactPc4115 : Artifact.submissionArtifact.instructionPC 4111 = 5095 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 50) = 5095
  rw [ladder_pc 50 (by decide)]
  rfl

@[simp] theorem compactPc4116 : Artifact.submissionArtifact.instructionPC 4112 = 5096 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 51) = 5096
  rw [ladder_pc 51 (by decide)]
  rfl

@[simp] theorem compactPc4117 : Artifact.submissionArtifact.instructionPC 4113 = 5097 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 52) = 5097
  rw [ladder_pc 52 (by decide)]
  rfl

@[simp] theorem compactPc4118 : Artifact.submissionArtifact.instructionPC 4114 = 5098 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 53) = 5098
  rw [ladder_pc 53 (by decide)]
  rfl

@[simp] theorem compactPc4119 : Artifact.submissionArtifact.instructionPC 4115 = 5100 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 54) = 5100
  rw [ladder_pc 54 (by decide)]
  rfl

@[simp] theorem compactPc4120 : Artifact.submissionArtifact.instructionPC 4116 = 5101 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 55) = 5101
  rw [ladder_pc 55 (by decide)]
  rfl

@[simp] theorem compactPc4121 : Artifact.submissionArtifact.instructionPC 4117 = 5102 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 56) = 5102
  rw [ladder_pc 56 (by decide)]
  rfl

@[simp] theorem compactPc4122 : Artifact.submissionArtifact.instructionPC 4118 = 5105 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 57) = 5105
  rw [ladder_pc 57 (by decide)]
  rfl

@[simp] theorem compactPc4123 : Artifact.submissionArtifact.instructionPC 4119 = 5106 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 58) = 5106
  rw [ladder_pc 58 (by decide)]
  rfl

@[simp] theorem compactPc4124 : Artifact.submissionArtifact.instructionPC 4120 = 5107 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 59) = 5107
  rw [ladder_pc 59 (by decide)]
  rfl

@[simp] theorem compactPc4125 : Artifact.submissionArtifact.instructionPC 4121 = 5108 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 60) = 5108
  rw [ladder_pc 60 (by decide)]
  rfl

@[simp] theorem compactPc4126 : Artifact.submissionArtifact.instructionPC 4122 = 5109 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 61) = 5109
  rw [ladder_pc 61 (by decide)]
  rfl

@[simp] theorem compactPc4127 : Artifact.submissionArtifact.instructionPC 4123 = 5110 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 62) = 5110
  rw [ladder_pc 62 (by decide)]
  rfl

@[simp] theorem compactPc4128 : Artifact.submissionArtifact.instructionPC 4124 = 5111 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 63) = 5111
  rw [ladder_pc 63 (by decide)]
  rfl

@[simp] theorem compactPc4129 : Artifact.submissionArtifact.instructionPC 4125 = 5112 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 64) = 5112
  rw [ladder_pc 64 (by decide)]
  rfl

@[simp] theorem compactPc4130 : Artifact.submissionArtifact.instructionPC 4126 = 5114 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 65) = 5114
  rw [ladder_pc 65 (by decide)]
  rfl

@[simp] theorem compactPc4131 : Artifact.submissionArtifact.instructionPC 4127 = 5115 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 66) = 5115
  rw [ladder_pc 66 (by decide)]
  rfl

@[simp] theorem compactPc4132 : Artifact.submissionArtifact.instructionPC 4128 = 5116 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 67) = 5116
  rw [ladder_pc 67 (by decide)]
  rfl

@[simp] theorem compactPc4133 : Artifact.submissionArtifact.instructionPC 4129 = 5119 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 68) = 5119
  rw [ladder_pc 68 (by decide)]
  rfl

@[simp] theorem compactPc4134 : Artifact.submissionArtifact.instructionPC 4130 = 5120 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 69) = 5120
  rw [ladder_pc 69 (by decide)]
  rfl

@[simp] theorem compactPc4135 : Artifact.submissionArtifact.instructionPC 4131 = 5122 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 70) = 5122
  rw [ladder_pc 70 (by decide)]
  rfl

@[simp] theorem compactPc4136 : Artifact.submissionArtifact.instructionPC 4132 = 5123 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 71) = 5123
  rw [ladder_pc 71 (by decide)]
  rfl

@[simp] theorem compactPc4137 : Artifact.submissionArtifact.instructionPC 4133 = 5124 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 72) = 5124
  rw [ladder_pc 72 (by decide)]
  rfl

@[simp] theorem compactPc4138 : Artifact.submissionArtifact.instructionPC 4134 = 5125 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 73) = 5125
  rw [ladder_pc 73 (by decide)]
  rfl

@[simp] theorem compactPc4139 : Artifact.submissionArtifact.instructionPC 4135 = 5126 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 74) = 5126
  rw [ladder_pc 74 (by decide)]
  rfl

@[simp] theorem compactPc4140 : Artifact.submissionArtifact.instructionPC 4136 = 5127 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 75) = 5127
  rw [ladder_pc 75 (by decide)]
  rfl

@[simp] theorem compactPc4141 : Artifact.submissionArtifact.instructionPC 4137 = 5129 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 76) = 5129
  rw [ladder_pc 76 (by decide)]
  rfl

@[simp] theorem compactPc4142 : Artifact.submissionArtifact.instructionPC 4138 = 5130 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 77) = 5130
  rw [ladder_pc 77 (by decide)]
  rfl

@[simp] theorem compactPc4143 : Artifact.submissionArtifact.instructionPC 4139 = 5131 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 78) = 5131
  rw [ladder_pc 78 (by decide)]
  rfl

@[simp] theorem compactPc4144 : Artifact.submissionArtifact.instructionPC 4140 = 5134 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 79) = 5134
  rw [ladder_pc 79 (by decide)]
  rfl

@[simp] theorem compactPc4145 : Artifact.submissionArtifact.instructionPC 4141 = 5135 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 80) = 5135
  rw [ladder_pc 80 (by decide)]
  rfl

@[simp] theorem compactPc4146 : Artifact.submissionArtifact.instructionPC 4142 = 5137 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 81) = 5137
  rw [ladder_pc 81 (by decide)]
  rfl

@[simp] theorem compactPc4147 : Artifact.submissionArtifact.instructionPC 4143 = 5138 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 82) = 5138
  rw [ladder_pc 82 (by decide)]
  rfl

@[simp] theorem compactPc4148 : Artifact.submissionArtifact.instructionPC 4144 = 5139 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 83) = 5139
  rw [ladder_pc 83 (by decide)]
  rfl

@[simp] theorem compactPc4149 : Artifact.submissionArtifact.instructionPC 4145 = 5140 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 84) = 5140
  rw [ladder_pc 84 (by decide)]
  rfl

@[simp] theorem compactPc4150 : Artifact.submissionArtifact.instructionPC 4146 = 5141 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 85) = 5141
  rw [ladder_pc 85 (by decide)]
  rfl

@[simp] theorem compactPc4151 : Artifact.submissionArtifact.instructionPC 4147 = 5142 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 86) = 5142
  rw [ladder_pc 86 (by decide)]
  rfl

@[simp] theorem compactPc4152 : Artifact.submissionArtifact.instructionPC 4148 = 5144 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 87) = 5144
  rw [ladder_pc 87 (by decide)]
  rfl

@[simp] theorem compactPc4153 : Artifact.submissionArtifact.instructionPC 4149 = 5145 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 88) = 5145
  rw [ladder_pc 88 (by decide)]
  rfl

@[simp] theorem compactPc4154 : Artifact.submissionArtifact.instructionPC 4150 = 5146 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 89) = 5146
  rw [ladder_pc 89 (by decide)]
  rfl

@[simp] theorem compactPc4155 : Artifact.submissionArtifact.instructionPC 4151 = 5149 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 90) = 5149
  rw [ladder_pc 90 (by decide)]
  rfl

@[simp] theorem compactPc4156 : Artifact.submissionArtifact.instructionPC 4152 = 5150 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 91) = 5150
  rw [ladder_pc 91 (by decide)]
  rfl

@[simp] theorem compactPc4157 : Artifact.submissionArtifact.instructionPC 4153 = 5152 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 92) = 5152
  rw [ladder_pc 92 (by decide)]
  rfl

@[simp] theorem compactPc4158 : Artifact.submissionArtifact.instructionPC 4154 = 5153 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 93) = 5153
  rw [ladder_pc 93 (by decide)]
  rfl

@[simp] theorem compactPc4159 : Artifact.submissionArtifact.instructionPC 4155 = 5154 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 94) = 5154
  rw [ladder_pc 94 (by decide)]
  rfl

@[simp] theorem compactPc4160 : Artifact.submissionArtifact.instructionPC 4156 = 5155 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 95) = 5155
  rw [ladder_pc 95 (by decide)]
  rfl

@[simp] theorem compactPc4161 : Artifact.submissionArtifact.instructionPC 4157 = 5156 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 96) = 5156
  rw [ladder_pc 96 (by decide)]
  rfl

@[simp] theorem compactPc4162 : Artifact.submissionArtifact.instructionPC 4158 = 5157 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 97) = 5157
  rw [ladder_pc 97 (by decide)]
  rfl

@[simp] theorem compactPc4163 : Artifact.submissionArtifact.instructionPC 4159 = 5163 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 98) = 5163
  rw [ladder_pc 98 (by decide)]
  rfl

@[simp] theorem compactPc4164 : Artifact.submissionArtifact.instructionPC 4160 = 5164 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 99) = 5164
  rw [ladder_pc 99 (by decide)]
  rfl

@[simp] theorem compactPc4165 : Artifact.submissionArtifact.instructionPC 4161 = 5166 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 100) = 5166
  rw [ladder_pc 100 (by decide)]
  rfl

@[simp] theorem compactPc4166 : Artifact.submissionArtifact.instructionPC 4162 = 5167 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 101) = 5167
  rw [ladder_pc 101 (by decide)]
  rfl

@[simp] theorem compactPc4167 : Artifact.submissionArtifact.instructionPC 4163 = 5168 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 102) = 5168
  rw [ladder_pc 102 (by decide)]
  rfl

@[simp] theorem compactPc4168 : Artifact.submissionArtifact.instructionPC 4164 = 5171 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 103) = 5171
  rw [ladder_pc 103 (by decide)]
  rfl

@[simp] theorem compactPc4169 : Artifact.submissionArtifact.instructionPC 4165 = 5172 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 104) = 5172
  rw [ladder_pc 104 (by decide)]
  rfl

@[simp] theorem compactPc4170 : Artifact.submissionArtifact.instructionPC 4166 = 5173 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 105) = 5173
  rw [ladder_pc 105 (by decide)]
  rfl

@[simp] theorem compactPc4171 : Artifact.submissionArtifact.instructionPC 4167 = 5174 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 106) = 5174
  rw [ladder_pc 106 (by decide)]
  rfl

@[simp] theorem compactPc4172 : Artifact.submissionArtifact.instructionPC 4168 = 5176 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 107) = 5176
  rw [ladder_pc 107 (by decide)]
  rfl

@[simp] theorem compactPc4173 : Artifact.submissionArtifact.instructionPC 4169 = 5177 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 108) = 5177
  rw [ladder_pc 108 (by decide)]
  rfl

@[simp] theorem compactPc4174 : Artifact.submissionArtifact.instructionPC 4170 = 5182 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 109) = 5182
  rw [ladder_pc 109 (by decide)]
  rfl

@[simp] theorem compactPc4175 : Artifact.submissionArtifact.instructionPC 4171 = 5187 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 110) = 5187
  rw [ladder_pc 110 (by decide)]
  rfl

@[simp] theorem compactPc4176 : Artifact.submissionArtifact.instructionPC 4172 = 5192 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 111) = 5192
  rw [ladder_pc 111 (by decide)]
  rfl

@[simp] theorem compactPc4177 : Artifact.submissionArtifact.instructionPC 4173 = 5197 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 112) = 5197
  rw [ladder_pc 112 (by decide)]
  rfl

@[simp] theorem compactPc4178 : Artifact.submissionArtifact.instructionPC 4174 = 5202 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 113) = 5202
  rw [ladder_pc 113 (by decide)]
  rfl

@[simp] theorem compactPc4179 : Artifact.submissionArtifact.instructionPC 4175 = 5205 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 114) = 5205
  rw [ladder_pc 114 (by decide)]
  rfl

@[simp] theorem compactPc4180 : Artifact.submissionArtifact.instructionPC 4176 = 5206 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 115) = 5206
  rw [ladder_pc 115 (by decide)]
  rfl

@[simp] theorem compactPc4181 : Artifact.submissionArtifact.instructionPC 4177 = 5207 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 116) = 5207
  rw [ladder_pc 116 (by decide)]
  rfl

@[simp] theorem compactPc4182 : Artifact.submissionArtifact.instructionPC 4178 = 5208 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 117) = 5208
  rw [ladder_pc 117 (by decide)]
  rfl

@[simp] theorem compactPc4183 : Artifact.submissionArtifact.instructionPC 4179 = 5209 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 118) = 5209
  rw [ladder_pc 118 (by decide)]
  rfl

@[simp] theorem compactPc4184 : Artifact.submissionArtifact.instructionPC 4180 = 5211 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 119) = 5211
  rw [ladder_pc 119 (by decide)]
  rfl

@[simp] theorem compactPc4185 : Artifact.submissionArtifact.instructionPC 4181 = 5212 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 120) = 5212
  rw [ladder_pc 120 (by decide)]
  rfl

@[simp] theorem compactPc4186 : Artifact.submissionArtifact.instructionPC 4182 = 5217 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 121) = 5217
  rw [ladder_pc 121 (by decide)]
  rfl

@[simp] theorem compactPc4187 : Artifact.submissionArtifact.instructionPC 4183 = 5222 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 122) = 5222
  rw [ladder_pc 122 (by decide)]
  rfl

@[simp] theorem compactPc4188 : Artifact.submissionArtifact.instructionPC 4184 = 5227 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 123) = 5227
  rw [ladder_pc 123 (by decide)]
  rfl

@[simp] theorem compactPc4189 : Artifact.submissionArtifact.instructionPC 4185 = 5232 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 124) = 5232
  rw [ladder_pc 124 (by decide)]
  rfl

@[simp] theorem compactPc4190 : Artifact.submissionArtifact.instructionPC 4186 = 5237 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 125) = 5237
  rw [ladder_pc 125 (by decide)]
  rfl

@[simp] theorem compactPc4191 : Artifact.submissionArtifact.instructionPC 4187 = 5240 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 126) = 5240
  rw [ladder_pc 126 (by decide)]
  rfl

@[simp] theorem compactPc4192 : Artifact.submissionArtifact.instructionPC 4188 = 5241 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 127) = 5241
  rw [ladder_pc 127 (by decide)]
  rfl

@[simp] theorem compactPc4193 : Artifact.submissionArtifact.instructionPC 4189 = 5242 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 128) = 5242
  rw [ladder_pc 128 (by decide)]
  rfl

@[simp] theorem compactPc4194 : Artifact.submissionArtifact.instructionPC 4190 = 5243 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 129) = 5243
  rw [ladder_pc 129 (by decide)]
  rfl

@[simp] theorem compactPc4195 : Artifact.submissionArtifact.instructionPC 4191 = 5244 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 130) = 5244
  rw [ladder_pc 130 (by decide)]
  rfl

@[simp] theorem compactPc4196 : Artifact.submissionArtifact.instructionPC 4192 = 5246 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 131) = 5246
  rw [ladder_pc 131 (by decide)]
  rfl

@[simp] theorem compactPc4197 : Artifact.submissionArtifact.instructionPC 4193 = 5247 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 132) = 5247
  rw [ladder_pc 132 (by decide)]
  rfl

@[simp] theorem compactPc4198 : Artifact.submissionArtifact.instructionPC 4194 = 5252 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 133) = 5252
  rw [ladder_pc 133 (by decide)]
  rfl

@[simp] theorem compactPc4199 : Artifact.submissionArtifact.instructionPC 4195 = 5257 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 134) = 5257
  rw [ladder_pc 134 (by decide)]
  rfl

@[simp] theorem compactPc4200 : Artifact.submissionArtifact.instructionPC 4196 = 5262 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 135) = 5262
  rw [ladder_pc 135 (by decide)]
  rfl

@[simp] theorem compactPc4201 : Artifact.submissionArtifact.instructionPC 4197 = 5267 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 136) = 5267
  rw [ladder_pc 136 (by decide)]
  rfl

@[simp] theorem compactPc4202 : Artifact.submissionArtifact.instructionPC 4198 = 5272 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 137) = 5272
  rw [ladder_pc 137 (by decide)]
  rfl

@[simp] theorem compactPc4203 : Artifact.submissionArtifact.instructionPC 4199 = 5275 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 138) = 5275
  rw [ladder_pc 138 (by decide)]
  rfl

@[simp] theorem compactPc4204 : Artifact.submissionArtifact.instructionPC 4200 = 5276 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 139) = 5276
  rw [ladder_pc 139 (by decide)]
  rfl

@[simp] theorem compactPc4205 : Artifact.submissionArtifact.instructionPC 4201 = 5277 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 140) = 5277
  rw [ladder_pc 140 (by decide)]
  rfl

@[simp] theorem compactPc4206 : Artifact.submissionArtifact.instructionPC 4202 = 5282 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 141) = 5282
  rw [ladder_pc 141 (by decide)]
  rfl

@[simp] theorem compactPc4207 : Artifact.submissionArtifact.instructionPC 4203 = 5287 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 142) = 5287
  rw [ladder_pc 142 (by decide)]
  rfl

@[simp] theorem compactPc4208 : Artifact.submissionArtifact.instructionPC 4204 = 5292 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 143) = 5292
  rw [ladder_pc 143 (by decide)]
  rfl

@[simp] theorem compactPc4209 : Artifact.submissionArtifact.instructionPC 4205 = 5297 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 144) = 5297
  rw [ladder_pc 144 (by decide)]
  rfl

@[simp] theorem compactPc4210 : Artifact.submissionArtifact.instructionPC 4206 = 5302 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 145) = 5302
  rw [ladder_pc 145 (by decide)]
  rfl

@[simp] theorem compactPc4211 : Artifact.submissionArtifact.instructionPC 4207 = 5303 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 146) = 5303
  rw [ladder_pc 146 (by decide)]
  rfl

@[simp] theorem compactPc4212 : Artifact.submissionArtifact.instructionPC 4208 = 5305 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 147) = 5305
  rw [ladder_pc 147 (by decide)]
  rfl

@[simp] theorem compactPc4213 : Artifact.submissionArtifact.instructionPC 4209 = 5306 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 148) = 5306
  rw [ladder_pc 148 (by decide)]
  rfl

@[simp] theorem compactPc4214 : Artifact.submissionArtifact.instructionPC 4210 = 5308 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 149) = 5308
  rw [ladder_pc 149 (by decide)]
  rfl

@[simp] theorem compactPc4215 : Artifact.submissionArtifact.instructionPC 4211 = 5309 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 150) = 5309
  rw [ladder_pc 150 (by decide)]
  rfl

@[simp] theorem compactPc4216 : Artifact.submissionArtifact.instructionPC 4212 = 5311 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 151) = 5311
  rw [ladder_pc 151 (by decide)]
  rfl

@[simp] theorem compactPc4217 : Artifact.submissionArtifact.instructionPC 4213 = 5312 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 152) = 5312
  rw [ladder_pc 152 (by decide)]
  rfl

@[simp] theorem compactPc4218 : Artifact.submissionArtifact.instructionPC 4214 = 5314 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 153) = 5314
  rw [ladder_pc 153 (by decide)]
  rfl

@[simp] theorem compactPc4219 : Artifact.submissionArtifact.instructionPC 4215 = 5315 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 154) = 5315
  rw [ladder_pc 154 (by decide)]
  rfl

@[simp] theorem compactPc4220 : Artifact.submissionArtifact.instructionPC 4216 = 5317 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 155) = 5317
  rw [ladder_pc 155 (by decide)]
  rfl

@[simp] theorem compactPc4221 : Artifact.submissionArtifact.instructionPC 4217 = 5318 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 156) = 5318
  rw [ladder_pc 156 (by decide)]
  rfl

@[simp] theorem compactPc4222 : Artifact.submissionArtifact.instructionPC 4218 = 5319 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 157) = 5319
  rw [ladder_pc 157 (by decide)]
  rfl

@[simp] theorem compactPc4223 : Artifact.submissionArtifact.instructionPC 4219 = 5320 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 158) = 5320
  rw [ladder_pc 158 (by decide)]
  rfl

@[simp] theorem compactPc4224 : Artifact.submissionArtifact.instructionPC 4220 = 5321 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 159) = 5321
  rw [ladder_pc 159 (by decide)]
  rfl

@[simp] theorem compactPc4225 : Artifact.submissionArtifact.instructionPC 4221 = 5322 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 160) = 5322
  rw [ladder_pc 160 (by decide)]
  rfl

@[simp] theorem compactPc4226 : Artifact.submissionArtifact.instructionPC 4222 = 5325 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 161) = 5325
  rw [ladder_pc 161 (by decide)]
  rfl

@[simp] theorem compactPc4227 : Artifact.submissionArtifact.instructionPC 4223 = 5328 := by
  show Artifact.submissionArtifact.instructionPC (4061 + 162) = 5328
  rw [ladder_pc 162 (by decide)]
  rfl

def laterPath : List Located :=
  [⟨4061, .op .JUMPDEST, (ladder_at 0 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4062, .op (.Dup ⟨2, by decide⟩), (ladder_at 1 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4063, .push ⟨2, by decide⟩ (UInt256.ofNat 464), (ladder_at 2 (by decide)).trans rfl, by decide⟩,
   ⟨4064, .op .JUMPI, (ladder_at 3 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩]

def prefixPath : List Located :=
  [⟨4061, .op .JUMPDEST, (ladder_at 0 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4062, .op (.Dup ⟨2, by decide⟩), (ladder_at 1 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4063, .push ⟨2, by decide⟩ (UInt256.ofNat 464), (ladder_at 2 (by decide)).trans rfl, by decide⟩,
   ⟨4064, .op .JUMPI, (ladder_at 3 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4065, .push ⟨1, by decide⟩ (UInt256.ofNat 32), (ladder_at 4 (by decide)).trans rfl, by decide⟩,
   ⟨4066, .push ⟨2, by decide⟩ (UInt256.ofNat 262), (ladder_at 5 (by decide)).trans rfl, by decide⟩,
   ⟨4067, .push ⟨0, by decide⟩ (UInt256.ofNat 0), (ladder_at 6 (by decide)).trans rfl, by decide⟩]

def firstComparePath : List Located :=
  [⟨4069, .push ⟨0, by decide⟩ (UInt256.ofNat 0), (ladder_at 8 (by decide)).trans rfl, by decide⟩,
   ⟨4070, .op .MLOAD, (ladder_at 9 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4071, .push ⟨0, by decide⟩ (UInt256.ofNat 0), (ladder_at 10 (by decide)).trans rfl, by decide⟩,
   ⟨4072, .op .CALLDATALOAD, (ladder_at 11 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4073, .op .XOR, (ladder_at 12 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4074, .push ⟨2, by decide⟩ (UInt256.ofNat 464), (ladder_at 13 (by decide)).trans rfl, by decide⟩,
   ⟨4075, .op .JUMPI, (ladder_at 14 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩]

def preparePath : List Located :=
  [⟨4076, .op .POP, (ladder_at 15 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4077, .push ⟨1, by decide⟩ (UInt256.ofNat 255), (ladder_at 16 (by decide)).trans rfl, by decide⟩,
   ⟨4078, .push ⟨0, by decide⟩ (UInt256.ofNat 0), (ladder_at 17 (by decide)).trans rfl, by decide⟩,
   ⟨4079, .op .NOT, (ladder_at 18 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4080, .op .DIV, (ladder_at 19 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4081, .push ⟨1, by decide⟩ (UInt256.ofNat 64), (ladder_at 20 (by decide)).trans rfl, by decide⟩,
   ⟨4082, .op .MUL, (ladder_at 21 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩]

def word1Path : List Located :=
  [⟨4083, .push ⟨32, by decide⟩ (UInt256.ofNat 75898346434861812577553744355519055536350986179947755549958789636940356975906), (ladder_at 22 (by decide)).trans rfl, by decide⟩,
   ⟨4084, .push ⟨1, by decide⟩ (UInt256.ofNat 32), (ladder_at 23 (by decide)).trans rfl, by decide⟩,
   ⟨4085, .op .CALLDATALOAD, (ladder_at 24 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4086, .op .XOR, (ladder_at 25 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4087, .push ⟨2, by decide⟩ (UInt256.ofNat 5320), (ladder_at 26 (by decide)).trans rfl, by decide⟩,
   ⟨4088, .op .JUMPI, (ladder_at 27 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩]

def word2Path : List Located :=
  [⟨4089, .push ⟨0, by decide⟩ (UInt256.ofNat 0), (ladder_at 28 (by decide)).trans rfl, by decide⟩,
   ⟨4090, .op .CALLDATALOAD, (ladder_at 29 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4091, .op (.Dup ⟨0, by decide⟩), (ladder_at 30 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4092, .op (.Dup ⟨2, by decide⟩), (ladder_at 31 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4093, .op .AND, (ladder_at 32 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4094, .op (.Dup ⟨0, by decide⟩), (ladder_at 33 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4095, .op .ADD, (ladder_at 34 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4096, .op .XOR, (ladder_at 35 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4097, .op (.Dup ⟨1, by decide⟩), (ladder_at 36 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4098, .op .XOR, (ladder_at 37 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4099, .push ⟨1, by decide⟩ (UInt256.ofNat 64), (ladder_at 38 (by decide)).trans rfl, by decide⟩,
   ⟨4100, .op .CALLDATALOAD, (ladder_at 39 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4101, .op .XOR, (ladder_at 40 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4102, .push ⟨2, by decide⟩ (UInt256.ofNat 5276), (ladder_at 41 (by decide)).trans rfl, by decide⟩,
   ⟨4103, .op .JUMPI, (ladder_at 42 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩]

def word3Path : List Located :=
  [⟨4104, .push ⟨1, by decide⟩ (UInt256.ofNat 32), (ladder_at 43 (by decide)).trans rfl, by decide⟩,
   ⟨4105, .op .CALLDATALOAD, (ladder_at 44 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4106, .op (.Dup ⟨0, by decide⟩), (ladder_at 45 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4107, .op (.Dup ⟨2, by decide⟩), (ladder_at 46 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4108, .op .AND, (ladder_at 47 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4109, .op (.Dup ⟨0, by decide⟩), (ladder_at 48 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4110, .op .ADD, (ladder_at 49 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4111, .op .XOR, (ladder_at 50 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4112, .op (.Dup ⟨1, by decide⟩), (ladder_at 51 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4113, .op .XOR, (ladder_at 52 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4114, .push ⟨1, by decide⟩ (UInt256.ofNat 96), (ladder_at 53 (by decide)).trans rfl, by decide⟩,
   ⟨4115, .op .CALLDATALOAD, (ladder_at 54 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4116, .op .XOR, (ladder_at 55 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4117, .push ⟨2, by decide⟩ (UInt256.ofNat 5276), (ladder_at 56 (by decide)).trans rfl, by decide⟩,
   ⟨4118, .op .JUMPI, (ladder_at 57 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩]

def word4Path : List Located :=
  [⟨4119, .push ⟨0, by decide⟩ (UInt256.ofNat 0), (ladder_at 58 (by decide)).trans rfl, by decide⟩,
   ⟨4120, .op .CALLDATALOAD, (ladder_at 59 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4121, .op (.Dup ⟨1, by decide⟩), (ladder_at 60 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4122, .op (.Dup ⟨0, by decide⟩), (ladder_at 61 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4123, .op .ADD, (ladder_at 62 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4124, .op .XOR, (ladder_at 63 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4125, .push ⟨1, by decide⟩ (UInt256.ofNat 128), (ladder_at 64 (by decide)).trans rfl, by decide⟩,
   ⟨4126, .op .CALLDATALOAD, (ladder_at 65 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4127, .op .XOR, (ladder_at 66 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4128, .push ⟨2, by decide⟩ (UInt256.ofNat 5241), (ladder_at 67 (by decide)).trans rfl, by decide⟩,
   ⟨4129, .op .JUMPI, (ladder_at 68 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩]

def word5Path : List Located :=
  [⟨4130, .push ⟨1, by decide⟩ (UInt256.ofNat 32), (ladder_at 69 (by decide)).trans rfl, by decide⟩,
   ⟨4131, .op .CALLDATALOAD, (ladder_at 70 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4132, .op (.Dup ⟨1, by decide⟩), (ladder_at 71 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4133, .op (.Dup ⟨0, by decide⟩), (ladder_at 72 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4134, .op .ADD, (ladder_at 73 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4135, .op .XOR, (ladder_at 74 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4136, .push ⟨1, by decide⟩ (UInt256.ofNat 160), (ladder_at 75 (by decide)).trans rfl, by decide⟩,
   ⟨4137, .op .CALLDATALOAD, (ladder_at 76 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4138, .op .XOR, (ladder_at 77 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4139, .push ⟨2, by decide⟩ (UInt256.ofNat 5241), (ladder_at 78 (by decide)).trans rfl, by decide⟩,
   ⟨4140, .op .JUMPI, (ladder_at 79 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩]

def word6Path : List Located :=
  [⟨4141, .push ⟨1, by decide⟩ (UInt256.ofNat 64), (ladder_at 80 (by decide)).trans rfl, by decide⟩,
   ⟨4142, .op .CALLDATALOAD, (ladder_at 81 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4143, .op (.Dup ⟨1, by decide⟩), (ladder_at 82 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4144, .op (.Dup ⟨0, by decide⟩), (ladder_at 83 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4145, .op .ADD, (ladder_at 84 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4146, .op .XOR, (ladder_at 85 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4147, .push ⟨1, by decide⟩ (UInt256.ofNat 192), (ladder_at 86 (by decide)).trans rfl, by decide⟩,
   ⟨4148, .op .CALLDATALOAD, (ladder_at 87 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4149, .op .XOR, (ladder_at 88 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4150, .push ⟨2, by decide⟩ (UInt256.ofNat 5206), (ladder_at 89 (by decide)).trans rfl, by decide⟩,
   ⟨4151, .op .JUMPI, (ladder_at 90 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩]

def word7Path : List Located :=
  [⟨4152, .push ⟨1, by decide⟩ (UInt256.ofNat 96), (ladder_at 91 (by decide)).trans rfl, by decide⟩,
   ⟨4153, .op .CALLDATALOAD, (ladder_at 92 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4154, .op (.Dup ⟨1, by decide⟩), (ladder_at 93 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4155, .op (.Dup ⟨0, by decide⟩), (ladder_at 94 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4156, .op .ADD, (ladder_at 95 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4157, .op .XOR, (ladder_at 96 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4158, .push ⟨5, by decide⟩ (UInt256.ofNat 99006248207), (ladder_at 97 (by decide)).trans rfl, by decide⟩,
   ⟨4159, .op .XOR, (ladder_at 98 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4160, .push ⟨1, by decide⟩ (UInt256.ofNat 224), (ladder_at 99 (by decide)).trans rfl, by decide⟩,
   ⟨4161, .op .CALLDATALOAD, (ladder_at 100 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4162, .op .XOR, (ladder_at 101 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4163, .push ⟨2, by decide⟩ (UInt256.ofNat 5206), (ladder_at 102 (by decide)).trans rfl, by decide⟩,
   ⟨4164, .op .JUMPI, (ladder_at 103 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩]

def h4Path : List Located :=
  [⟨4165, .op (.Swap ⟨1, by decide⟩), (ladder_at 104 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4166, .op .POP, (ladder_at 105 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4167, .push ⟨1, by decide⟩ (UInt256.ofNat 192), (ladder_at 106 (by decide)).trans rfl, by decide⟩,
   ⟨4168, .op (.Swap ⟨1, by decide⟩), (ladder_at 107 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4169, .push ⟨4, by decide⟩ (UInt256.ofNat 737150935), (ladder_at 108 (by decide)).trans rfl, by decide⟩,
   ⟨4170, .push ⟨4, by decide⟩ (UInt256.ofNat 4264519132), (ladder_at 109 (by decide)).trans rfl, by decide⟩,
   ⟨4171, .push ⟨4, by decide⟩ (UInt256.ofNat 3044672391), (ladder_at 110 (by decide)).trans rfl, by decide⟩,
   ⟨4172, .push ⟨4, by decide⟩ (UInt256.ofNat 1663407839), (ladder_at 111 (by decide)).trans rfl, by decide⟩,
   ⟨4173, .push ⟨4, by decide⟩ (UInt256.ofNat 4072035125), (ladder_at 112 (by decide)).trans rfl, by decide⟩,
   ⟨4174, .push ⟨2, by decide⟩ (UInt256.ofNat 5302), (ladder_at 113 (by decide)).trans rfl, by decide⟩,
   ⟨4175, .op .JUMP, (ladder_at 114 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩]

def h3Path : List Located :=
  [⟨4176, .op .JUMPDEST, (ladder_at 115 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4177, .op (.Swap ⟨1, by decide⟩), (ladder_at 116 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4178, .op .POP, (ladder_at 117 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4179, .push ⟨1, by decide⟩ (UInt256.ofNat 128), (ladder_at 118 (by decide)).trans rfl, by decide⟩,
   ⟨4180, .op (.Swap ⟨1, by decide⟩), (ladder_at 119 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4181, .push ⟨4, by decide⟩ (UInt256.ofNat 3850323193), (ladder_at 120 (by decide)).trans rfl, by decide⟩,
   ⟨4182, .push ⟨4, by decide⟩ (UInt256.ofNat 928826907), (ladder_at 121 (by decide)).trans rfl, by decide⟩,
   ⟨4183, .push ⟨4, by decide⟩ (UInt256.ofNat 358732556), (ladder_at 122 (by decide)).trans rfl, by decide⟩,
   ⟨4184, .push ⟨4, by decide⟩ (UInt256.ofNat 695251451), (ladder_at 123 (by decide)).trans rfl, by decide⟩,
   ⟨4185, .push ⟨4, by decide⟩ (UInt256.ofNat 1393315003), (ladder_at 124 (by decide)).trans rfl, by decide⟩,
   ⟨4186, .push ⟨2, by decide⟩ (UInt256.ofNat 5302), (ladder_at 125 (by decide)).trans rfl, by decide⟩,
   ⟨4187, .op .JUMP, (ladder_at 126 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩]

def h2Path : List Located :=
  [⟨4188, .op .JUMPDEST, (ladder_at 127 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4189, .op (.Swap ⟨1, by decide⟩), (ladder_at 128 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4190, .op .POP, (ladder_at 129 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4191, .push ⟨1, by decide⟩ (UInt256.ofNat 64), (ladder_at 130 (by decide)).trans rfl, by decide⟩,
   ⟨4192, .op (.Swap ⟨1, by decide⟩), (ladder_at 131 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4193, .push ⟨4, by decide⟩ (UInt256.ofNat 2543018249), (ladder_at 132 (by decide)).trans rfl, by decide⟩,
   ⟨4194, .push ⟨4, by decide⟩ (UInt256.ofNat 3354522469), (ladder_at 133 (by decide)).trans rfl, by decide⟩,
   ⟨4195, .push ⟨4, by decide⟩ (UInt256.ofNat 3681030016), (ladder_at 134 (by decide)).trans rfl, by decide⟩,
   ⟨4196, .push ⟨4, by decide⟩ (UInt256.ofNat 514068704), (ladder_at 135 (by decide)).trans rfl, by decide⟩,
   ⟨4197, .push ⟨4, by decide⟩ (UInt256.ofNat 2807398299), (ladder_at 136 (by decide)).trans rfl, by decide⟩,
   ⟨4198, .push ⟨2, by decide⟩ (UInt256.ofNat 5302), (ladder_at 137 (by decide)).trans rfl, by decide⟩,
   ⟨4199, .op .JUMP, (ladder_at 138 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩]

def h1Path : List Located :=
  [⟨4200, .op .JUMPDEST, (ladder_at 139 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4201, .push ⟨4, by decide⟩ (UInt256.ofNat 1007308478), (ladder_at 140 (by decide)).trans rfl, by decide⟩,
   ⟨4202, .push ⟨4, by decide⟩ (UInt256.ofNat 220066081), (ladder_at 141 (by decide)).trans rfl, by decide⟩,
   ⟨4203, .push ⟨4, by decide⟩ (UInt256.ofNat 621343384), (ladder_at 142 (by decide)).trans rfl, by decide⟩,
   ⟨4204, .push ⟨4, by decide⟩ (UInt256.ofNat 2391128076), (ladder_at 143 (by decide)).trans rfl, by decide⟩,
   ⟨4205, .push ⟨4, by decide⟩ (UInt256.ofNat 1080717082), (ladder_at 144 (by decide)).trans rfl, by decide⟩]

def storePath : List Located :=
  [⟨4206, .op .JUMPDEST, (ladder_at 145 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4207, .push ⟨1, by decide⟩ (UInt256.ofNat 32), (ladder_at 146 (by decide)).trans rfl, by decide⟩,
   ⟨4208, .op .MSTORE, (ladder_at 147 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4209, .push ⟨1, by decide⟩ (UInt256.ofNat 64), (ladder_at 148 (by decide)).trans rfl, by decide⟩,
   ⟨4210, .op .MSTORE, (ladder_at 149 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4211, .push ⟨1, by decide⟩ (UInt256.ofNat 96), (ladder_at 150 (by decide)).trans rfl, by decide⟩,
   ⟨4212, .op .MSTORE, (ladder_at 151 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4213, .push ⟨1, by decide⟩ (UInt256.ofNat 128), (ladder_at 152 (by decide)).trans rfl, by decide⟩,
   ⟨4214, .op .MSTORE, (ladder_at 153 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4215, .push ⟨1, by decide⟩ (UInt256.ofNat 160), (ladder_at 154 (by decide)).trans rfl, by decide⟩,
   ⟨4216, .op .MSTORE, (ladder_at 155 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4217, .op .POP, (ladder_at 156 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4218, .op .JUMP, (ladder_at 157 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩]

def bailPath : List Located :=
  [⟨4219, .op .JUMPDEST, (ladder_at 158 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4220, .op .POP, (ladder_at 159 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4221, .push ⟨2, by decide⟩ (UInt256.ofNat 736), (ladder_at 160 (by decide)).trans rfl, by decide⟩,
   ⟨4222, .push ⟨2, by decide⟩ (UInt256.ofNat 464), (ladder_at 161 (by decide)).trans rfl, by decide⟩,
   ⟨4223, .op .JUMP, (ladder_at 162 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PrefixStatePaths
