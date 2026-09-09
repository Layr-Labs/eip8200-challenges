import Batteries.Tactic.OpenPrivate
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Artifact
set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000

/-!
# Located paths of the depth-3 patterned-prefix ladder (instructions 4072..4264)

The ladder occupies the trailing 297 bytes (pc 4990..5286).  Its PC and
instruction lemmas are derived from a split of the instruction list at index
4072 so every `rfl` evaluates only the 193-instruction ladder segment.
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

private theorem ladderBefore_length : ladderBefore.length = 4072 := by
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
    Artifact.submissionArtifact.instructionPC (4072 + i) =
      4990 + ArtifactByteLength.byteLength (ladderSegment.take i) := by
  rw [ArtifactByteLength.byteLength_eq_assemble]
  exact ArtifactSegment.instructionPC_segment_of_bounds Artifact.submissionArtifact
    ladderBefore ladderSegment [] 4072 4990 artifact_ladder_split ladderBefore_length
    ladderBefore_pc i (by rw [ladderSegment_length]; exact hi)

private theorem ladder_at (i : Nat) (hi : i < 193) :
    Artifact.submissionArtifact.instructions[4072 + i]? = ladderSegment[i]? := by
  have h := ArtifactSegment.getElem?_segment Artifact.submissionArtifact
    ladderBefore ladderSegment [] artifact_ladder_split i (by rw [ladderSegment_length]; exact hi)
  rwa [ladderBefore_length] at h

/-! ## Instruction PCs -/

@[simp] theorem pc4072 : Artifact.submissionArtifact.instructionPC 4072 = 4990 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 0) = 4990
  rw [ladder_pc 0 (by decide)]
  rfl

@[simp] theorem pc4073 : Artifact.submissionArtifact.instructionPC 4073 = 4991 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 1) = 4991
  rw [ladder_pc 1 (by decide)]
  rfl

@[simp] theorem pc4074 : Artifact.submissionArtifact.instructionPC 4074 = 4992 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 2) = 4992
  rw [ladder_pc 2 (by decide)]
  rfl

@[simp] theorem pc4075 : Artifact.submissionArtifact.instructionPC 4075 = 4995 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 3) = 4995
  rw [ladder_pc 3 (by decide)]
  rfl

@[simp] theorem pc4076 : Artifact.submissionArtifact.instructionPC 4076 = 4996 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 4) = 4996
  rw [ladder_pc 4 (by decide)]
  rfl

@[simp] theorem pc4077 : Artifact.submissionArtifact.instructionPC 4077 = 4998 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 5) = 4998
  rw [ladder_pc 5 (by decide)]
  rfl

@[simp] theorem pc4078 : Artifact.submissionArtifact.instructionPC 4078 = 5001 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 6) = 5001
  rw [ladder_pc 6 (by decide)]
  rfl

@[simp] theorem pc4079 : Artifact.submissionArtifact.instructionPC 4079 = 5002 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 7) = 5002
  rw [ladder_pc 7 (by decide)]
  rfl

@[simp] theorem pc4080 : Artifact.submissionArtifact.instructionPC 4080 = 5003 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 8) = 5003
  rw [ladder_pc 8 (by decide)]
  rfl

@[simp] theorem pc4081 : Artifact.submissionArtifact.instructionPC 4081 = 5004 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 9) = 5004
  rw [ladder_pc 9 (by decide)]
  rfl

@[simp] theorem pc4082 : Artifact.submissionArtifact.instructionPC 4082 = 5005 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 10) = 5005
  rw [ladder_pc 10 (by decide)]
  rfl

@[simp] theorem pc4083 : Artifact.submissionArtifact.instructionPC 4083 = 5006 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 11) = 5006
  rw [ladder_pc 11 (by decide)]
  rfl

@[simp] theorem pc4084 : Artifact.submissionArtifact.instructionPC 4084 = 5007 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 12) = 5007
  rw [ladder_pc 12 (by decide)]
  rfl

@[simp] theorem pc4085 : Artifact.submissionArtifact.instructionPC 4085 = 5008 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 13) = 5008
  rw [ladder_pc 13 (by decide)]
  rfl

@[simp] theorem pc4086 : Artifact.submissionArtifact.instructionPC 4086 = 5011 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 14) = 5011
  rw [ladder_pc 14 (by decide)]
  rfl

@[simp] theorem pc4087 : Artifact.submissionArtifact.instructionPC 4087 = 5012 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 15) = 5012
  rw [ladder_pc 15 (by decide)]
  rfl

@[simp] theorem pc4088 : Artifact.submissionArtifact.instructionPC 4088 = 5014 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 16) = 5014
  rw [ladder_pc 16 (by decide)]
  rfl

@[simp] theorem pc4089 : Artifact.submissionArtifact.instructionPC 4089 = 5015 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 17) = 5015
  rw [ladder_pc 17 (by decide)]
  rfl

@[simp] theorem pc4090 : Artifact.submissionArtifact.instructionPC 4090 = 5016 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 18) = 5016
  rw [ladder_pc 18 (by decide)]
  rfl

@[simp] theorem pc4091 : Artifact.submissionArtifact.instructionPC 4091 = 5017 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 19) = 5017
  rw [ladder_pc 19 (by decide)]
  rfl

@[simp] theorem pc4092 : Artifact.submissionArtifact.instructionPC 4092 = 5019 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 20) = 5019
  rw [ladder_pc 20 (by decide)]
  rfl

@[simp] theorem pc4093 : Artifact.submissionArtifact.instructionPC 4093 = 5020 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 21) = 5020
  rw [ladder_pc 21 (by decide)]
  rfl

@[simp] theorem pc4094 : Artifact.submissionArtifact.instructionPC 4094 = 5021 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 22) = 5021
  rw [ladder_pc 22 (by decide)]
  rfl

@[simp] theorem pc4095 : Artifact.submissionArtifact.instructionPC 4095 = 5022 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 23) = 5022
  rw [ladder_pc 23 (by decide)]
  rfl

@[simp] theorem pc4096 : Artifact.submissionArtifact.instructionPC 4096 = 5023 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 24) = 5023
  rw [ladder_pc 24 (by decide)]
  rfl

@[simp] theorem pc4097 : Artifact.submissionArtifact.instructionPC 4097 = 5025 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 25) = 5025
  rw [ladder_pc 25 (by decide)]
  rfl

@[simp] theorem pc4098 : Artifact.submissionArtifact.instructionPC 4098 = 5026 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 26) = 5026
  rw [ladder_pc 26 (by decide)]
  rfl

@[simp] theorem pc4099 : Artifact.submissionArtifact.instructionPC 4099 = 5027 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 27) = 5027
  rw [ladder_pc 27 (by decide)]
  rfl

@[simp] theorem pc4100 : Artifact.submissionArtifact.instructionPC 4100 = 5028 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 28) = 5028
  rw [ladder_pc 28 (by decide)]
  rfl

@[simp] theorem pc4101 : Artifact.submissionArtifact.instructionPC 4101 = 5029 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 29) = 5029
  rw [ladder_pc 29 (by decide)]
  rfl

@[simp] theorem pc4102 : Artifact.submissionArtifact.instructionPC 4102 = 5030 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 30) = 5030
  rw [ladder_pc 30 (by decide)]
  rfl

@[simp] theorem pc4103 : Artifact.submissionArtifact.instructionPC 4103 = 5031 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 31) = 5031
  rw [ladder_pc 31 (by decide)]
  rfl

@[simp] theorem pc4104 : Artifact.submissionArtifact.instructionPC 4104 = 5032 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 32) = 5032
  rw [ladder_pc 32 (by decide)]
  rfl

@[simp] theorem pc4105 : Artifact.submissionArtifact.instructionPC 4105 = 5033 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 33) = 5033
  rw [ladder_pc 33 (by decide)]
  rfl

@[simp] theorem pc4106 : Artifact.submissionArtifact.instructionPC 4106 = 5034 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 34) = 5034
  rw [ladder_pc 34 (by decide)]
  rfl

@[simp] theorem pc4107 : Artifact.submissionArtifact.instructionPC 4107 = 5035 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 35) = 5035
  rw [ladder_pc 35 (by decide)]
  rfl

@[simp] theorem pc4108 : Artifact.submissionArtifact.instructionPC 4108 = 5036 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 36) = 5036
  rw [ladder_pc 36 (by decide)]
  rfl

@[simp] theorem pc4109 : Artifact.submissionArtifact.instructionPC 4109 = 5037 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 37) = 5037
  rw [ladder_pc 37 (by decide)]
  rfl

@[simp] theorem pc4110 : Artifact.submissionArtifact.instructionPC 4110 = 5038 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 38) = 5038
  rw [ladder_pc 38 (by decide)]
  rfl

@[simp] theorem pc4111 : Artifact.submissionArtifact.instructionPC 4111 = 5039 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 39) = 5039
  rw [ladder_pc 39 (by decide)]
  rfl

@[simp] theorem pc4112 : Artifact.submissionArtifact.instructionPC 4112 = 5040 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 40) = 5040
  rw [ladder_pc 40 (by decide)]
  rfl

@[simp] theorem pc4113 : Artifact.submissionArtifact.instructionPC 4113 = 5042 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 41) = 5042
  rw [ladder_pc 41 (by decide)]
  rfl

@[simp] theorem pc4114 : Artifact.submissionArtifact.instructionPC 4114 = 5043 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 42) = 5043
  rw [ladder_pc 42 (by decide)]
  rfl

@[simp] theorem pc4115 : Artifact.submissionArtifact.instructionPC 4115 = 5044 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 43) = 5044
  rw [ladder_pc 43 (by decide)]
  rfl

@[simp] theorem pc4116 : Artifact.submissionArtifact.instructionPC 4116 = 5047 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 44) = 5047
  rw [ladder_pc 44 (by decide)]
  rfl

@[simp] theorem pc4117 : Artifact.submissionArtifact.instructionPC 4117 = 5048 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 45) = 5048
  rw [ladder_pc 45 (by decide)]
  rfl

@[simp] theorem pc4118 : Artifact.submissionArtifact.instructionPC 4118 = 5049 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 46) = 5049
  rw [ladder_pc 46 (by decide)]
  rfl

@[simp] theorem pc4119 : Artifact.submissionArtifact.instructionPC 4119 = 5050 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 47) = 5050
  rw [ladder_pc 47 (by decide)]
  rfl

@[simp] theorem pc4120 : Artifact.submissionArtifact.instructionPC 4120 = 5051 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 48) = 5051
  rw [ladder_pc 48 (by decide)]
  rfl

@[simp] theorem pc4121 : Artifact.submissionArtifact.instructionPC 4121 = 5052 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 49) = 5052
  rw [ladder_pc 49 (by decide)]
  rfl

@[simp] theorem pc4122 : Artifact.submissionArtifact.instructionPC 4122 = 5053 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 50) = 5053
  rw [ladder_pc 50 (by decide)]
  rfl

@[simp] theorem pc4123 : Artifact.submissionArtifact.instructionPC 4123 = 5054 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 51) = 5054
  rw [ladder_pc 51 (by decide)]
  rfl

@[simp] theorem pc4124 : Artifact.submissionArtifact.instructionPC 4124 = 5055 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 52) = 5055
  rw [ladder_pc 52 (by decide)]
  rfl

@[simp] theorem pc4125 : Artifact.submissionArtifact.instructionPC 4125 = 5056 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 53) = 5056
  rw [ladder_pc 53 (by decide)]
  rfl

@[simp] theorem pc4126 : Artifact.submissionArtifact.instructionPC 4126 = 5057 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 54) = 5057
  rw [ladder_pc 54 (by decide)]
  rfl

@[simp] theorem pc4127 : Artifact.submissionArtifact.instructionPC 4127 = 5058 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 55) = 5058
  rw [ladder_pc 55 (by decide)]
  rfl

@[simp] theorem pc4128 : Artifact.submissionArtifact.instructionPC 4128 = 5059 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 56) = 5059
  rw [ladder_pc 56 (by decide)]
  rfl

@[simp] theorem pc4129 : Artifact.submissionArtifact.instructionPC 4129 = 5060 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 57) = 5060
  rw [ladder_pc 57 (by decide)]
  rfl

@[simp] theorem pc4130 : Artifact.submissionArtifact.instructionPC 4130 = 5062 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 58) = 5062
  rw [ladder_pc 58 (by decide)]
  rfl

@[simp] theorem pc4131 : Artifact.submissionArtifact.instructionPC 4131 = 5063 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 59) = 5063
  rw [ladder_pc 59 (by decide)]
  rfl

@[simp] theorem pc4132 : Artifact.submissionArtifact.instructionPC 4132 = 5064 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 60) = 5064
  rw [ladder_pc 60 (by decide)]
  rfl

@[simp] theorem pc4133 : Artifact.submissionArtifact.instructionPC 4133 = 5067 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 61) = 5067
  rw [ladder_pc 61 (by decide)]
  rfl

@[simp] theorem pc4134 : Artifact.submissionArtifact.instructionPC 4134 = 5068 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 62) = 5068
  rw [ladder_pc 62 (by decide)]
  rfl

@[simp] theorem pc4135 : Artifact.submissionArtifact.instructionPC 4135 = 5069 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 63) = 5069
  rw [ladder_pc 63 (by decide)]
  rfl

@[simp] theorem pc4136 : Artifact.submissionArtifact.instructionPC 4136 = 5070 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 64) = 5070
  rw [ladder_pc 64 (by decide)]
  rfl

@[simp] theorem pc4137 : Artifact.submissionArtifact.instructionPC 4137 = 5071 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 65) = 5071
  rw [ladder_pc 65 (by decide)]
  rfl

@[simp] theorem pc4138 : Artifact.submissionArtifact.instructionPC 4138 = 5072 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 66) = 5072
  rw [ladder_pc 66 (by decide)]
  rfl

@[simp] theorem pc4139 : Artifact.submissionArtifact.instructionPC 4139 = 5073 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 67) = 5073
  rw [ladder_pc 67 (by decide)]
  rfl

@[simp] theorem pc4140 : Artifact.submissionArtifact.instructionPC 4140 = 5074 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 68) = 5074
  rw [ladder_pc 68 (by decide)]
  rfl

@[simp] theorem pc4141 : Artifact.submissionArtifact.instructionPC 4141 = 5075 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 69) = 5075
  rw [ladder_pc 69 (by decide)]
  rfl

@[simp] theorem pc4142 : Artifact.submissionArtifact.instructionPC 4142 = 5076 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 70) = 5076
  rw [ladder_pc 70 (by decide)]
  rfl

@[simp] theorem pc4143 : Artifact.submissionArtifact.instructionPC 4143 = 5077 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 71) = 5077
  rw [ladder_pc 71 (by decide)]
  rfl

@[simp] theorem pc4144 : Artifact.submissionArtifact.instructionPC 4144 = 5078 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 72) = 5078
  rw [ladder_pc 72 (by decide)]
  rfl

@[simp] theorem pc4145 : Artifact.submissionArtifact.instructionPC 4145 = 5079 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 73) = 5079
  rw [ladder_pc 73 (by decide)]
  rfl

@[simp] theorem pc4146 : Artifact.submissionArtifact.instructionPC 4146 = 5080 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 74) = 5080
  rw [ladder_pc 74 (by decide)]
  rfl

@[simp] theorem pc4147 : Artifact.submissionArtifact.instructionPC 4147 = 5082 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 75) = 5082
  rw [ladder_pc 75 (by decide)]
  rfl

@[simp] theorem pc4148 : Artifact.submissionArtifact.instructionPC 4148 = 5083 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 76) = 5083
  rw [ladder_pc 76 (by decide)]
  rfl

@[simp] theorem pc4149 : Artifact.submissionArtifact.instructionPC 4149 = 5084 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 77) = 5084
  rw [ladder_pc 77 (by decide)]
  rfl

@[simp] theorem pc4150 : Artifact.submissionArtifact.instructionPC 4150 = 5087 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 78) = 5087
  rw [ladder_pc 78 (by decide)]
  rfl

@[simp] theorem pc4151 : Artifact.submissionArtifact.instructionPC 4151 = 5088 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 79) = 5088
  rw [ladder_pc 79 (by decide)]
  rfl

@[simp] theorem pc4152 : Artifact.submissionArtifact.instructionPC 4152 = 5089 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 80) = 5089
  rw [ladder_pc 80 (by decide)]
  rfl

@[simp] theorem pc4153 : Artifact.submissionArtifact.instructionPC 4153 = 5090 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 81) = 5090
  rw [ladder_pc 81 (by decide)]
  rfl

@[simp] theorem pc4154 : Artifact.submissionArtifact.instructionPC 4154 = 5091 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 82) = 5091
  rw [ladder_pc 82 (by decide)]
  rfl

@[simp] theorem pc4155 : Artifact.submissionArtifact.instructionPC 4155 = 5092 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 83) = 5092
  rw [ladder_pc 83 (by decide)]
  rfl

@[simp] theorem pc4156 : Artifact.submissionArtifact.instructionPC 4156 = 5093 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 84) = 5093
  rw [ladder_pc 84 (by decide)]
  rfl

@[simp] theorem pc4157 : Artifact.submissionArtifact.instructionPC 4157 = 5094 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 85) = 5094
  rw [ladder_pc 85 (by decide)]
  rfl

@[simp] theorem pc4158 : Artifact.submissionArtifact.instructionPC 4158 = 5095 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 86) = 5095
  rw [ladder_pc 86 (by decide)]
  rfl

@[simp] theorem pc4159 : Artifact.submissionArtifact.instructionPC 4159 = 5096 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 87) = 5096
  rw [ladder_pc 87 (by decide)]
  rfl

@[simp] theorem pc4160 : Artifact.submissionArtifact.instructionPC 4160 = 5097 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 88) = 5097
  rw [ladder_pc 88 (by decide)]
  rfl

@[simp] theorem pc4161 : Artifact.submissionArtifact.instructionPC 4161 = 5098 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 89) = 5098
  rw [ladder_pc 89 (by decide)]
  rfl

@[simp] theorem pc4162 : Artifact.submissionArtifact.instructionPC 4162 = 5099 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 90) = 5099
  rw [ladder_pc 90 (by decide)]
  rfl

@[simp] theorem pc4163 : Artifact.submissionArtifact.instructionPC 4163 = 5100 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 91) = 5100
  rw [ladder_pc 91 (by decide)]
  rfl

@[simp] theorem pc4164 : Artifact.submissionArtifact.instructionPC 4164 = 5102 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 92) = 5102
  rw [ladder_pc 92 (by decide)]
  rfl

@[simp] theorem pc4165 : Artifact.submissionArtifact.instructionPC 4165 = 5103 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 93) = 5103
  rw [ladder_pc 93 (by decide)]
  rfl

@[simp] theorem pc4166 : Artifact.submissionArtifact.instructionPC 4166 = 5104 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 94) = 5104
  rw [ladder_pc 94 (by decide)]
  rfl

@[simp] theorem pc4167 : Artifact.submissionArtifact.instructionPC 4167 = 5107 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 95) = 5107
  rw [ladder_pc 95 (by decide)]
  rfl

@[simp] theorem pc4168 : Artifact.submissionArtifact.instructionPC 4168 = 5108 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 96) = 5108
  rw [ladder_pc 96 (by decide)]
  rfl

@[simp] theorem pc4169 : Artifact.submissionArtifact.instructionPC 4169 = 5109 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 97) = 5109
  rw [ladder_pc 97 (by decide)]
  rfl

@[simp] theorem pc4170 : Artifact.submissionArtifact.instructionPC 4170 = 5110 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 98) = 5110
  rw [ladder_pc 98 (by decide)]
  rfl

@[simp] theorem pc4171 : Artifact.submissionArtifact.instructionPC 4171 = 5111 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 99) = 5111
  rw [ladder_pc 99 (by decide)]
  rfl

@[simp] theorem pc4172 : Artifact.submissionArtifact.instructionPC 4172 = 5112 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 100) = 5112
  rw [ladder_pc 100 (by decide)]
  rfl

@[simp] theorem pc4173 : Artifact.submissionArtifact.instructionPC 4173 = 5113 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 101) = 5113
  rw [ladder_pc 101 (by decide)]
  rfl

@[simp] theorem pc4174 : Artifact.submissionArtifact.instructionPC 4174 = 5114 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 102) = 5114
  rw [ladder_pc 102 (by decide)]
  rfl

@[simp] theorem pc4175 : Artifact.submissionArtifact.instructionPC 4175 = 5115 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 103) = 5115
  rw [ladder_pc 103 (by decide)]
  rfl

@[simp] theorem pc4176 : Artifact.submissionArtifact.instructionPC 4176 = 5116 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 104) = 5116
  rw [ladder_pc 104 (by decide)]
  rfl

@[simp] theorem pc4177 : Artifact.submissionArtifact.instructionPC 4177 = 5117 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 105) = 5117
  rw [ladder_pc 105 (by decide)]
  rfl

@[simp] theorem pc4178 : Artifact.submissionArtifact.instructionPC 4178 = 5118 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 106) = 5118
  rw [ladder_pc 106 (by decide)]
  rfl

@[simp] theorem pc4179 : Artifact.submissionArtifact.instructionPC 4179 = 5119 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 107) = 5119
  rw [ladder_pc 107 (by decide)]
  rfl

@[simp] theorem pc4180 : Artifact.submissionArtifact.instructionPC 4180 = 5120 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 108) = 5120
  rw [ladder_pc 108 (by decide)]
  rfl

@[simp] theorem pc4181 : Artifact.submissionArtifact.instructionPC 4181 = 5122 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 109) = 5122
  rw [ladder_pc 109 (by decide)]
  rfl

@[simp] theorem pc4182 : Artifact.submissionArtifact.instructionPC 4182 = 5123 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 110) = 5123
  rw [ladder_pc 110 (by decide)]
  rfl

@[simp] theorem pc4183 : Artifact.submissionArtifact.instructionPC 4183 = 5124 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 111) = 5124
  rw [ladder_pc 111 (by decide)]
  rfl

@[simp] theorem pc4184 : Artifact.submissionArtifact.instructionPC 4184 = 5127 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 112) = 5127
  rw [ladder_pc 112 (by decide)]
  rfl

@[simp] theorem pc4185 : Artifact.submissionArtifact.instructionPC 4185 = 5128 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 113) = 5128
  rw [ladder_pc 113 (by decide)]
  rfl

@[simp] theorem pc4186 : Artifact.submissionArtifact.instructionPC 4186 = 5129 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 114) = 5129
  rw [ladder_pc 114 (by decide)]
  rfl

@[simp] theorem pc4187 : Artifact.submissionArtifact.instructionPC 4187 = 5130 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 115) = 5130
  rw [ladder_pc 115 (by decide)]
  rfl

@[simp] theorem pc4188 : Artifact.submissionArtifact.instructionPC 4188 = 5131 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 116) = 5131
  rw [ladder_pc 116 (by decide)]
  rfl

@[simp] theorem pc4189 : Artifact.submissionArtifact.instructionPC 4189 = 5132 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 117) = 5132
  rw [ladder_pc 117 (by decide)]
  rfl

@[simp] theorem pc4190 : Artifact.submissionArtifact.instructionPC 4190 = 5133 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 118) = 5133
  rw [ladder_pc 118 (by decide)]
  rfl

@[simp] theorem pc4191 : Artifact.submissionArtifact.instructionPC 4191 = 5134 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 119) = 5134
  rw [ladder_pc 119 (by decide)]
  rfl

@[simp] theorem pc4192 : Artifact.submissionArtifact.instructionPC 4192 = 5135 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 120) = 5135
  rw [ladder_pc 120 (by decide)]
  rfl

@[simp] theorem pc4193 : Artifact.submissionArtifact.instructionPC 4193 = 5137 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 121) = 5137
  rw [ladder_pc 121 (by decide)]
  rfl

@[simp] theorem pc4194 : Artifact.submissionArtifact.instructionPC 4194 = 5138 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 122) = 5138
  rw [ladder_pc 122 (by decide)]
  rfl

@[simp] theorem pc4195 : Artifact.submissionArtifact.instructionPC 4195 = 5143 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 123) = 5143
  rw [ladder_pc 123 (by decide)]
  rfl

@[simp] theorem pc4196 : Artifact.submissionArtifact.instructionPC 4196 = 5145 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 124) = 5145
  rw [ladder_pc 124 (by decide)]
  rfl

@[simp] theorem pc4197 : Artifact.submissionArtifact.instructionPC 4197 = 5146 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 125) = 5146
  rw [ladder_pc 125 (by decide)]
  rfl

@[simp] theorem pc4198 : Artifact.submissionArtifact.instructionPC 4198 = 5151 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 126) = 5151
  rw [ladder_pc 126 (by decide)]
  rfl

@[simp] theorem pc4199 : Artifact.submissionArtifact.instructionPC 4199 = 5153 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 127) = 5153
  rw [ladder_pc 127 (by decide)]
  rfl

@[simp] theorem pc4200 : Artifact.submissionArtifact.instructionPC 4200 = 5154 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 128) = 5154
  rw [ladder_pc 128 (by decide)]
  rfl

@[simp] theorem pc4201 : Artifact.submissionArtifact.instructionPC 4201 = 5159 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 129) = 5159
  rw [ladder_pc 129 (by decide)]
  rfl

@[simp] theorem pc4202 : Artifact.submissionArtifact.instructionPC 4202 = 5161 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 130) = 5161
  rw [ladder_pc 130 (by decide)]
  rfl

@[simp] theorem pc4203 : Artifact.submissionArtifact.instructionPC 4203 = 5162 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 131) = 5162
  rw [ladder_pc 131 (by decide)]
  rfl

@[simp] theorem pc4204 : Artifact.submissionArtifact.instructionPC 4204 = 5167 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 132) = 5167
  rw [ladder_pc 132 (by decide)]
  rfl

@[simp] theorem pc4205 : Artifact.submissionArtifact.instructionPC 4205 = 5169 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 133) = 5169
  rw [ladder_pc 133 (by decide)]
  rfl

@[simp] theorem pc4206 : Artifact.submissionArtifact.instructionPC 4206 = 5170 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 134) = 5170
  rw [ladder_pc 134 (by decide)]
  rfl

@[simp] theorem pc4207 : Artifact.submissionArtifact.instructionPC 4207 = 5175 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 135) = 5175
  rw [ladder_pc 135 (by decide)]
  rfl

@[simp] theorem pc4208 : Artifact.submissionArtifact.instructionPC 4208 = 5177 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 136) = 5177
  rw [ladder_pc 136 (by decide)]
  rfl

@[simp] theorem pc4209 : Artifact.submissionArtifact.instructionPC 4209 = 5178 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 137) = 5178
  rw [ladder_pc 137 (by decide)]
  rfl

@[simp] theorem pc4210 : Artifact.submissionArtifact.instructionPC 4210 = 5179 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 138) = 5179
  rw [ladder_pc 138 (by decide)]
  rfl

@[simp] theorem pc4211 : Artifact.submissionArtifact.instructionPC 4211 = 5180 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 139) = 5180
  rw [ladder_pc 139 (by decide)]
  rfl

@[simp] theorem pc4212 : Artifact.submissionArtifact.instructionPC 4212 = 5181 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 140) = 5181
  rw [ladder_pc 140 (by decide)]
  rfl

@[simp] theorem pc4213 : Artifact.submissionArtifact.instructionPC 4213 = 5182 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 141) = 5182
  rw [ladder_pc 141 (by decide)]
  rfl

@[simp] theorem pc4214 : Artifact.submissionArtifact.instructionPC 4214 = 5183 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 142) = 5183
  rw [ladder_pc 142 (by decide)]
  rfl

@[simp] theorem pc4215 : Artifact.submissionArtifact.instructionPC 4215 = 5184 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 143) = 5184
  rw [ladder_pc 143 (by decide)]
  rfl

@[simp] theorem pc4216 : Artifact.submissionArtifact.instructionPC 4216 = 5185 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 144) = 5185
  rw [ladder_pc 144 (by decide)]
  rfl

@[simp] theorem pc4217 : Artifact.submissionArtifact.instructionPC 4217 = 5186 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 145) = 5186
  rw [ladder_pc 145 (by decide)]
  rfl

@[simp] theorem pc4218 : Artifact.submissionArtifact.instructionPC 4218 = 5187 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 146) = 5187
  rw [ladder_pc 146 (by decide)]
  rfl

@[simp] theorem pc4219 : Artifact.submissionArtifact.instructionPC 4219 = 5189 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 147) = 5189
  rw [ladder_pc 147 (by decide)]
  rfl

@[simp] theorem pc4220 : Artifact.submissionArtifact.instructionPC 4220 = 5190 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 148) = 5190
  rw [ladder_pc 148 (by decide)]
  rfl

@[simp] theorem pc4221 : Artifact.submissionArtifact.instructionPC 4221 = 5195 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 149) = 5195
  rw [ladder_pc 149 (by decide)]
  rfl

@[simp] theorem pc4222 : Artifact.submissionArtifact.instructionPC 4222 = 5197 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 150) = 5197
  rw [ladder_pc 150 (by decide)]
  rfl

@[simp] theorem pc4223 : Artifact.submissionArtifact.instructionPC 4223 = 5198 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 151) = 5198
  rw [ladder_pc 151 (by decide)]
  rfl

@[simp] theorem pc4224 : Artifact.submissionArtifact.instructionPC 4224 = 5203 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 152) = 5203
  rw [ladder_pc 152 (by decide)]
  rfl

@[simp] theorem pc4225 : Artifact.submissionArtifact.instructionPC 4225 = 5205 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 153) = 5205
  rw [ladder_pc 153 (by decide)]
  rfl

@[simp] theorem pc4226 : Artifact.submissionArtifact.instructionPC 4226 = 5206 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 154) = 5206
  rw [ladder_pc 154 (by decide)]
  rfl

@[simp] theorem pc4227 : Artifact.submissionArtifact.instructionPC 4227 = 5211 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 155) = 5211
  rw [ladder_pc 155 (by decide)]
  rfl

@[simp] theorem pc4228 : Artifact.submissionArtifact.instructionPC 4228 = 5213 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 156) = 5213
  rw [ladder_pc 156 (by decide)]
  rfl

@[simp] theorem pc4229 : Artifact.submissionArtifact.instructionPC 4229 = 5214 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 157) = 5214
  rw [ladder_pc 157 (by decide)]
  rfl

@[simp] theorem pc4230 : Artifact.submissionArtifact.instructionPC 4230 = 5219 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 158) = 5219
  rw [ladder_pc 158 (by decide)]
  rfl

@[simp] theorem pc4231 : Artifact.submissionArtifact.instructionPC 4231 = 5221 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 159) = 5221
  rw [ladder_pc 159 (by decide)]
  rfl

@[simp] theorem pc4232 : Artifact.submissionArtifact.instructionPC 4232 = 5222 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 160) = 5222
  rw [ladder_pc 160 (by decide)]
  rfl

@[simp] theorem pc4233 : Artifact.submissionArtifact.instructionPC 4233 = 5227 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 161) = 5227
  rw [ladder_pc 161 (by decide)]
  rfl

@[simp] theorem pc4234 : Artifact.submissionArtifact.instructionPC 4234 = 5229 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 162) = 5229
  rw [ladder_pc 162 (by decide)]
  rfl

@[simp] theorem pc4235 : Artifact.submissionArtifact.instructionPC 4235 = 5230 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 163) = 5230
  rw [ladder_pc 163 (by decide)]
  rfl

@[simp] theorem pc4236 : Artifact.submissionArtifact.instructionPC 4236 = 5231 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 164) = 5231
  rw [ladder_pc 164 (by decide)]
  rfl

@[simp] theorem pc4237 : Artifact.submissionArtifact.instructionPC 4237 = 5232 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 165) = 5232
  rw [ladder_pc 165 (by decide)]
  rfl

@[simp] theorem pc4238 : Artifact.submissionArtifact.instructionPC 4238 = 5233 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 166) = 5233
  rw [ladder_pc 166 (by decide)]
  rfl

@[simp] theorem pc4239 : Artifact.submissionArtifact.instructionPC 4239 = 5234 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 167) = 5234
  rw [ladder_pc 167 (by decide)]
  rfl

@[simp] theorem pc4240 : Artifact.submissionArtifact.instructionPC 4240 = 5235 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 168) = 5235
  rw [ladder_pc 168 (by decide)]
  rfl

@[simp] theorem pc4241 : Artifact.submissionArtifact.instructionPC 4241 = 5236 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 169) = 5236
  rw [ladder_pc 169 (by decide)]
  rfl

@[simp] theorem pc4242 : Artifact.submissionArtifact.instructionPC 4242 = 5237 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 170) = 5237
  rw [ladder_pc 170 (by decide)]
  rfl

@[simp] theorem pc4243 : Artifact.submissionArtifact.instructionPC 4243 = 5242 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 171) = 5242
  rw [ladder_pc 171 (by decide)]
  rfl

@[simp] theorem pc4244 : Artifact.submissionArtifact.instructionPC 4244 = 5244 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 172) = 5244
  rw [ladder_pc 172 (by decide)]
  rfl

@[simp] theorem pc4245 : Artifact.submissionArtifact.instructionPC 4245 = 5245 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 173) = 5245
  rw [ladder_pc 173 (by decide)]
  rfl

@[simp] theorem pc4246 : Artifact.submissionArtifact.instructionPC 4246 = 5250 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 174) = 5250
  rw [ladder_pc 174 (by decide)]
  rfl

@[simp] theorem pc4247 : Artifact.submissionArtifact.instructionPC 4247 = 5252 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 175) = 5252
  rw [ladder_pc 175 (by decide)]
  rfl

@[simp] theorem pc4248 : Artifact.submissionArtifact.instructionPC 4248 = 5253 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 176) = 5253
  rw [ladder_pc 176 (by decide)]
  rfl

@[simp] theorem pc4249 : Artifact.submissionArtifact.instructionPC 4249 = 5258 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 177) = 5258
  rw [ladder_pc 177 (by decide)]
  rfl

@[simp] theorem pc4250 : Artifact.submissionArtifact.instructionPC 4250 = 5260 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 178) = 5260
  rw [ladder_pc 178 (by decide)]
  rfl

@[simp] theorem pc4251 : Artifact.submissionArtifact.instructionPC 4251 = 5261 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 179) = 5261
  rw [ladder_pc 179 (by decide)]
  rfl

@[simp] theorem pc4252 : Artifact.submissionArtifact.instructionPC 4252 = 5266 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 180) = 5266
  rw [ladder_pc 180 (by decide)]
  rfl

@[simp] theorem pc4253 : Artifact.submissionArtifact.instructionPC 4253 = 5268 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 181) = 5268
  rw [ladder_pc 181 (by decide)]
  rfl

@[simp] theorem pc4254 : Artifact.submissionArtifact.instructionPC 4254 = 5269 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 182) = 5269
  rw [ladder_pc 182 (by decide)]
  rfl

@[simp] theorem pc4255 : Artifact.submissionArtifact.instructionPC 4255 = 5274 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 183) = 5274
  rw [ladder_pc 183 (by decide)]
  rfl

@[simp] theorem pc4256 : Artifact.submissionArtifact.instructionPC 4256 = 5276 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 184) = 5276
  rw [ladder_pc 184 (by decide)]
  rfl

@[simp] theorem pc4257 : Artifact.submissionArtifact.instructionPC 4257 = 5277 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 185) = 5277
  rw [ladder_pc 185 (by decide)]
  rfl

@[simp] theorem pc4258 : Artifact.submissionArtifact.instructionPC 4258 = 5278 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 186) = 5278
  rw [ladder_pc 186 (by decide)]
  rfl

@[simp] theorem pc4259 : Artifact.submissionArtifact.instructionPC 4259 = 5279 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 187) = 5279
  rw [ladder_pc 187 (by decide)]
  rfl

@[simp] theorem pc4260 : Artifact.submissionArtifact.instructionPC 4260 = 5280 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 188) = 5280
  rw [ladder_pc 188 (by decide)]
  rfl

@[simp] theorem pc4261 : Artifact.submissionArtifact.instructionPC 4261 = 5281 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 189) = 5281
  rw [ladder_pc 189 (by decide)]
  rfl

@[simp] theorem pc4262 : Artifact.submissionArtifact.instructionPC 4262 = 5282 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 190) = 5282
  rw [ladder_pc 190 (by decide)]
  rfl

@[simp] theorem pc4263 : Artifact.submissionArtifact.instructionPC 4263 = 5283 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 191) = 5283
  rw [ladder_pc 191 (by decide)]
  rfl

@[simp] theorem pc4264 : Artifact.submissionArtifact.instructionPC 4264 = 5286 := by
  show Artifact.submissionArtifact.instructionPC (4072 + 192) = 5286
  rw [ladder_pc 192 (by decide)]
  rfl

/-! ## Paths -/

def laterPath : List Located :=
  [⟨4072, .op .JUMPDEST, (ladder_at 0 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4073, .op (.Dup ⟨2, by decide⟩), (ladder_at 1 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4074, .push ⟨2, by decide⟩ (UInt256.ofNat 464), (ladder_at 2 (by decide)).trans rfl, by decide⟩,
   ⟨4075, .op .JUMPI, (ladder_at 3 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩]

def prefixPath : List Located :=
  [⟨4072, .op .JUMPDEST, (ladder_at 0 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4073, .op (.Dup ⟨2, by decide⟩), (ladder_at 1 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4074, .push ⟨2, by decide⟩ (UInt256.ofNat 464), (ladder_at 2 (by decide)).trans rfl, by decide⟩,
   ⟨4075, .op .JUMPI, (ladder_at 3 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4076, .push ⟨1, by decide⟩ (UInt256.ofNat 32), (ladder_at 4 (by decide)).trans rfl, by decide⟩,
   ⟨4077, .push ⟨2, by decide⟩ (UInt256.ofNat 262), (ladder_at 5 (by decide)).trans rfl, by decide⟩,
   ⟨4078, .push ⟨0, by decide⟩ (UInt256.ofNat 0), (ladder_at 6 (by decide)).trans rfl, by decide⟩]

def firstComparePath : List Located :=
  [⟨4080, .push ⟨0, by decide⟩ (UInt256.ofNat 0), (ladder_at 8 (by decide)).trans rfl, by decide⟩,
   ⟨4081, .op .MLOAD, (ladder_at 9 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4082, .push ⟨0, by decide⟩ (UInt256.ofNat 0), (ladder_at 10 (by decide)).trans rfl, by decide⟩,
   ⟨4083, .op .CALLDATALOAD, (ladder_at 11 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4084, .op .XOR, (ladder_at 12 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4085, .push ⟨2, by decide⟩ (UInt256.ofNat 464), (ladder_at 13 (by decide)).trans rfl, by decide⟩,
   ⟨4086, .op .JUMPI, (ladder_at 14 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩]

def setupPath : List Located :=
  [⟨4087, .push ⟨1, by decide⟩ (UInt256.ofNat 255), (ladder_at 15 (by decide)).trans rfl, by decide⟩,
   ⟨4088, .push ⟨0, by decide⟩ (UInt256.ofNat 0), (ladder_at 16 (by decide)).trans rfl, by decide⟩,
   ⟨4089, .op .NOT, (ladder_at 17 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4090, .op .DIV, (ladder_at 18 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4091, .push ⟨1, by decide⟩ (UInt256.ofNat 127), (ladder_at 19 (by decide)).trans rfl, by decide⟩,
   ⟨4092, .op .MUL, (ladder_at 20 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4093, .op (.Dup ⟨0, by decide⟩), (ladder_at 21 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4094, .op .NOT, (ladder_at 22 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4095, .op (.Dup ⟨0, by decide⟩), (ladder_at 23 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4096, .push ⟨1, by decide⟩ (UInt256.ofNat 2), (ladder_at 24 (by decide)).trans rfl, by decide⟩,
   ⟨4097, .op .SHR, (ladder_at 25 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4098, .push ⟨0, by decide⟩ (UInt256.ofNat 0), (ladder_at 26 (by decide)).trans rfl, by decide⟩,
   ⟨4099, .op .MLOAD, (ladder_at 27 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩]

def rung1Path : List Located :=
  [⟨4100, .op (.Dup ⟨0, by decide⟩), (ladder_at 28 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4101, .op (.Dup ⟨4, by decide⟩), (ladder_at 29 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4102, .op .AND, (ladder_at 30 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4103, .op (.Dup ⟨2, by decide⟩), (ladder_at 31 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4104, .op .ADD, (ladder_at 32 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4105, .op (.Swap ⟨0, by decide⟩), (ladder_at 33 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4106, .op (.Dup ⟨3, by decide⟩), (ladder_at 34 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4107, .op .AND, (ladder_at 35 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4108, .op .XOR, (ladder_at 36 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4109, .op (.Dup ⟨2, by decide⟩), (ladder_at 37 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4110, .op .XOR, (ladder_at 38 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4111, .op (.Dup ⟨0, by decide⟩), (ladder_at 39 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4112, .push ⟨1, by decide⟩ (UInt256.ofNat 32), (ladder_at 40 (by decide)).trans rfl, by decide⟩,
   ⟨4113, .op .CALLDATALOAD, (ladder_at 41 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4114, .op .XOR, (ladder_at 42 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4115, .push ⟨2, by decide⟩ (UInt256.ofNat 5278), (ladder_at 43 (by decide)).trans rfl, by decide⟩,
   ⟨4116, .op .JUMPI, (ladder_at 44 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩]

def rung2Path : List Located :=
  [⟨4117, .op (.Dup ⟨0, by decide⟩), (ladder_at 45 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4118, .op (.Dup ⟨4, by decide⟩), (ladder_at 46 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4119, .op .AND, (ladder_at 47 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4120, .op (.Dup ⟨2, by decide⟩), (ladder_at 48 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4121, .op .ADD, (ladder_at 49 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4122, .op (.Swap ⟨0, by decide⟩), (ladder_at 50 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4123, .op (.Dup ⟨3, by decide⟩), (ladder_at 51 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4124, .op .AND, (ladder_at 52 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4125, .op .XOR, (ladder_at 53 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4126, .op (.Dup ⟨2, by decide⟩), (ladder_at 54 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4127, .op .XOR, (ladder_at 55 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4128, .op (.Dup ⟨0, by decide⟩), (ladder_at 56 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4129, .push ⟨1, by decide⟩ (UInt256.ofNat 64), (ladder_at 57 (by decide)).trans rfl, by decide⟩,
   ⟨4130, .op .CALLDATALOAD, (ladder_at 58 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4131, .op .XOR, (ladder_at 59 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4132, .push ⟨2, by decide⟩ (UInt256.ofNat 5231), (ladder_at 60 (by decide)).trans rfl, by decide⟩,
   ⟨4133, .op .JUMPI, (ladder_at 61 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩]

def rung3Path : List Located :=
  [⟨4134, .op (.Dup ⟨0, by decide⟩), (ladder_at 62 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4135, .op (.Dup ⟨4, by decide⟩), (ladder_at 63 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4136, .op .AND, (ladder_at 64 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4137, .op (.Dup ⟨2, by decide⟩), (ladder_at 65 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4138, .op .ADD, (ladder_at 66 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4139, .op (.Swap ⟨0, by decide⟩), (ladder_at 67 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4140, .op (.Dup ⟨3, by decide⟩), (ladder_at 68 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4141, .op .AND, (ladder_at 69 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4142, .op .XOR, (ladder_at 70 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4143, .op (.Dup ⟨2, by decide⟩), (ladder_at 71 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4144, .op .XOR, (ladder_at 72 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4145, .op (.Dup ⟨0, by decide⟩), (ladder_at 73 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4146, .push ⟨1, by decide⟩ (UInt256.ofNat 96), (ladder_at 74 (by decide)).trans rfl, by decide⟩,
   ⟨4147, .op .CALLDATALOAD, (ladder_at 75 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4148, .op .XOR, (ladder_at 76 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4149, .push ⟨2, by decide⟩ (UInt256.ofNat 5231), (ladder_at 77 (by decide)).trans rfl, by decide⟩,
   ⟨4150, .op .JUMPI, (ladder_at 78 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩]

def rung4Path : List Located :=
  [⟨4151, .op (.Dup ⟨0, by decide⟩), (ladder_at 79 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4152, .op (.Dup ⟨4, by decide⟩), (ladder_at 80 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4153, .op .AND, (ladder_at 81 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4154, .op (.Dup ⟨2, by decide⟩), (ladder_at 82 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4155, .op .ADD, (ladder_at 83 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4156, .op (.Swap ⟨0, by decide⟩), (ladder_at 84 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4157, .op (.Dup ⟨3, by decide⟩), (ladder_at 85 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4158, .op .AND, (ladder_at 86 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4159, .op .XOR, (ladder_at 87 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4160, .op (.Dup ⟨2, by decide⟩), (ladder_at 88 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4161, .op .XOR, (ladder_at 89 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4162, .op (.Dup ⟨0, by decide⟩), (ladder_at 90 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4163, .push ⟨1, by decide⟩ (UInt256.ofNat 128), (ladder_at 91 (by decide)).trans rfl, by decide⟩,
   ⟨4164, .op .CALLDATALOAD, (ladder_at 92 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4165, .op .XOR, (ladder_at 93 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4166, .push ⟨2, by decide⟩ (UInt256.ofNat 5179), (ladder_at 94 (by decide)).trans rfl, by decide⟩,
   ⟨4167, .op .JUMPI, (ladder_at 95 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩]

def rung5Path : List Located :=
  [⟨4168, .op (.Dup ⟨0, by decide⟩), (ladder_at 96 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4169, .op (.Dup ⟨4, by decide⟩), (ladder_at 97 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4170, .op .AND, (ladder_at 98 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4171, .op (.Dup ⟨2, by decide⟩), (ladder_at 99 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4172, .op .ADD, (ladder_at 100 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4173, .op (.Swap ⟨0, by decide⟩), (ladder_at 101 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4174, .op (.Dup ⟨3, by decide⟩), (ladder_at 102 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4175, .op .AND, (ladder_at 103 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4176, .op .XOR, (ladder_at 104 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4177, .op (.Dup ⟨2, by decide⟩), (ladder_at 105 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4178, .op .XOR, (ladder_at 106 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4179, .op (.Dup ⟨0, by decide⟩), (ladder_at 107 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4180, .push ⟨1, by decide⟩ (UInt256.ofNat 160), (ladder_at 108 (by decide)).trans rfl, by decide⟩,
   ⟨4181, .op .CALLDATALOAD, (ladder_at 109 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4182, .op .XOR, (ladder_at 110 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4183, .push ⟨2, by decide⟩ (UInt256.ofNat 5179), (ladder_at 111 (by decide)).trans rfl, by decide⟩,
   ⟨4184, .op .JUMPI, (ladder_at 112 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩]

def hit3Path : List Located :=
  [⟨4185, .op .POP, (ladder_at 113 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4186, .op .POP, (ladder_at 114 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4187, .op .POP, (ladder_at 115 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4188, .op .POP, (ladder_at 116 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4189, .op .POP, (ladder_at 117 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4190, .op (.Swap ⟨0, by decide⟩), (ladder_at 118 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4191, .op .POP, (ladder_at 119 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4192, .push ⟨1, by decide⟩ (UInt256.ofNat 128), (ladder_at 120 (by decide)).trans rfl, by decide⟩,
   ⟨4193, .op (.Swap ⟨0, by decide⟩), (ladder_at 121 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4194, .push ⟨4, by decide⟩ (UInt256.ofNat 1393315003), (ladder_at 122 (by decide)).trans rfl, by decide⟩,
   ⟨4195, .push ⟨1, by decide⟩ (UInt256.ofNat 32), (ladder_at 123 (by decide)).trans rfl, by decide⟩,
   ⟨4196, .op .MSTORE, (ladder_at 124 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4197, .push ⟨4, by decide⟩ (UInt256.ofNat 695251451), (ladder_at 125 (by decide)).trans rfl, by decide⟩,
   ⟨4198, .push ⟨1, by decide⟩ (UInt256.ofNat 64), (ladder_at 126 (by decide)).trans rfl, by decide⟩,
   ⟨4199, .op .MSTORE, (ladder_at 127 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4200, .push ⟨4, by decide⟩ (UInt256.ofNat 358732556), (ladder_at 128 (by decide)).trans rfl, by decide⟩,
   ⟨4201, .push ⟨1, by decide⟩ (UInt256.ofNat 96), (ladder_at 129 (by decide)).trans rfl, by decide⟩,
   ⟨4202, .op .MSTORE, (ladder_at 130 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4203, .push ⟨4, by decide⟩ (UInt256.ofNat 928826907), (ladder_at 131 (by decide)).trans rfl, by decide⟩,
   ⟨4204, .push ⟨1, by decide⟩ (UInt256.ofNat 128), (ladder_at 132 (by decide)).trans rfl, by decide⟩,
   ⟨4205, .op .MSTORE, (ladder_at 133 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4206, .push ⟨4, by decide⟩ (UInt256.ofNat 3850323193), (ladder_at 134 (by decide)).trans rfl, by decide⟩,
   ⟨4207, .push ⟨1, by decide⟩ (UInt256.ofNat 160), (ladder_at 135 (by decide)).trans rfl, by decide⟩,
   ⟨4208, .op .MSTORE, (ladder_at 136 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4209, .op .JUMP, (ladder_at 137 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩]

def hit2Path : List Located :=
  [⟨4210, .op .JUMPDEST, (ladder_at 138 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4211, .op .POP, (ladder_at 139 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4212, .op .POP, (ladder_at 140 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4213, .op .POP, (ladder_at 141 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4214, .op .POP, (ladder_at 142 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4215, .op .POP, (ladder_at 143 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4216, .op (.Swap ⟨0, by decide⟩), (ladder_at 144 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4217, .op .POP, (ladder_at 145 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4218, .push ⟨1, by decide⟩ (UInt256.ofNat 64), (ladder_at 146 (by decide)).trans rfl, by decide⟩,
   ⟨4219, .op (.Swap ⟨0, by decide⟩), (ladder_at 147 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4220, .push ⟨4, by decide⟩ (UInt256.ofNat 2807398299), (ladder_at 148 (by decide)).trans rfl, by decide⟩,
   ⟨4221, .push ⟨1, by decide⟩ (UInt256.ofNat 32), (ladder_at 149 (by decide)).trans rfl, by decide⟩,
   ⟨4222, .op .MSTORE, (ladder_at 150 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4223, .push ⟨4, by decide⟩ (UInt256.ofNat 514068704), (ladder_at 151 (by decide)).trans rfl, by decide⟩,
   ⟨4224, .push ⟨1, by decide⟩ (UInt256.ofNat 64), (ladder_at 152 (by decide)).trans rfl, by decide⟩,
   ⟨4225, .op .MSTORE, (ladder_at 153 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4226, .push ⟨4, by decide⟩ (UInt256.ofNat 3681030016), (ladder_at 154 (by decide)).trans rfl, by decide⟩,
   ⟨4227, .push ⟨1, by decide⟩ (UInt256.ofNat 96), (ladder_at 155 (by decide)).trans rfl, by decide⟩,
   ⟨4228, .op .MSTORE, (ladder_at 156 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4229, .push ⟨4, by decide⟩ (UInt256.ofNat 3354522469), (ladder_at 157 (by decide)).trans rfl, by decide⟩,
   ⟨4230, .push ⟨1, by decide⟩ (UInt256.ofNat 128), (ladder_at 158 (by decide)).trans rfl, by decide⟩,
   ⟨4231, .op .MSTORE, (ladder_at 159 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4232, .push ⟨4, by decide⟩ (UInt256.ofNat 2543018249), (ladder_at 160 (by decide)).trans rfl, by decide⟩,
   ⟨4233, .push ⟨1, by decide⟩ (UInt256.ofNat 160), (ladder_at 161 (by decide)).trans rfl, by decide⟩,
   ⟨4234, .op .MSTORE, (ladder_at 162 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4235, .op .JUMP, (ladder_at 163 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩]

def hit1Path : List Located :=
  [⟨4236, .op .JUMPDEST, (ladder_at 164 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4237, .op .POP, (ladder_at 165 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4238, .op .POP, (ladder_at 166 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4239, .op .POP, (ladder_at 167 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4240, .op .POP, (ladder_at 168 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4241, .op .POP, (ladder_at 169 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4242, .push ⟨4, by decide⟩ (UInt256.ofNat 1080717082), (ladder_at 170 (by decide)).trans rfl, by decide⟩,
   ⟨4243, .push ⟨1, by decide⟩ (UInt256.ofNat 32), (ladder_at 171 (by decide)).trans rfl, by decide⟩,
   ⟨4244, .op .MSTORE, (ladder_at 172 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4245, .push ⟨4, by decide⟩ (UInt256.ofNat 2391128076), (ladder_at 173 (by decide)).trans rfl, by decide⟩,
   ⟨4246, .push ⟨1, by decide⟩ (UInt256.ofNat 64), (ladder_at 174 (by decide)).trans rfl, by decide⟩,
   ⟨4247, .op .MSTORE, (ladder_at 175 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4248, .push ⟨4, by decide⟩ (UInt256.ofNat 621343384), (ladder_at 176 (by decide)).trans rfl, by decide⟩,
   ⟨4249, .push ⟨1, by decide⟩ (UInt256.ofNat 96), (ladder_at 177 (by decide)).trans rfl, by decide⟩,
   ⟨4250, .op .MSTORE, (ladder_at 178 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4251, .push ⟨4, by decide⟩ (UInt256.ofNat 220066081), (ladder_at 179 (by decide)).trans rfl, by decide⟩,
   ⟨4252, .push ⟨1, by decide⟩ (UInt256.ofNat 128), (ladder_at 180 (by decide)).trans rfl, by decide⟩,
   ⟨4253, .op .MSTORE, (ladder_at 181 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4254, .push ⟨4, by decide⟩ (UInt256.ofNat 1007308478), (ladder_at 182 (by decide)).trans rfl, by decide⟩,
   ⟨4255, .push ⟨1, by decide⟩ (UInt256.ofNat 160), (ladder_at 183 (by decide)).trans rfl, by decide⟩,
   ⟨4256, .op .MSTORE, (ladder_at 184 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4257, .op .JUMP, (ladder_at 185 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩]

def bailPath : List Located :=
  [⟨4258, .op .JUMPDEST, (ladder_at 186 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4259, .op .POP, (ladder_at 187 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4260, .op .POP, (ladder_at 188 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4261, .op .POP, (ladder_at 189 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4262, .op .POP, (ladder_at 190 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4263, .push ⟨2, by decide⟩ (UInt256.ofNat 464), (ladder_at 191 (by decide)).trans rfl, by decide⟩,
   ⟨4264, .op .JUMP, (ladder_at 192 (by decide)).trans rfl, wfOp (by decide) trivial rfl⟩]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PrefixStatePaths
