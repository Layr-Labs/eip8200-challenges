import Batteries.Tactic.OpenPrivate
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactSegment
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedSwar
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedGuardSpec
import Challenge.EvmProof.Stepper
import Challenge.Ripemd160.ProofSupport.InitialState
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Artifact

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000

/-!
# States and paths of the scalar-SWAR patterned-1000 guard

The guard carries the expected word forward instead of storing thirty-two of
them, so the scan is one loop: `wordPath` derives the word and routes the four
straddling offsets to `straddlePath`, and `comparePath` folds the difference
into the accumulator and advances the offset and the scalar.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open PatternedInputData PatternedDigest PatternedGuardSpec PatternedSwar


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
  from Challenge.Ripemd160.Submission.Proofs.Bytecode.Artifact

private def scanPrefix : List YulEvmCompiler.Instr :=
  []

private def scanBefore : List YulEvmCompiler.Instr :=
  scanPrefix ++ submissionInstructionsChunk0.take 53

private def scanSuffix : List YulEvmCompiler.Instr :=
  submissionInstructionsChunk0.drop 53 ++ submissionInstructionsChunk1 ++ submissionInstructionsChunk2 ++ submissionInstructionsChunk3 ++ submissionInstructionsChunk4 ++ submissionInstructionsChunk5 ++ submissionInstructionsChunk6 ++ submissionInstructionsChunk7 ++ submissionInstructionsChunk8 ++ submissionInstructionsChunk9 ++ submissionInstructionsChunk10 ++ submissionInstructionsChunk11 ++ submissionInstructionsChunk12 ++ submissionInstructionsChunk13 ++ submissionInstructionsChunk14 ++ submissionInstructionsChunk15 ++ submissionInstructionsChunk16 ++ submissionInstructionsChunk17 ++ submissionInstructionsChunk18 ++ submissionInstructionsChunk19 ++ submissionInstructionsChunk20

private theorem scanBefore_length : scanBefore.length = 53 := by
  simp [scanBefore, scanPrefix]

private theorem scanSuffix_length : scanSuffix.length = 4146 := by
  simp [scanSuffix]

private theorem artifact_scan_split :
    Artifact.submissionArtifact.instructions = scanBefore ++ scanSuffix ++ [] := by
  change Artifact.submissionInstructions = _
  have hprefix : Artifact.submissionInstructions =
      scanPrefix ++
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
    submissionInstructionsChunk20 := by
    simp only [Artifact.submissionInstructions, scanPrefix, List.append_assoc, List.nil_append]
  have hchunk : submissionInstructionsChunk0 =
      submissionInstructionsChunk0.take 53 ++ submissionInstructionsChunk0.drop 53 := by
    exact (List.take_append_drop 53 submissionInstructionsChunk0).symm
  rw [hprefix]
  conv_lhs => rw [hchunk]
  simp only [scanBefore, scanSuffix, List.append_assoc, List.append_nil]

private theorem scanBefore_pc :
    (YulEvmCompiler.assembleBytes scanBefore).length = 70 := by rfl

private theorem artifact_instruction_projection :
    Artifact.submissionArtifact.instructions = Artifact.submissionInstructions := by rfl

private theorem scan_instruction_at (index : Nat)
    (hlo : 53 ≤ index) (hhi : index < 4167) :
    Artifact.submissionInstructions[index]? = scanSuffix[index - 53]? := by
  have hi : index - 53 < scanSuffix.length := by
    rw [scanSuffix_length]
    omega
  have h := ArtifactSegment.getElem?_segment Artifact.submissionArtifact
    scanBefore scanSuffix [] artifact_scan_split (index - 53) hi
  simpa only [artifact_instruction_projection, scanBefore_length,
    Nat.add_sub_of_le hlo] using h

private theorem scan_instruction_pc (index : Nat)
    (hlo : 53 ≤ index) (hhi : index ≤ 4167) :
    Artifact.submissionArtifact.instructionPC index =
      70 + (YulEvmCompiler.assembleBytes (scanSuffix.take (index - 53))).length := by
  have hi : index - 53 ≤ scanSuffix.length := by
    rw [scanSuffix_length]
    omega
  have h := ArtifactSegment.instructionPC_segment_of_bounds Artifact.submissionArtifact
    scanBefore scanSuffix [] 53 70 artifact_scan_split scanBefore_length
    scanBefore_pc (index - 53) hi
  simpa only [Nat.add_sub_of_le hlo] using h

def wfOp {op : Operation}
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op)
    (hplain : YulEvmCompiler.plainOp op)
    (havailable : op.availableInFork .Osaka = true) :
    Challenge.EvmProof.Stepper.WellFormed .Osaka (.op op) :=
  ⟨hopcode, hplain, havailable⟩

abbrev Located := Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka

def opAt (index : Nat) (op : Operation)
    (hget : Artifact.submissionInstructions[index]? = some (.op op) := by
      first
      | rw [scan_instruction_at] <;> first | rfl | decide
      | rfl)
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op := by decide)
    (hplain : YulEvmCompiler.plainOp op := by trivial)
    (havailable : op.availableInFork .Osaka = true := by rfl) : Located :=
  ⟨index, .op op, hget, wfOp hopcode hplain havailable⟩

def pushAt (index : Nat) (width : Fin 33) (value : UInt256)
    (hget : Artifact.submissionInstructions[index]? = some (.push width value) := by
      first
      | rw [scan_instruction_at] <;> first | rfl | decide
      | rfl)
    (hwf : Challenge.EvmProof.Stepper.WellFormed .Osaka
      (.push width value) := by decide) : Located :=
  ⟨index, .push width value, hget, hwf⟩

abbrev run := Challenge.EvmProof.Stepper.runLocatedBlock
  (artifact := Artifact.submissionArtifact) (fork := .Osaka)

/-- Push the five constants and start the scan. -/
def setupPath : List Located :=
  [pushAt 63 1 255,
   pushAt 64 0 0,
   opAt 65 .NOT,
   opAt 66 .DIV,
   pushAt 67 32 3244493450063667868678674439968361782956185527883176199882357678282131398018,
   opAt 68 (.Dup ⟨1, by decide⟩),
   pushAt 69 1 7,
   opAt 70 .SHL,
   opAt 71 (.Dup ⟨0, by decide⟩),
   opAt 72 .NOT,
   opAt 73 (.Swap ⟨0, by decide⟩),
   opAt 74 (.Swap ⟨2, by decide⟩),
   opAt 75 (.Dup ⟨2, by decide⟩),
   opAt 76 (.Dup ⟨2, by decide⟩),
   opAt 77 .AND,
   pushAt 78 0 0,
   pushAt 79 0 0,
   pushAt 80 0 0]

/-- Derive the expected word and test for a straddler. -/
def wordPath : List Located :=
  [opAt 81 .JUMPDEST, opAt 82 (.Dup ⟨0, by decide⟩),
   opAt 83 (.Dup ⟨5, by decide⟩), opAt 84 .MUL,
   opAt 85 (.Dup ⟨0, by decide⟩), opAt 86 (.Dup ⟨7, by decide⟩),
   opAt 87 .AND, opAt 88 (.Dup ⟨5, by decide⟩), opAt 89 .ADD,
   opAt 90 (.Dup ⟨1, by decide⟩), opAt 91 (.Dup ⟨9, by decide⟩),
   opAt 92 .XOR, opAt 93 (.Dup ⟨10, by decide⟩), opAt 94 .AND,
   opAt 95 .XOR, opAt 96 (.Dup ⟨3, by decide⟩), pushAt 97 1 255,
   opAt 98 .AND, pushAt 99 1 224, opAt 100 .XOR, pushAt 101 1 216,
   opAt 102 .JUMPI]

/-- Fold one word into the accumulator and advance. -/
def comparePath : List Located :=
  [opAt 133 .JUMPDEST,
   opAt 134 (.Dup ⟨3, by decide⟩),
   opAt 135 .CALLDATALOAD,
   opAt 136 .XOR,
   pushAt 137 4 1073790976,
   opAt 138 (.Dup ⟨4, by decide⟩),
   opAt 139 .CALLDATASIZE,
   opAt 140 .SUB,
   opAt 141 .SHR,
   pushAt 142 1 255,
   opAt 143 .AND,
   opAt 144 .SHR,
   opAt 145 (.Dup ⟨4, by decide⟩),
   opAt 146 .OR,
   opAt 147 (.Swap ⟨3, by decide⟩),
   opAt 148 .POP,
   opAt 149 .POP,
   pushAt 150 1 160,
   opAt 151 .ADD,
   pushAt 152 1 255,
   opAt 153 .AND,
   opAt 154 (.Swap ⟨0, by decide⟩),
   pushAt 155 1 32,
   opAt 156 .ADD,
   opAt 157 (.Swap ⟨0, by decide⟩),
   opAt 158 .CALLDATASIZE,
   opAt 159 (.Dup ⟨2, by decide⟩),
   opAt 160 .LT,
   pushAt 161 1 155,
   opAt 162 .JUMPI,
   opAt 163 (.Dup ⟨2, by decide⟩)]

/-- The padded tail word, the cleanup and the miss test. -/
def tailPath : List Located :=
  [opAt 190 .JUMPDEST, opAt 192 (.Swap ⟨2, by decide⟩), opAt 193 .POP,
   opAt 194 (.Swap ⟨1, by decide⟩), opAt 195 (.Swap ⟨6, by decide⟩), opAt 196 .POP,
   opAt 197 .POP, opAt 198 .POP, opAt 199 .POP, opAt 200 .POP, opAt 201 .POP, opAt 202 .POP,
   pushAt 203 2 368, opAt 204 .JUMPI]

/-- Store and return the stored digest. -/
def returnPath : List Located :=
  [opAt 171 .CALLDATASIZE, pushAt 173 2 376, opAt 174 .EQ,
   pushAt 175 20 644824770394507154413287103057882351908521126009, opAt 176 .MUL,
   pushAt 183 20 766350606435067737561421097975693824639675460820, opAt 184 .XOR,
   pushAt 185 0 0, opAt 186 .MSTORE, opAt 187 .MSIZE, pushAt 188 0 0,
   opAt 189 .RETURN]

/-- Shift the correction constant out of `M`. -/
def straddleCorrPath : List Located :=
  [opAt 103 .JUMPDEST, opAt 104 (.Dup ⟨6, by decide⟩),
   opAt 105 (.Dup ⟨4, by decide⟩), pushAt 106 1 8, opAt 107 .SHR,
   pushAt 108 1 5, opAt 109 .MUL, pushAt 110 1 27, opAt 111 .SUB,
   pushAt 112 1 3, opAt 113 .SHL, opAt 114 .SHR, pushAt 115 1 11,
   opAt 116 .MUL]

/-- Apply the correction to the expected word. -/
def straddleAddPath : List Located :=
  [opAt 117 (.Dup ⟨1, by decide⟩), opAt 118 (.Dup ⟨9, by decide⟩),
   opAt 119 .AND, opAt 120 (.Dup ⟨1, by decide⟩), opAt 121 .ADD,
   opAt 122 (.Dup ⟨2, by decide⟩), opAt 123 (.Dup ⟨12, by decide⟩),
   opAt 124 .AND, opAt 125 .XOR, opAt 126 (.Swap ⟨1, by decide⟩),
   opAt 127 .POP, opAt 128 .POP]

/-- Bump the scalar and rejoin the scan. -/
def straddleBackPath : List Located :=
  [opAt 129 (.Swap ⟨1, by decide⟩), pushAt 130 1 11, opAt 131 .ADD,
   opAt 132 (.Swap ⟨1, by decide⟩)]


@[simp] theorem pc2903 : Artifact.submissionArtifact.instructionPC 63 = 0x67 :=
  by rw [scan_instruction_pc 63 (by decide) (by decide)]; rfl
@[simp] theorem pc2904 : Artifact.submissionArtifact.instructionPC 63 = 0x67 :=
  by rw [scan_instruction_pc 63 (by decide) (by decide)]; rfl
@[simp] theorem pc2905 : Artifact.submissionArtifact.instructionPC 67 = 0x6c :=
  by rw [scan_instruction_pc 67 (by decide) (by decide)]; rfl
@[simp] theorem pc2906 : Artifact.submissionArtifact.instructionPC 72 = 0x92 :=
  by rw [scan_instruction_pc 72 (by decide) (by decide)]; rfl
@[simp] theorem pc2907 : Artifact.submissionArtifact.instructionPC 74 = 0x94 :=
  by rw [scan_instruction_pc 74 (by decide) (by decide)]; rfl
@[simp] theorem pc2908 : Artifact.submissionArtifact.instructionPC 75 = 0x95 :=
  by rw [scan_instruction_pc 75 (by decide) (by decide)]; rfl
@[simp] theorem pc2909 : Artifact.submissionArtifact.instructionPC 76 = 0x96 :=
  by rw [scan_instruction_pc 76 (by decide) (by decide)]; rfl
@[simp] theorem pc2910 : Artifact.submissionArtifact.instructionPC 77 = 0x97 :=
  by rw [scan_instruction_pc 77 (by decide) (by decide)]; rfl
@[simp] theorem pc2911 : Artifact.submissionArtifact.instructionPC 78 = 0x98 :=
  by rw [scan_instruction_pc 78 (by decide) (by decide)]; rfl
@[simp] theorem pc2912 : Artifact.submissionArtifact.instructionPC 79 = 0x99 :=
  by rw [scan_instruction_pc 79 (by decide) (by decide)]; rfl
@[simp] theorem pc2913 : Artifact.submissionArtifact.instructionPC 80 = 0x9a :=
  by rw [scan_instruction_pc 80 (by decide) (by decide)]; rfl
@[simp] theorem pc2914 : Artifact.submissionArtifact.instructionPC 81 = 0x9b :=
  by rw [scan_instruction_pc 81 (by decide) (by decide)]; rfl
@[simp] theorem pc2915 : Artifact.submissionArtifact.instructionPC 82 = 0x9c :=
  by rw [scan_instruction_pc 82 (by decide) (by decide)]; rfl
@[simp] theorem pc2916 : Artifact.submissionArtifact.instructionPC 83 = 0x9d :=
  by rw [scan_instruction_pc 83 (by decide) (by decide)]; rfl
@[simp] theorem pc2917 : Artifact.submissionArtifact.instructionPC 84 = 0x9e :=
  by rw [scan_instruction_pc 84 (by decide) (by decide)]; rfl
@[simp] theorem pc2918 : Artifact.submissionArtifact.instructionPC 85 = 0x9f :=
  by rw [scan_instruction_pc 85 (by decide) (by decide)]; rfl
@[simp] theorem pc2919 : Artifact.submissionArtifact.instructionPC 86 = 0xa0 :=
  by rw [scan_instruction_pc 86 (by decide) (by decide)]; rfl
@[simp] theorem pc2920 : Artifact.submissionArtifact.instructionPC 87 = 0xa1 :=
  by rw [scan_instruction_pc 87 (by decide) (by decide)]; rfl
@[simp] theorem pc2921 : Artifact.submissionArtifact.instructionPC 88 = 0xa2 :=
  by rw [scan_instruction_pc 88 (by decide) (by decide)]; rfl
@[simp] theorem pc2922 : Artifact.submissionArtifact.instructionPC 89 = 0xa3 :=
  by rw [scan_instruction_pc 89 (by decide) (by decide)]; rfl
@[simp] theorem pc2923 : Artifact.submissionArtifact.instructionPC 90 = 0xa4 :=
  by rw [scan_instruction_pc 90 (by decide) (by decide)]; rfl
@[simp] theorem pc2924 : Artifact.submissionArtifact.instructionPC 91 = 0xa5 :=
  by rw [scan_instruction_pc 91 (by decide) (by decide)]; rfl
@[simp] theorem pc2925 : Artifact.submissionArtifact.instructionPC 92 = 0xa6 :=
  by rw [scan_instruction_pc 92 (by decide) (by decide)]; rfl
@[simp] theorem pc2926 : Artifact.submissionArtifact.instructionPC 93 = 0xa7 :=
  by rw [scan_instruction_pc 93 (by decide) (by decide)]; rfl
@[simp] theorem pc2927 : Artifact.submissionArtifact.instructionPC 94 = 0xa8 :=
  by rw [scan_instruction_pc 94 (by decide) (by decide)]; rfl
@[simp] theorem pc2928 : Artifact.submissionArtifact.instructionPC 95 = 0xa9 :=
  by rw [scan_instruction_pc 95 (by decide) (by decide)]; rfl
@[simp] theorem pc2929 : Artifact.submissionArtifact.instructionPC 96 = 0xaa :=
  by rw [scan_instruction_pc 96 (by decide) (by decide)]; rfl
@[simp] theorem pc2930 : Artifact.submissionArtifact.instructionPC 97 = 0xab :=
  by rw [scan_instruction_pc 97 (by decide) (by decide)]; rfl
@[simp] theorem pc2931 : Artifact.submissionArtifact.instructionPC 98 = 0xad :=
  by rw [scan_instruction_pc 98 (by decide) (by decide)]; rfl
@[simp] theorem pc2932 : Artifact.submissionArtifact.instructionPC 99 = 0xae :=
  by rw [scan_instruction_pc 99 (by decide) (by decide)]; rfl
@[simp] theorem pc2933 : Artifact.submissionArtifact.instructionPC 100 = 0xb0 :=
  by rw [scan_instruction_pc 100 (by decide) (by decide)]; rfl
@[simp] theorem pc2934 : Artifact.submissionArtifact.instructionPC 101 = 0xb1 :=
  by rw [scan_instruction_pc 101 (by decide) (by decide)]; rfl
@[simp] theorem pc2935 : Artifact.submissionArtifact.instructionPC 102 = 0xb3 :=
  by rw [scan_instruction_pc 102 (by decide) (by decide)]; rfl
@[simp] theorem pc2936 : Artifact.submissionArtifact.instructionPC 133 = 0xd8 :=
  by rw [scan_instruction_pc 133 (by decide) (by decide)]; rfl
@[simp] theorem pc2937 : Artifact.submissionArtifact.instructionPC 134 = 0xd9 :=
  by rw [scan_instruction_pc 134 (by decide) (by decide)]; rfl
@[simp] theorem pc2938 : Artifact.submissionArtifact.instructionPC 135 = 0xda :=
  by rw [scan_instruction_pc 135 (by decide) (by decide)]; rfl
@[simp] theorem pc2939 : Artifact.submissionArtifact.instructionPC 136 = 0xdb :=
  by rw [scan_instruction_pc 136 (by decide) (by decide)]; rfl
@[simp] theorem pc2940 : Artifact.submissionArtifact.instructionPC 145 = 0xe9 :=
  by rw [scan_instruction_pc 145 (by decide) (by decide)]; rfl
@[simp] theorem pc2941 : Artifact.submissionArtifact.instructionPC 146 = 0xea :=
  by rw [scan_instruction_pc 146 (by decide) (by decide)]; rfl
@[simp] theorem pc2942 : Artifact.submissionArtifact.instructionPC 147 = 0xeb :=
  by rw [scan_instruction_pc 147 (by decide) (by decide)]; rfl
@[simp] theorem pc2943 : Artifact.submissionArtifact.instructionPC 148 = 0xec :=
  by rw [scan_instruction_pc 148 (by decide) (by decide)]; rfl
@[simp] theorem pc2944 : Artifact.submissionArtifact.instructionPC 149 = 0xed :=
  by rw [scan_instruction_pc 149 (by decide) (by decide)]; rfl
@[simp] theorem pc2945 : Artifact.submissionArtifact.instructionPC 150 = 0xee :=
  by rw [scan_instruction_pc 150 (by decide) (by decide)]; rfl
@[simp] theorem pc2946 : Artifact.submissionArtifact.instructionPC 150 = 0xee :=
  by rw [scan_instruction_pc 150 (by decide) (by decide)]; rfl
@[simp] theorem pc2947 : Artifact.submissionArtifact.instructionPC 151 = 0xf0 :=
  by rw [scan_instruction_pc 151 (by decide) (by decide)]; rfl
@[simp] theorem pc2948 : Artifact.submissionArtifact.instructionPC 152 = 0xf1 :=
  by rw [scan_instruction_pc 152 (by decide) (by decide)]; rfl
@[simp] theorem pc2949 : Artifact.submissionArtifact.instructionPC 153 = 0xf3 :=
  by rw [scan_instruction_pc 153 (by decide) (by decide)]; rfl
@[simp] theorem pc2950 : Artifact.submissionArtifact.instructionPC 154 = 0xf4 :=
  by rw [scan_instruction_pc 154 (by decide) (by decide)]; rfl
@[simp] theorem pc2951 : Artifact.submissionArtifact.instructionPC 154 = 0xf4 :=
  by rw [scan_instruction_pc 154 (by decide) (by decide)]; rfl
@[simp] theorem pc2952 : Artifact.submissionArtifact.instructionPC 154 = 0xf4 :=
  by rw [scan_instruction_pc 154 (by decide) (by decide)]; rfl
@[simp] theorem pc2953 : Artifact.submissionArtifact.instructionPC 155 = 0xf5 :=
  by rw [scan_instruction_pc 155 (by decide) (by decide)]; rfl
@[simp] theorem pc2954 : Artifact.submissionArtifact.instructionPC 156 = 0xf7 :=
  by rw [scan_instruction_pc 156 (by decide) (by decide)]; rfl
@[simp] theorem pc2955 : Artifact.submissionArtifact.instructionPC 157 = 0xf8 :=
  by rw [scan_instruction_pc 157 (by decide) (by decide)]; rfl
@[simp] theorem pc2956 : Artifact.submissionArtifact.instructionPC 150 = 0xee :=
  by rw [scan_instruction_pc 150 (by decide) (by decide)]; rfl
@[simp] theorem pc2957 : Artifact.submissionArtifact.instructionPC 150 = 0xee :=
  by rw [scan_instruction_pc 150 (by decide) (by decide)]; rfl
@[simp] theorem pc2958 : Artifact.submissionArtifact.instructionPC 151 = 0xf0 :=
  by rw [scan_instruction_pc 151 (by decide) (by decide)]; rfl
@[simp] theorem pc2959 : Artifact.submissionArtifact.instructionPC 152 = 0xf1 :=
  by rw [scan_instruction_pc 152 (by decide) (by decide)]; rfl
@[simp] theorem pc2960 : Artifact.submissionArtifact.instructionPC 153 = 0xf3 :=
  by rw [scan_instruction_pc 153 (by decide) (by decide)]; rfl
@[simp] theorem pc2961 : Artifact.submissionArtifact.instructionPC 154 = 0xf4 :=
  by rw [scan_instruction_pc 154 (by decide) (by decide)]; rfl
@[simp] theorem pc2962 : Artifact.submissionArtifact.instructionPC 155 = 0xf5 :=
  by rw [scan_instruction_pc 155 (by decide) (by decide)]; rfl
@[simp] theorem pc2963 : Artifact.submissionArtifact.instructionPC 156 = 0xf7 :=
  by rw [scan_instruction_pc 156 (by decide) (by decide)]; rfl
@[simp] theorem pc2964 : Artifact.submissionArtifact.instructionPC 157 = 0xf8 :=
  by rw [scan_instruction_pc 157 (by decide) (by decide)]; rfl
@[simp] theorem pc2965 : Artifact.submissionArtifact.instructionPC 158 = 0xf9 :=
  by rw [scan_instruction_pc 158 (by decide) (by decide)]; rfl
@[simp] theorem pc2966 : Artifact.submissionArtifact.instructionPC 159 = 0xfa :=
  by rw [scan_instruction_pc 159 (by decide) (by decide)]; rfl
@[simp] theorem pc2967 : Artifact.submissionArtifact.instructionPC 160 = 0xfb :=
  by rw [scan_instruction_pc 160 (by decide) (by decide)]; rfl
@[simp] theorem pc2968 : Artifact.submissionArtifact.instructionPC 161 = 0xfc :=
  by rw [scan_instruction_pc 161 (by decide) (by decide)]; rfl
@[simp] theorem pc2969 : Artifact.submissionArtifact.instructionPC 162 = 0xfe :=
  by rw [scan_instruction_pc 162 (by decide) (by decide)]; rfl
@[simp] theorem pc2969a : Artifact.submissionArtifact.instructionPC 190 = 0x15f :=
  by rw [scan_instruction_pc 190 (by decide) (by decide)]; rfl
@[simp] theorem pc2970 : Artifact.submissionArtifact.instructionPC 192 = 0x161 :=
  by rw [scan_instruction_pc 192 (by decide) (by decide)]; rfl
@[simp] theorem pc2971 : Artifact.submissionArtifact.instructionPC 193 = 0x162 :=
  by rw [scan_instruction_pc 193 (by decide) (by decide)]; rfl
@[simp] theorem pc2972 : Artifact.submissionArtifact.instructionPC 194 = 0x163 :=
  by rw [scan_instruction_pc 194 (by decide) (by decide)]; rfl
@[simp] theorem pc2973 : Artifact.submissionArtifact.instructionPC 195 = 0x164 :=
  by rw [scan_instruction_pc 195 (by decide) (by decide)]; rfl
@[simp] theorem pc2974 : Artifact.submissionArtifact.instructionPC 196 = 0x165 :=
  by rw [scan_instruction_pc 196 (by decide) (by decide)]; rfl
@[simp] theorem pc2975 : Artifact.submissionArtifact.instructionPC 197 = 0x166 :=
  by rw [scan_instruction_pc 197 (by decide) (by decide)]; rfl
@[simp] theorem pc2976 : Artifact.submissionArtifact.instructionPC 198 = 0x167 :=
  by rw [scan_instruction_pc 198 (by decide) (by decide)]; rfl
@[simp] theorem pc2977 : Artifact.submissionArtifact.instructionPC 199 = 0x168 :=
  by rw [scan_instruction_pc 199 (by decide) (by decide)]; rfl
@[simp] theorem pc2978 : Artifact.submissionArtifact.instructionPC 200 = 0x169 :=
  by rw [scan_instruction_pc 200 (by decide) (by decide)]; rfl
@[simp] theorem pc2979 : Artifact.submissionArtifact.instructionPC 201 = 0x16a :=
  by rw [scan_instruction_pc 201 (by decide) (by decide)]; rfl
@[simp] theorem pc2980 : Artifact.submissionArtifact.instructionPC 202 = 0x16b :=
  by rw [scan_instruction_pc 202 (by decide) (by decide)]; rfl
@[simp] theorem pc2981 : Artifact.submissionArtifact.instructionPC 203 = 0x16c :=
  by rw [scan_instruction_pc 203 (by decide) (by decide)]; rfl
@[simp] theorem pc2982 : Artifact.submissionArtifact.instructionPC 204 = 0x16f :=
  by rw [scan_instruction_pc 204 (by decide) (by decide)]; rfl
@[simp] theorem pc_ins249 : Artifact.submissionArtifact.instructionPC 171 = 0x10c :=
  by rw [scan_instruction_pc 171 (by decide) (by decide)]; rfl
@[simp] theorem pc_ins250 : Artifact.submissionArtifact.instructionPC 173 = 0x10e :=
  by rw [scan_instruction_pc 173 (by decide) (by decide)]; rfl
@[simp] theorem pc_ins251 : Artifact.submissionArtifact.instructionPC 174 = 0x111 :=
  by rw [scan_instruction_pc 174 (by decide) (by decide)]; rfl
@[simp] theorem pc_ins252 : Artifact.submissionArtifact.instructionPC 175 = 0x112 :=
  by rw [scan_instruction_pc 175 (by decide) (by decide)]; rfl
@[simp] theorem pc_ins253 : Artifact.submissionArtifact.instructionPC 176 = 0x127 :=
  by rw [scan_instruction_pc 176 (by decide) (by decide)]; rfl
@[simp] theorem pc_ins255 : Artifact.submissionArtifact.instructionPC 184 = 0x159 :=
  by rw [scan_instruction_pc 184 (by decide) (by decide)]; rfl
@[simp] theorem pc_ins217 : Artifact.submissionArtifact.instructionPC 158 = 0xf9 :=
  by rw [scan_instruction_pc 158 (by decide) (by decide)]; rfl
@[simp] theorem pc_ins218 : Artifact.submissionArtifact.instructionPC 159 = 0xfa :=
  by rw [scan_instruction_pc 159 (by decide) (by decide)]; rfl
@[simp] theorem pc_ins219 : Artifact.submissionArtifact.instructionPC 160 = 0xfb :=
  by rw [scan_instruction_pc 160 (by decide) (by decide)]; rfl
@[simp] theorem pc_ins220 : Artifact.submissionArtifact.instructionPC 161 = 0xfc :=
  by rw [scan_instruction_pc 161 (by decide) (by decide)]; rfl
@[simp] theorem pc_ins221 : Artifact.submissionArtifact.instructionPC 162 = 0xfe :=
  by rw [scan_instruction_pc 162 (by decide) (by decide)]; rfl
@[simp] theorem pc2983 : Artifact.submissionArtifact.instructionPC 183 = 0x144 :=
  by rw [scan_instruction_pc 183 (by decide) (by decide)]; rfl
@[simp] theorem pc2984 : Artifact.submissionArtifact.instructionPC 185 = 0x15a :=
  by rw [scan_instruction_pc 185 (by decide) (by decide)]; rfl
@[simp] theorem pc2985 : Artifact.submissionArtifact.instructionPC 186 = 0x15b :=
  by rw [scan_instruction_pc 186 (by decide) (by decide)]; rfl
@[simp] theorem pc2986 : Artifact.submissionArtifact.instructionPC 187 = 0x15c :=
  by rw [scan_instruction_pc 187 (by decide) (by decide)]; rfl
@[simp] theorem pc2987 : Artifact.submissionArtifact.instructionPC 188 = 0x15d :=
  by rw [scan_instruction_pc 188 (by decide) (by decide)]; rfl
@[simp] theorem pc2988 : Artifact.submissionArtifact.instructionPC 189 = 0x15e :=
  by rw [scan_instruction_pc 189 (by decide) (by decide)]; rfl
@[simp] theorem pc2989 : Artifact.submissionArtifact.instructionPC 103 = 0xb4 :=
  by rw [scan_instruction_pc 103 (by decide) (by decide)]; rfl
@[simp] theorem pc2990 : Artifact.submissionArtifact.instructionPC 104 = 0xb5 :=
  by rw [scan_instruction_pc 104 (by decide) (by decide)]; rfl
@[simp] theorem pc2991 : Artifact.submissionArtifact.instructionPC 105 = 0xb6 :=
  by rw [scan_instruction_pc 105 (by decide) (by decide)]; rfl
@[simp] theorem pc2992 : Artifact.submissionArtifact.instructionPC 106 = 0xb7 :=
  by rw [scan_instruction_pc 106 (by decide) (by decide)]; rfl
@[simp] theorem pc2993 : Artifact.submissionArtifact.instructionPC 107 = 0xb9 :=
  by rw [scan_instruction_pc 107 (by decide) (by decide)]; rfl
@[simp] theorem pc2994 : Artifact.submissionArtifact.instructionPC 108 = 0xba :=
  by rw [scan_instruction_pc 108 (by decide) (by decide)]; rfl
@[simp] theorem pc2995 : Artifact.submissionArtifact.instructionPC 109 = 0xbc :=
  by rw [scan_instruction_pc 109 (by decide) (by decide)]; rfl
@[simp] theorem pc2996 : Artifact.submissionArtifact.instructionPC 110 = 0xbd :=
  by rw [scan_instruction_pc 110 (by decide) (by decide)]; rfl
@[simp] theorem pc2997 : Artifact.submissionArtifact.instructionPC 111 = 0xbf :=
  by rw [scan_instruction_pc 111 (by decide) (by decide)]; rfl
@[simp] theorem pc2998 : Artifact.submissionArtifact.instructionPC 112 = 0xc0 :=
  by rw [scan_instruction_pc 112 (by decide) (by decide)]; rfl
@[simp] theorem pc2999 : Artifact.submissionArtifact.instructionPC 113 = 0xc2 :=
  by rw [scan_instruction_pc 113 (by decide) (by decide)]; rfl
@[simp] theorem pc3000 : Artifact.submissionArtifact.instructionPC 114 = 0xc3 :=
  by rw [scan_instruction_pc 114 (by decide) (by decide)]; rfl
@[simp] theorem pc3001 : Artifact.submissionArtifact.instructionPC 115 = 0xc4 :=
  by rw [scan_instruction_pc 115 (by decide) (by decide)]; rfl
@[simp] theorem pc3002 : Artifact.submissionArtifact.instructionPC 116 = 0xc6 :=
  by rw [scan_instruction_pc 116 (by decide) (by decide)]; rfl
@[simp] theorem pc3003 : Artifact.submissionArtifact.instructionPC 117 = 0xc7 :=
  by rw [scan_instruction_pc 117 (by decide) (by decide)]; rfl
@[simp] theorem pc3004 : Artifact.submissionArtifact.instructionPC 118 = 0xc8 :=
  by rw [scan_instruction_pc 118 (by decide) (by decide)]; rfl
@[simp] theorem pc3005 : Artifact.submissionArtifact.instructionPC 119 = 0xc9 :=
  by rw [scan_instruction_pc 119 (by decide) (by decide)]; rfl
@[simp] theorem pc3006 : Artifact.submissionArtifact.instructionPC 120 = 0xca :=
  by rw [scan_instruction_pc 120 (by decide) (by decide)]; rfl
@[simp] theorem pc3007 : Artifact.submissionArtifact.instructionPC 121 = 0xcb :=
  by rw [scan_instruction_pc 121 (by decide) (by decide)]; rfl
@[simp] theorem pc3008 : Artifact.submissionArtifact.instructionPC 122 = 0xcc :=
  by rw [scan_instruction_pc 122 (by decide) (by decide)]; rfl
@[simp] theorem pc3009 : Artifact.submissionArtifact.instructionPC 123 = 0xcd :=
  by rw [scan_instruction_pc 123 (by decide) (by decide)]; rfl
@[simp] theorem pc3010 : Artifact.submissionArtifact.instructionPC 124 = 0xce :=
  by rw [scan_instruction_pc 124 (by decide) (by decide)]; rfl
@[simp] theorem pc3011 : Artifact.submissionArtifact.instructionPC 125 = 0xcf :=
  by rw [scan_instruction_pc 125 (by decide) (by decide)]; rfl
@[simp] theorem pc3012 : Artifact.submissionArtifact.instructionPC 126 = 0xd0 :=
  by rw [scan_instruction_pc 126 (by decide) (by decide)]; rfl
@[simp] theorem pc3013 : Artifact.submissionArtifact.instructionPC 127 = 0xd1 :=
  by rw [scan_instruction_pc 127 (by decide) (by decide)]; rfl
@[simp] theorem pc3014 : Artifact.submissionArtifact.instructionPC 128 = 0xd2 :=
  by rw [scan_instruction_pc 128 (by decide) (by decide)]; rfl
@[simp] theorem pc3015 : Artifact.submissionArtifact.instructionPC 129 = 0xd3 :=
  by rw [scan_instruction_pc 129 (by decide) (by decide)]; rfl
@[simp] theorem pc3016 : Artifact.submissionArtifact.instructionPC 130 = 0xd4 :=
  by rw [scan_instruction_pc 130 (by decide) (by decide)]; rfl
@[simp] theorem pc3017 : Artifact.submissionArtifact.instructionPC 131 = 0xd6 :=
  by rw [scan_instruction_pc 131 (by decide) (by decide)]; rfl
@[simp] theorem pc3018 : Artifact.submissionArtifact.instructionPC 132 = 0xd7 :=
  by rw [scan_instruction_pc 132 (by decide) (by decide)]; rfl
@[simp] theorem pc3019 : Artifact.submissionArtifact.instructionPC 133 = 0xd8 :=
  by rw [scan_instruction_pc 133 (by decide) (by decide)]; rfl
#print axioms scan_instruction_at
#print axioms scan_instruction_pc
#print axioms setupPath
#print axioms wordPath
#print axioms comparePath
#print axioms tailPath
#print axioms returnPath
#print axioms straddleCorrPath
#print axioms straddleAddPath
#print axioms straddleBackPath
#print axioms pc2903

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan
