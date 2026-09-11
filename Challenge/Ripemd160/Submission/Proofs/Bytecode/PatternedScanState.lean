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
  scanPrefix ++ submissionInstructionsChunk0.take 51

private def scanSuffix : List YulEvmCompiler.Instr :=
  submissionInstructionsChunk0.drop 51 ++ submissionInstructionsChunk1 ++ submissionInstructionsChunk2 ++ submissionInstructionsChunk3 ++ submissionInstructionsChunk4 ++ submissionInstructionsChunk5 ++ submissionInstructionsChunk6 ++ submissionInstructionsChunk7 ++ submissionInstructionsChunk8 ++ submissionInstructionsChunk9 ++ submissionInstructionsChunk10 ++ submissionInstructionsChunk11 ++ submissionInstructionsChunk12 ++ submissionInstructionsChunk13 ++ submissionInstructionsChunk14 ++ submissionInstructionsChunk15 ++ submissionInstructionsChunk16 ++ submissionInstructionsChunk17 ++ submissionInstructionsChunk18 ++ submissionInstructionsChunk19 ++ submissionInstructionsChunk20

private theorem scanBefore_length : scanBefore.length = 51 := by
  simp [scanBefore, scanPrefix]

private theorem scanSuffix_length : scanSuffix.length = 4094 := by
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
      submissionInstructionsChunk0.take 51 ++ submissionInstructionsChunk0.drop 51 := by
    exact (List.take_append_drop 51 submissionInstructionsChunk0).symm
  rw [hprefix]
  conv_lhs => rw [hchunk]
  simp only [scanBefore, scanSuffix, List.append_assoc, List.append_nil]

private theorem scanBefore_pc :
    (YulEvmCompiler.assembleBytes scanBefore).length = 68 := by rfl

private theorem artifact_instruction_projection :
    Artifact.submissionArtifact.instructions = Artifact.submissionInstructions := by rfl

private theorem scan_instruction_at (index : Nat)
    (hlo : 51 ≤ index) (hhi : index < 4136) :
    Artifact.submissionInstructions[index]? = scanSuffix[index - 51]? := by
  have hi : index - 51 < scanSuffix.length := by
    rw [scanSuffix_length]
    omega
  have h := ArtifactSegment.getElem?_segment Artifact.submissionArtifact
    scanBefore scanSuffix [] artifact_scan_split (index - 51) hi
  simpa only [artifact_instruction_projection, scanBefore_length,
    Nat.add_sub_of_le hlo] using h

private theorem scan_instruction_pc (index : Nat)
    (hlo : 51 ≤ index) (hhi : index ≤ 4136) :
    Artifact.submissionArtifact.instructionPC index =
      68 + (YulEvmCompiler.assembleBytes (scanSuffix.take (index - 51))).length := by
  have hi : index - 51 ≤ scanSuffix.length := by
    rw [scanSuffix_length]
    omega
  have h := ArtifactSegment.instructionPC_segment_of_bounds Artifact.submissionArtifact
    scanBefore scanSuffix [] 51 68 artifact_scan_split scanBefore_length
    scanBefore_pc (index - 51) hi
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
  [pushAt 61 1 255,
   pushAt 62 0 0,
   opAt 63 .NOT,
   opAt 64 .DIV,
   pushAt 65 32 3244493450063667868678674439968361782956185527883176199882357678282131398018,
   opAt 66 (.Dup ⟨1, by decide⟩),
   pushAt 67 1 7,
   opAt 68 .SHL,
   opAt 69 (.Dup ⟨0, by decide⟩),
   opAt 70 .NOT,
   opAt 71 (.Swap ⟨0, by decide⟩),
   opAt 72 (.Swap ⟨2, by decide⟩),
   opAt 73 (.Dup ⟨2, by decide⟩),
   opAt 74 (.Dup ⟨2, by decide⟩),
   opAt 75 .AND,
   pushAt 76 0 0,
   pushAt 77 0 0,
   pushAt 78 0 0]

/-- Derive the expected word and test for a straddler. -/
def wordPath : List Located :=
  [opAt 79 .JUMPDEST, opAt 80 (.Dup ⟨0, by decide⟩),
   opAt 81 (.Dup ⟨5, by decide⟩), opAt 82 .MUL,
   opAt 83 (.Dup ⟨0, by decide⟩), opAt 84 (.Dup ⟨7, by decide⟩),
   opAt 85 .AND, opAt 86 (.Dup ⟨5, by decide⟩), opAt 87 .ADD,
   opAt 88 (.Dup ⟨1, by decide⟩), opAt 89 (.Dup ⟨9, by decide⟩),
   opAt 90 .XOR, opAt 91 (.Dup ⟨10, by decide⟩), opAt 92 .AND,
   opAt 93 .XOR, opAt 94 (.Dup ⟨3, by decide⟩), opAt 95 .NOT,
   pushAt 96 1 224, opAt 97 .AND, pushAt 98 1 207,
   opAt 99 .JUMPI]

/-- Fold one word into the accumulator and advance. -/
def comparePath : List Located :=
  [opAt 127 .JUMPDEST,
   opAt 128 (.Dup ⟨3, by decide⟩),
   opAt 129 .CALLDATALOAD,
   opAt 130 .XOR,
   pushAt 131 5 18253660656,
   opAt 132 (.Dup ⟨4, by decide⟩),
   opAt 133 .CALLDATASIZE,
   opAt 134 .SUB,
   opAt 135 .SHR,
   pushAt 136 1 248,
   opAt 137 .AND,
   opAt 138 .SHR,
   opAt 139 (.Dup ⟨4, by decide⟩),
   opAt 140 .OR,
   opAt 141 (.Swap ⟨3, by decide⟩),
   opAt 142 .POP,
   opAt 143 .POP,
   pushAt 144 1 160,
   opAt 145 .ADD,
   pushAt 146 1 255,
   opAt 147 .AND,
   opAt 148 (.Swap ⟨0, by decide⟩),
   pushAt 149 1 32,
   opAt 150 .ADD,
   opAt 151 (.Swap ⟨0, by decide⟩),
   opAt 152 .CALLDATASIZE,
   opAt 153 (.Dup ⟨2, by decide⟩),
   opAt 154 .LT,
   pushAt 155 1 152,
   opAt 156 .JUMPI,
   opAt 157 (.Dup ⟨2, by decide⟩)]

/-- The padded tail word, the cleanup and the miss test. -/
def tailPath : List Located :=
  [opAt 184 .JUMPDEST, opAt 186 (.Swap ⟨2, by decide⟩), opAt 187 .POP,
   opAt 188 (.Swap ⟨1, by decide⟩), opAt 189 (.Swap ⟨6, by decide⟩), opAt 190 .POP,
   opAt 191 .POP, opAt 192 .POP, opAt 193 .POP, opAt 194 .POP, opAt 195 .POP, opAt 196 .POP,
   pushAt 197 2 360, opAt 198 .JUMPI]

/-- Store and return the stored digest. -/
def returnPath : List Located :=
  [opAt 165 .CALLDATASIZE, pushAt 167 2 376, opAt 168 .EQ,
   pushAt 169 20 644824770394507154413287103057882351908521126009, opAt 170 .MUL,
   pushAt 177 20 766350606435067737561421097975693824639675460820, opAt 178 .XOR,
   pushAt 179 0 0, opAt 180 .MSTORE, opAt 181 .MSIZE, pushAt 182 0 0,
   opAt 183 .RETURN]

/-- Shift the correction constant out of `M`. -/
def straddleCorrPath : List Located :=
  [opAt 100 (.Dup ⟨6, by decide⟩),
   opAt 101 (.Dup ⟨4, by decide⟩), pushAt 102 1 8, opAt 103 .SHR,
   pushAt 104 1 40, opAt 105 .MUL, pushAt 106 1 216, opAt 107 .SUB,
   opAt 108 .SHR, pushAt 109 1 11,
   opAt 110 .MUL]

/-- Apply the correction to the expected word. -/
def straddleAddPath : List Located :=
  [opAt 111 (.Dup ⟨1, by decide⟩), opAt 112 (.Dup ⟨9, by decide⟩),
   opAt 113 .AND, opAt 114 (.Dup ⟨1, by decide⟩), opAt 115 .ADD,
   opAt 116 (.Dup ⟨2, by decide⟩), opAt 117 (.Dup ⟨12, by decide⟩),
   opAt 118 .AND, opAt 119 .XOR, opAt 120 (.Swap ⟨1, by decide⟩),
   opAt 121 .POP, opAt 122 .POP]

/-- Bump the scalar and rejoin the scan. -/
def straddleBackPath : List Located :=
  [opAt 123 (.Swap ⟨1, by decide⟩), pushAt 124 1 11, opAt 125 .ADD,
   opAt 126 (.Swap ⟨1, by decide⟩)]


@[simp] theorem pc2903 : Artifact.submissionArtifact.instructionPC 61 = 0x64 :=
  by rw [scan_instruction_pc 61 (by decide) (by decide)]; rfl
@[simp] theorem pc2904 : Artifact.submissionArtifact.instructionPC 61 = 0x64 :=
  by rw [scan_instruction_pc 61 (by decide) (by decide)]; rfl
@[simp] theorem pc2905 : Artifact.submissionArtifact.instructionPC 65 = 0x69 :=
  by rw [scan_instruction_pc 65 (by decide) (by decide)]; rfl
@[simp] theorem pc2906 : Artifact.submissionArtifact.instructionPC 70 = 0x8f :=
  by rw [scan_instruction_pc 70 (by decide) (by decide)]; rfl
@[simp] theorem pc2907 : Artifact.submissionArtifact.instructionPC 72 = 0x91 :=
  by rw [scan_instruction_pc 72 (by decide) (by decide)]; rfl
@[simp] theorem pc2908 : Artifact.submissionArtifact.instructionPC 73 = 0x92 :=
  by rw [scan_instruction_pc 73 (by decide) (by decide)]; rfl
@[simp] theorem pc2909 : Artifact.submissionArtifact.instructionPC 74 = 0x93 :=
  by rw [scan_instruction_pc 74 (by decide) (by decide)]; rfl
@[simp] theorem pc2910 : Artifact.submissionArtifact.instructionPC 75 = 0x94 :=
  by rw [scan_instruction_pc 75 (by decide) (by decide)]; rfl
@[simp] theorem pc2911 : Artifact.submissionArtifact.instructionPC 76 = 0x95 :=
  by rw [scan_instruction_pc 76 (by decide) (by decide)]; rfl
@[simp] theorem pc2912 : Artifact.submissionArtifact.instructionPC 77 = 0x96 :=
  by rw [scan_instruction_pc 77 (by decide) (by decide)]; rfl
@[simp] theorem pc2913 : Artifact.submissionArtifact.instructionPC 78 = 0x97 :=
  by rw [scan_instruction_pc 78 (by decide) (by decide)]; rfl
@[simp] theorem pc2914 : Artifact.submissionArtifact.instructionPC 79 = 0x98 :=
  by rw [scan_instruction_pc 79 (by decide) (by decide)]; rfl
@[simp] theorem pc2915 : Artifact.submissionArtifact.instructionPC 80 = 0x99 :=
  by rw [scan_instruction_pc 80 (by decide) (by decide)]; rfl
@[simp] theorem pc2916 : Artifact.submissionArtifact.instructionPC 81 = 0x9a :=
  by rw [scan_instruction_pc 81 (by decide) (by decide)]; rfl
@[simp] theorem pc2917 : Artifact.submissionArtifact.instructionPC 82 = 0x9b :=
  by rw [scan_instruction_pc 82 (by decide) (by decide)]; rfl
@[simp] theorem pc2918 : Artifact.submissionArtifact.instructionPC 83 = 0x9c :=
  by rw [scan_instruction_pc 83 (by decide) (by decide)]; rfl
@[simp] theorem pc2919 : Artifact.submissionArtifact.instructionPC 84 = 0x9d :=
  by rw [scan_instruction_pc 84 (by decide) (by decide)]; rfl
@[simp] theorem pc2920 : Artifact.submissionArtifact.instructionPC 85 = 0x9e :=
  by rw [scan_instruction_pc 85 (by decide) (by decide)]; rfl
@[simp] theorem pc2921 : Artifact.submissionArtifact.instructionPC 86 = 0x9f :=
  by rw [scan_instruction_pc 86 (by decide) (by decide)]; rfl
@[simp] theorem pc2922 : Artifact.submissionArtifact.instructionPC 87 = 0xa0 :=
  by rw [scan_instruction_pc 87 (by decide) (by decide)]; rfl
@[simp] theorem pc2923 : Artifact.submissionArtifact.instructionPC 88 = 0xa1 :=
  by rw [scan_instruction_pc 88 (by decide) (by decide)]; rfl
@[simp] theorem pc2924 : Artifact.submissionArtifact.instructionPC 89 = 0xa2 :=
  by rw [scan_instruction_pc 89 (by decide) (by decide)]; rfl
@[simp] theorem pc2925 : Artifact.submissionArtifact.instructionPC 90 = 0xa3 :=
  by rw [scan_instruction_pc 90 (by decide) (by decide)]; rfl
@[simp] theorem pc2926 : Artifact.submissionArtifact.instructionPC 91 = 0xa4 :=
  by rw [scan_instruction_pc 91 (by decide) (by decide)]; rfl
@[simp] theorem pc2927 : Artifact.submissionArtifact.instructionPC 92 = 0xa5 :=
  by rw [scan_instruction_pc 92 (by decide) (by decide)]; rfl
@[simp] theorem pc2928 : Artifact.submissionArtifact.instructionPC 93 = 0xa6 :=
  by rw [scan_instruction_pc 93 (by decide) (by decide)]; rfl
@[simp] theorem pc2929 : Artifact.submissionArtifact.instructionPC 94 = 0xa7 :=
  by rw [scan_instruction_pc 94 (by decide) (by decide)]; rfl
@[simp] theorem pc2930 : Artifact.submissionArtifact.instructionPC 95 = 0xa8 :=
  by rw [scan_instruction_pc 95 (by decide) (by decide)]; rfl
@[simp] theorem pc2931 : Artifact.submissionArtifact.instructionPC 96 = 0xa9 :=
  by rw [scan_instruction_pc 96 (by decide) (by decide)]; rfl
@[simp] theorem pc2932 : Artifact.submissionArtifact.instructionPC 97 = 0xab :=
  by rw [scan_instruction_pc 97 (by decide) (by decide)]; rfl
@[simp] theorem pc2934 : Artifact.submissionArtifact.instructionPC 98 = 0xac :=
  by rw [scan_instruction_pc 98 (by decide) (by decide)]; rfl
@[simp] theorem pc2935 : Artifact.submissionArtifact.instructionPC 99 = 0xae :=
  by rw [scan_instruction_pc 99 (by decide) (by decide)]; rfl
@[simp] theorem pc2936 : Artifact.submissionArtifact.instructionPC 127 = 0xcf :=
  by rw [scan_instruction_pc 127 (by decide) (by decide)]; rfl
@[simp] theorem pc2937 : Artifact.submissionArtifact.instructionPC 128 = 0xd0 :=
  by rw [scan_instruction_pc 128 (by decide) (by decide)]; rfl
@[simp] theorem pc2938 : Artifact.submissionArtifact.instructionPC 129 = 0xd1 :=
  by rw [scan_instruction_pc 129 (by decide) (by decide)]; rfl
@[simp] theorem pc2939 : Artifact.submissionArtifact.instructionPC 130 = 0xd2 :=
  by rw [scan_instruction_pc 130 (by decide) (by decide)]; rfl
@[simp] theorem pc2940 : Artifact.submissionArtifact.instructionPC 139 = 0xe1 :=
  by rw [scan_instruction_pc 139 (by decide) (by decide)]; rfl
@[simp] theorem pc2941 : Artifact.submissionArtifact.instructionPC 140 = 0xe2 :=
  by rw [scan_instruction_pc 140 (by decide) (by decide)]; rfl
@[simp] theorem pc2942 : Artifact.submissionArtifact.instructionPC 141 = 0xe3 :=
  by rw [scan_instruction_pc 141 (by decide) (by decide)]; rfl
@[simp] theorem pc2943 : Artifact.submissionArtifact.instructionPC 142 = 0xe4 :=
  by rw [scan_instruction_pc 142 (by decide) (by decide)]; rfl
@[simp] theorem pc2944 : Artifact.submissionArtifact.instructionPC 143 = 0xe5 :=
  by rw [scan_instruction_pc 143 (by decide) (by decide)]; rfl
@[simp] theorem pc2945 : Artifact.submissionArtifact.instructionPC 144 = 0xe6 :=
  by rw [scan_instruction_pc 144 (by decide) (by decide)]; rfl
@[simp] theorem pc2946 : Artifact.submissionArtifact.instructionPC 144 = 0xe6 :=
  by rw [scan_instruction_pc 144 (by decide) (by decide)]; rfl
@[simp] theorem pc2947 : Artifact.submissionArtifact.instructionPC 145 = 0xe8 :=
  by rw [scan_instruction_pc 145 (by decide) (by decide)]; rfl
@[simp] theorem pc2948 : Artifact.submissionArtifact.instructionPC 146 = 0xe9 :=
  by rw [scan_instruction_pc 146 (by decide) (by decide)]; rfl
@[simp] theorem pc2949 : Artifact.submissionArtifact.instructionPC 147 = 0xeb :=
  by rw [scan_instruction_pc 147 (by decide) (by decide)]; rfl
@[simp] theorem pc2950 : Artifact.submissionArtifact.instructionPC 148 = 0xec :=
  by rw [scan_instruction_pc 148 (by decide) (by decide)]; rfl
@[simp] theorem pc2951 : Artifact.submissionArtifact.instructionPC 148 = 0xec :=
  by rw [scan_instruction_pc 148 (by decide) (by decide)]; rfl
@[simp] theorem pc2952 : Artifact.submissionArtifact.instructionPC 148 = 0xec :=
  by rw [scan_instruction_pc 148 (by decide) (by decide)]; rfl
@[simp] theorem pc2953 : Artifact.submissionArtifact.instructionPC 149 = 0xed :=
  by rw [scan_instruction_pc 149 (by decide) (by decide)]; rfl
@[simp] theorem pc2954 : Artifact.submissionArtifact.instructionPC 150 = 0xef :=
  by rw [scan_instruction_pc 150 (by decide) (by decide)]; rfl
@[simp] theorem pc2955 : Artifact.submissionArtifact.instructionPC 151 = 0xf0 :=
  by rw [scan_instruction_pc 151 (by decide) (by decide)]; rfl
@[simp] theorem pc2956 : Artifact.submissionArtifact.instructionPC 144 = 0xe6 :=
  by rw [scan_instruction_pc 144 (by decide) (by decide)]; rfl
@[simp] theorem pc2957 : Artifact.submissionArtifact.instructionPC 144 = 0xe6 :=
  by rw [scan_instruction_pc 144 (by decide) (by decide)]; rfl
@[simp] theorem pc2958 : Artifact.submissionArtifact.instructionPC 145 = 0xe8 :=
  by rw [scan_instruction_pc 145 (by decide) (by decide)]; rfl
@[simp] theorem pc2959 : Artifact.submissionArtifact.instructionPC 146 = 0xe9 :=
  by rw [scan_instruction_pc 146 (by decide) (by decide)]; rfl
@[simp] theorem pc2960 : Artifact.submissionArtifact.instructionPC 147 = 0xeb :=
  by rw [scan_instruction_pc 147 (by decide) (by decide)]; rfl
@[simp] theorem pc2961 : Artifact.submissionArtifact.instructionPC 148 = 0xec :=
  by rw [scan_instruction_pc 148 (by decide) (by decide)]; rfl
@[simp] theorem pc2962 : Artifact.submissionArtifact.instructionPC 149 = 0xed :=
  by rw [scan_instruction_pc 149 (by decide) (by decide)]; rfl
@[simp] theorem pc2963 : Artifact.submissionArtifact.instructionPC 150 = 0xef :=
  by rw [scan_instruction_pc 150 (by decide) (by decide)]; rfl
@[simp] theorem pc2964 : Artifact.submissionArtifact.instructionPC 151 = 0xf0 :=
  by rw [scan_instruction_pc 151 (by decide) (by decide)]; rfl
@[simp] theorem pc2965 : Artifact.submissionArtifact.instructionPC 152 = 0xf1 :=
  by rw [scan_instruction_pc 152 (by decide) (by decide)]; rfl
@[simp] theorem pc2966 : Artifact.submissionArtifact.instructionPC 153 = 0xf2 :=
  by rw [scan_instruction_pc 153 (by decide) (by decide)]; rfl
@[simp] theorem pc2967 : Artifact.submissionArtifact.instructionPC 154 = 0xf3 :=
  by rw [scan_instruction_pc 154 (by decide) (by decide)]; rfl
@[simp] theorem pc2968 : Artifact.submissionArtifact.instructionPC 155 = 0xf4 :=
  by rw [scan_instruction_pc 155 (by decide) (by decide)]; rfl
@[simp] theorem pc2969 : Artifact.submissionArtifact.instructionPC 156 = 0xf6 :=
  by rw [scan_instruction_pc 156 (by decide) (by decide)]; rfl
@[simp] theorem pc2969a : Artifact.submissionArtifact.instructionPC 184 = 0x157 :=
  by rw [scan_instruction_pc 184 (by decide) (by decide)]; rfl
@[simp] theorem pc2970 : Artifact.submissionArtifact.instructionPC 186 = 0x159 :=
  by rw [scan_instruction_pc 186 (by decide) (by decide)]; rfl
@[simp] theorem pc2971 : Artifact.submissionArtifact.instructionPC 187 = 0x15a :=
  by rw [scan_instruction_pc 187 (by decide) (by decide)]; rfl
@[simp] theorem pc2972 : Artifact.submissionArtifact.instructionPC 188 = 0x15b :=
  by rw [scan_instruction_pc 188 (by decide) (by decide)]; rfl
@[simp] theorem pc2973 : Artifact.submissionArtifact.instructionPC 189 = 0x15c :=
  by rw [scan_instruction_pc 189 (by decide) (by decide)]; rfl
@[simp] theorem pc2974 : Artifact.submissionArtifact.instructionPC 190 = 0x15d :=
  by rw [scan_instruction_pc 190 (by decide) (by decide)]; rfl
@[simp] theorem pc2975 : Artifact.submissionArtifact.instructionPC 191 = 0x15e :=
  by rw [scan_instruction_pc 191 (by decide) (by decide)]; rfl
@[simp] theorem pc2976 : Artifact.submissionArtifact.instructionPC 192 = 0x15f :=
  by rw [scan_instruction_pc 192 (by decide) (by decide)]; rfl
@[simp] theorem pc2977 : Artifact.submissionArtifact.instructionPC 193 = 0x160 :=
  by rw [scan_instruction_pc 193 (by decide) (by decide)]; rfl
@[simp] theorem pc2978 : Artifact.submissionArtifact.instructionPC 194 = 0x161 :=
  by rw [scan_instruction_pc 194 (by decide) (by decide)]; rfl
@[simp] theorem pc2979 : Artifact.submissionArtifact.instructionPC 195 = 0x162 :=
  by rw [scan_instruction_pc 195 (by decide) (by decide)]; rfl
@[simp] theorem pc2980 : Artifact.submissionArtifact.instructionPC 196 = 0x163 :=
  by rw [scan_instruction_pc 196 (by decide) (by decide)]; rfl
@[simp] theorem pc2981 : Artifact.submissionArtifact.instructionPC 197 = 0x164 :=
  by rw [scan_instruction_pc 197 (by decide) (by decide)]; rfl
@[simp] theorem pc2982 : Artifact.submissionArtifact.instructionPC 198 = 0x167 :=
  by rw [scan_instruction_pc 198 (by decide) (by decide)]; rfl
@[simp] theorem pc_ins249 : Artifact.submissionArtifact.instructionPC 165 = 0x104 :=
  by rw [scan_instruction_pc 165 (by decide) (by decide)]; rfl
@[simp] theorem pc_ins250 : Artifact.submissionArtifact.instructionPC 167 = 0x106 :=
  by rw [scan_instruction_pc 167 (by decide) (by decide)]; rfl
@[simp] theorem pc_ins251 : Artifact.submissionArtifact.instructionPC 168 = 0x109 :=
  by rw [scan_instruction_pc 168 (by decide) (by decide)]; rfl
@[simp] theorem pc_ins252 : Artifact.submissionArtifact.instructionPC 169 = 0x10a :=
  by rw [scan_instruction_pc 169 (by decide) (by decide)]; rfl
@[simp] theorem pc_ins253 : Artifact.submissionArtifact.instructionPC 170 = 0x11f :=
  by rw [scan_instruction_pc 170 (by decide) (by decide)]; rfl
@[simp] theorem pc_ins255 : Artifact.submissionArtifact.instructionPC 178 = 0x151 :=
  by rw [scan_instruction_pc 178 (by decide) (by decide)]; rfl
@[simp] theorem pc_ins217 : Artifact.submissionArtifact.instructionPC 152 = 0xf1 :=
  by rw [scan_instruction_pc 152 (by decide) (by decide)]; rfl
@[simp] theorem pc_ins218 : Artifact.submissionArtifact.instructionPC 153 = 0xf2 :=
  by rw [scan_instruction_pc 153 (by decide) (by decide)]; rfl
@[simp] theorem pc_ins219 : Artifact.submissionArtifact.instructionPC 154 = 0xf3 :=
  by rw [scan_instruction_pc 154 (by decide) (by decide)]; rfl
@[simp] theorem pc_ins220 : Artifact.submissionArtifact.instructionPC 155 = 0xf4 :=
  by rw [scan_instruction_pc 155 (by decide) (by decide)]; rfl
@[simp] theorem pc_ins221 : Artifact.submissionArtifact.instructionPC 156 = 0xf6 :=
  by rw [scan_instruction_pc 156 (by decide) (by decide)]; rfl
@[simp] theorem pc2983 : Artifact.submissionArtifact.instructionPC 177 = 0x13c :=
  by rw [scan_instruction_pc 177 (by decide) (by decide)]; rfl
@[simp] theorem pc2984 : Artifact.submissionArtifact.instructionPC 179 = 0x152 :=
  by rw [scan_instruction_pc 179 (by decide) (by decide)]; rfl
@[simp] theorem pc2985 : Artifact.submissionArtifact.instructionPC 180 = 0x153 :=
  by rw [scan_instruction_pc 180 (by decide) (by decide)]; rfl
@[simp] theorem pc2986 : Artifact.submissionArtifact.instructionPC 181 = 0x154 :=
  by rw [scan_instruction_pc 181 (by decide) (by decide)]; rfl
@[simp] theorem pc2987 : Artifact.submissionArtifact.instructionPC 182 = 0x155 :=
  by rw [scan_instruction_pc 182 (by decide) (by decide)]; rfl
@[simp] theorem pc2988 : Artifact.submissionArtifact.instructionPC 183 = 0x156 :=
  by rw [scan_instruction_pc 183 (by decide) (by decide)]; rfl
@[simp] theorem pc2989 : Artifact.submissionArtifact.instructionPC 100 = 0xaf :=
  by rw [scan_instruction_pc 100 (by decide) (by decide)]; rfl
@[simp] theorem pc2990 : Artifact.submissionArtifact.instructionPC 100 = 0xaf :=
  by rw [scan_instruction_pc 100 (by decide) (by decide)]; rfl
@[simp] theorem pc2991 : Artifact.submissionArtifact.instructionPC 101 = 0xb0 :=
  by rw [scan_instruction_pc 101 (by decide) (by decide)]; rfl
@[simp] theorem pc2992 : Artifact.submissionArtifact.instructionPC 102 = 0xb1 :=
  by rw [scan_instruction_pc 102 (by decide) (by decide)]; rfl
@[simp] theorem pc2993 : Artifact.submissionArtifact.instructionPC 103 = 0xb3 :=
  by rw [scan_instruction_pc 103 (by decide) (by decide)]; rfl
@[simp] theorem pc2994 : Artifact.submissionArtifact.instructionPC 104 = 0xb4 :=
  by rw [scan_instruction_pc 104 (by decide) (by decide)]; rfl
@[simp] theorem pc2995 : Artifact.submissionArtifact.instructionPC 105 = 0xb6 :=
  by rw [scan_instruction_pc 105 (by decide) (by decide)]; rfl
@[simp] theorem pc2996 : Artifact.submissionArtifact.instructionPC 106 = 0xb7 :=
  by rw [scan_instruction_pc 106 (by decide) (by decide)]; rfl
@[simp] theorem pc2997 : Artifact.submissionArtifact.instructionPC 107 = 0xb9 :=
  by rw [scan_instruction_pc 107 (by decide) (by decide)]; rfl
@[simp] theorem pc2998 : Artifact.submissionArtifact.instructionPC 108 = 0xba :=
  by rw [scan_instruction_pc 108 (by decide) (by decide)]; rfl
@[simp] theorem pc2999 : Artifact.submissionArtifact.instructionPC 108 = 0xba :=
  by rw [scan_instruction_pc 108 (by decide) (by decide)]; rfl
@[simp] theorem pc3000 : Artifact.submissionArtifact.instructionPC 108 = 0xba :=
  by rw [scan_instruction_pc 108 (by decide) (by decide)]; rfl
@[simp] theorem pc3001 : Artifact.submissionArtifact.instructionPC 109 = 0xbb :=
  by rw [scan_instruction_pc 109 (by decide) (by decide)]; rfl
@[simp] theorem pc3002 : Artifact.submissionArtifact.instructionPC 110 = 0xbd :=
  by rw [scan_instruction_pc 110 (by decide) (by decide)]; rfl
@[simp] theorem pc3003 : Artifact.submissionArtifact.instructionPC 111 = 0xbe :=
  by rw [scan_instruction_pc 111 (by decide) (by decide)]; rfl
@[simp] theorem pc3004 : Artifact.submissionArtifact.instructionPC 112 = 0xbf :=
  by rw [scan_instruction_pc 112 (by decide) (by decide)]; rfl
@[simp] theorem pc3005 : Artifact.submissionArtifact.instructionPC 113 = 0xc0 :=
  by rw [scan_instruction_pc 113 (by decide) (by decide)]; rfl
@[simp] theorem pc3006 : Artifact.submissionArtifact.instructionPC 114 = 0xc1 :=
  by rw [scan_instruction_pc 114 (by decide) (by decide)]; rfl
@[simp] theorem pc3007 : Artifact.submissionArtifact.instructionPC 115 = 0xc2 :=
  by rw [scan_instruction_pc 115 (by decide) (by decide)]; rfl
@[simp] theorem pc3008 : Artifact.submissionArtifact.instructionPC 116 = 0xc3 :=
  by rw [scan_instruction_pc 116 (by decide) (by decide)]; rfl
@[simp] theorem pc3009 : Artifact.submissionArtifact.instructionPC 117 = 0xc4 :=
  by rw [scan_instruction_pc 117 (by decide) (by decide)]; rfl
@[simp] theorem pc3010 : Artifact.submissionArtifact.instructionPC 118 = 0xc5 :=
  by rw [scan_instruction_pc 118 (by decide) (by decide)]; rfl
@[simp] theorem pc3011 : Artifact.submissionArtifact.instructionPC 119 = 0xc6 :=
  by rw [scan_instruction_pc 119 (by decide) (by decide)]; rfl
@[simp] theorem pc3012 : Artifact.submissionArtifact.instructionPC 120 = 0xc7 :=
  by rw [scan_instruction_pc 120 (by decide) (by decide)]; rfl
@[simp] theorem pc3013 : Artifact.submissionArtifact.instructionPC 121 = 0xc8 :=
  by rw [scan_instruction_pc 121 (by decide) (by decide)]; rfl
@[simp] theorem pc3014 : Artifact.submissionArtifact.instructionPC 122 = 0xc9 :=
  by rw [scan_instruction_pc 122 (by decide) (by decide)]; rfl
@[simp] theorem pc3015 : Artifact.submissionArtifact.instructionPC 123 = 0xca :=
  by rw [scan_instruction_pc 123 (by decide) (by decide)]; rfl
@[simp] theorem pc3016 : Artifact.submissionArtifact.instructionPC 124 = 0xcb :=
  by rw [scan_instruction_pc 124 (by decide) (by decide)]; rfl
@[simp] theorem pc3017 : Artifact.submissionArtifact.instructionPC 125 = 0xcd :=
  by rw [scan_instruction_pc 125 (by decide) (by decide)]; rfl
@[simp] theorem pc3018 : Artifact.submissionArtifact.instructionPC 126 = 0xce :=
  by rw [scan_instruction_pc 126 (by decide) (by decide)]; rfl
@[simp] theorem pc3019 : Artifact.submissionArtifact.instructionPC 127 = 0xcf :=
  by rw [scan_instruction_pc 127 (by decide) (by decide)]; rfl
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
