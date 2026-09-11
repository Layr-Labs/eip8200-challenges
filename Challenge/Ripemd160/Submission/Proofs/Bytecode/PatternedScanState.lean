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

private theorem scanSuffix_length : scanSuffix.length = 4059 := by
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
    (hlo : 51 ≤ index) (hhi : index < 4110) :
    Artifact.submissionInstructions[index]? = scanSuffix[index - 51]? := by
  have hi : index - 51 < scanSuffix.length := by
    rw [scanSuffix_length]
    omega
  have h := ArtifactSegment.getElem?_segment Artifact.submissionArtifact
    scanBefore scanSuffix [] artifact_scan_split (index - 51) hi
  simpa only [artifact_instruction_projection, scanBefore_length,
    Nat.add_sub_of_le hlo] using h

private theorem scan_instruction_pc (index : Nat)
    (hlo : 51 ≤ index) (hhi : index ≤ 4110) :
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
   pushAt 131 5 4446160832,
   opAt 132 (.Dup ⟨4, by decide⟩),
   opAt 133 .CALLDATASIZE,
   opAt 134 .SUB,
   opAt 137 .SHR,
   pushAt 138 1 248,
   opAt 139 .AND,
   opAt 140 .SHR,
   opAt 141 (.Dup ⟨4, by decide⟩),
   opAt 142 .OR,
   opAt 143 (.Swap ⟨3, by decide⟩),
   opAt 144 .POP,
   opAt 145 .POP,
   pushAt 146 1 160,
   opAt 147 .ADD,
   pushAt 148 1 255,
   opAt 149 .AND,
   opAt 150 (.Swap ⟨0, by decide⟩),
   pushAt 151 1 32,
   opAt 152 .ADD,
   opAt 153 (.Swap ⟨0, by decide⟩),
   opAt 154 .CALLDATASIZE,
   opAt 155 (.Dup ⟨2, by decide⟩),
   opAt 156 .LT,
   pushAt 157 1 152,
   opAt 158 .JUMPI,
   opAt 159 (.Dup ⟨2, by decide⟩)]

/-- The padded tail word, the cleanup and the miss test. -/
def tailPath : List Located :=
  [opAt 164 .JUMPDEST, opAt 166 (.Swap ⟨2, by decide⟩), opAt 167 .POP,
   opAt 168 (.Swap ⟨1, by decide⟩), opAt 169 (.Swap ⟨6, by decide⟩), opAt 170 .POP,
   opAt 171 .POP, opAt 172 .POP, opAt 173 .POP, opAt 174 .POP, opAt 175 .POP, opAt 176 .POP,
   pushAt 177 2 393, opAt 178 .JUMPI]

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


@[simp] theorem pc2903 : Artifact.submissionArtifact.instructionPC 61 = 100 :=
  by rw [scan_instruction_pc 61 (by decide) (by decide)]; rfl
@[simp] theorem pc2904 : Artifact.submissionArtifact.instructionPC 61 = 100 :=
  by rw [scan_instruction_pc 61 (by decide) (by decide)]; rfl
@[simp] theorem pc2905 : Artifact.submissionArtifact.instructionPC 65 = 105 :=
  by rw [scan_instruction_pc 65 (by decide) (by decide)]; rfl
@[simp] theorem pc2906 : Artifact.submissionArtifact.instructionPC 70 = 143 :=
  by rw [scan_instruction_pc 70 (by decide) (by decide)]; rfl
@[simp] theorem pc2907 : Artifact.submissionArtifact.instructionPC 72 = 145 :=
  by rw [scan_instruction_pc 72 (by decide) (by decide)]; rfl
@[simp] theorem pc2908 : Artifact.submissionArtifact.instructionPC 73 = 146 :=
  by rw [scan_instruction_pc 73 (by decide) (by decide)]; rfl
@[simp] theorem pc2909 : Artifact.submissionArtifact.instructionPC 74 = 147 :=
  by rw [scan_instruction_pc 74 (by decide) (by decide)]; rfl
@[simp] theorem pc2910 : Artifact.submissionArtifact.instructionPC 75 = 148 :=
  by rw [scan_instruction_pc 75 (by decide) (by decide)]; rfl
@[simp] theorem pc2911 : Artifact.submissionArtifact.instructionPC 76 = 149 :=
  by rw [scan_instruction_pc 76 (by decide) (by decide)]; rfl
@[simp] theorem pc2912 : Artifact.submissionArtifact.instructionPC 77 = 150 :=
  by rw [scan_instruction_pc 77 (by decide) (by decide)]; rfl
@[simp] theorem pc2913 : Artifact.submissionArtifact.instructionPC 78 = 151 :=
  by rw [scan_instruction_pc 78 (by decide) (by decide)]; rfl
@[simp] theorem pc2914 : Artifact.submissionArtifact.instructionPC 79 = 152 :=
  by rw [scan_instruction_pc 79 (by decide) (by decide)]; rfl
@[simp] theorem pc2915 : Artifact.submissionArtifact.instructionPC 80 = 153 :=
  by rw [scan_instruction_pc 80 (by decide) (by decide)]; rfl
@[simp] theorem pc2916 : Artifact.submissionArtifact.instructionPC 81 = 154 :=
  by rw [scan_instruction_pc 81 (by decide) (by decide)]; rfl
@[simp] theorem pc2917 : Artifact.submissionArtifact.instructionPC 82 = 155 :=
  by rw [scan_instruction_pc 82 (by decide) (by decide)]; rfl
@[simp] theorem pc2918 : Artifact.submissionArtifact.instructionPC 83 = 156 :=
  by rw [scan_instruction_pc 83 (by decide) (by decide)]; rfl
@[simp] theorem pc2919 : Artifact.submissionArtifact.instructionPC 84 = 157 :=
  by rw [scan_instruction_pc 84 (by decide) (by decide)]; rfl
@[simp] theorem pc2920 : Artifact.submissionArtifact.instructionPC 85 = 158 :=
  by rw [scan_instruction_pc 85 (by decide) (by decide)]; rfl
@[simp] theorem pc2921 : Artifact.submissionArtifact.instructionPC 86 = 159 :=
  by rw [scan_instruction_pc 86 (by decide) (by decide)]; rfl
@[simp] theorem pc2922 : Artifact.submissionArtifact.instructionPC 87 = 160 :=
  by rw [scan_instruction_pc 87 (by decide) (by decide)]; rfl
@[simp] theorem pc2923 : Artifact.submissionArtifact.instructionPC 88 = 161 :=
  by rw [scan_instruction_pc 88 (by decide) (by decide)]; rfl
@[simp] theorem pc2924 : Artifact.submissionArtifact.instructionPC 89 = 162 :=
  by rw [scan_instruction_pc 89 (by decide) (by decide)]; rfl
@[simp] theorem pc2925 : Artifact.submissionArtifact.instructionPC 90 = 163 :=
  by rw [scan_instruction_pc 90 (by decide) (by decide)]; rfl
@[simp] theorem pc2926 : Artifact.submissionArtifact.instructionPC 91 = 164 :=
  by rw [scan_instruction_pc 91 (by decide) (by decide)]; rfl
@[simp] theorem pc2927 : Artifact.submissionArtifact.instructionPC 92 = 165 :=
  by rw [scan_instruction_pc 92 (by decide) (by decide)]; rfl
@[simp] theorem pc2928 : Artifact.submissionArtifact.instructionPC 93 = 166 :=
  by rw [scan_instruction_pc 93 (by decide) (by decide)]; rfl
@[simp] theorem pc2929 : Artifact.submissionArtifact.instructionPC 94 = 167 :=
  by rw [scan_instruction_pc 94 (by decide) (by decide)]; rfl
@[simp] theorem pc2930 : Artifact.submissionArtifact.instructionPC 95 = 168 :=
  by rw [scan_instruction_pc 95 (by decide) (by decide)]; rfl
@[simp] theorem pc2931 : Artifact.submissionArtifact.instructionPC 96 = 169 :=
  by rw [scan_instruction_pc 96 (by decide) (by decide)]; rfl
@[simp] theorem pc2932 : Artifact.submissionArtifact.instructionPC 97 = 171 :=
  by rw [scan_instruction_pc 97 (by decide) (by decide)]; rfl
@[simp] theorem pc2934 : Artifact.submissionArtifact.instructionPC 98 = 172 :=
  by rw [scan_instruction_pc 98 (by decide) (by decide)]; rfl
@[simp] theorem pc2935 : Artifact.submissionArtifact.instructionPC 99 = 174 :=
  by rw [scan_instruction_pc 99 (by decide) (by decide)]; rfl
@[simp] theorem pc2936 : Artifact.submissionArtifact.instructionPC 127 = 207 :=
  by rw [scan_instruction_pc 127 (by decide) (by decide)]; rfl
@[simp] theorem pc2937 : Artifact.submissionArtifact.instructionPC 128 = 208 :=
  by rw [scan_instruction_pc 128 (by decide) (by decide)]; rfl
@[simp] theorem pc2938 : Artifact.submissionArtifact.instructionPC 129 = 209 :=
  by rw [scan_instruction_pc 129 (by decide) (by decide)]; rfl
@[simp] theorem pc2939 : Artifact.submissionArtifact.instructionPC 130 = 210 :=
  by rw [scan_instruction_pc 130 (by decide) (by decide)]; rfl
@[simp] theorem pc2940 : Artifact.submissionArtifact.instructionPC 141 = 228 :=
  by rw [scan_instruction_pc 141 (by decide) (by decide)]; rfl
@[simp] theorem pc2941 : Artifact.submissionArtifact.instructionPC 142 = 229 :=
  by rw [scan_instruction_pc 142 (by decide) (by decide)]; rfl
@[simp] theorem pc2942 : Artifact.submissionArtifact.instructionPC 143 = 230 :=
  by rw [scan_instruction_pc 143 (by decide) (by decide)]; rfl
@[simp] theorem pc2943 : Artifact.submissionArtifact.instructionPC 144 = 231 :=
  by rw [scan_instruction_pc 144 (by decide) (by decide)]; rfl
@[simp] theorem pc2944 : Artifact.submissionArtifact.instructionPC 145 = 232 :=
  by rw [scan_instruction_pc 145 (by decide) (by decide)]; rfl
@[simp] theorem pc2945 : Artifact.submissionArtifact.instructionPC 146 = 233 :=
  by rw [scan_instruction_pc 146 (by decide) (by decide)]; rfl
@[simp] theorem pc2946 : Artifact.submissionArtifact.instructionPC 146 = 233 :=
  by rw [scan_instruction_pc 146 (by decide) (by decide)]; rfl
@[simp] theorem pc2947 : Artifact.submissionArtifact.instructionPC 147 = 235 :=
  by rw [scan_instruction_pc 147 (by decide) (by decide)]; rfl
@[simp] theorem pc2948 : Artifact.submissionArtifact.instructionPC 148 = 236 :=
  by rw [scan_instruction_pc 148 (by decide) (by decide)]; rfl
@[simp] theorem pc2949 : Artifact.submissionArtifact.instructionPC 149 = 238 :=
  by rw [scan_instruction_pc 149 (by decide) (by decide)]; rfl
@[simp] theorem pc2950 : Artifact.submissionArtifact.instructionPC 150 = 239 :=
  by rw [scan_instruction_pc 150 (by decide) (by decide)]; rfl
@[simp] theorem pc2951 : Artifact.submissionArtifact.instructionPC 150 = 239 :=
  by rw [scan_instruction_pc 150 (by decide) (by decide)]; rfl
@[simp] theorem pc2952 : Artifact.submissionArtifact.instructionPC 150 = 239 :=
  by rw [scan_instruction_pc 150 (by decide) (by decide)]; rfl
@[simp] theorem pc2953 : Artifact.submissionArtifact.instructionPC 151 = 240 :=
  by rw [scan_instruction_pc 151 (by decide) (by decide)]; rfl
@[simp] theorem pc2954 : Artifact.submissionArtifact.instructionPC 152 = 242 :=
  by rw [scan_instruction_pc 152 (by decide) (by decide)]; rfl
@[simp] theorem pc2955 : Artifact.submissionArtifact.instructionPC 153 = 243 :=
  by rw [scan_instruction_pc 153 (by decide) (by decide)]; rfl
@[simp] theorem pc2956 : Artifact.submissionArtifact.instructionPC 146 = 233 :=
  by rw [scan_instruction_pc 146 (by decide) (by decide)]; rfl
@[simp] theorem pc2957 : Artifact.submissionArtifact.instructionPC 146 = 233 :=
  by rw [scan_instruction_pc 146 (by decide) (by decide)]; rfl
@[simp] theorem pc2958 : Artifact.submissionArtifact.instructionPC 147 = 235 :=
  by rw [scan_instruction_pc 147 (by decide) (by decide)]; rfl
@[simp] theorem pc2959 : Artifact.submissionArtifact.instructionPC 148 = 236 :=
  by rw [scan_instruction_pc 148 (by decide) (by decide)]; rfl
@[simp] theorem pc2960 : Artifact.submissionArtifact.instructionPC 149 = 238 :=
  by rw [scan_instruction_pc 149 (by decide) (by decide)]; rfl
@[simp] theorem pc2961 : Artifact.submissionArtifact.instructionPC 150 = 239 :=
  by rw [scan_instruction_pc 150 (by decide) (by decide)]; rfl
@[simp] theorem pc2962 : Artifact.submissionArtifact.instructionPC 151 = 240 :=
  by rw [scan_instruction_pc 151 (by decide) (by decide)]; rfl
@[simp] theorem pc2963 : Artifact.submissionArtifact.instructionPC 152 = 242 :=
  by rw [scan_instruction_pc 152 (by decide) (by decide)]; rfl
@[simp] theorem pc2964 : Artifact.submissionArtifact.instructionPC 153 = 243 :=
  by rw [scan_instruction_pc 153 (by decide) (by decide)]; rfl
@[simp] theorem pc2965 : Artifact.submissionArtifact.instructionPC 154 = 244 :=
  by rw [scan_instruction_pc 154 (by decide) (by decide)]; rfl
@[simp] theorem pc2966 : Artifact.submissionArtifact.instructionPC 155 = 245 :=
  by rw [scan_instruction_pc 155 (by decide) (by decide)]; rfl
@[simp] theorem pc2967 : Artifact.submissionArtifact.instructionPC 156 = 246 :=
  by rw [scan_instruction_pc 156 (by decide) (by decide)]; rfl
@[simp] theorem pc2968 : Artifact.submissionArtifact.instructionPC 157 = 247 :=
  by rw [scan_instruction_pc 157 (by decide) (by decide)]; rfl
@[simp] theorem pc2969 : Artifact.submissionArtifact.instructionPC 158 = 249 :=
  by rw [scan_instruction_pc 158 (by decide) (by decide)]; rfl
@[simp] theorem pc2969a : Artifact.submissionArtifact.instructionPC 164 = 259 :=
  by rw [scan_instruction_pc 164 (by decide) (by decide)]; rfl
@[simp] theorem pc2970 : Artifact.submissionArtifact.instructionPC 166 = 261 :=
  by rw [scan_instruction_pc 166 (by decide) (by decide)]; rfl
@[simp] theorem pc2971 : Artifact.submissionArtifact.instructionPC 167 = 262 :=
  by rw [scan_instruction_pc 167 (by decide) (by decide)]; rfl
@[simp] theorem pc2972 : Artifact.submissionArtifact.instructionPC 168 = 263 :=
  by rw [scan_instruction_pc 168 (by decide) (by decide)]; rfl
@[simp] theorem pc2973 : Artifact.submissionArtifact.instructionPC 169 = 264 :=
  by rw [scan_instruction_pc 169 (by decide) (by decide)]; rfl
@[simp] theorem pc2974 : Artifact.submissionArtifact.instructionPC 170 = 265 :=
  by rw [scan_instruction_pc 170 (by decide) (by decide)]; rfl
@[simp] theorem pc2975 : Artifact.submissionArtifact.instructionPC 171 = 266 :=
  by rw [scan_instruction_pc 171 (by decide) (by decide)]; rfl
@[simp] theorem pc2976 : Artifact.submissionArtifact.instructionPC 172 = 267 :=
  by rw [scan_instruction_pc 172 (by decide) (by decide)]; rfl
@[simp] theorem pc2977 : Artifact.submissionArtifact.instructionPC 173 = 268 :=
  by rw [scan_instruction_pc 173 (by decide) (by decide)]; rfl
@[simp] theorem pc2978 : Artifact.submissionArtifact.instructionPC 174 = 269 :=
  by rw [scan_instruction_pc 174 (by decide) (by decide)]; rfl
@[simp] theorem pc2979 : Artifact.submissionArtifact.instructionPC 175 = 270 :=
  by rw [scan_instruction_pc 175 (by decide) (by decide)]; rfl
@[simp] theorem pc2980 : Artifact.submissionArtifact.instructionPC 176 = 271 :=
  by rw [scan_instruction_pc 176 (by decide) (by decide)]; rfl
@[simp] theorem pc2981 : Artifact.submissionArtifact.instructionPC 177 = 272 :=
  by rw [scan_instruction_pc 177 (by decide) (by decide)]; rfl
@[simp] theorem pc2982 : Artifact.submissionArtifact.instructionPC 178 = 275 :=
  by rw [scan_instruction_pc 178 (by decide) (by decide)]; rfl






@[simp] theorem pc_ins217 : Artifact.submissionArtifact.instructionPC 154 = 244 :=
  by rw [scan_instruction_pc 154 (by decide) (by decide)]; rfl
@[simp] theorem pc_ins218 : Artifact.submissionArtifact.instructionPC 155 = 245 :=
  by rw [scan_instruction_pc 155 (by decide) (by decide)]; rfl
@[simp] theorem pc_ins219 : Artifact.submissionArtifact.instructionPC 156 = 246 :=
  by rw [scan_instruction_pc 156 (by decide) (by decide)]; rfl
@[simp] theorem pc_ins220 : Artifact.submissionArtifact.instructionPC 157 = 247 :=
  by rw [scan_instruction_pc 157 (by decide) (by decide)]; rfl
@[simp] theorem pc_ins221 : Artifact.submissionArtifact.instructionPC 158 = 249 :=
  by rw [scan_instruction_pc 158 (by decide) (by decide)]; rfl






@[simp] theorem pc2989 : Artifact.submissionArtifact.instructionPC 100 = 175 :=
  by rw [scan_instruction_pc 100 (by decide) (by decide)]; rfl
@[simp] theorem pc2990 : Artifact.submissionArtifact.instructionPC 100 = 175 :=
  by rw [scan_instruction_pc 100 (by decide) (by decide)]; rfl
@[simp] theorem pc2991 : Artifact.submissionArtifact.instructionPC 101 = 176 :=
  by rw [scan_instruction_pc 101 (by decide) (by decide)]; rfl
@[simp] theorem pc2992 : Artifact.submissionArtifact.instructionPC 102 = 177 :=
  by rw [scan_instruction_pc 102 (by decide) (by decide)]; rfl
@[simp] theorem pc2993 : Artifact.submissionArtifact.instructionPC 103 = 179 :=
  by rw [scan_instruction_pc 103 (by decide) (by decide)]; rfl
@[simp] theorem pc2994 : Artifact.submissionArtifact.instructionPC 104 = 180 :=
  by rw [scan_instruction_pc 104 (by decide) (by decide)]; rfl
@[simp] theorem pc2995 : Artifact.submissionArtifact.instructionPC 105 = 182 :=
  by rw [scan_instruction_pc 105 (by decide) (by decide)]; rfl
@[simp] theorem pc2996 : Artifact.submissionArtifact.instructionPC 106 = 183 :=
  by rw [scan_instruction_pc 106 (by decide) (by decide)]; rfl
@[simp] theorem pc2997 : Artifact.submissionArtifact.instructionPC 107 = 185 :=
  by rw [scan_instruction_pc 107 (by decide) (by decide)]; rfl
@[simp] theorem pc2998 : Artifact.submissionArtifact.instructionPC 108 = 186 :=
  by rw [scan_instruction_pc 108 (by decide) (by decide)]; rfl
@[simp] theorem pc2999 : Artifact.submissionArtifact.instructionPC 108 = 186 :=
  by rw [scan_instruction_pc 108 (by decide) (by decide)]; rfl
@[simp] theorem pc3000 : Artifact.submissionArtifact.instructionPC 108 = 186 :=
  by rw [scan_instruction_pc 108 (by decide) (by decide)]; rfl
@[simp] theorem pc3001 : Artifact.submissionArtifact.instructionPC 109 = 187 :=
  by rw [scan_instruction_pc 109 (by decide) (by decide)]; rfl
@[simp] theorem pc3002 : Artifact.submissionArtifact.instructionPC 110 = 189 :=
  by rw [scan_instruction_pc 110 (by decide) (by decide)]; rfl
@[simp] theorem pc3003 : Artifact.submissionArtifact.instructionPC 111 = 190 :=
  by rw [scan_instruction_pc 111 (by decide) (by decide)]; rfl
@[simp] theorem pc3004 : Artifact.submissionArtifact.instructionPC 112 = 191 :=
  by rw [scan_instruction_pc 112 (by decide) (by decide)]; rfl
@[simp] theorem pc3005 : Artifact.submissionArtifact.instructionPC 113 = 192 :=
  by rw [scan_instruction_pc 113 (by decide) (by decide)]; rfl
@[simp] theorem pc3006 : Artifact.submissionArtifact.instructionPC 114 = 193 :=
  by rw [scan_instruction_pc 114 (by decide) (by decide)]; rfl
@[simp] theorem pc3007 : Artifact.submissionArtifact.instructionPC 115 = 194 :=
  by rw [scan_instruction_pc 115 (by decide) (by decide)]; rfl
@[simp] theorem pc3008 : Artifact.submissionArtifact.instructionPC 116 = 195 :=
  by rw [scan_instruction_pc 116 (by decide) (by decide)]; rfl
@[simp] theorem pc3009 : Artifact.submissionArtifact.instructionPC 117 = 196 :=
  by rw [scan_instruction_pc 117 (by decide) (by decide)]; rfl
@[simp] theorem pc3010 : Artifact.submissionArtifact.instructionPC 118 = 197 :=
  by rw [scan_instruction_pc 118 (by decide) (by decide)]; rfl
@[simp] theorem pc3011 : Artifact.submissionArtifact.instructionPC 119 = 198 :=
  by rw [scan_instruction_pc 119 (by decide) (by decide)]; rfl
@[simp] theorem pc3012 : Artifact.submissionArtifact.instructionPC 120 = 199 :=
  by rw [scan_instruction_pc 120 (by decide) (by decide)]; rfl
@[simp] theorem pc3013 : Artifact.submissionArtifact.instructionPC 121 = 200 :=
  by rw [scan_instruction_pc 121 (by decide) (by decide)]; rfl
@[simp] theorem pc3014 : Artifact.submissionArtifact.instructionPC 122 = 201 :=
  by rw [scan_instruction_pc 122 (by decide) (by decide)]; rfl
@[simp] theorem pc3015 : Artifact.submissionArtifact.instructionPC 123 = 202 :=
  by rw [scan_instruction_pc 123 (by decide) (by decide)]; rfl
@[simp] theorem pc3016 : Artifact.submissionArtifact.instructionPC 124 = 203 :=
  by rw [scan_instruction_pc 124 (by decide) (by decide)]; rfl
@[simp] theorem pc3017 : Artifact.submissionArtifact.instructionPC 125 = 205 :=
  by rw [scan_instruction_pc 125 (by decide) (by decide)]; rfl
@[simp] theorem pc3018 : Artifact.submissionArtifact.instructionPC 126 = 206 :=
  by rw [scan_instruction_pc 126 (by decide) (by decide)]; rfl
@[simp] theorem pc3019 : Artifact.submissionArtifact.instructionPC 127 = 207 :=
  by rw [scan_instruction_pc 127 (by decide) (by decide)]; rfl
#print axioms scan_instruction_at
#print axioms scan_instruction_pc
#print axioms setupPath
#print axioms wordPath
#print axioms comparePath
#print axioms tailPath
#print axioms straddleCorrPath
#print axioms straddleAddPath
#print axioms straddleBackPath
#print axioms pc2903

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan
