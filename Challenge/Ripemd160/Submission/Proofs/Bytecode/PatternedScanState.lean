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
  scanPrefix ++ submissionInstructionsChunk0.take 56

private def scanSuffix : List YulEvmCompiler.Instr :=
  submissionInstructionsChunk0.drop 56 ++ submissionInstructionsChunk1 ++ submissionInstructionsChunk2 ++ submissionInstructionsChunk3 ++ submissionInstructionsChunk4 ++ submissionInstructionsChunk5 ++ submissionInstructionsChunk6 ++ submissionInstructionsChunk7 ++ submissionInstructionsChunk8 ++ submissionInstructionsChunk9 ++ submissionInstructionsChunk10 ++ submissionInstructionsChunk11 ++ submissionInstructionsChunk12 ++ submissionInstructionsChunk13 ++ submissionInstructionsChunk14 ++ submissionInstructionsChunk15 ++ submissionInstructionsChunk16 ++ submissionInstructionsChunk17 ++ submissionInstructionsChunk18 ++ submissionInstructionsChunk19 ++ submissionInstructionsChunk20

private theorem scanBefore_length : scanBefore.length = 56 := by
  simp [scanBefore, scanPrefix]

private theorem scanSuffix_length : scanSuffix.length = 3932 := by
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
      submissionInstructionsChunk0.take 56 ++ submissionInstructionsChunk0.drop 56 := by
    exact (List.take_append_drop 56 submissionInstructionsChunk0).symm
  rw [hprefix]
  conv_lhs => rw [hchunk]
  simp only [scanBefore, scanSuffix, List.append_assoc, List.append_nil]

private theorem scanBefore_pc :
    (YulEvmCompiler.assembleBytes scanBefore).length = 76 := by rfl

private theorem artifact_instruction_projection :
    Artifact.submissionArtifact.instructions = Artifact.submissionInstructions := by rfl

private theorem scan_instruction_at (index : Nat)
    (hlo : 56 ≤ index) (hhi : index < 3988) :
    Artifact.submissionInstructions[index]? = scanSuffix[index - 56]? := by
  have hi : index - 56 < scanSuffix.length := by
    rw [scanSuffix_length]
    omega
  have h := ArtifactSegment.getElem?_segment Artifact.submissionArtifact
    scanBefore scanSuffix [] artifact_scan_split (index - 56) hi
  simpa only [artifact_instruction_projection, scanBefore_length,
    Nat.add_sub_of_le hlo] using h

private theorem scan_instruction_pc (index : Nat)
    (hlo : 56 ≤ index) (hhi : index ≤ 3988) :
    Artifact.submissionArtifact.instructionPC index =
      76 + (YulEvmCompiler.assembleBytes (scanSuffix.take (index - 56))).length := by
  have hi : index - 56 ≤ scanSuffix.length := by
    rw [scanSuffix_length]
    omega
  have h := ArtifactSegment.instructionPC_segment_of_bounds Artifact.submissionArtifact
    scanBefore scanSuffix [] 56 76 artifact_scan_split scanBefore_length
    scanBefore_pc (index - 56) hi
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
  [pushAt 66 1 255,
   pushAt 67 0 0,
   opAt 68 .NOT,
   opAt 69 .DIV,
   pushAt 70 32 3244493450063667868678674439968361782956185527883176199882357678282131398018,
   opAt 71 (.Dup ⟨1, by decide⟩),
   pushAt 72 1 7,
   opAt 73 .SHL,
   opAt 74 (.Dup ⟨0, by decide⟩),
   opAt 75 .NOT,
   opAt 76 (.Swap ⟨0, by decide⟩),
   opAt 77 (.Swap ⟨2, by decide⟩),
   opAt 78 (.Dup ⟨2, by decide⟩),
   opAt 79 (.Dup ⟨2, by decide⟩),
   opAt 80 .AND,
   pushAt 81 0 0,
   pushAt 82 0 0,
   pushAt 83 0 0]

/-- Derive the expected word and test for a straddler. -/
def wordPath : List Located :=
  [opAt 84 .JUMPDEST, opAt 85 (.Dup ⟨0, by decide⟩),
   opAt 86 (.Dup ⟨5, by decide⟩), opAt 87 .MUL,
   opAt 88 (.Dup ⟨6, by decide⟩), opAt 89 (.Dup ⟨1, by decide⟩),
   opAt 90 .AND, opAt 91 (.Dup ⟨5, by decide⟩), opAt 92 .ADD,
   opAt 93 (.Dup ⟨1, by decide⟩), opAt 94 (.Dup ⟨9, by decide⟩),
   opAt 95 .XOR, opAt 96 (.Dup ⟨10, by decide⟩), opAt 97 .AND,
   opAt 98 .XOR, opAt 99 (.Dup ⟨3, by decide⟩), opAt 100 .NOT,
   pushAt 101 1 224, opAt 102 .AND, pushAt 103 1 215,
   opAt 104 .JUMPI]

/-- Fold one word into the accumulator and advance. -/
def comparePath : List Located :=
  [opAt 132 .JUMPDEST,
   opAt 133 (.Dup ⟨3, by decide⟩),
   opAt 134 .CALLDATALOAD,
   opAt 135 .XOR,
   pushAt 136 5 4446160832,
   opAt 137 (.Dup ⟨4, by decide⟩),
   opAt 138 .CALLDATASIZE,
   opAt 139 .SUB,
   opAt 142 .SHR,
   pushAt 143 1 248,
   opAt 144 .AND,
   opAt 145 .SHR,
   opAt 146 (.Dup ⟨4, by decide⟩),
   opAt 147 .OR,
   opAt 148 (.Swap ⟨3, by decide⟩),
   opAt 149 .POP,
   opAt 150 .POP,
   pushAt 151 1 160,
   opAt 152 .ADD,
   pushAt 153 1 255,
   opAt 154 .AND,
   opAt 155 (.Swap ⟨0, by decide⟩),
   pushAt 156 1 32,
   opAt 157 .ADD,
   opAt 158 (.Swap ⟨0, by decide⟩),
   opAt 159 .CALLDATASIZE,
   opAt 160 (.Dup ⟨2, by decide⟩),
   opAt 161 .LT,
   pushAt 162 1 160,
   opAt 163 .JUMPI,
   opAt 164 (.Dup ⟨2, by decide⟩)]

/-- The padded tail word, the cleanup and the miss test. -/
def tailPath : List Located :=
  [opAt 168 .POP, opAt 169 .POP, opAt 170 .POP,
   opAt 171 .POP, opAt 172 .POP, opAt 173 .POP, opAt 174 .POP, opAt 175 .POP]

/-- Shift the correction constant out of `M`. -/
def straddleCorrPath : List Located :=
  [opAt 105 (.Dup ⟨6, by decide⟩),
   opAt 106 (.Dup ⟨4, by decide⟩), pushAt 107 1 8, opAt 108 .SHR,
   pushAt 109 1 40, opAt 110 .MUL, pushAt 111 1 216, opAt 112 .SUB,
   opAt 113 .SHR, pushAt 114 1 11,
   opAt 115 .MUL]

/-- Apply the correction to the expected word. -/
def straddleAddPath : List Located :=
  [opAt 116 (.Dup ⟨1, by decide⟩), opAt 117 (.Dup ⟨9, by decide⟩),
   opAt 118 .AND, opAt 119 (.Dup ⟨1, by decide⟩), opAt 120 .ADD,
   opAt 121 (.Dup ⟨2, by decide⟩), opAt 122 (.Dup ⟨12, by decide⟩),
   opAt 123 .AND, opAt 124 .XOR, opAt 125 (.Swap ⟨1, by decide⟩),
   opAt 126 .POP, opAt 127 .POP]

/-- Bump the scalar and rejoin the scan. -/
def straddleBackPath : List Located :=
  [opAt 128 (.Swap ⟨1, by decide⟩), pushAt 129 1 11, opAt 130 .ADD,
   opAt 131 (.Swap ⟨1, by decide⟩)]


@[simp] theorem pc2903 : Artifact.submissionArtifact.instructionPC 66 = 108 :=
  by rw [scan_instruction_pc 66 (by decide) (by decide)]; rfl
@[simp] theorem pc2904 : Artifact.submissionArtifact.instructionPC 66 = 108 :=
  by rw [scan_instruction_pc 66 (by decide) (by decide)]; rfl
@[simp] theorem pc2905 : Artifact.submissionArtifact.instructionPC 70 = 113 :=
  by rw [scan_instruction_pc 70 (by decide) (by decide)]; rfl
@[simp] theorem pc2906 : Artifact.submissionArtifact.instructionPC 75 = 151 :=
  by rw [scan_instruction_pc 75 (by decide) (by decide)]; rfl
@[simp] theorem pc2907 : Artifact.submissionArtifact.instructionPC 77 = 153 :=
  by rw [scan_instruction_pc 77 (by decide) (by decide)]; rfl
@[simp] theorem pc2908 : Artifact.submissionArtifact.instructionPC 78 = 154 :=
  by rw [scan_instruction_pc 78 (by decide) (by decide)]; rfl
@[simp] theorem pc2909 : Artifact.submissionArtifact.instructionPC 79 = 155 :=
  by rw [scan_instruction_pc 79 (by decide) (by decide)]; rfl
@[simp] theorem pc2910 : Artifact.submissionArtifact.instructionPC 80 = 156 :=
  by rw [scan_instruction_pc 80 (by decide) (by decide)]; rfl
@[simp] theorem pc2911 : Artifact.submissionArtifact.instructionPC 81 = 157 :=
  by rw [scan_instruction_pc 81 (by decide) (by decide)]; rfl
@[simp] theorem pc2912 : Artifact.submissionArtifact.instructionPC 82 = 158 :=
  by rw [scan_instruction_pc 82 (by decide) (by decide)]; rfl
@[simp] theorem pc2913 : Artifact.submissionArtifact.instructionPC 83 = 159 :=
  by rw [scan_instruction_pc 83 (by decide) (by decide)]; rfl
@[simp] theorem pc2914 : Artifact.submissionArtifact.instructionPC 84 = 160 :=
  by rw [scan_instruction_pc 84 (by decide) (by decide)]; rfl
@[simp] theorem pc2915 : Artifact.submissionArtifact.instructionPC 85 = 161 :=
  by rw [scan_instruction_pc 85 (by decide) (by decide)]; rfl
@[simp] theorem pc2916 : Artifact.submissionArtifact.instructionPC 86 = 162 :=
  by rw [scan_instruction_pc 86 (by decide) (by decide)]; rfl
@[simp] theorem pc2917 : Artifact.submissionArtifact.instructionPC 87 = 163 :=
  by rw [scan_instruction_pc 87 (by decide) (by decide)]; rfl
@[simp] theorem pc2918 : Artifact.submissionArtifact.instructionPC 88 = 164 :=
  by rw [scan_instruction_pc 88 (by decide) (by decide)]; rfl
@[simp] theorem pc2919 : Artifact.submissionArtifact.instructionPC 89 = 165 :=
  by rw [scan_instruction_pc 89 (by decide) (by decide)]; rfl
@[simp] theorem pc2920 : Artifact.submissionArtifact.instructionPC 90 = 166 :=
  by rw [scan_instruction_pc 90 (by decide) (by decide)]; rfl
@[simp] theorem pc2921 : Artifact.submissionArtifact.instructionPC 91 = 167 :=
  by rw [scan_instruction_pc 91 (by decide) (by decide)]; rfl
@[simp] theorem pc2922 : Artifact.submissionArtifact.instructionPC 92 = 168 :=
  by rw [scan_instruction_pc 92 (by decide) (by decide)]; rfl
@[simp] theorem pc2923 : Artifact.submissionArtifact.instructionPC 93 = 169 :=
  by rw [scan_instruction_pc 93 (by decide) (by decide)]; rfl
@[simp] theorem pc2924 : Artifact.submissionArtifact.instructionPC 94 = 170 :=
  by rw [scan_instruction_pc 94 (by decide) (by decide)]; rfl
@[simp] theorem pc2925 : Artifact.submissionArtifact.instructionPC 95 = 171 :=
  by rw [scan_instruction_pc 95 (by decide) (by decide)]; rfl
@[simp] theorem pc2926 : Artifact.submissionArtifact.instructionPC 96 = 172 :=
  by rw [scan_instruction_pc 96 (by decide) (by decide)]; rfl
@[simp] theorem pc2927 : Artifact.submissionArtifact.instructionPC 97 = 173 :=
  by rw [scan_instruction_pc 97 (by decide) (by decide)]; rfl
@[simp] theorem pc2928 : Artifact.submissionArtifact.instructionPC 98 = 174 :=
  by rw [scan_instruction_pc 98 (by decide) (by decide)]; rfl
@[simp] theorem pc2929 : Artifact.submissionArtifact.instructionPC 99 = 175 :=
  by rw [scan_instruction_pc 99 (by decide) (by decide)]; rfl
@[simp] theorem pc2930 : Artifact.submissionArtifact.instructionPC 100 = 176 :=
  by rw [scan_instruction_pc 100 (by decide) (by decide)]; rfl
@[simp] theorem pc2931 : Artifact.submissionArtifact.instructionPC 101 = 177 :=
  by rw [scan_instruction_pc 101 (by decide) (by decide)]; rfl
@[simp] theorem pc2932 : Artifact.submissionArtifact.instructionPC 102 = 179 :=
  by rw [scan_instruction_pc 102 (by decide) (by decide)]; rfl
@[simp] theorem pc2934 : Artifact.submissionArtifact.instructionPC 103 = 180 :=
  by rw [scan_instruction_pc 103 (by decide) (by decide)]; rfl
@[simp] theorem pc2935 : Artifact.submissionArtifact.instructionPC 104 = 182 :=
  by rw [scan_instruction_pc 104 (by decide) (by decide)]; rfl
@[simp] theorem pc2936 : Artifact.submissionArtifact.instructionPC 132 = 215 :=
  by rw [scan_instruction_pc 132 (by decide) (by decide)]; rfl
@[simp] theorem pc2937 : Artifact.submissionArtifact.instructionPC 133 = 216 :=
  by rw [scan_instruction_pc 133 (by decide) (by decide)]; rfl
@[simp] theorem pc2938 : Artifact.submissionArtifact.instructionPC 134 = 217 :=
  by rw [scan_instruction_pc 134 (by decide) (by decide)]; rfl
@[simp] theorem pc2939 : Artifact.submissionArtifact.instructionPC 135 = 218 :=
  by rw [scan_instruction_pc 135 (by decide) (by decide)]; rfl
@[simp] theorem pc2940 : Artifact.submissionArtifact.instructionPC 146 = 236 :=
  by rw [scan_instruction_pc 146 (by decide) (by decide)]; rfl
@[simp] theorem pc2941 : Artifact.submissionArtifact.instructionPC 147 = 237 :=
  by rw [scan_instruction_pc 147 (by decide) (by decide)]; rfl
@[simp] theorem pc2942 : Artifact.submissionArtifact.instructionPC 148 = 238 :=
  by rw [scan_instruction_pc 148 (by decide) (by decide)]; rfl
@[simp] theorem pc2943 : Artifact.submissionArtifact.instructionPC 149 = 239 :=
  by rw [scan_instruction_pc 149 (by decide) (by decide)]; rfl
@[simp] theorem pc2944 : Artifact.submissionArtifact.instructionPC 150 = 240 :=
  by rw [scan_instruction_pc 150 (by decide) (by decide)]; rfl
@[simp] theorem pc2945 : Artifact.submissionArtifact.instructionPC 151 = 241 :=
  by rw [scan_instruction_pc 151 (by decide) (by decide)]; rfl
@[simp] theorem pc2946 : Artifact.submissionArtifact.instructionPC 151 = 241 :=
  by rw [scan_instruction_pc 151 (by decide) (by decide)]; rfl
@[simp] theorem pc2947 : Artifact.submissionArtifact.instructionPC 152 = 243 :=
  by rw [scan_instruction_pc 152 (by decide) (by decide)]; rfl
@[simp] theorem pc2948 : Artifact.submissionArtifact.instructionPC 153 = 244 :=
  by rw [scan_instruction_pc 153 (by decide) (by decide)]; rfl
@[simp] theorem pc2949 : Artifact.submissionArtifact.instructionPC 154 = 246 :=
  by rw [scan_instruction_pc 154 (by decide) (by decide)]; rfl
@[simp] theorem pc2950 : Artifact.submissionArtifact.instructionPC 155 = 247 :=
  by rw [scan_instruction_pc 155 (by decide) (by decide)]; rfl
@[simp] theorem pc2951 : Artifact.submissionArtifact.instructionPC 155 = 247 :=
  by rw [scan_instruction_pc 155 (by decide) (by decide)]; rfl
@[simp] theorem pc2952 : Artifact.submissionArtifact.instructionPC 155 = 247 :=
  by rw [scan_instruction_pc 155 (by decide) (by decide)]; rfl
@[simp] theorem pc2953 : Artifact.submissionArtifact.instructionPC 156 = 248 :=
  by rw [scan_instruction_pc 156 (by decide) (by decide)]; rfl
@[simp] theorem pc2954 : Artifact.submissionArtifact.instructionPC 157 = 250 :=
  by rw [scan_instruction_pc 157 (by decide) (by decide)]; rfl
@[simp] theorem pc2955 : Artifact.submissionArtifact.instructionPC 158 = 251 :=
  by rw [scan_instruction_pc 158 (by decide) (by decide)]; rfl
@[simp] theorem pc2956 : Artifact.submissionArtifact.instructionPC 151 = 241 :=
  by rw [scan_instruction_pc 151 (by decide) (by decide)]; rfl
@[simp] theorem pc2957 : Artifact.submissionArtifact.instructionPC 151 = 241 :=
  by rw [scan_instruction_pc 151 (by decide) (by decide)]; rfl
@[simp] theorem pc2958 : Artifact.submissionArtifact.instructionPC 152 = 243 :=
  by rw [scan_instruction_pc 152 (by decide) (by decide)]; rfl
@[simp] theorem pc2959 : Artifact.submissionArtifact.instructionPC 153 = 244 :=
  by rw [scan_instruction_pc 153 (by decide) (by decide)]; rfl
@[simp] theorem pc2960 : Artifact.submissionArtifact.instructionPC 154 = 246 :=
  by rw [scan_instruction_pc 154 (by decide) (by decide)]; rfl
@[simp] theorem pc2961 : Artifact.submissionArtifact.instructionPC 155 = 247 :=
  by rw [scan_instruction_pc 155 (by decide) (by decide)]; rfl
@[simp] theorem pc2962 : Artifact.submissionArtifact.instructionPC 156 = 248 :=
  by rw [scan_instruction_pc 156 (by decide) (by decide)]; rfl
@[simp] theorem pc2963 : Artifact.submissionArtifact.instructionPC 157 = 250 :=
  by rw [scan_instruction_pc 157 (by decide) (by decide)]; rfl
@[simp] theorem pc2964 : Artifact.submissionArtifact.instructionPC 158 = 251 :=
  by rw [scan_instruction_pc 158 (by decide) (by decide)]; rfl
@[simp] theorem pc2965 : Artifact.submissionArtifact.instructionPC 159 = 252 :=
  by rw [scan_instruction_pc 159 (by decide) (by decide)]; rfl
@[simp] theorem pc2966 : Artifact.submissionArtifact.instructionPC 160 = 253 :=
  by rw [scan_instruction_pc 160 (by decide) (by decide)]; rfl
@[simp] theorem pc2967 : Artifact.submissionArtifact.instructionPC 161 = 254 :=
  by rw [scan_instruction_pc 161 (by decide) (by decide)]; rfl
@[simp] theorem pc2968 : Artifact.submissionArtifact.instructionPC 162 = 255 :=
  by rw [scan_instruction_pc 162 (by decide) (by decide)]; rfl
@[simp] theorem pc2969 : Artifact.submissionArtifact.instructionPC 163 = 257 :=
  by rw [scan_instruction_pc 163 (by decide) (by decide)]; rfl
@[simp] theorem pc2969a : Artifact.submissionArtifact.instructionPC 168 = 264 :=
  by rw [scan_instruction_pc 168 (by decide) (by decide)]; rfl
@[simp] theorem pc2970 : Artifact.submissionArtifact.instructionPC 169 = 265 :=
  by rw [scan_instruction_pc 169 (by decide) (by decide)]; rfl
@[simp] theorem pc2971 : Artifact.submissionArtifact.instructionPC 170 = 266 :=
  by rw [scan_instruction_pc 170 (by decide) (by decide)]; rfl
@[simp] theorem pc2972 : Artifact.submissionArtifact.instructionPC 171 = 267 :=
  by rw [scan_instruction_pc 171 (by decide) (by decide)]; rfl
@[simp] theorem pc2973 : Artifact.submissionArtifact.instructionPC 172 = 268 :=
  by rw [scan_instruction_pc 172 (by decide) (by decide)]; rfl
@[simp] theorem pc2974 : Artifact.submissionArtifact.instructionPC 168 = 264 :=
  by rw [scan_instruction_pc 168 (by decide) (by decide)]; rfl
@[simp] theorem pc2975 : Artifact.submissionArtifact.instructionPC 169 = 265 :=
  by rw [scan_instruction_pc 169 (by decide) (by decide)]; rfl
@[simp] theorem pc2976 : Artifact.submissionArtifact.instructionPC 170 = 266 :=
  by rw [scan_instruction_pc 170 (by decide) (by decide)]; rfl
@[simp] theorem pc2977 : Artifact.submissionArtifact.instructionPC 171 = 267 :=
  by rw [scan_instruction_pc 171 (by decide) (by decide)]; rfl
@[simp] theorem pc2978 : Artifact.submissionArtifact.instructionPC 172 = 268 :=
  by rw [scan_instruction_pc 172 (by decide) (by decide)]; rfl
@[simp] theorem pc2979 : Artifact.submissionArtifact.instructionPC 173 = 269 :=
  by rw [scan_instruction_pc 173 (by decide) (by decide)]; rfl
@[simp] theorem pc2980 : Artifact.submissionArtifact.instructionPC 174 = 270 :=
  by rw [scan_instruction_pc 174 (by decide) (by decide)]; rfl
@[simp] theorem pc2981 : Artifact.submissionArtifact.instructionPC 180 = 282 :=
  by rw [scan_instruction_pc 180 (by decide) (by decide)]; rfl
@[simp] theorem pc2982 : Artifact.submissionArtifact.instructionPC 181 = 287 :=
  by rw [scan_instruction_pc 181 (by decide) (by decide)]; rfl






@[simp] theorem pc_ins217 : Artifact.submissionArtifact.instructionPC 159 = 252 :=
  by rw [scan_instruction_pc 159 (by decide) (by decide)]; rfl
@[simp] theorem pc_ins218 : Artifact.submissionArtifact.instructionPC 160 = 253 :=
  by rw [scan_instruction_pc 160 (by decide) (by decide)]; rfl
@[simp] theorem pc_ins219 : Artifact.submissionArtifact.instructionPC 161 = 254 :=
  by rw [scan_instruction_pc 161 (by decide) (by decide)]; rfl
@[simp] theorem pc_ins220 : Artifact.submissionArtifact.instructionPC 162 = 255 :=
  by rw [scan_instruction_pc 162 (by decide) (by decide)]; rfl
@[simp] theorem pc_ins221 : Artifact.submissionArtifact.instructionPC 163 = 257 :=
  by rw [scan_instruction_pc 163 (by decide) (by decide)]; rfl






@[simp] theorem pc2989 : Artifact.submissionArtifact.instructionPC 105 = 183 :=
  by rw [scan_instruction_pc 105 (by decide) (by decide)]; rfl
@[simp] theorem pc2990 : Artifact.submissionArtifact.instructionPC 105 = 183 :=
  by rw [scan_instruction_pc 105 (by decide) (by decide)]; rfl
@[simp] theorem pc2991 : Artifact.submissionArtifact.instructionPC 106 = 184 :=
  by rw [scan_instruction_pc 106 (by decide) (by decide)]; rfl
@[simp] theorem pc2992 : Artifact.submissionArtifact.instructionPC 107 = 185 :=
  by rw [scan_instruction_pc 107 (by decide) (by decide)]; rfl
@[simp] theorem pc2993 : Artifact.submissionArtifact.instructionPC 108 = 187 :=
  by rw [scan_instruction_pc 108 (by decide) (by decide)]; rfl
@[simp] theorem pc2994 : Artifact.submissionArtifact.instructionPC 109 = 188 :=
  by rw [scan_instruction_pc 109 (by decide) (by decide)]; rfl
@[simp] theorem pc2995 : Artifact.submissionArtifact.instructionPC 110 = 190 :=
  by rw [scan_instruction_pc 110 (by decide) (by decide)]; rfl
@[simp] theorem pc2996 : Artifact.submissionArtifact.instructionPC 111 = 191 :=
  by rw [scan_instruction_pc 111 (by decide) (by decide)]; rfl
@[simp] theorem pc2997 : Artifact.submissionArtifact.instructionPC 112 = 193 :=
  by rw [scan_instruction_pc 112 (by decide) (by decide)]; rfl
@[simp] theorem pc2998 : Artifact.submissionArtifact.instructionPC 113 = 194 :=
  by rw [scan_instruction_pc 113 (by decide) (by decide)]; rfl
@[simp] theorem pc2999 : Artifact.submissionArtifact.instructionPC 113 = 194 :=
  by rw [scan_instruction_pc 113 (by decide) (by decide)]; rfl
@[simp] theorem pc3000 : Artifact.submissionArtifact.instructionPC 113 = 194 :=
  by rw [scan_instruction_pc 113 (by decide) (by decide)]; rfl
@[simp] theorem pc3001 : Artifact.submissionArtifact.instructionPC 114 = 195 :=
  by rw [scan_instruction_pc 114 (by decide) (by decide)]; rfl
@[simp] theorem pc3002 : Artifact.submissionArtifact.instructionPC 115 = 197 :=
  by rw [scan_instruction_pc 115 (by decide) (by decide)]; rfl
@[simp] theorem pc3003 : Artifact.submissionArtifact.instructionPC 116 = 198 :=
  by rw [scan_instruction_pc 116 (by decide) (by decide)]; rfl
@[simp] theorem pc3004 : Artifact.submissionArtifact.instructionPC 117 = 199 :=
  by rw [scan_instruction_pc 117 (by decide) (by decide)]; rfl
@[simp] theorem pc3005 : Artifact.submissionArtifact.instructionPC 118 = 200 :=
  by rw [scan_instruction_pc 118 (by decide) (by decide)]; rfl
@[simp] theorem pc3006 : Artifact.submissionArtifact.instructionPC 119 = 201 :=
  by rw [scan_instruction_pc 119 (by decide) (by decide)]; rfl
@[simp] theorem pc3007 : Artifact.submissionArtifact.instructionPC 120 = 202 :=
  by rw [scan_instruction_pc 120 (by decide) (by decide)]; rfl
@[simp] theorem pc3008 : Artifact.submissionArtifact.instructionPC 121 = 203 :=
  by rw [scan_instruction_pc 121 (by decide) (by decide)]; rfl
@[simp] theorem pc3009 : Artifact.submissionArtifact.instructionPC 122 = 204 :=
  by rw [scan_instruction_pc 122 (by decide) (by decide)]; rfl
@[simp] theorem pc3010 : Artifact.submissionArtifact.instructionPC 123 = 205 :=
  by rw [scan_instruction_pc 123 (by decide) (by decide)]; rfl
@[simp] theorem pc3011 : Artifact.submissionArtifact.instructionPC 124 = 206 :=
  by rw [scan_instruction_pc 124 (by decide) (by decide)]; rfl
@[simp] theorem pc3012 : Artifact.submissionArtifact.instructionPC 125 = 207 :=
  by rw [scan_instruction_pc 125 (by decide) (by decide)]; rfl
@[simp] theorem pc3013 : Artifact.submissionArtifact.instructionPC 126 = 208 :=
  by rw [scan_instruction_pc 126 (by decide) (by decide)]; rfl
@[simp] theorem pc3014 : Artifact.submissionArtifact.instructionPC 127 = 209 :=
  by rw [scan_instruction_pc 127 (by decide) (by decide)]; rfl
@[simp] theorem pc3015 : Artifact.submissionArtifact.instructionPC 128 = 210 :=
  by rw [scan_instruction_pc 128 (by decide) (by decide)]; rfl
@[simp] theorem pc3016 : Artifact.submissionArtifact.instructionPC 129 = 211 :=
  by rw [scan_instruction_pc 129 (by decide) (by decide)]; rfl
@[simp] theorem pc3017 : Artifact.submissionArtifact.instructionPC 130 = 213 :=
  by rw [scan_instruction_pc 130 (by decide) (by decide)]; rfl
@[simp] theorem pc3018 : Artifact.submissionArtifact.instructionPC 131 = 214 :=
  by rw [scan_instruction_pc 131 (by decide) (by decide)]; rfl
@[simp] theorem pc3019 : Artifact.submissionArtifact.instructionPC 132 = 215 :=
  by rw [scan_instruction_pc 132 (by decide) (by decide)]; rfl
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
