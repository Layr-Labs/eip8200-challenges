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

private def scanPrefix : List YulEvmCompiler.Instr :=
  []

private def scanBefore : List YulEvmCompiler.Instr :=
  scanPrefix ++ submissionInstructionsChunk0.take 152

private def scanSuffix : List YulEvmCompiler.Instr :=
  submissionInstructionsChunk0.drop 152 ++ submissionInstructionsChunk1 ++ submissionInstructionsChunk2 ++ submissionInstructionsChunk3 ++ submissionInstructionsChunk4 ++ submissionInstructionsChunk5 ++ submissionInstructionsChunk6 ++ submissionInstructionsChunk7 ++ submissionInstructionsChunk8 ++ submissionInstructionsChunk9 ++ submissionInstructionsChunk10 ++ submissionInstructionsChunk11 ++ submissionInstructionsChunk12 ++ submissionInstructionsChunk13 ++ submissionInstructionsChunk14 ++ submissionInstructionsChunk15 ++ submissionInstructionsChunk16 ++ submissionInstructionsChunk17 ++ submissionInstructionsChunk18 ++ submissionInstructionsChunk19 ++ submissionInstructionsChunk20 ++ submissionInstructionsChunk21

private theorem scanBefore_length : scanBefore.length = 152 := by
  simp [scanBefore, scanPrefix]

private theorem scanSuffix_length : scanSuffix.length = 4137 := by
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
    submissionInstructionsChunk20 ++
    submissionInstructionsChunk21 := by
    simp only [Artifact.submissionInstructions, scanPrefix, List.append_assoc, List.nil_append]
  have hchunk : submissionInstructionsChunk0 =
      submissionInstructionsChunk0.take 152 ++ submissionInstructionsChunk0.drop 152 := by
    exact (List.take_append_drop 152 submissionInstructionsChunk0).symm
  rw [hprefix]
  conv_lhs => rw [hchunk]
  simp only [scanBefore, scanSuffix, List.append_assoc, List.append_nil]

private theorem scanBefore_pc :
    (YulEvmCompiler.assembleBytes scanBefore).length = 319 := by rfl

private theorem artifact_instruction_projection :
    Artifact.submissionArtifact.instructions = Artifact.submissionInstructions := by rfl

private theorem scan_instruction_at (index : Nat)
    (hlo : 152 ≤ index) (hhi : index < 4289) :
    Artifact.submissionInstructions[index]? = scanSuffix[index - 152]? := by
  have hi : index - 152 < scanSuffix.length := by
    rw [scanSuffix_length]
    omega
  have h := ArtifactSegment.getElem?_segment Artifact.submissionArtifact
    scanBefore scanSuffix [] artifact_scan_split (index - 152) hi
  simpa only [artifact_instruction_projection, scanBefore_length,
    Nat.add_sub_of_le hlo] using h

private theorem scan_instruction_pc (index : Nat)
    (hlo : 152 ≤ index) (hhi : index ≤ 4289) :
    Artifact.submissionArtifact.instructionPC index =
      319 + (YulEvmCompiler.assembleBytes (scanSuffix.take (index - 152))).length := by
  have hi : index - 152 ≤ scanSuffix.length := by
    rw [scanSuffix_length]
    omega
  have h := ArtifactSegment.instructionPC_segment_of_bounds Artifact.submissionArtifact
    scanBefore scanSuffix [] 152 319 artifact_scan_split scanBefore_length
    scanBefore_pc (index - 152) hi
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
  [pushAt 152 1 255,
   pushAt 153 0 0,
   opAt 154 .NOT,
   opAt 155 .DIV,
   pushAt 156 32 3244493450063667868678674439968361782956185527883176199882357678282131398018,
   opAt 157 (.Dup ⟨1, by decide⟩),
   pushAt 158 1 7,
   opAt 159 .SHL,
   opAt 160 (.Dup ⟨0, by decide⟩),
   opAt 161 .NOT,
   opAt 162 (.Swap ⟨0, by decide⟩),
   opAt 163 (.Swap ⟨2, by decide⟩),
   opAt 164 (.Dup ⟨2, by decide⟩),
   opAt 165 (.Dup ⟨2, by decide⟩),
   opAt 166 .AND,
   pushAt 167 0 0,
   pushAt 168 0 0,
   pushAt 169 0 0]

/-- Derive the expected word and test for a straddler. -/
def wordPath : List Located :=
  [opAt 170 .JUMPDEST, opAt 171 (.Dup ⟨0, by decide⟩),
   opAt 172 (.Dup ⟨5, by decide⟩), opAt 173 .MUL,
   opAt 174 (.Dup ⟨0, by decide⟩), opAt 175 (.Dup ⟨7, by decide⟩),
   opAt 176 .AND, opAt 177 (.Dup ⟨5, by decide⟩), opAt 178 .ADD,
   opAt 179 (.Dup ⟨1, by decide⟩), opAt 180 (.Dup ⟨9, by decide⟩),
   opAt 181 .XOR, opAt 182 (.Dup ⟨10, by decide⟩), opAt 183 .AND,
   opAt 184 .XOR, opAt 185 (.Dup ⟨3, by decide⟩), pushAt 186 1 255,
   opAt 187 .AND, pushAt 188 1 224, opAt 189 .EQ, pushAt 190 2 484,
   opAt 191 .JUMPI]

/-- Fold one word into the accumulator and advance. -/
def comparePath : List Located :=
  [opAt 192 .JUMPDEST, opAt 193 (.Dup ⟨3, by decide⟩),
   opAt 194 .CALLDATALOAD, opAt 195 .XOR, opAt 196 (.Dup ⟨4, by decide⟩),
   opAt 197 .OR, opAt 198 (.Swap ⟨3, by decide⟩), opAt 199 .POP,
   opAt 200 .POP, pushAt 201 1 160,
   opAt 202 .ADD, pushAt 203 1 255, opAt 204 .AND,
   opAt 205 (.Swap ⟨0, by decide⟩), pushAt 206 1 32, opAt 207 .ADD,
   opAt 208 (.Swap ⟨0, by decide⟩), opAt 209 (.Dup ⟨1, by decide⟩), pushAt 210 2 992, opAt 211 .GT,
   pushAt 212 2 371, opAt 213 .JUMPI]

/-- The padded tail word, the cleanup and the miss test. -/
def tailPath : List Located :=
  [opAt 214 (.Dup ⟨1, by decide⟩), opAt 215 .CALLDATALOAD,
   pushAt 216 8 9848759918901945995, pushAt 217 1 192, opAt 218 .SHL,
   opAt 219 .XOR, opAt 220 (.Dup ⟨3, by decide⟩), opAt 221 .OR,
   opAt 222 (.Swap ⟨2, by decide⟩), opAt 223 .POP,
   opAt 224 (.Swap ⟨1, by decide⟩), opAt 225 (.Swap ⟨6, by decide⟩),
   opAt 226 .POP, opAt 227 .POP, opAt 228 .POP, opAt 229 .POP,
   opAt 230 .POP, opAt 231 .POP, opAt 232 .POP, pushAt 233 1 3,
   opAt 234 .JUMPI]

/-- Store and return the stored digest. -/
def returnPath : List Located :=
  [pushAt 235 21 766350606435067737561421097975693824639675460820,
   pushAt 236 0 0, opAt 237 .MSTORE, opAt 238 .MSIZE, pushAt 239 0 0,
   opAt 240 .RETURN]

/-- Shift the correction constant out of `M`. -/
def straddleCorrPath : List Located :=
  [opAt 241 .JUMPDEST, opAt 242 (.Dup ⟨6, by decide⟩),
   opAt 243 (.Dup ⟨4, by decide⟩), pushAt 244 1 8, opAt 245 .SHR,
   pushAt 246 1 5, opAt 247 .MUL, pushAt 248 1 27, opAt 249 .SUB,
   pushAt 250 1 3, opAt 251 .SHL, opAt 252 .SHR, pushAt 253 1 11,
   opAt 254 .MUL]

/-- Apply the correction to the expected word. -/
def straddleAddPath : List Located :=
  [opAt 255 (.Dup ⟨1, by decide⟩), opAt 256 (.Dup ⟨9, by decide⟩),
   opAt 257 .AND, opAt 258 (.Dup ⟨1, by decide⟩), opAt 259 .ADD,
   opAt 260 (.Dup ⟨2, by decide⟩), opAt 261 (.Dup ⟨12, by decide⟩),
   opAt 262 .AND, opAt 263 .XOR, opAt 264 (.Swap ⟨1, by decide⟩),
   opAt 265 .POP, opAt 266 .POP]

/-- Bump the scalar and rejoin the scan. -/
def straddleBackPath : List Located :=
  [opAt 267 (.Swap ⟨1, by decide⟩), pushAt 268 1 11, opAt 269 .ADD,
   opAt 270 (.Swap ⟨1, by decide⟩), pushAt 271 3 397,
   opAt 272 .JUMP]


@[simp] theorem pc2903 : Artifact.submissionArtifact.instructionPC 152 = 0x13f :=
  by rw [scan_instruction_pc 152 (by decide) (by decide)]; rfl
@[simp] theorem pc2904 : Artifact.submissionArtifact.instructionPC 152 = 0x13f :=
  by rw [scan_instruction_pc 152 (by decide) (by decide)]; rfl
@[simp] theorem pc2905 : Artifact.submissionArtifact.instructionPC 156 = 0x144 :=
  by rw [scan_instruction_pc 156 (by decide) (by decide)]; rfl
@[simp] theorem pc2906 : Artifact.submissionArtifact.instructionPC 161 = 0x16a :=
  by rw [scan_instruction_pc 161 (by decide) (by decide)]; rfl
@[simp] theorem pc2907 : Artifact.submissionArtifact.instructionPC 163 = 0x16c :=
  by rw [scan_instruction_pc 163 (by decide) (by decide)]; rfl
@[simp] theorem pc2908 : Artifact.submissionArtifact.instructionPC 164 = 0x16d :=
  by rw [scan_instruction_pc 164 (by decide) (by decide)]; rfl
@[simp] theorem pc2909 : Artifact.submissionArtifact.instructionPC 165 = 0x16e :=
  by rw [scan_instruction_pc 165 (by decide) (by decide)]; rfl
@[simp] theorem pc2910 : Artifact.submissionArtifact.instructionPC 166 = 0x16f :=
  by rw [scan_instruction_pc 166 (by decide) (by decide)]; rfl
@[simp] theorem pc2911 : Artifact.submissionArtifact.instructionPC 167 = 0x170 :=
  by rw [scan_instruction_pc 167 (by decide) (by decide)]; rfl
@[simp] theorem pc2912 : Artifact.submissionArtifact.instructionPC 168 = 0x171 :=
  by rw [scan_instruction_pc 168 (by decide) (by decide)]; rfl
@[simp] theorem pc2913 : Artifact.submissionArtifact.instructionPC 169 = 0x172 :=
  by rw [scan_instruction_pc 169 (by decide) (by decide)]; rfl
@[simp] theorem pc2914 : Artifact.submissionArtifact.instructionPC 170 = 0x173 :=
  by rw [scan_instruction_pc 170 (by decide) (by decide)]; rfl
@[simp] theorem pc2915 : Artifact.submissionArtifact.instructionPC 171 = 0x174 :=
  by rw [scan_instruction_pc 171 (by decide) (by decide)]; rfl
@[simp] theorem pc2916 : Artifact.submissionArtifact.instructionPC 172 = 0x175 :=
  by rw [scan_instruction_pc 172 (by decide) (by decide)]; rfl
@[simp] theorem pc2917 : Artifact.submissionArtifact.instructionPC 173 = 0x176 :=
  by rw [scan_instruction_pc 173 (by decide) (by decide)]; rfl
@[simp] theorem pc2918 : Artifact.submissionArtifact.instructionPC 174 = 0x177 :=
  by rw [scan_instruction_pc 174 (by decide) (by decide)]; rfl
@[simp] theorem pc2919 : Artifact.submissionArtifact.instructionPC 175 = 0x178 :=
  by rw [scan_instruction_pc 175 (by decide) (by decide)]; rfl
@[simp] theorem pc2920 : Artifact.submissionArtifact.instructionPC 176 = 0x179 :=
  by rw [scan_instruction_pc 176 (by decide) (by decide)]; rfl
@[simp] theorem pc2921 : Artifact.submissionArtifact.instructionPC 177 = 0x17a :=
  by rw [scan_instruction_pc 177 (by decide) (by decide)]; rfl
@[simp] theorem pc2922 : Artifact.submissionArtifact.instructionPC 178 = 0x17b :=
  by rw [scan_instruction_pc 178 (by decide) (by decide)]; rfl
@[simp] theorem pc2923 : Artifact.submissionArtifact.instructionPC 179 = 0x17c :=
  by rw [scan_instruction_pc 179 (by decide) (by decide)]; rfl
@[simp] theorem pc2924 : Artifact.submissionArtifact.instructionPC 180 = 0x17d :=
  by rw [scan_instruction_pc 180 (by decide) (by decide)]; rfl
@[simp] theorem pc2925 : Artifact.submissionArtifact.instructionPC 181 = 0x17e :=
  by rw [scan_instruction_pc 181 (by decide) (by decide)]; rfl
@[simp] theorem pc2926 : Artifact.submissionArtifact.instructionPC 182 = 0x17f :=
  by rw [scan_instruction_pc 182 (by decide) (by decide)]; rfl
@[simp] theorem pc2927 : Artifact.submissionArtifact.instructionPC 183 = 0x180 :=
  by rw [scan_instruction_pc 183 (by decide) (by decide)]; rfl
@[simp] theorem pc2928 : Artifact.submissionArtifact.instructionPC 184 = 0x181 :=
  by rw [scan_instruction_pc 184 (by decide) (by decide)]; rfl
@[simp] theorem pc2929 : Artifact.submissionArtifact.instructionPC 185 = 0x182 :=
  by rw [scan_instruction_pc 185 (by decide) (by decide)]; rfl
@[simp] theorem pc2930 : Artifact.submissionArtifact.instructionPC 186 = 0x183 :=
  by rw [scan_instruction_pc 186 (by decide) (by decide)]; rfl
@[simp] theorem pc2931 : Artifact.submissionArtifact.instructionPC 187 = 0x185 :=
  by rw [scan_instruction_pc 187 (by decide) (by decide)]; rfl
@[simp] theorem pc2932 : Artifact.submissionArtifact.instructionPC 188 = 0x186 :=
  by rw [scan_instruction_pc 188 (by decide) (by decide)]; rfl
@[simp] theorem pc2933 : Artifact.submissionArtifact.instructionPC 189 = 0x188 :=
  by rw [scan_instruction_pc 189 (by decide) (by decide)]; rfl
@[simp] theorem pc2934 : Artifact.submissionArtifact.instructionPC 190 = 0x189 :=
  by rw [scan_instruction_pc 190 (by decide) (by decide)]; rfl
@[simp] theorem pc2935 : Artifact.submissionArtifact.instructionPC 191 = 0x18c :=
  by rw [scan_instruction_pc 191 (by decide) (by decide)]; rfl
@[simp] theorem pc2936 : Artifact.submissionArtifact.instructionPC 192 = 0x18d :=
  by rw [scan_instruction_pc 192 (by decide) (by decide)]; rfl
@[simp] theorem pc2937 : Artifact.submissionArtifact.instructionPC 193 = 0x18e :=
  by rw [scan_instruction_pc 193 (by decide) (by decide)]; rfl
@[simp] theorem pc2938 : Artifact.submissionArtifact.instructionPC 194 = 0x18f :=
  by rw [scan_instruction_pc 194 (by decide) (by decide)]; rfl
@[simp] theorem pc2939 : Artifact.submissionArtifact.instructionPC 195 = 0x190 :=
  by rw [scan_instruction_pc 195 (by decide) (by decide)]; rfl
@[simp] theorem pc2940 : Artifact.submissionArtifact.instructionPC 196 = 0x191 :=
  by rw [scan_instruction_pc 196 (by decide) (by decide)]; rfl
@[simp] theorem pc2941 : Artifact.submissionArtifact.instructionPC 197 = 0x192 :=
  by rw [scan_instruction_pc 197 (by decide) (by decide)]; rfl
@[simp] theorem pc2942 : Artifact.submissionArtifact.instructionPC 198 = 0x193 :=
  by rw [scan_instruction_pc 198 (by decide) (by decide)]; rfl
@[simp] theorem pc2943 : Artifact.submissionArtifact.instructionPC 199 = 0x194 :=
  by rw [scan_instruction_pc 199 (by decide) (by decide)]; rfl
@[simp] theorem pc2944 : Artifact.submissionArtifact.instructionPC 200 = 0x195 :=
  by rw [scan_instruction_pc 200 (by decide) (by decide)]; rfl
@[simp] theorem pc2945 : Artifact.submissionArtifact.instructionPC 201 = 0x196 :=
  by rw [scan_instruction_pc 201 (by decide) (by decide)]; rfl
@[simp] theorem pc2946 : Artifact.submissionArtifact.instructionPC 201 = 0x196 :=
  by rw [scan_instruction_pc 201 (by decide) (by decide)]; rfl
@[simp] theorem pc2947 : Artifact.submissionArtifact.instructionPC 202 = 0x198 :=
  by rw [scan_instruction_pc 202 (by decide) (by decide)]; rfl
@[simp] theorem pc2948 : Artifact.submissionArtifact.instructionPC 203 = 0x199 :=
  by rw [scan_instruction_pc 203 (by decide) (by decide)]; rfl
@[simp] theorem pc2949 : Artifact.submissionArtifact.instructionPC 204 = 0x19b :=
  by rw [scan_instruction_pc 204 (by decide) (by decide)]; rfl
@[simp] theorem pc2950 : Artifact.submissionArtifact.instructionPC 205 = 0x19c :=
  by rw [scan_instruction_pc 205 (by decide) (by decide)]; rfl
@[simp] theorem pc2951 : Artifact.submissionArtifact.instructionPC 205 = 0x19c :=
  by rw [scan_instruction_pc 205 (by decide) (by decide)]; rfl
@[simp] theorem pc2952 : Artifact.submissionArtifact.instructionPC 205 = 0x19c :=
  by rw [scan_instruction_pc 205 (by decide) (by decide)]; rfl
@[simp] theorem pc2953 : Artifact.submissionArtifact.instructionPC 206 = 0x19d :=
  by rw [scan_instruction_pc 206 (by decide) (by decide)]; rfl
@[simp] theorem pc2954 : Artifact.submissionArtifact.instructionPC 207 = 0x19f :=
  by rw [scan_instruction_pc 207 (by decide) (by decide)]; rfl
@[simp] theorem pc2955 : Artifact.submissionArtifact.instructionPC 208 = 0x1a0 :=
  by rw [scan_instruction_pc 208 (by decide) (by decide)]; rfl
@[simp] theorem pc2956 : Artifact.submissionArtifact.instructionPC 209 = 0x1a1 :=
  by rw [scan_instruction_pc 209 (by decide) (by decide)]; rfl
@[simp] theorem pc2957 : Artifact.submissionArtifact.instructionPC 209 = 0x1a1 :=
  by rw [scan_instruction_pc 209 (by decide) (by decide)]; rfl
@[simp] theorem pc2958 : Artifact.submissionArtifact.instructionPC 210 = 0x1a2 :=
  by rw [scan_instruction_pc 210 (by decide) (by decide)]; rfl
@[simp] theorem pc2959 : Artifact.submissionArtifact.instructionPC 211 = 0x1a5 :=
  by rw [scan_instruction_pc 211 (by decide) (by decide)]; rfl
@[simp] theorem pc2960 : Artifact.submissionArtifact.instructionPC 212 = 0x1a6 :=
  by rw [scan_instruction_pc 212 (by decide) (by decide)]; rfl
@[simp] theorem pc2961 : Artifact.submissionArtifact.instructionPC 213 = 0x1a9 :=
  by rw [scan_instruction_pc 213 (by decide) (by decide)]; rfl
@[simp] theorem pc2962 : Artifact.submissionArtifact.instructionPC 214 = 0x1aa :=
  by rw [scan_instruction_pc 214 (by decide) (by decide)]; rfl
@[simp] theorem pc2963 : Artifact.submissionArtifact.instructionPC 215 = 0x1ab :=
  by rw [scan_instruction_pc 215 (by decide) (by decide)]; rfl
@[simp] theorem pc2964 : Artifact.submissionArtifact.instructionPC 216 = 0x1ac :=
  by rw [scan_instruction_pc 216 (by decide) (by decide)]; rfl
@[simp] theorem pc2965 : Artifact.submissionArtifact.instructionPC 217 = 0x1b5 :=
  by rw [scan_instruction_pc 217 (by decide) (by decide)]; rfl
@[simp] theorem pc2966 : Artifact.submissionArtifact.instructionPC 218 = 0x1b7 :=
  by rw [scan_instruction_pc 218 (by decide) (by decide)]; rfl
@[simp] theorem pc2967 : Artifact.submissionArtifact.instructionPC 219 = 0x1b8 :=
  by rw [scan_instruction_pc 219 (by decide) (by decide)]; rfl
@[simp] theorem pc2968 : Artifact.submissionArtifact.instructionPC 220 = 0x1b9 :=
  by rw [scan_instruction_pc 220 (by decide) (by decide)]; rfl
@[simp] theorem pc2969 : Artifact.submissionArtifact.instructionPC 221 = 0x1ba :=
  by rw [scan_instruction_pc 221 (by decide) (by decide)]; rfl
@[simp] theorem pc2970 : Artifact.submissionArtifact.instructionPC 222 = 0x1bb :=
  by rw [scan_instruction_pc 222 (by decide) (by decide)]; rfl
@[simp] theorem pc2971 : Artifact.submissionArtifact.instructionPC 223 = 0x1bc :=
  by rw [scan_instruction_pc 223 (by decide) (by decide)]; rfl
@[simp] theorem pc2972 : Artifact.submissionArtifact.instructionPC 224 = 0x1bd :=
  by rw [scan_instruction_pc 224 (by decide) (by decide)]; rfl
@[simp] theorem pc2973 : Artifact.submissionArtifact.instructionPC 225 = 0x1be :=
  by rw [scan_instruction_pc 225 (by decide) (by decide)]; rfl
@[simp] theorem pc2974 : Artifact.submissionArtifact.instructionPC 226 = 0x1bf :=
  by rw [scan_instruction_pc 226 (by decide) (by decide)]; rfl
@[simp] theorem pc2975 : Artifact.submissionArtifact.instructionPC 227 = 0x1c0 :=
  by rw [scan_instruction_pc 227 (by decide) (by decide)]; rfl
@[simp] theorem pc2976 : Artifact.submissionArtifact.instructionPC 228 = 0x1c1 :=
  by rw [scan_instruction_pc 228 (by decide) (by decide)]; rfl
@[simp] theorem pc2977 : Artifact.submissionArtifact.instructionPC 229 = 0x1c2 :=
  by rw [scan_instruction_pc 229 (by decide) (by decide)]; rfl
@[simp] theorem pc2978 : Artifact.submissionArtifact.instructionPC 230 = 0x1c3 :=
  by rw [scan_instruction_pc 230 (by decide) (by decide)]; rfl
@[simp] theorem pc2979 : Artifact.submissionArtifact.instructionPC 231 = 0x1c4 :=
  by rw [scan_instruction_pc 231 (by decide) (by decide)]; rfl
@[simp] theorem pc2980 : Artifact.submissionArtifact.instructionPC 232 = 0x1c5 :=
  by rw [scan_instruction_pc 232 (by decide) (by decide)]; rfl
@[simp] theorem pc2981 : Artifact.submissionArtifact.instructionPC 233 = 0x1c6 :=
  by rw [scan_instruction_pc 233 (by decide) (by decide)]; rfl
@[simp] theorem pc2982 : Artifact.submissionArtifact.instructionPC 234 = 0x1c8 :=
  by rw [scan_instruction_pc 234 (by decide) (by decide)]; rfl
@[simp] theorem pc2983 : Artifact.submissionArtifact.instructionPC 235 = 0x1c9 :=
  by rw [scan_instruction_pc 235 (by decide) (by decide)]; rfl
@[simp] theorem pc2984 : Artifact.submissionArtifact.instructionPC 236 = 0x1df :=
  by rw [scan_instruction_pc 236 (by decide) (by decide)]; rfl
@[simp] theorem pc2985 : Artifact.submissionArtifact.instructionPC 237 = 0x1e0 :=
  by rw [scan_instruction_pc 237 (by decide) (by decide)]; rfl
@[simp] theorem pc2986 : Artifact.submissionArtifact.instructionPC 238 = 0x1e1 :=
  by rw [scan_instruction_pc 238 (by decide) (by decide)]; rfl
@[simp] theorem pc2987 : Artifact.submissionArtifact.instructionPC 239 = 0x1e2 :=
  by rw [scan_instruction_pc 239 (by decide) (by decide)]; rfl
@[simp] theorem pc2988 : Artifact.submissionArtifact.instructionPC 240 = 0x1e3 :=
  by rw [scan_instruction_pc 240 (by decide) (by decide)]; rfl
@[simp] theorem pc2989 : Artifact.submissionArtifact.instructionPC 241 = 0x1e4 :=
  by rw [scan_instruction_pc 241 (by decide) (by decide)]; rfl
@[simp] theorem pc2990 : Artifact.submissionArtifact.instructionPC 242 = 0x1e5 :=
  by rw [scan_instruction_pc 242 (by decide) (by decide)]; rfl
@[simp] theorem pc2991 : Artifact.submissionArtifact.instructionPC 243 = 0x1e6 :=
  by rw [scan_instruction_pc 243 (by decide) (by decide)]; rfl
@[simp] theorem pc2992 : Artifact.submissionArtifact.instructionPC 244 = 0x1e7 :=
  by rw [scan_instruction_pc 244 (by decide) (by decide)]; rfl
@[simp] theorem pc2993 : Artifact.submissionArtifact.instructionPC 245 = 0x1e9 :=
  by rw [scan_instruction_pc 245 (by decide) (by decide)]; rfl
@[simp] theorem pc2994 : Artifact.submissionArtifact.instructionPC 246 = 0x1ea :=
  by rw [scan_instruction_pc 246 (by decide) (by decide)]; rfl
@[simp] theorem pc2995 : Artifact.submissionArtifact.instructionPC 247 = 0x1ec :=
  by rw [scan_instruction_pc 247 (by decide) (by decide)]; rfl
@[simp] theorem pc2996 : Artifact.submissionArtifact.instructionPC 248 = 0x1ed :=
  by rw [scan_instruction_pc 248 (by decide) (by decide)]; rfl
@[simp] theorem pc2997 : Artifact.submissionArtifact.instructionPC 249 = 0x1ef :=
  by rw [scan_instruction_pc 249 (by decide) (by decide)]; rfl
@[simp] theorem pc2998 : Artifact.submissionArtifact.instructionPC 250 = 0x1f0 :=
  by rw [scan_instruction_pc 250 (by decide) (by decide)]; rfl
@[simp] theorem pc2999 : Artifact.submissionArtifact.instructionPC 251 = 0x1f2 :=
  by rw [scan_instruction_pc 251 (by decide) (by decide)]; rfl
@[simp] theorem pc3000 : Artifact.submissionArtifact.instructionPC 252 = 0x1f3 :=
  by rw [scan_instruction_pc 252 (by decide) (by decide)]; rfl
@[simp] theorem pc3001 : Artifact.submissionArtifact.instructionPC 253 = 0x1f4 :=
  by rw [scan_instruction_pc 253 (by decide) (by decide)]; rfl
@[simp] theorem pc3002 : Artifact.submissionArtifact.instructionPC 254 = 0x1f6 :=
  by rw [scan_instruction_pc 254 (by decide) (by decide)]; rfl
@[simp] theorem pc3003 : Artifact.submissionArtifact.instructionPC 255 = 0x1f7 :=
  by rw [scan_instruction_pc 255 (by decide) (by decide)]; rfl
@[simp] theorem pc3004 : Artifact.submissionArtifact.instructionPC 256 = 0x1f8 :=
  by rw [scan_instruction_pc 256 (by decide) (by decide)]; rfl
@[simp] theorem pc3005 : Artifact.submissionArtifact.instructionPC 257 = 0x1f9 :=
  by rw [scan_instruction_pc 257 (by decide) (by decide)]; rfl
@[simp] theorem pc3006 : Artifact.submissionArtifact.instructionPC 258 = 0x1fa :=
  by rw [scan_instruction_pc 258 (by decide) (by decide)]; rfl
@[simp] theorem pc3007 : Artifact.submissionArtifact.instructionPC 259 = 0x1fb :=
  by rw [scan_instruction_pc 259 (by decide) (by decide)]; rfl
@[simp] theorem pc3008 : Artifact.submissionArtifact.instructionPC 260 = 0x1fc :=
  by rw [scan_instruction_pc 260 (by decide) (by decide)]; rfl
@[simp] theorem pc3009 : Artifact.submissionArtifact.instructionPC 261 = 0x1fd :=
  by rw [scan_instruction_pc 261 (by decide) (by decide)]; rfl
@[simp] theorem pc3010 : Artifact.submissionArtifact.instructionPC 262 = 0x1fe :=
  by rw [scan_instruction_pc 262 (by decide) (by decide)]; rfl
@[simp] theorem pc3011 : Artifact.submissionArtifact.instructionPC 263 = 0x1ff :=
  by rw [scan_instruction_pc 263 (by decide) (by decide)]; rfl
@[simp] theorem pc3012 : Artifact.submissionArtifact.instructionPC 264 = 0x200 :=
  by rw [scan_instruction_pc 264 (by decide) (by decide)]; rfl
@[simp] theorem pc3013 : Artifact.submissionArtifact.instructionPC 265 = 0x201 :=
  by rw [scan_instruction_pc 265 (by decide) (by decide)]; rfl
@[simp] theorem pc3014 : Artifact.submissionArtifact.instructionPC 266 = 0x202 :=
  by rw [scan_instruction_pc 266 (by decide) (by decide)]; rfl
@[simp] theorem pc3015 : Artifact.submissionArtifact.instructionPC 267 = 0x203 :=
  by rw [scan_instruction_pc 267 (by decide) (by decide)]; rfl
@[simp] theorem pc3016 : Artifact.submissionArtifact.instructionPC 268 = 0x204 :=
  by rw [scan_instruction_pc 268 (by decide) (by decide)]; rfl
@[simp] theorem pc3017 : Artifact.submissionArtifact.instructionPC 269 = 0x206 :=
  by rw [scan_instruction_pc 269 (by decide) (by decide)]; rfl
@[simp] theorem pc3018 : Artifact.submissionArtifact.instructionPC 270 = 0x207 :=
  by rw [scan_instruction_pc 270 (by decide) (by decide)]; rfl
@[simp] theorem pc3019 : Artifact.submissionArtifact.instructionPC 271 = 0x208 :=
  by rw [scan_instruction_pc 271 (by decide) (by decide)]; rfl
@[simp] theorem pc3020 : Artifact.submissionArtifact.instructionPC 271 = 0x208 :=
  by rw [scan_instruction_pc 271 (by decide) (by decide)]; rfl
@[simp] theorem pc3021 : Artifact.submissionArtifact.instructionPC 272 = 0x20c :=
  by rw [scan_instruction_pc 272 (by decide) (by decide)]; rfl
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
#print axioms pc3021

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan
