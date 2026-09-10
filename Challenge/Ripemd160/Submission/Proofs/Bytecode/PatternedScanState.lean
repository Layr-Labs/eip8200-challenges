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
  scanPrefix ++ submissionInstructionsChunk0.take 151

private def scanSuffix : List YulEvmCompiler.Instr :=
  submissionInstructionsChunk0.drop 151 ++ submissionInstructionsChunk1 ++ submissionInstructionsChunk2 ++ submissionInstructionsChunk3 ++ submissionInstructionsChunk4 ++ submissionInstructionsChunk5 ++ submissionInstructionsChunk6 ++ submissionInstructionsChunk7 ++ submissionInstructionsChunk8 ++ submissionInstructionsChunk9 ++ submissionInstructionsChunk10 ++ submissionInstructionsChunk11 ++ submissionInstructionsChunk12 ++ submissionInstructionsChunk13 ++ submissionInstructionsChunk14 ++ submissionInstructionsChunk15 ++ submissionInstructionsChunk16 ++ submissionInstructionsChunk17 ++ submissionInstructionsChunk18 ++ submissionInstructionsChunk19 ++ submissionInstructionsChunk20

private theorem scanBefore_length : scanBefore.length = 151 := by
  simp [scanBefore, scanPrefix]

private theorem scanSuffix_length : scanSuffix.length = 4022 := by
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
      submissionInstructionsChunk0.take 151 ++ submissionInstructionsChunk0.drop 151 := by
    exact (List.take_append_drop 151 submissionInstructionsChunk0).symm
  rw [hprefix]
  conv_lhs => rw [hchunk]
  simp only [scanBefore, scanSuffix, List.append_assoc, List.append_nil]

private theorem scanBefore_pc :
    (YulEvmCompiler.assembleBytes scanBefore).length = 239 := by rfl

private theorem artifact_instruction_projection :
    Artifact.submissionArtifact.instructions = Artifact.submissionInstructions := by rfl

private theorem scan_instruction_at (index : Nat)
    (hlo : 151 ≤ index) (hhi : index < 4173) :
    Artifact.submissionInstructions[index]? = scanSuffix[index - 151]? := by
  have hi : index - 151 < scanSuffix.length := by
    rw [scanSuffix_length]
    omega
  have h := ArtifactSegment.getElem?_segment Artifact.submissionArtifact
    scanBefore scanSuffix [] artifact_scan_split (index - 151) hi
  simpa only [artifact_instruction_projection, scanBefore_length,
    Nat.add_sub_of_le hlo] using h

private theorem scan_instruction_pc (index : Nat)
    (hlo : 151 ≤ index) (hhi : index ≤ 4173) :
    Artifact.submissionArtifact.instructionPC index =
      239 + (YulEvmCompiler.assembleBytes (scanSuffix.take (index - 151))).length := by
  have hi : index - 151 ≤ scanSuffix.length := by
    rw [scanSuffix_length]
    omega
  have h := ArtifactSegment.instructionPC_segment_of_bounds Artifact.submissionArtifact
    scanBefore scanSuffix [] 151 239 artifact_scan_split scanBefore_length
    scanBefore_pc (index - 151) hi
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
  [pushAt 161 1 255,
   pushAt 162 0 0,
   opAt 163 .NOT,
   opAt 164 .DIV,
   pushAt 165 32 3244493450063667868678674439968361782956185527883176199882357678282131398018,
   opAt 166 (.Dup ⟨1, by decide⟩),
   pushAt 167 1 7,
   opAt 168 .SHL,
   opAt 169 (.Dup ⟨0, by decide⟩),
   opAt 170 .NOT,
   opAt 171 (.Swap ⟨0, by decide⟩),
   opAt 172 (.Swap ⟨2, by decide⟩),
   opAt 173 (.Dup ⟨2, by decide⟩),
   opAt 174 (.Dup ⟨2, by decide⟩),
   opAt 175 .AND,
   pushAt 176 0 0,
   pushAt 177 0 0,
   pushAt 178 0 0]

/-- Derive the expected word and test for a straddler. -/
def wordPath : List Located :=
  [opAt 179 .JUMPDEST, opAt 180 (.Dup ⟨0, by decide⟩),
   opAt 181 (.Dup ⟨5, by decide⟩), opAt 182 .MUL,
   opAt 183 (.Dup ⟨0, by decide⟩), opAt 184 (.Dup ⟨7, by decide⟩),
   opAt 185 .AND, opAt 186 (.Dup ⟨5, by decide⟩), opAt 187 .ADD,
   opAt 188 (.Dup ⟨1, by decide⟩), opAt 189 (.Dup ⟨9, by decide⟩),
   opAt 190 .XOR, opAt 191 (.Dup ⟨10, by decide⟩), opAt 192 .AND,
   opAt 193 .XOR, opAt 194 (.Dup ⟨3, by decide⟩), pushAt 195 1 255,
   opAt 196 .AND, pushAt 197 1 224, opAt 198 .XOR, pushAt 199 2 385,
   opAt 200 .JUMPI]

/-- Fold one word into the accumulator and advance. -/
def comparePath : List Located :=
  [opAt 231 .JUMPDEST,
   opAt 232 (.Dup ⟨3, by decide⟩),
   opAt 233 .CALLDATALOAD,
   opAt 234 .XOR,
   pushAt 235 4 1073790976,
   opAt 236 (.Dup ⟨4, by decide⟩),
   opAt 237 .CALLDATASIZE,
   opAt 238 .SUB,
   opAt 239 .SHR,
   pushAt 240 1 255,
   opAt 241 .AND,
   opAt 242 .SHR,
   opAt 243 (.Dup ⟨4, by decide⟩),
   opAt 244 .OR,
   opAt 245 (.Swap ⟨3, by decide⟩),
   opAt 246 .POP,
   opAt 247 .POP,
   pushAt 248 1 160,
   opAt 249 .ADD,
   pushAt 250 1 255,
   opAt 251 .AND,
   opAt 252 (.Swap ⟨0, by decide⟩),
   pushAt 253 1 32,
   opAt 254 .ADD,
   opAt 255 (.Swap ⟨0, by decide⟩),
   opAt 256 .CALLDATASIZE,
   opAt 257 (.Dup ⟨2, by decide⟩),
   opAt 258 .LT,
   pushAt 259 2 323,
   opAt 260 .JUMPI,
   opAt 261 (.Dup ⟨2, by decide⟩)]

/-- The padded tail word, the cleanup and the miss test. -/
def tailPath : List Located :=
  [opAt 283 .JUMPDEST, opAt 285 (.Swap ⟨2, by decide⟩), opAt 286 .POP,
   opAt 287 (.Swap ⟨1, by decide⟩), opAt 288 (.Swap ⟨6, by decide⟩), opAt 289 .POP,
   opAt 290 .POP, opAt 291 .POP, opAt 292 .POP, opAt 293 .POP, opAt 294 .POP, opAt 295 .POP,
   pushAt 296 1 3, opAt 297 .JUMPI]

/-- Store and return the stored digest. -/
def returnPath : List Located :=
  [opAt 264 .CALLDATASIZE, pushAt 266 2 376, opAt 267 .EQ,
   pushAt 268 20 644824770394507154413287103057882351908521126009, opAt 269 .MUL,
   pushAt 276 20 766350606435067737561421097975693824639675460820, opAt 277 .XOR,
   pushAt 278 0 0, opAt 279 .MSTORE, opAt 280 .MSIZE, pushAt 281 0 0,
   opAt 282 .RETURN]

/-- Shift the correction constant out of `M`. -/
def straddleCorrPath : List Located :=
  [opAt 201 .JUMPDEST, opAt 202 (.Dup ⟨6, by decide⟩),
   opAt 203 (.Dup ⟨4, by decide⟩), pushAt 204 1 8, opAt 205 .SHR,
   pushAt 206 1 5, opAt 207 .MUL, pushAt 208 1 27, opAt 209 .SUB,
   pushAt 210 1 3, opAt 211 .SHL, opAt 212 .SHR, pushAt 213 1 11,
   opAt 214 .MUL]

/-- Apply the correction to the expected word. -/
def straddleAddPath : List Located :=
  [opAt 215 (.Dup ⟨1, by decide⟩), opAt 216 (.Dup ⟨9, by decide⟩),
   opAt 217 .AND, opAt 218 (.Dup ⟨1, by decide⟩), opAt 219 .ADD,
   opAt 220 (.Dup ⟨2, by decide⟩), opAt 221 (.Dup ⟨12, by decide⟩),
   opAt 222 .AND, opAt 223 .XOR, opAt 224 (.Swap ⟨1, by decide⟩),
   opAt 225 .POP, opAt 226 .POP]

/-- Bump the scalar and rejoin the scan. -/
def straddleBackPath : List Located :=
  [opAt 227 (.Swap ⟨1, by decide⟩), pushAt 228 1 11, opAt 229 .ADD,
   opAt 230 (.Swap ⟨1, by decide⟩)]


@[simp] theorem pc2903 : Artifact.submissionArtifact.instructionPC 161 = 0x10f :=
  by rw [scan_instruction_pc 161 (by decide) (by decide)]; rfl
@[simp] theorem pc2904 : Artifact.submissionArtifact.instructionPC 161 = 0x10f :=
  by rw [scan_instruction_pc 161 (by decide) (by decide)]; rfl
@[simp] theorem pc2905 : Artifact.submissionArtifact.instructionPC 165 = 0x114 :=
  by rw [scan_instruction_pc 165 (by decide) (by decide)]; rfl
@[simp] theorem pc2906 : Artifact.submissionArtifact.instructionPC 170 = 0x13a :=
  by rw [scan_instruction_pc 170 (by decide) (by decide)]; rfl
@[simp] theorem pc2907 : Artifact.submissionArtifact.instructionPC 172 = 0x13c :=
  by rw [scan_instruction_pc 172 (by decide) (by decide)]; rfl
@[simp] theorem pc2908 : Artifact.submissionArtifact.instructionPC 173 = 0x13d :=
  by rw [scan_instruction_pc 173 (by decide) (by decide)]; rfl
@[simp] theorem pc2909 : Artifact.submissionArtifact.instructionPC 174 = 0x13e :=
  by rw [scan_instruction_pc 174 (by decide) (by decide)]; rfl
@[simp] theorem pc2910 : Artifact.submissionArtifact.instructionPC 175 = 0x13f :=
  by rw [scan_instruction_pc 175 (by decide) (by decide)]; rfl
@[simp] theorem pc2911 : Artifact.submissionArtifact.instructionPC 176 = 0x140 :=
  by rw [scan_instruction_pc 176 (by decide) (by decide)]; rfl
@[simp] theorem pc2912 : Artifact.submissionArtifact.instructionPC 177 = 0x141 :=
  by rw [scan_instruction_pc 177 (by decide) (by decide)]; rfl
@[simp] theorem pc2913 : Artifact.submissionArtifact.instructionPC 178 = 0x142 :=
  by rw [scan_instruction_pc 178 (by decide) (by decide)]; rfl
@[simp] theorem pc2914 : Artifact.submissionArtifact.instructionPC 179 = 0x143 :=
  by rw [scan_instruction_pc 179 (by decide) (by decide)]; rfl
@[simp] theorem pc2915 : Artifact.submissionArtifact.instructionPC 180 = 0x144 :=
  by rw [scan_instruction_pc 180 (by decide) (by decide)]; rfl
@[simp] theorem pc2916 : Artifact.submissionArtifact.instructionPC 181 = 0x145 :=
  by rw [scan_instruction_pc 181 (by decide) (by decide)]; rfl
@[simp] theorem pc2917 : Artifact.submissionArtifact.instructionPC 182 = 0x146 :=
  by rw [scan_instruction_pc 182 (by decide) (by decide)]; rfl
@[simp] theorem pc2918 : Artifact.submissionArtifact.instructionPC 183 = 0x147 :=
  by rw [scan_instruction_pc 183 (by decide) (by decide)]; rfl
@[simp] theorem pc2919 : Artifact.submissionArtifact.instructionPC 184 = 0x148 :=
  by rw [scan_instruction_pc 184 (by decide) (by decide)]; rfl
@[simp] theorem pc2920 : Artifact.submissionArtifact.instructionPC 185 = 0x149 :=
  by rw [scan_instruction_pc 185 (by decide) (by decide)]; rfl
@[simp] theorem pc2921 : Artifact.submissionArtifact.instructionPC 186 = 0x14a :=
  by rw [scan_instruction_pc 186 (by decide) (by decide)]; rfl
@[simp] theorem pc2922 : Artifact.submissionArtifact.instructionPC 187 = 0x14b :=
  by rw [scan_instruction_pc 187 (by decide) (by decide)]; rfl
@[simp] theorem pc2923 : Artifact.submissionArtifact.instructionPC 188 = 0x14c :=
  by rw [scan_instruction_pc 188 (by decide) (by decide)]; rfl
@[simp] theorem pc2924 : Artifact.submissionArtifact.instructionPC 189 = 0x14d :=
  by rw [scan_instruction_pc 189 (by decide) (by decide)]; rfl
@[simp] theorem pc2925 : Artifact.submissionArtifact.instructionPC 190 = 0x14e :=
  by rw [scan_instruction_pc 190 (by decide) (by decide)]; rfl
@[simp] theorem pc2926 : Artifact.submissionArtifact.instructionPC 191 = 0x14f :=
  by rw [scan_instruction_pc 191 (by decide) (by decide)]; rfl
@[simp] theorem pc2927 : Artifact.submissionArtifact.instructionPC 192 = 0x150 :=
  by rw [scan_instruction_pc 192 (by decide) (by decide)]; rfl
@[simp] theorem pc2928 : Artifact.submissionArtifact.instructionPC 193 = 0x151 :=
  by rw [scan_instruction_pc 193 (by decide) (by decide)]; rfl
@[simp] theorem pc2929 : Artifact.submissionArtifact.instructionPC 194 = 0x152 :=
  by rw [scan_instruction_pc 194 (by decide) (by decide)]; rfl
@[simp] theorem pc2930 : Artifact.submissionArtifact.instructionPC 195 = 0x153 :=
  by rw [scan_instruction_pc 195 (by decide) (by decide)]; rfl
@[simp] theorem pc2931 : Artifact.submissionArtifact.instructionPC 196 = 0x155 :=
  by rw [scan_instruction_pc 196 (by decide) (by decide)]; rfl
@[simp] theorem pc2932 : Artifact.submissionArtifact.instructionPC 197 = 0x156 :=
  by rw [scan_instruction_pc 197 (by decide) (by decide)]; rfl
@[simp] theorem pc2933 : Artifact.submissionArtifact.instructionPC 198 = 0x158 :=
  by rw [scan_instruction_pc 198 (by decide) (by decide)]; rfl
@[simp] theorem pc2934 : Artifact.submissionArtifact.instructionPC 199 = 0x159 :=
  by rw [scan_instruction_pc 199 (by decide) (by decide)]; rfl
@[simp] theorem pc2935 : Artifact.submissionArtifact.instructionPC 200 = 0x15c :=
  by rw [scan_instruction_pc 200 (by decide) (by decide)]; rfl
@[simp] theorem pc2936 : Artifact.submissionArtifact.instructionPC 231 = 0x181 :=
  by rw [scan_instruction_pc 231 (by decide) (by decide)]; rfl
@[simp] theorem pc2937 : Artifact.submissionArtifact.instructionPC 232 = 0x182 :=
  by rw [scan_instruction_pc 232 (by decide) (by decide)]; rfl
@[simp] theorem pc2938 : Artifact.submissionArtifact.instructionPC 233 = 0x183 :=
  by rw [scan_instruction_pc 233 (by decide) (by decide)]; rfl
@[simp] theorem pc2939 : Artifact.submissionArtifact.instructionPC 234 = 0x184 :=
  by rw [scan_instruction_pc 234 (by decide) (by decide)]; rfl
@[simp] theorem pc2940 : Artifact.submissionArtifact.instructionPC 243 = 0x192 :=
  by rw [scan_instruction_pc 243 (by decide) (by decide)]; rfl
@[simp] theorem pc2941 : Artifact.submissionArtifact.instructionPC 244 = 0x193 :=
  by rw [scan_instruction_pc 244 (by decide) (by decide)]; rfl
@[simp] theorem pc2942 : Artifact.submissionArtifact.instructionPC 245 = 0x194 :=
  by rw [scan_instruction_pc 245 (by decide) (by decide)]; rfl
@[simp] theorem pc2943 : Artifact.submissionArtifact.instructionPC 246 = 0x195 :=
  by rw [scan_instruction_pc 246 (by decide) (by decide)]; rfl
@[simp] theorem pc2944 : Artifact.submissionArtifact.instructionPC 247 = 0x196 :=
  by rw [scan_instruction_pc 247 (by decide) (by decide)]; rfl
@[simp] theorem pc2945 : Artifact.submissionArtifact.instructionPC 248 = 0x197 :=
  by rw [scan_instruction_pc 248 (by decide) (by decide)]; rfl
@[simp] theorem pc2946 : Artifact.submissionArtifact.instructionPC 248 = 0x197 :=
  by rw [scan_instruction_pc 248 (by decide) (by decide)]; rfl
@[simp] theorem pc2947 : Artifact.submissionArtifact.instructionPC 249 = 0x199 :=
  by rw [scan_instruction_pc 249 (by decide) (by decide)]; rfl
@[simp] theorem pc2948 : Artifact.submissionArtifact.instructionPC 250 = 0x19a :=
  by rw [scan_instruction_pc 250 (by decide) (by decide)]; rfl
@[simp] theorem pc2949 : Artifact.submissionArtifact.instructionPC 251 = 0x19c :=
  by rw [scan_instruction_pc 251 (by decide) (by decide)]; rfl
@[simp] theorem pc2950 : Artifact.submissionArtifact.instructionPC 252 = 0x19d :=
  by rw [scan_instruction_pc 252 (by decide) (by decide)]; rfl
@[simp] theorem pc2951 : Artifact.submissionArtifact.instructionPC 252 = 0x19d :=
  by rw [scan_instruction_pc 252 (by decide) (by decide)]; rfl
@[simp] theorem pc2952 : Artifact.submissionArtifact.instructionPC 252 = 0x19d :=
  by rw [scan_instruction_pc 252 (by decide) (by decide)]; rfl
@[simp] theorem pc2953 : Artifact.submissionArtifact.instructionPC 253 = 0x19e :=
  by rw [scan_instruction_pc 253 (by decide) (by decide)]; rfl
@[simp] theorem pc2954 : Artifact.submissionArtifact.instructionPC 254 = 0x1a0 :=
  by rw [scan_instruction_pc 254 (by decide) (by decide)]; rfl
@[simp] theorem pc2955 : Artifact.submissionArtifact.instructionPC 255 = 0x1a1 :=
  by rw [scan_instruction_pc 255 (by decide) (by decide)]; rfl
@[simp] theorem pc2956 : Artifact.submissionArtifact.instructionPC 248 = 0x197 :=
  by rw [scan_instruction_pc 248 (by decide) (by decide)]; rfl
@[simp] theorem pc2957 : Artifact.submissionArtifact.instructionPC 248 = 0x197 :=
  by rw [scan_instruction_pc 248 (by decide) (by decide)]; rfl
@[simp] theorem pc2958 : Artifact.submissionArtifact.instructionPC 249 = 0x199 :=
  by rw [scan_instruction_pc 249 (by decide) (by decide)]; rfl
@[simp] theorem pc2959 : Artifact.submissionArtifact.instructionPC 250 = 0x19a :=
  by rw [scan_instruction_pc 250 (by decide) (by decide)]; rfl
@[simp] theorem pc2960 : Artifact.submissionArtifact.instructionPC 251 = 0x19c :=
  by rw [scan_instruction_pc 251 (by decide) (by decide)]; rfl
@[simp] theorem pc2961 : Artifact.submissionArtifact.instructionPC 252 = 0x19d :=
  by rw [scan_instruction_pc 252 (by decide) (by decide)]; rfl
@[simp] theorem pc2962 : Artifact.submissionArtifact.instructionPC 253 = 0x19e :=
  by rw [scan_instruction_pc 253 (by decide) (by decide)]; rfl
@[simp] theorem pc2963 : Artifact.submissionArtifact.instructionPC 254 = 0x1a0 :=
  by rw [scan_instruction_pc 254 (by decide) (by decide)]; rfl
@[simp] theorem pc2964 : Artifact.submissionArtifact.instructionPC 255 = 0x1a1 :=
  by rw [scan_instruction_pc 255 (by decide) (by decide)]; rfl
@[simp] theorem pc2965 : Artifact.submissionArtifact.instructionPC 256 = 0x1a2 :=
  by rw [scan_instruction_pc 256 (by decide) (by decide)]; rfl
@[simp] theorem pc2966 : Artifact.submissionArtifact.instructionPC 257 = 0x1a3 :=
  by rw [scan_instruction_pc 257 (by decide) (by decide)]; rfl
@[simp] theorem pc2967 : Artifact.submissionArtifact.instructionPC 258 = 0x1a4 :=
  by rw [scan_instruction_pc 258 (by decide) (by decide)]; rfl
@[simp] theorem pc2968 : Artifact.submissionArtifact.instructionPC 259 = 0x1a5 :=
  by rw [scan_instruction_pc 259 (by decide) (by decide)]; rfl
@[simp] theorem pc2969 : Artifact.submissionArtifact.instructionPC 260 = 0x1a8 :=
  by rw [scan_instruction_pc 260 (by decide) (by decide)]; rfl
@[simp] theorem pc2969a : Artifact.submissionArtifact.instructionPC 283 = 0x201 :=
  by rw [scan_instruction_pc 283 (by decide) (by decide)]; rfl
@[simp] theorem pc2970 : Artifact.submissionArtifact.instructionPC 285 = 0x203 :=
  by rw [scan_instruction_pc 285 (by decide) (by decide)]; rfl
@[simp] theorem pc2971 : Artifact.submissionArtifact.instructionPC 286 = 0x204 :=
  by rw [scan_instruction_pc 286 (by decide) (by decide)]; rfl
@[simp] theorem pc2972 : Artifact.submissionArtifact.instructionPC 287 = 0x205 :=
  by rw [scan_instruction_pc 287 (by decide) (by decide)]; rfl
@[simp] theorem pc2973 : Artifact.submissionArtifact.instructionPC 288 = 0x206 :=
  by rw [scan_instruction_pc 288 (by decide) (by decide)]; rfl
@[simp] theorem pc2974 : Artifact.submissionArtifact.instructionPC 289 = 0x207 :=
  by rw [scan_instruction_pc 289 (by decide) (by decide)]; rfl
@[simp] theorem pc2975 : Artifact.submissionArtifact.instructionPC 290 = 0x208 :=
  by rw [scan_instruction_pc 290 (by decide) (by decide)]; rfl
@[simp] theorem pc2976 : Artifact.submissionArtifact.instructionPC 291 = 0x209 :=
  by rw [scan_instruction_pc 291 (by decide) (by decide)]; rfl
@[simp] theorem pc2977 : Artifact.submissionArtifact.instructionPC 292 = 0x20a :=
  by rw [scan_instruction_pc 292 (by decide) (by decide)]; rfl
@[simp] theorem pc2978 : Artifact.submissionArtifact.instructionPC 293 = 0x20b :=
  by rw [scan_instruction_pc 293 (by decide) (by decide)]; rfl
@[simp] theorem pc2979 : Artifact.submissionArtifact.instructionPC 294 = 0x20c :=
  by rw [scan_instruction_pc 294 (by decide) (by decide)]; rfl
@[simp] theorem pc2980 : Artifact.submissionArtifact.instructionPC 295 = 0x20d :=
  by rw [scan_instruction_pc 295 (by decide) (by decide)]; rfl
@[simp] theorem pc2981 : Artifact.submissionArtifact.instructionPC 296 = 0x20e :=
  by rw [scan_instruction_pc 296 (by decide) (by decide)]; rfl
@[simp] theorem pc2982 : Artifact.submissionArtifact.instructionPC 297 = 0x210 :=
  by rw [scan_instruction_pc 297 (by decide) (by decide)]; rfl
@[simp] theorem pc_ins249 : Artifact.submissionArtifact.instructionPC 264 = 0x1ae :=
  by rw [scan_instruction_pc 264 (by decide) (by decide)]; rfl
@[simp] theorem pc_ins250 : Artifact.submissionArtifact.instructionPC 266 = 0x1b0 :=
  by rw [scan_instruction_pc 266 (by decide) (by decide)]; rfl
@[simp] theorem pc_ins251 : Artifact.submissionArtifact.instructionPC 267 = 0x1b3 :=
  by rw [scan_instruction_pc 267 (by decide) (by decide)]; rfl
@[simp] theorem pc_ins252 : Artifact.submissionArtifact.instructionPC 268 = 0x1b4 :=
  by rw [scan_instruction_pc 268 (by decide) (by decide)]; rfl
@[simp] theorem pc_ins253 : Artifact.submissionArtifact.instructionPC 269 = 0x1c9 :=
  by rw [scan_instruction_pc 269 (by decide) (by decide)]; rfl
@[simp] theorem pc_ins255 : Artifact.submissionArtifact.instructionPC 277 = 0x1fb :=
  by rw [scan_instruction_pc 277 (by decide) (by decide)]; rfl
@[simp] theorem pc_ins217 : Artifact.submissionArtifact.instructionPC 256 = 0x1a2 :=
  by rw [scan_instruction_pc 256 (by decide) (by decide)]; rfl
@[simp] theorem pc_ins218 : Artifact.submissionArtifact.instructionPC 257 = 0x1a3 :=
  by rw [scan_instruction_pc 257 (by decide) (by decide)]; rfl
@[simp] theorem pc_ins219 : Artifact.submissionArtifact.instructionPC 258 = 0x1a4 :=
  by rw [scan_instruction_pc 258 (by decide) (by decide)]; rfl
@[simp] theorem pc_ins220 : Artifact.submissionArtifact.instructionPC 259 = 0x1a5 :=
  by rw [scan_instruction_pc 259 (by decide) (by decide)]; rfl
@[simp] theorem pc_ins221 : Artifact.submissionArtifact.instructionPC 260 = 0x1a8 :=
  by rw [scan_instruction_pc 260 (by decide) (by decide)]; rfl
@[simp] theorem pc2983 : Artifact.submissionArtifact.instructionPC 276 = 0x1e6 :=
  by rw [scan_instruction_pc 276 (by decide) (by decide)]; rfl
@[simp] theorem pc2984 : Artifact.submissionArtifact.instructionPC 278 = 0x1fc :=
  by rw [scan_instruction_pc 278 (by decide) (by decide)]; rfl
@[simp] theorem pc2985 : Artifact.submissionArtifact.instructionPC 279 = 0x1fd :=
  by rw [scan_instruction_pc 279 (by decide) (by decide)]; rfl
@[simp] theorem pc2986 : Artifact.submissionArtifact.instructionPC 280 = 0x1fe :=
  by rw [scan_instruction_pc 280 (by decide) (by decide)]; rfl
@[simp] theorem pc2987 : Artifact.submissionArtifact.instructionPC 281 = 0x1ff :=
  by rw [scan_instruction_pc 281 (by decide) (by decide)]; rfl
@[simp] theorem pc2988 : Artifact.submissionArtifact.instructionPC 282 = 0x200 :=
  by rw [scan_instruction_pc 282 (by decide) (by decide)]; rfl
@[simp] theorem pc2989 : Artifact.submissionArtifact.instructionPC 201 = 0x15d :=
  by rw [scan_instruction_pc 201 (by decide) (by decide)]; rfl
@[simp] theorem pc2990 : Artifact.submissionArtifact.instructionPC 202 = 0x15e :=
  by rw [scan_instruction_pc 202 (by decide) (by decide)]; rfl
@[simp] theorem pc2991 : Artifact.submissionArtifact.instructionPC 203 = 0x15f :=
  by rw [scan_instruction_pc 203 (by decide) (by decide)]; rfl
@[simp] theorem pc2992 : Artifact.submissionArtifact.instructionPC 204 = 0x160 :=
  by rw [scan_instruction_pc 204 (by decide) (by decide)]; rfl
@[simp] theorem pc2993 : Artifact.submissionArtifact.instructionPC 205 = 0x162 :=
  by rw [scan_instruction_pc 205 (by decide) (by decide)]; rfl
@[simp] theorem pc2994 : Artifact.submissionArtifact.instructionPC 206 = 0x163 :=
  by rw [scan_instruction_pc 206 (by decide) (by decide)]; rfl
@[simp] theorem pc2995 : Artifact.submissionArtifact.instructionPC 207 = 0x165 :=
  by rw [scan_instruction_pc 207 (by decide) (by decide)]; rfl
@[simp] theorem pc2996 : Artifact.submissionArtifact.instructionPC 208 = 0x166 :=
  by rw [scan_instruction_pc 208 (by decide) (by decide)]; rfl
@[simp] theorem pc2997 : Artifact.submissionArtifact.instructionPC 209 = 0x168 :=
  by rw [scan_instruction_pc 209 (by decide) (by decide)]; rfl
@[simp] theorem pc2998 : Artifact.submissionArtifact.instructionPC 210 = 0x169 :=
  by rw [scan_instruction_pc 210 (by decide) (by decide)]; rfl
@[simp] theorem pc2999 : Artifact.submissionArtifact.instructionPC 211 = 0x16b :=
  by rw [scan_instruction_pc 211 (by decide) (by decide)]; rfl
@[simp] theorem pc3000 : Artifact.submissionArtifact.instructionPC 212 = 0x16c :=
  by rw [scan_instruction_pc 212 (by decide) (by decide)]; rfl
@[simp] theorem pc3001 : Artifact.submissionArtifact.instructionPC 213 = 0x16d :=
  by rw [scan_instruction_pc 213 (by decide) (by decide)]; rfl
@[simp] theorem pc3002 : Artifact.submissionArtifact.instructionPC 214 = 0x16f :=
  by rw [scan_instruction_pc 214 (by decide) (by decide)]; rfl
@[simp] theorem pc3003 : Artifact.submissionArtifact.instructionPC 215 = 0x170 :=
  by rw [scan_instruction_pc 215 (by decide) (by decide)]; rfl
@[simp] theorem pc3004 : Artifact.submissionArtifact.instructionPC 216 = 0x171 :=
  by rw [scan_instruction_pc 216 (by decide) (by decide)]; rfl
@[simp] theorem pc3005 : Artifact.submissionArtifact.instructionPC 217 = 0x172 :=
  by rw [scan_instruction_pc 217 (by decide) (by decide)]; rfl
@[simp] theorem pc3006 : Artifact.submissionArtifact.instructionPC 218 = 0x173 :=
  by rw [scan_instruction_pc 218 (by decide) (by decide)]; rfl
@[simp] theorem pc3007 : Artifact.submissionArtifact.instructionPC 219 = 0x174 :=
  by rw [scan_instruction_pc 219 (by decide) (by decide)]; rfl
@[simp] theorem pc3008 : Artifact.submissionArtifact.instructionPC 220 = 0x175 :=
  by rw [scan_instruction_pc 220 (by decide) (by decide)]; rfl
@[simp] theorem pc3009 : Artifact.submissionArtifact.instructionPC 221 = 0x176 :=
  by rw [scan_instruction_pc 221 (by decide) (by decide)]; rfl
@[simp] theorem pc3010 : Artifact.submissionArtifact.instructionPC 222 = 0x177 :=
  by rw [scan_instruction_pc 222 (by decide) (by decide)]; rfl
@[simp] theorem pc3011 : Artifact.submissionArtifact.instructionPC 223 = 0x178 :=
  by rw [scan_instruction_pc 223 (by decide) (by decide)]; rfl
@[simp] theorem pc3012 : Artifact.submissionArtifact.instructionPC 224 = 0x179 :=
  by rw [scan_instruction_pc 224 (by decide) (by decide)]; rfl
@[simp] theorem pc3013 : Artifact.submissionArtifact.instructionPC 225 = 0x17a :=
  by rw [scan_instruction_pc 225 (by decide) (by decide)]; rfl
@[simp] theorem pc3014 : Artifact.submissionArtifact.instructionPC 226 = 0x17b :=
  by rw [scan_instruction_pc 226 (by decide) (by decide)]; rfl
@[simp] theorem pc3015 : Artifact.submissionArtifact.instructionPC 227 = 0x17c :=
  by rw [scan_instruction_pc 227 (by decide) (by decide)]; rfl
@[simp] theorem pc3016 : Artifact.submissionArtifact.instructionPC 228 = 0x17d :=
  by rw [scan_instruction_pc 228 (by decide) (by decide)]; rfl
@[simp] theorem pc3017 : Artifact.submissionArtifact.instructionPC 229 = 0x17f :=
  by rw [scan_instruction_pc 229 (by decide) (by decide)]; rfl
@[simp] theorem pc3018 : Artifact.submissionArtifact.instructionPC 230 = 0x180 :=
  by rw [scan_instruction_pc 230 (by decide) (by decide)]; rfl
@[simp] theorem pc3019 : Artifact.submissionArtifact.instructionPC 231 = 0x181 :=
  by rw [scan_instruction_pc 231 (by decide) (by decide)]; rfl
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
