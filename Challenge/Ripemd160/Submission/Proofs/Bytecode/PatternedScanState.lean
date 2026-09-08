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
  scanPrefix ++ submissionInstructionsChunk0.take 150

private def scanSuffix : List YulEvmCompiler.Instr :=
  submissionInstructionsChunk0.drop 150 ++ submissionInstructionsChunk1 ++ submissionInstructionsChunk2 ++ submissionInstructionsChunk3 ++ submissionInstructionsChunk4 ++ submissionInstructionsChunk5 ++ submissionInstructionsChunk6 ++ submissionInstructionsChunk7 ++ submissionInstructionsChunk8 ++ submissionInstructionsChunk9 ++ submissionInstructionsChunk10 ++ submissionInstructionsChunk11 ++ submissionInstructionsChunk12 ++ submissionInstructionsChunk13 ++ submissionInstructionsChunk14 ++ submissionInstructionsChunk15 ++ submissionInstructionsChunk16 ++ submissionInstructionsChunk17 ++ submissionInstructionsChunk18 ++ submissionInstructionsChunk19 ++ submissionInstructionsChunk20 ++ submissionInstructionsChunk21

private theorem scanBefore_length : scanBefore.length = 150 := by
  simp [scanBefore, scanPrefix]

private theorem scanSuffix_length : scanSuffix.length = 4159 := by
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
      submissionInstructionsChunk0.take 150 ++ submissionInstructionsChunk0.drop 150 := by
    exact (List.take_append_drop 150 submissionInstructionsChunk0).symm
  rw [hprefix]
  conv_lhs => rw [hchunk]
  simp only [scanBefore, scanSuffix, List.append_assoc, List.append_nil]

private theorem scanBefore_pc :
    (YulEvmCompiler.assembleBytes scanBefore).length = 256 := by rfl

private theorem artifact_instruction_projection :
    Artifact.submissionArtifact.instructions = Artifact.submissionInstructions := by rfl

private theorem scan_instruction_at (index : Nat)
    (hlo : 150 ≤ index) (hhi : index < 4309) :
    Artifact.submissionInstructions[index]? = scanSuffix[index - 150]? := by
  have hi : index - 150 < scanSuffix.length := by
    rw [scanSuffix_length]
    omega
  have h := ArtifactSegment.getElem?_segment Artifact.submissionArtifact
    scanBefore scanSuffix [] artifact_scan_split (index - 150) hi
  simpa only [artifact_instruction_projection, scanBefore_length,
    Nat.add_sub_of_le hlo] using h

private theorem scan_instruction_pc (index : Nat)
    (hlo : 150 ≤ index) (hhi : index ≤ 4309) :
    Artifact.submissionArtifact.instructionPC index =
      256 + (YulEvmCompiler.assembleBytes (scanSuffix.take (index - 150))).length := by
  have hi : index - 150 ≤ scanSuffix.length := by
    rw [scanSuffix_length]
    omega
  have h := ArtifactSegment.instructionPC_segment_of_bounds Artifact.submissionArtifact
    scanBefore scanSuffix [] 150 256 artifact_scan_split scanBefore_length
    scanBefore_pc (index - 150) hi
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
  [pushAt 150 1 255,
   pushAt 151 0 0,
   opAt 152 .NOT,
   opAt 153 .DIV,
   pushAt 154 32 3244493450063667868678674439968361782956185527883176199882357678282131398018,
   opAt 155 (.Dup ⟨1, by decide⟩),
   pushAt 156 1 7,
   opAt 157 .SHL,
   opAt 158 (.Dup ⟨0, by decide⟩),
   opAt 159 .NOT,
   opAt 160 (.Swap ⟨0, by decide⟩),
   opAt 161 (.Swap ⟨2, by decide⟩),
   opAt 162 (.Dup ⟨2, by decide⟩),
   opAt 163 (.Dup ⟨2, by decide⟩),
   opAt 164 .AND,
   pushAt 165 0 0,
   pushAt 166 0 0,
   pushAt 167 0 0]

/-- Derive the expected word and test for a straddler. -/
def wordPath : List Located :=
  [opAt 168 .JUMPDEST, opAt 169 (.Dup ⟨0, by decide⟩),
   opAt 170 (.Dup ⟨5, by decide⟩), opAt 171 .MUL,
   opAt 172 (.Dup ⟨0, by decide⟩), opAt 173 (.Dup ⟨7, by decide⟩),
   opAt 174 .AND, opAt 175 (.Dup ⟨5, by decide⟩), opAt 176 .ADD,
   opAt 177 (.Dup ⟨1, by decide⟩), opAt 178 (.Dup ⟨9, by decide⟩),
   opAt 179 .XOR, opAt 180 (.Dup ⟨10, by decide⟩), opAt 181 .AND,
   opAt 182 .XOR, opAt 183 (.Dup ⟨3, by decide⟩), pushAt 184 1 255,
   opAt 185 .AND, pushAt 186 1 224, opAt 187 .EQ, pushAt 188 2 422,
   opAt 189 .JUMPI]

/-- Fold one word into the accumulator and advance. -/
def comparePath : List Located :=
  [opAt 190 .JUMPDEST, opAt 191 (.Dup ⟨3, by decide⟩),
   opAt 192 .CALLDATALOAD, opAt 193 .XOR, opAt 194 (.Dup ⟨4, by decide⟩),
   opAt 195 .OR, opAt 196 (.Swap ⟨3, by decide⟩), opAt 197 .POP,
   opAt 198 .POP, pushAt 199 1 160,
   opAt 200 .ADD, pushAt 201 1 255, opAt 202 .AND,
   opAt 203 (.Swap ⟨0, by decide⟩), pushAt 204 1 32, opAt 205 .ADD,
   opAt 206 (.Swap ⟨0, by decide⟩), opAt 207 (.Dup ⟨1, by decide⟩), pushAt 208 2 992, opAt 209 .GT,
   pushAt 210 2 307, opAt 211 .JUMPI]

/-- The padded tail word, the cleanup and the miss test. -/
def tailPath : List Located :=
  [pushAt 212 2 992, opAt 213 .CALLDATALOAD,
   pushAt 214 8 9848759918901945995, pushAt 215 1 192, opAt 216 .SHL,
   opAt 217 .XOR, opAt 218 (.Dup ⟨3, by decide⟩), opAt 219 .OR,
   opAt 220 (.Swap ⟨2, by decide⟩), opAt 221 .POP,
   opAt 222 (.Swap ⟨1, by decide⟩), opAt 223 (.Swap ⟨6, by decide⟩),
   opAt 224 .POP, opAt 225 .POP, opAt 226 .POP, opAt 227 .POP,
   opAt 228 .POP, opAt 229 .POP, opAt 230 .POP, pushAt 231 1 3,
   opAt 232 .JUMPI]

/-- Store and return the stored digest. -/
def returnPath : List Located :=
  [pushAt 233 20 766350606435067737561421097975693824639675460820,
   pushAt 234 0 0, opAt 235 .MSTORE, pushAt 236 1 32, pushAt 237 0 0,
   opAt 238 .RETURN]

/-- Shift the correction constant out of `M`. -/
def straddleCorrPath : List Located :=
  [opAt 239 .JUMPDEST, opAt 240 (.Dup ⟨6, by decide⟩),
   opAt 241 (.Dup ⟨4, by decide⟩), pushAt 242 1 8, opAt 243 .SHR,
   pushAt 244 1 5, opAt 245 .MUL, pushAt 246 1 27, opAt 247 .SUB,
   pushAt 248 1 3, opAt 249 .SHL, opAt 250 .SHR, pushAt 251 1 11,
   opAt 252 .MUL]

/-- Apply the correction to the expected word. -/
def straddleAddPath : List Located :=
  [opAt 253 (.Dup ⟨1, by decide⟩), opAt 254 (.Dup ⟨9, by decide⟩),
   opAt 255 .AND, opAt 256 (.Dup ⟨1, by decide⟩), opAt 257 .ADD,
   opAt 258 (.Dup ⟨2, by decide⟩), opAt 259 (.Dup ⟨12, by decide⟩),
   opAt 260 .AND, opAt 261 .XOR, opAt 262 (.Swap ⟨1, by decide⟩),
   opAt 263 .POP, opAt 264 .POP]

/-- Bump the scalar and rejoin the scan. -/
def straddleBackPath : List Located :=
  [opAt 265 (.Dup ⟨2, by decide⟩), pushAt 266 1 11, opAt 267 .ADD,
   opAt 268 (.Swap ⟨2, by decide⟩), opAt 269 .POP, pushAt 270 2 333,
   opAt 271 .JUMP]


@[simp] theorem pc2903 : Artifact.submissionArtifact.instructionPC 150 = 255 :=
  by rw [scan_instruction_pc 150 (by decide) (by decide)]; rfl
@[simp] theorem pc2904 : Artifact.submissionArtifact.instructionPC 150 = 255 :=
  by rw [scan_instruction_pc 150 (by decide) (by decide)]; rfl
@[simp] theorem pc2905 : Artifact.submissionArtifact.instructionPC 154 = 260 :=
  by rw [scan_instruction_pc 154 (by decide) (by decide)]; rfl
@[simp] theorem pc2906 : Artifact.submissionArtifact.instructionPC 159 = 298 :=
  by rw [scan_instruction_pc 159 (by decide) (by decide)]; rfl
@[simp] theorem pc2907 : Artifact.submissionArtifact.instructionPC 161 = 300 :=
  by rw [scan_instruction_pc 161 (by decide) (by decide)]; rfl
@[simp] theorem pc2908 : Artifact.submissionArtifact.instructionPC 162 = 301 :=
  by rw [scan_instruction_pc 162 (by decide) (by decide)]; rfl
@[simp] theorem pc2909 : Artifact.submissionArtifact.instructionPC 163 = 302 :=
  by rw [scan_instruction_pc 163 (by decide) (by decide)]; rfl
@[simp] theorem pc2910 : Artifact.submissionArtifact.instructionPC 164 = 303 :=
  by rw [scan_instruction_pc 164 (by decide) (by decide)]; rfl
@[simp] theorem pc2911 : Artifact.submissionArtifact.instructionPC 165 = 304 :=
  by rw [scan_instruction_pc 165 (by decide) (by decide)]; rfl
@[simp] theorem pc2912 : Artifact.submissionArtifact.instructionPC 166 = 305 :=
  by rw [scan_instruction_pc 166 (by decide) (by decide)]; rfl
@[simp] theorem pc2913 : Artifact.submissionArtifact.instructionPC 167 = 306 :=
  by rw [scan_instruction_pc 167 (by decide) (by decide)]; rfl
@[simp] theorem pc2914 : Artifact.submissionArtifact.instructionPC 168 = 307 :=
  by rw [scan_instruction_pc 168 (by decide) (by decide)]; rfl
@[simp] theorem pc2915 : Artifact.submissionArtifact.instructionPC 169 = 308 :=
  by rw [scan_instruction_pc 169 (by decide) (by decide)]; rfl
@[simp] theorem pc2916 : Artifact.submissionArtifact.instructionPC 170 = 309 :=
  by rw [scan_instruction_pc 170 (by decide) (by decide)]; rfl
@[simp] theorem pc2917 : Artifact.submissionArtifact.instructionPC 171 = 310 :=
  by rw [scan_instruction_pc 171 (by decide) (by decide)]; rfl
@[simp] theorem pc2918 : Artifact.submissionArtifact.instructionPC 172 = 311 :=
  by rw [scan_instruction_pc 172 (by decide) (by decide)]; rfl
@[simp] theorem pc2919 : Artifact.submissionArtifact.instructionPC 173 = 312 :=
  by rw [scan_instruction_pc 173 (by decide) (by decide)]; rfl
@[simp] theorem pc2920 : Artifact.submissionArtifact.instructionPC 174 = 313 :=
  by rw [scan_instruction_pc 174 (by decide) (by decide)]; rfl
@[simp] theorem pc2921 : Artifact.submissionArtifact.instructionPC 175 = 314 :=
  by rw [scan_instruction_pc 175 (by decide) (by decide)]; rfl
@[simp] theorem pc2922 : Artifact.submissionArtifact.instructionPC 176 = 315 :=
  by rw [scan_instruction_pc 176 (by decide) (by decide)]; rfl
@[simp] theorem pc2923 : Artifact.submissionArtifact.instructionPC 177 = 316 :=
  by rw [scan_instruction_pc 177 (by decide) (by decide)]; rfl
@[simp] theorem pc2924 : Artifact.submissionArtifact.instructionPC 178 = 317 :=
  by rw [scan_instruction_pc 178 (by decide) (by decide)]; rfl
@[simp] theorem pc2925 : Artifact.submissionArtifact.instructionPC 179 = 318 :=
  by rw [scan_instruction_pc 179 (by decide) (by decide)]; rfl
@[simp] theorem pc2926 : Artifact.submissionArtifact.instructionPC 180 = 319 :=
  by rw [scan_instruction_pc 180 (by decide) (by decide)]; rfl
@[simp] theorem pc2927 : Artifact.submissionArtifact.instructionPC 181 = 320 :=
  by rw [scan_instruction_pc 181 (by decide) (by decide)]; rfl
@[simp] theorem pc2928 : Artifact.submissionArtifact.instructionPC 182 = 321 :=
  by rw [scan_instruction_pc 182 (by decide) (by decide)]; rfl
@[simp] theorem pc2929 : Artifact.submissionArtifact.instructionPC 183 = 322 :=
  by rw [scan_instruction_pc 183 (by decide) (by decide)]; rfl
@[simp] theorem pc2930 : Artifact.submissionArtifact.instructionPC 184 = 323 :=
  by rw [scan_instruction_pc 184 (by decide) (by decide)]; rfl
@[simp] theorem pc2931 : Artifact.submissionArtifact.instructionPC 185 = 325 :=
  by rw [scan_instruction_pc 185 (by decide) (by decide)]; rfl
@[simp] theorem pc2932 : Artifact.submissionArtifact.instructionPC 186 = 326 :=
  by rw [scan_instruction_pc 186 (by decide) (by decide)]; rfl
@[simp] theorem pc2933 : Artifact.submissionArtifact.instructionPC 187 = 328 :=
  by rw [scan_instruction_pc 187 (by decide) (by decide)]; rfl
@[simp] theorem pc2934 : Artifact.submissionArtifact.instructionPC 188 = 329 :=
  by rw [scan_instruction_pc 188 (by decide) (by decide)]; rfl
@[simp] theorem pc2935 : Artifact.submissionArtifact.instructionPC 189 = 332 :=
  by rw [scan_instruction_pc 189 (by decide) (by decide)]; rfl
@[simp] theorem pc2936 : Artifact.submissionArtifact.instructionPC 190 = 333 :=
  by rw [scan_instruction_pc 190 (by decide) (by decide)]; rfl
@[simp] theorem pc2937 : Artifact.submissionArtifact.instructionPC 191 = 334 :=
  by rw [scan_instruction_pc 191 (by decide) (by decide)]; rfl
@[simp] theorem pc2938 : Artifact.submissionArtifact.instructionPC 192 = 335 :=
  by rw [scan_instruction_pc 192 (by decide) (by decide)]; rfl
@[simp] theorem pc2939 : Artifact.submissionArtifact.instructionPC 193 = 336 :=
  by rw [scan_instruction_pc 193 (by decide) (by decide)]; rfl
@[simp] theorem pc2940 : Artifact.submissionArtifact.instructionPC 194 = 337 :=
  by rw [scan_instruction_pc 194 (by decide) (by decide)]; rfl
@[simp] theorem pc2941 : Artifact.submissionArtifact.instructionPC 195 = 338 :=
  by rw [scan_instruction_pc 195 (by decide) (by decide)]; rfl
@[simp] theorem pc2942 : Artifact.submissionArtifact.instructionPC 196 = 339 :=
  by rw [scan_instruction_pc 196 (by decide) (by decide)]; rfl
@[simp] theorem pc2943 : Artifact.submissionArtifact.instructionPC 197 = 340 :=
  by rw [scan_instruction_pc 197 (by decide) (by decide)]; rfl
@[simp] theorem pc2944 : Artifact.submissionArtifact.instructionPC 198 = 341 :=
  by rw [scan_instruction_pc 198 (by decide) (by decide)]; rfl
@[simp] theorem pc2945 : Artifact.submissionArtifact.instructionPC 199 = 342 :=
  by rw [scan_instruction_pc 199 (by decide) (by decide)]; rfl
@[simp] theorem pc2946 : Artifact.submissionArtifact.instructionPC 199 = 342 :=
  by rw [scan_instruction_pc 199 (by decide) (by decide)]; rfl
@[simp] theorem pc2947 : Artifact.submissionArtifact.instructionPC 200 = 344 :=
  by rw [scan_instruction_pc 200 (by decide) (by decide)]; rfl
@[simp] theorem pc2948 : Artifact.submissionArtifact.instructionPC 201 = 345 :=
  by rw [scan_instruction_pc 201 (by decide) (by decide)]; rfl
@[simp] theorem pc2949 : Artifact.submissionArtifact.instructionPC 202 = 347 :=
  by rw [scan_instruction_pc 202 (by decide) (by decide)]; rfl
@[simp] theorem pc2950 : Artifact.submissionArtifact.instructionPC 203 = 348 :=
  by rw [scan_instruction_pc 203 (by decide) (by decide)]; rfl
@[simp] theorem pc2951 : Artifact.submissionArtifact.instructionPC 203 = 348 :=
  by rw [scan_instruction_pc 203 (by decide) (by decide)]; rfl
@[simp] theorem pc2952 : Artifact.submissionArtifact.instructionPC 203 = 348 :=
  by rw [scan_instruction_pc 203 (by decide) (by decide)]; rfl
@[simp] theorem pc2953 : Artifact.submissionArtifact.instructionPC 204 = 349 :=
  by rw [scan_instruction_pc 204 (by decide) (by decide)]; rfl
@[simp] theorem pc2954 : Artifact.submissionArtifact.instructionPC 205 = 351 :=
  by rw [scan_instruction_pc 205 (by decide) (by decide)]; rfl
@[simp] theorem pc2955 : Artifact.submissionArtifact.instructionPC 206 = 352 :=
  by rw [scan_instruction_pc 206 (by decide) (by decide)]; rfl
@[simp] theorem pc2956 : Artifact.submissionArtifact.instructionPC 207 = 353 :=
  by rw [scan_instruction_pc 207 (by decide) (by decide)]; rfl
@[simp] theorem pc2957 : Artifact.submissionArtifact.instructionPC 207 = 353 :=
  by rw [scan_instruction_pc 207 (by decide) (by decide)]; rfl
@[simp] theorem pc2958 : Artifact.submissionArtifact.instructionPC 208 = 354 :=
  by rw [scan_instruction_pc 208 (by decide) (by decide)]; rfl
@[simp] theorem pc2959 : Artifact.submissionArtifact.instructionPC 209 = 357 :=
  by rw [scan_instruction_pc 209 (by decide) (by decide)]; rfl
@[simp] theorem pc2960 : Artifact.submissionArtifact.instructionPC 210 = 358 :=
  by rw [scan_instruction_pc 210 (by decide) (by decide)]; rfl
@[simp] theorem pc2961 : Artifact.submissionArtifact.instructionPC 211 = 361 :=
  by rw [scan_instruction_pc 211 (by decide) (by decide)]; rfl
@[simp] theorem pc2962 : Artifact.submissionArtifact.instructionPC 212 = 362 :=
  by rw [scan_instruction_pc 212 (by decide) (by decide)]; rfl
@[simp] theorem pc2963 : Artifact.submissionArtifact.instructionPC 213 = 365 :=
  by rw [scan_instruction_pc 213 (by decide) (by decide)]; rfl
@[simp] theorem pc2964 : Artifact.submissionArtifact.instructionPC 214 = 366 :=
  by rw [scan_instruction_pc 214 (by decide) (by decide)]; rfl
@[simp] theorem pc2965 : Artifact.submissionArtifact.instructionPC 215 = 375 :=
  by rw [scan_instruction_pc 215 (by decide) (by decide)]; rfl
@[simp] theorem pc2966 : Artifact.submissionArtifact.instructionPC 216 = 377 :=
  by rw [scan_instruction_pc 216 (by decide) (by decide)]; rfl
@[simp] theorem pc2967 : Artifact.submissionArtifact.instructionPC 217 = 378 :=
  by rw [scan_instruction_pc 217 (by decide) (by decide)]; rfl
@[simp] theorem pc2968 : Artifact.submissionArtifact.instructionPC 218 = 379 :=
  by rw [scan_instruction_pc 218 (by decide) (by decide)]; rfl
@[simp] theorem pc2969 : Artifact.submissionArtifact.instructionPC 219 = 380 :=
  by rw [scan_instruction_pc 219 (by decide) (by decide)]; rfl
@[simp] theorem pc2970 : Artifact.submissionArtifact.instructionPC 220 = 381 :=
  by rw [scan_instruction_pc 220 (by decide) (by decide)]; rfl
@[simp] theorem pc2971 : Artifact.submissionArtifact.instructionPC 221 = 382 :=
  by rw [scan_instruction_pc 221 (by decide) (by decide)]; rfl
@[simp] theorem pc2972 : Artifact.submissionArtifact.instructionPC 222 = 383 :=
  by rw [scan_instruction_pc 222 (by decide) (by decide)]; rfl
@[simp] theorem pc2973 : Artifact.submissionArtifact.instructionPC 223 = 384 :=
  by rw [scan_instruction_pc 223 (by decide) (by decide)]; rfl
@[simp] theorem pc2974 : Artifact.submissionArtifact.instructionPC 224 = 385 :=
  by rw [scan_instruction_pc 224 (by decide) (by decide)]; rfl
@[simp] theorem pc2975 : Artifact.submissionArtifact.instructionPC 225 = 386 :=
  by rw [scan_instruction_pc 225 (by decide) (by decide)]; rfl
@[simp] theorem pc2976 : Artifact.submissionArtifact.instructionPC 226 = 387 :=
  by rw [scan_instruction_pc 226 (by decide) (by decide)]; rfl
@[simp] theorem pc2977 : Artifact.submissionArtifact.instructionPC 227 = 388 :=
  by rw [scan_instruction_pc 227 (by decide) (by decide)]; rfl
@[simp] theorem pc2978 : Artifact.submissionArtifact.instructionPC 228 = 389 :=
  by rw [scan_instruction_pc 228 (by decide) (by decide)]; rfl
@[simp] theorem pc2979 : Artifact.submissionArtifact.instructionPC 229 = 390 :=
  by rw [scan_instruction_pc 229 (by decide) (by decide)]; rfl
@[simp] theorem pc2980 : Artifact.submissionArtifact.instructionPC 230 = 391 :=
  by rw [scan_instruction_pc 230 (by decide) (by decide)]; rfl
@[simp] theorem pc2981 : Artifact.submissionArtifact.instructionPC 231 = 392 :=
  by rw [scan_instruction_pc 231 (by decide) (by decide)]; rfl
@[simp] theorem pc2982 : Artifact.submissionArtifact.instructionPC 232 = 394 :=
  by rw [scan_instruction_pc 232 (by decide) (by decide)]; rfl
@[simp] theorem pc2983 : Artifact.submissionArtifact.instructionPC 233 = 395 :=
  by rw [scan_instruction_pc 233 (by decide) (by decide)]; rfl
@[simp] theorem pc2984 : Artifact.submissionArtifact.instructionPC 234 = 416 :=
  by rw [scan_instruction_pc 234 (by decide) (by decide)]; rfl
@[simp] theorem pc2985 : Artifact.submissionArtifact.instructionPC 235 = 417 :=
  by rw [scan_instruction_pc 235 (by decide) (by decide)]; rfl
@[simp] theorem pc2986 : Artifact.submissionArtifact.instructionPC 236 = 418 :=
  by rw [scan_instruction_pc 236 (by decide) (by decide)]; rfl
@[simp] theorem pc2987 : Artifact.submissionArtifact.instructionPC 237 = 420 :=
  by rw [scan_instruction_pc 237 (by decide) (by decide)]; rfl
@[simp] theorem pc2988 : Artifact.submissionArtifact.instructionPC 238 = 421 :=
  by rw [scan_instruction_pc 238 (by decide) (by decide)]; rfl
@[simp] theorem pc2989 : Artifact.submissionArtifact.instructionPC 239 = 422 :=
  by rw [scan_instruction_pc 239 (by decide) (by decide)]; rfl
@[simp] theorem pc2990 : Artifact.submissionArtifact.instructionPC 240 = 423 :=
  by rw [scan_instruction_pc 240 (by decide) (by decide)]; rfl
@[simp] theorem pc2991 : Artifact.submissionArtifact.instructionPC 241 = 424 :=
  by rw [scan_instruction_pc 241 (by decide) (by decide)]; rfl
@[simp] theorem pc2992 : Artifact.submissionArtifact.instructionPC 242 = 425 :=
  by rw [scan_instruction_pc 242 (by decide) (by decide)]; rfl
@[simp] theorem pc2993 : Artifact.submissionArtifact.instructionPC 243 = 427 :=
  by rw [scan_instruction_pc 243 (by decide) (by decide)]; rfl
@[simp] theorem pc2994 : Artifact.submissionArtifact.instructionPC 244 = 428 :=
  by rw [scan_instruction_pc 244 (by decide) (by decide)]; rfl
@[simp] theorem pc2995 : Artifact.submissionArtifact.instructionPC 245 = 430 :=
  by rw [scan_instruction_pc 245 (by decide) (by decide)]; rfl
@[simp] theorem pc2996 : Artifact.submissionArtifact.instructionPC 246 = 431 :=
  by rw [scan_instruction_pc 246 (by decide) (by decide)]; rfl
@[simp] theorem pc2997 : Artifact.submissionArtifact.instructionPC 247 = 433 :=
  by rw [scan_instruction_pc 247 (by decide) (by decide)]; rfl
@[simp] theorem pc2998 : Artifact.submissionArtifact.instructionPC 248 = 434 :=
  by rw [scan_instruction_pc 248 (by decide) (by decide)]; rfl
@[simp] theorem pc2999 : Artifact.submissionArtifact.instructionPC 249 = 436 :=
  by rw [scan_instruction_pc 249 (by decide) (by decide)]; rfl
@[simp] theorem pc3000 : Artifact.submissionArtifact.instructionPC 250 = 437 :=
  by rw [scan_instruction_pc 250 (by decide) (by decide)]; rfl
@[simp] theorem pc3001 : Artifact.submissionArtifact.instructionPC 251 = 438 :=
  by rw [scan_instruction_pc 251 (by decide) (by decide)]; rfl
@[simp] theorem pc3002 : Artifact.submissionArtifact.instructionPC 252 = 440 :=
  by rw [scan_instruction_pc 252 (by decide) (by decide)]; rfl
@[simp] theorem pc3003 : Artifact.submissionArtifact.instructionPC 253 = 441 :=
  by rw [scan_instruction_pc 253 (by decide) (by decide)]; rfl
@[simp] theorem pc3004 : Artifact.submissionArtifact.instructionPC 254 = 442 :=
  by rw [scan_instruction_pc 254 (by decide) (by decide)]; rfl
@[simp] theorem pc3005 : Artifact.submissionArtifact.instructionPC 255 = 443 :=
  by rw [scan_instruction_pc 255 (by decide) (by decide)]; rfl
@[simp] theorem pc3006 : Artifact.submissionArtifact.instructionPC 256 = 444 :=
  by rw [scan_instruction_pc 256 (by decide) (by decide)]; rfl
@[simp] theorem pc3007 : Artifact.submissionArtifact.instructionPC 257 = 445 :=
  by rw [scan_instruction_pc 257 (by decide) (by decide)]; rfl
@[simp] theorem pc3008 : Artifact.submissionArtifact.instructionPC 258 = 446 :=
  by rw [scan_instruction_pc 258 (by decide) (by decide)]; rfl
@[simp] theorem pc3009 : Artifact.submissionArtifact.instructionPC 259 = 447 :=
  by rw [scan_instruction_pc 259 (by decide) (by decide)]; rfl
@[simp] theorem pc3010 : Artifact.submissionArtifact.instructionPC 260 = 448 :=
  by rw [scan_instruction_pc 260 (by decide) (by decide)]; rfl
@[simp] theorem pc3011 : Artifact.submissionArtifact.instructionPC 261 = 449 :=
  by rw [scan_instruction_pc 261 (by decide) (by decide)]; rfl
@[simp] theorem pc3012 : Artifact.submissionArtifact.instructionPC 262 = 450 :=
  by rw [scan_instruction_pc 262 (by decide) (by decide)]; rfl
@[simp] theorem pc3013 : Artifact.submissionArtifact.instructionPC 263 = 451 :=
  by rw [scan_instruction_pc 263 (by decide) (by decide)]; rfl
@[simp] theorem pc3014 : Artifact.submissionArtifact.instructionPC 264 = 452 :=
  by rw [scan_instruction_pc 264 (by decide) (by decide)]; rfl
@[simp] theorem pc3015 : Artifact.submissionArtifact.instructionPC 265 = 453 :=
  by rw [scan_instruction_pc 265 (by decide) (by decide)]; rfl
@[simp] theorem pc3016 : Artifact.submissionArtifact.instructionPC 266 = 454 :=
  by rw [scan_instruction_pc 266 (by decide) (by decide)]; rfl
@[simp] theorem pc3017 : Artifact.submissionArtifact.instructionPC 267 = 456 :=
  by rw [scan_instruction_pc 267 (by decide) (by decide)]; rfl
@[simp] theorem pc3018 : Artifact.submissionArtifact.instructionPC 268 = 457 :=
  by rw [scan_instruction_pc 268 (by decide) (by decide)]; rfl
@[simp] theorem pc3019 : Artifact.submissionArtifact.instructionPC 269 = 458 :=
  by rw [scan_instruction_pc 269 (by decide) (by decide)]; rfl
@[simp] theorem pc3020 : Artifact.submissionArtifact.instructionPC 270 = 459 :=
  by rw [scan_instruction_pc 270 (by decide) (by decide)]; rfl
@[simp] theorem pc3021 : Artifact.submissionArtifact.instructionPC 271 = 462 :=
  by rw [scan_instruction_pc 271 (by decide) (by decide)]; rfl
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
