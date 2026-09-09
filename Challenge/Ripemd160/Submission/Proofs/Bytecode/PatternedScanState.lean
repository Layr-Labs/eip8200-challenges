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
  scanPrefix ++ submissionInstructionsChunk0.take 150

private def scanSuffix : List YulEvmCompiler.Instr :=
  submissionInstructionsChunk0.drop 150 ++ submissionInstructionsChunk1 ++ submissionInstructionsChunk2 ++ submissionInstructionsChunk3 ++ submissionInstructionsChunk4 ++ submissionInstructionsChunk5 ++ submissionInstructionsChunk6 ++ submissionInstructionsChunk7 ++ submissionInstructionsChunk8 ++ submissionInstructionsChunk9 ++ submissionInstructionsChunk10 ++ submissionInstructionsChunk11 ++ submissionInstructionsChunk12 ++ submissionInstructionsChunk13 ++ submissionInstructionsChunk14 ++ submissionInstructionsChunk15 ++ submissionInstructionsChunk16 ++ submissionInstructionsChunk17 ++ submissionInstructionsChunk18 ++ submissionInstructionsChunk19 ++ submissionInstructionsChunk20

private theorem scanBefore_length : scanBefore.length = 150 := by
  simp [scanBefore, scanPrefix]

private theorem scanSuffix_length : scanSuffix.length = 4014 := by
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
      submissionInstructionsChunk0.take 150 ++ submissionInstructionsChunk0.drop 150 := by
    exact (List.take_append_drop 150 submissionInstructionsChunk0).symm
  rw [hprefix]
  conv_lhs => rw [hchunk]
  simp only [scanBefore, scanSuffix, List.append_assoc, List.append_nil]

private theorem scanBefore_pc :
    (YulEvmCompiler.assembleBytes scanBefore).length = 238 := by rfl

private theorem artifact_instruction_projection :
    Artifact.submissionArtifact.instructions = Artifact.submissionInstructions := by rfl

private theorem scan_instruction_at (index : Nat)
    (hlo : 150 ≤ index) (hhi : index < 4144) :
    Artifact.submissionInstructions[index]? = scanSuffix[index - 150]? := by
  have hi : index - 150 < scanSuffix.length := by
    rw [scanSuffix_length]
    omega
  have h := ArtifactSegment.getElem?_segment Artifact.submissionArtifact
    scanBefore scanSuffix [] artifact_scan_split (index - 150) hi
  simpa only [artifact_instruction_projection, scanBefore_length,
    Nat.add_sub_of_le hlo] using h

private theorem scan_instruction_pc (index : Nat)
    (hlo : 150 ≤ index) (hhi : index ≤ 4144) :
    Artifact.submissionArtifact.instructionPC index =
      238 + (YulEvmCompiler.assembleBytes (scanSuffix.take (index - 150))).length := by
  have hi : index - 150 ≤ scanSuffix.length := by
    rw [scanSuffix_length]
    omega
  have h := ArtifactSegment.instructionPC_segment_of_bounds Artifact.submissionArtifact
    scanBefore scanSuffix [] 150 238 artifact_scan_split scanBefore_length
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
  [pushAt 160 1 255,
   pushAt 161 0 0,
   opAt 162 .NOT,
   opAt 163 .DIV,
   pushAt 164 32 3244493450063667868678674439968361782956185527883176199882357678282131398018,
   opAt 165 (.Dup ⟨1, by decide⟩),
   pushAt 166 1 7,
   opAt 167 .SHL,
   opAt 168 (.Dup ⟨0, by decide⟩),
   opAt 169 .NOT,
   opAt 170 (.Swap ⟨0, by decide⟩),
   opAt 171 (.Swap ⟨2, by decide⟩),
   opAt 172 (.Dup ⟨2, by decide⟩),
   opAt 173 (.Dup ⟨2, by decide⟩),
   opAt 174 .AND,
   pushAt 175 0 0,
   pushAt 176 0 0,
   pushAt 177 0 0]

/-- Derive the expected word and test for a straddler. -/
def wordPath : List Located :=
  [opAt 178 .JUMPDEST, opAt 179 (.Dup ⟨0, by decide⟩),
   opAt 180 (.Dup ⟨5, by decide⟩), opAt 181 .MUL,
   opAt 182 (.Dup ⟨0, by decide⟩), opAt 183 (.Dup ⟨7, by decide⟩),
   opAt 184 .AND, opAt 185 (.Dup ⟨5, by decide⟩), opAt 186 .ADD,
   opAt 187 (.Dup ⟨1, by decide⟩), opAt 188 (.Dup ⟨9, by decide⟩),
   opAt 189 .XOR, opAt 190 (.Dup ⟨10, by decide⟩), opAt 191 .AND,
   opAt 192 .XOR, opAt 193 (.Dup ⟨3, by decide⟩), pushAt 194 1 255,
   opAt 195 .AND, pushAt 196 1 224, opAt 197 .EQ, pushAt 198 2 463,
   opAt 199 .JUMPI]

/-- Fold one word into the accumulator and advance. -/
def comparePath : List Located :=
  [opAt 200 .JUMPDEST, opAt 201 (.Dup ⟨3, by decide⟩), opAt 202 .CALLDATALOAD, opAt 203 .XOR,
   opAt 204 (.Dup ⟨3, by decide⟩), opAt 205 .CALLDATASIZE, opAt 206 .SUB, pushAt 207 1 32,
   opAt 208 (.Dup ⟨1, by decide⟩), opAt 209 .LT, opAt 210 (.Swap ⟨0, by decide⟩),
   pushAt 211 1 32, opAt 212 .SUB, opAt 213 .MUL, pushAt 214 1 3, opAt 215 .SHL,
   opAt 216 .SHR, opAt 217 (.Dup ⟨4, by decide⟩), opAt 218 .OR,
   opAt 219 (.Swap ⟨3, by decide⟩), opAt 220 .POP, opAt 221 .POP, pushAt 222 1 160,
   opAt 223 .ADD, pushAt 224 1 255, opAt 225 .AND, opAt 226 (.Swap ⟨0, by decide⟩),
   pushAt 227 1 32, opAt 228 .ADD, opAt 229 (.Swap ⟨0, by decide⟩), opAt 230 .CALLDATASIZE,
   opAt 231 (.Dup ⟨2, by decide⟩), opAt 232 .GT, pushAt 233 1 168, opAt 234 .JUMPI,
   pushAt 235 2 322, opAt 236 .JUMP]

/-- The padded tail word, the cleanup and the miss test. -/
def tailPath : List Located :=
  [opAt 237 .JUMPDEST, opAt 238 (.Swap ⟨2, by decide⟩), opAt 239 .POP,
   opAt 240 (.Swap ⟨1, by decide⟩), opAt 241 (.Swap ⟨6, by decide⟩), opAt 242 .POP,
   opAt 243 .POP, opAt 244 .POP, opAt 245 .POP, opAt 246 .POP, opAt 247 .POP, opAt 248 .POP,
   pushAt 249 1 3, opAt 250 .JUMPI]

/-- Store and return the stored digest. -/
def returnPath : List Located :=
  [opAt 251 .CALLDATASIZE, pushAt 252 2 376, opAt 253 .EQ,
   pushAt 254 20 644824770394507154413287103057882351908521126009, opAt 255 .MUL,
   pushAt 256 20 766350606435067737561421097975693824639675460820, opAt 257 .XOR,
   pushAt 258 0 0, opAt 259 .MSTORE, opAt 260 .MSIZE, pushAt 261 0 0,
   opAt 262 .RETURN]

/-- Shift the correction constant out of `M`. -/
def straddleCorrPath : List Located :=
  [opAt 263 .JUMPDEST, opAt 264 (.Dup ⟨6, by decide⟩),
   opAt 265 (.Dup ⟨4, by decide⟩), pushAt 266 1 8, opAt 267 .SHR,
   pushAt 268 1 5, opAt 269 .MUL, pushAt 270 1 27, opAt 271 .SUB,
   pushAt 272 1 3, opAt 273 .SHL, opAt 274 .SHR, pushAt 275 1 11,
   opAt 276 .MUL]

/-- Apply the correction to the expected word. -/
def straddleAddPath : List Located :=
  [opAt 277 (.Dup ⟨1, by decide⟩), opAt 278 (.Dup ⟨9, by decide⟩),
   opAt 279 .AND, opAt 280 (.Dup ⟨1, by decide⟩), opAt 281 .ADD,
   opAt 282 (.Dup ⟨2, by decide⟩), opAt 283 (.Dup ⟨12, by decide⟩),
   opAt 284 .AND, opAt 285 .XOR, opAt 286 (.Swap ⟨1, by decide⟩),
   opAt 287 .POP, opAt 288 .POP]

/-- Bump the scalar and rejoin the scan. -/
def straddleBackPath : List Located :=
  [opAt 289 (.Dup ⟨2, by decide⟩), pushAt 290 1 11, opAt 291 .ADD,
   opAt 292 (.Swap ⟨2, by decide⟩), opAt 293 .POP, pushAt 294 2 348,
   opAt 295 .JUMP]


@[simp] theorem pc2903 : Artifact.submissionArtifact.instructionPC 160 = 0x10e :=
  by rw [scan_instruction_pc 160 (by decide) (by decide)]; rfl
@[simp] theorem pc2904 : Artifact.submissionArtifact.instructionPC 160 = 0x10e :=
  by rw [scan_instruction_pc 160 (by decide) (by decide)]; rfl
@[simp] theorem pc2905 : Artifact.submissionArtifact.instructionPC 164 = 0x113 :=
  by rw [scan_instruction_pc 164 (by decide) (by decide)]; rfl
@[simp] theorem pc2906 : Artifact.submissionArtifact.instructionPC 169 = 0x139 :=
  by rw [scan_instruction_pc 169 (by decide) (by decide)]; rfl
@[simp] theorem pc2907 : Artifact.submissionArtifact.instructionPC 171 = 0x13b :=
  by rw [scan_instruction_pc 171 (by decide) (by decide)]; rfl
@[simp] theorem pc2908 : Artifact.submissionArtifact.instructionPC 172 = 0x13c :=
  by rw [scan_instruction_pc 172 (by decide) (by decide)]; rfl
@[simp] theorem pc2909 : Artifact.submissionArtifact.instructionPC 173 = 0x13d :=
  by rw [scan_instruction_pc 173 (by decide) (by decide)]; rfl
@[simp] theorem pc2910 : Artifact.submissionArtifact.instructionPC 174 = 0x13e :=
  by rw [scan_instruction_pc 174 (by decide) (by decide)]; rfl
@[simp] theorem pc2911 : Artifact.submissionArtifact.instructionPC 175 = 0x13f :=
  by rw [scan_instruction_pc 175 (by decide) (by decide)]; rfl
@[simp] theorem pc2912 : Artifact.submissionArtifact.instructionPC 176 = 0x140 :=
  by rw [scan_instruction_pc 176 (by decide) (by decide)]; rfl
@[simp] theorem pc2913 : Artifact.submissionArtifact.instructionPC 177 = 0x141 :=
  by rw [scan_instruction_pc 177 (by decide) (by decide)]; rfl
@[simp] theorem pc2914 : Artifact.submissionArtifact.instructionPC 178 = 0x142 :=
  by rw [scan_instruction_pc 178 (by decide) (by decide)]; rfl
@[simp] theorem pc2915 : Artifact.submissionArtifact.instructionPC 179 = 0x143 :=
  by rw [scan_instruction_pc 179 (by decide) (by decide)]; rfl
@[simp] theorem pc2916 : Artifact.submissionArtifact.instructionPC 180 = 0x144 :=
  by rw [scan_instruction_pc 180 (by decide) (by decide)]; rfl
@[simp] theorem pc2917 : Artifact.submissionArtifact.instructionPC 181 = 0x145 :=
  by rw [scan_instruction_pc 181 (by decide) (by decide)]; rfl
@[simp] theorem pc2918 : Artifact.submissionArtifact.instructionPC 182 = 0x146 :=
  by rw [scan_instruction_pc 182 (by decide) (by decide)]; rfl
@[simp] theorem pc2919 : Artifact.submissionArtifact.instructionPC 183 = 0x147 :=
  by rw [scan_instruction_pc 183 (by decide) (by decide)]; rfl
@[simp] theorem pc2920 : Artifact.submissionArtifact.instructionPC 184 = 0x148 :=
  by rw [scan_instruction_pc 184 (by decide) (by decide)]; rfl
@[simp] theorem pc2921 : Artifact.submissionArtifact.instructionPC 185 = 0x149 :=
  by rw [scan_instruction_pc 185 (by decide) (by decide)]; rfl
@[simp] theorem pc2922 : Artifact.submissionArtifact.instructionPC 186 = 0x14a :=
  by rw [scan_instruction_pc 186 (by decide) (by decide)]; rfl
@[simp] theorem pc2923 : Artifact.submissionArtifact.instructionPC 187 = 0x14b :=
  by rw [scan_instruction_pc 187 (by decide) (by decide)]; rfl
@[simp] theorem pc2924 : Artifact.submissionArtifact.instructionPC 188 = 0x14c :=
  by rw [scan_instruction_pc 188 (by decide) (by decide)]; rfl
@[simp] theorem pc2925 : Artifact.submissionArtifact.instructionPC 189 = 0x14d :=
  by rw [scan_instruction_pc 189 (by decide) (by decide)]; rfl
@[simp] theorem pc2926 : Artifact.submissionArtifact.instructionPC 190 = 0x14e :=
  by rw [scan_instruction_pc 190 (by decide) (by decide)]; rfl
@[simp] theorem pc2927 : Artifact.submissionArtifact.instructionPC 191 = 0x14f :=
  by rw [scan_instruction_pc 191 (by decide) (by decide)]; rfl
@[simp] theorem pc2928 : Artifact.submissionArtifact.instructionPC 192 = 0x150 :=
  by rw [scan_instruction_pc 192 (by decide) (by decide)]; rfl
@[simp] theorem pc2929 : Artifact.submissionArtifact.instructionPC 193 = 0x151 :=
  by rw [scan_instruction_pc 193 (by decide) (by decide)]; rfl
@[simp] theorem pc2930 : Artifact.submissionArtifact.instructionPC 194 = 0x152 :=
  by rw [scan_instruction_pc 194 (by decide) (by decide)]; rfl
@[simp] theorem pc2931 : Artifact.submissionArtifact.instructionPC 195 = 0x154 :=
  by rw [scan_instruction_pc 195 (by decide) (by decide)]; rfl
@[simp] theorem pc2932 : Artifact.submissionArtifact.instructionPC 196 = 0x155 :=
  by rw [scan_instruction_pc 196 (by decide) (by decide)]; rfl
@[simp] theorem pc2933 : Artifact.submissionArtifact.instructionPC 197 = 0x157 :=
  by rw [scan_instruction_pc 197 (by decide) (by decide)]; rfl
@[simp] theorem pc2934 : Artifact.submissionArtifact.instructionPC 198 = 0x158 :=
  by rw [scan_instruction_pc 198 (by decide) (by decide)]; rfl
@[simp] theorem pc2935 : Artifact.submissionArtifact.instructionPC 199 = 0x15b :=
  by rw [scan_instruction_pc 199 (by decide) (by decide)]; rfl
@[simp] theorem pc2936 : Artifact.submissionArtifact.instructionPC 200 = 0x15c :=
  by rw [scan_instruction_pc 200 (by decide) (by decide)]; rfl
@[simp] theorem pc2937 : Artifact.submissionArtifact.instructionPC 201 = 0x15d :=
  by rw [scan_instruction_pc 201 (by decide) (by decide)]; rfl
@[simp] theorem pc2938 : Artifact.submissionArtifact.instructionPC 202 = 0x15e :=
  by rw [scan_instruction_pc 202 (by decide) (by decide)]; rfl
@[simp] theorem pc2939 : Artifact.submissionArtifact.instructionPC 203 = 0x15f :=
  by rw [scan_instruction_pc 203 (by decide) (by decide)]; rfl
@[simp] theorem pc2940 : Artifact.submissionArtifact.instructionPC 217 = 0x170 :=
  by rw [scan_instruction_pc 217 (by decide) (by decide)]; rfl
@[simp] theorem pc2941 : Artifact.submissionArtifact.instructionPC 218 = 0x171 :=
  by rw [scan_instruction_pc 218 (by decide) (by decide)]; rfl
@[simp] theorem pc2942 : Artifact.submissionArtifact.instructionPC 219 = 0x172 :=
  by rw [scan_instruction_pc 219 (by decide) (by decide)]; rfl
@[simp] theorem pc2943 : Artifact.submissionArtifact.instructionPC 220 = 0x173 :=
  by rw [scan_instruction_pc 220 (by decide) (by decide)]; rfl
@[simp] theorem pc2944 : Artifact.submissionArtifact.instructionPC 221 = 0x174 :=
  by rw [scan_instruction_pc 221 (by decide) (by decide)]; rfl
@[simp] theorem pc2945 : Artifact.submissionArtifact.instructionPC 222 = 0x175 :=
  by rw [scan_instruction_pc 222 (by decide) (by decide)]; rfl
@[simp] theorem pc2946 : Artifact.submissionArtifact.instructionPC 222 = 0x175 :=
  by rw [scan_instruction_pc 222 (by decide) (by decide)]; rfl
@[simp] theorem pc2947 : Artifact.submissionArtifact.instructionPC 223 = 0x177 :=
  by rw [scan_instruction_pc 223 (by decide) (by decide)]; rfl
@[simp] theorem pc2948 : Artifact.submissionArtifact.instructionPC 224 = 0x178 :=
  by rw [scan_instruction_pc 224 (by decide) (by decide)]; rfl
@[simp] theorem pc2949 : Artifact.submissionArtifact.instructionPC 225 = 0x17a :=
  by rw [scan_instruction_pc 225 (by decide) (by decide)]; rfl
@[simp] theorem pc2950 : Artifact.submissionArtifact.instructionPC 226 = 0x17b :=
  by rw [scan_instruction_pc 226 (by decide) (by decide)]; rfl
@[simp] theorem pc2951 : Artifact.submissionArtifact.instructionPC 226 = 0x17b :=
  by rw [scan_instruction_pc 226 (by decide) (by decide)]; rfl
@[simp] theorem pc2952 : Artifact.submissionArtifact.instructionPC 226 = 0x17b :=
  by rw [scan_instruction_pc 226 (by decide) (by decide)]; rfl
@[simp] theorem pc2953 : Artifact.submissionArtifact.instructionPC 227 = 0x17c :=
  by rw [scan_instruction_pc 227 (by decide) (by decide)]; rfl
@[simp] theorem pc2954 : Artifact.submissionArtifact.instructionPC 228 = 0x17e :=
  by rw [scan_instruction_pc 228 (by decide) (by decide)]; rfl
@[simp] theorem pc2955 : Artifact.submissionArtifact.instructionPC 229 = 0x17f :=
  by rw [scan_instruction_pc 229 (by decide) (by decide)]; rfl
@[simp] theorem pc2956 : Artifact.submissionArtifact.instructionPC 222 = 0x175 :=
  by rw [scan_instruction_pc 222 (by decide) (by decide)]; rfl
@[simp] theorem pc2957 : Artifact.submissionArtifact.instructionPC 222 = 0x175 :=
  by rw [scan_instruction_pc 222 (by decide) (by decide)]; rfl
@[simp] theorem pc2958 : Artifact.submissionArtifact.instructionPC 223 = 0x177 :=
  by rw [scan_instruction_pc 223 (by decide) (by decide)]; rfl
@[simp] theorem pc2959 : Artifact.submissionArtifact.instructionPC 224 = 0x178 :=
  by rw [scan_instruction_pc 224 (by decide) (by decide)]; rfl
@[simp] theorem pc2960 : Artifact.submissionArtifact.instructionPC 225 = 0x17a :=
  by rw [scan_instruction_pc 225 (by decide) (by decide)]; rfl
@[simp] theorem pc2961 : Artifact.submissionArtifact.instructionPC 226 = 0x17b :=
  by rw [scan_instruction_pc 226 (by decide) (by decide)]; rfl
@[simp] theorem pc2962 : Artifact.submissionArtifact.instructionPC 227 = 0x17c :=
  by rw [scan_instruction_pc 227 (by decide) (by decide)]; rfl
@[simp] theorem pc2963 : Artifact.submissionArtifact.instructionPC 228 = 0x17e :=
  by rw [scan_instruction_pc 228 (by decide) (by decide)]; rfl
@[simp] theorem pc2964 : Artifact.submissionArtifact.instructionPC 229 = 0x17f :=
  by rw [scan_instruction_pc 229 (by decide) (by decide)]; rfl
@[simp] theorem pc2965 : Artifact.submissionArtifact.instructionPC 230 = 0x180 :=
  by rw [scan_instruction_pc 230 (by decide) (by decide)]; rfl
@[simp] theorem pc2966 : Artifact.submissionArtifact.instructionPC 231 = 0x181 :=
  by rw [scan_instruction_pc 231 (by decide) (by decide)]; rfl
@[simp] theorem pc2967 : Artifact.submissionArtifact.instructionPC 232 = 0x182 :=
  by rw [scan_instruction_pc 232 (by decide) (by decide)]; rfl
@[simp] theorem pc2968 : Artifact.submissionArtifact.instructionPC 233 = 0x183 :=
  by rw [scan_instruction_pc 233 (by decide) (by decide)]; rfl
@[simp] theorem pc2969 : Artifact.submissionArtifact.instructionPC 234 = 0x185 :=
  by rw [scan_instruction_pc 234 (by decide) (by decide)]; rfl
@[simp] theorem pc2969a : Artifact.submissionArtifact.instructionPC 237 = 0x18a :=
  by rw [scan_instruction_pc 237 (by decide) (by decide)]; rfl
@[simp] theorem pc2970 : Artifact.submissionArtifact.instructionPC 238 = 0x18b :=
  by rw [scan_instruction_pc 238 (by decide) (by decide)]; rfl
@[simp] theorem pc2971 : Artifact.submissionArtifact.instructionPC 239 = 0x18c :=
  by rw [scan_instruction_pc 239 (by decide) (by decide)]; rfl
@[simp] theorem pc2972 : Artifact.submissionArtifact.instructionPC 240 = 0x18d :=
  by rw [scan_instruction_pc 240 (by decide) (by decide)]; rfl
@[simp] theorem pc2973 : Artifact.submissionArtifact.instructionPC 241 = 0x18e :=
  by rw [scan_instruction_pc 241 (by decide) (by decide)]; rfl
@[simp] theorem pc2974 : Artifact.submissionArtifact.instructionPC 242 = 0x18f :=
  by rw [scan_instruction_pc 242 (by decide) (by decide)]; rfl
@[simp] theorem pc2975 : Artifact.submissionArtifact.instructionPC 243 = 0x190 :=
  by rw [scan_instruction_pc 243 (by decide) (by decide)]; rfl
@[simp] theorem pc2976 : Artifact.submissionArtifact.instructionPC 244 = 0x191 :=
  by rw [scan_instruction_pc 244 (by decide) (by decide)]; rfl
@[simp] theorem pc2977 : Artifact.submissionArtifact.instructionPC 245 = 0x192 :=
  by rw [scan_instruction_pc 245 (by decide) (by decide)]; rfl
@[simp] theorem pc2978 : Artifact.submissionArtifact.instructionPC 246 = 0x193 :=
  by rw [scan_instruction_pc 246 (by decide) (by decide)]; rfl
@[simp] theorem pc2979 : Artifact.submissionArtifact.instructionPC 247 = 0x194 :=
  by rw [scan_instruction_pc 247 (by decide) (by decide)]; rfl
@[simp] theorem pc2980 : Artifact.submissionArtifact.instructionPC 248 = 0x195 :=
  by rw [scan_instruction_pc 248 (by decide) (by decide)]; rfl
@[simp] theorem pc2981 : Artifact.submissionArtifact.instructionPC 249 = 0x196 :=
  by rw [scan_instruction_pc 249 (by decide) (by decide)]; rfl
@[simp] theorem pc2982 : Artifact.submissionArtifact.instructionPC 250 = 0x198 :=
  by rw [scan_instruction_pc 250 (by decide) (by decide)]; rfl
@[simp] theorem pc_ins249 : Artifact.submissionArtifact.instructionPC 251 = 0x199 :=
  by rw [scan_instruction_pc 251 (by decide) (by decide)]; rfl
@[simp] theorem pc_ins250 : Artifact.submissionArtifact.instructionPC 252 = 0x19a :=
  by rw [scan_instruction_pc 252 (by decide) (by decide)]; rfl
@[simp] theorem pc_ins251 : Artifact.submissionArtifact.instructionPC 253 = 0x19d :=
  by rw [scan_instruction_pc 253 (by decide) (by decide)]; rfl
@[simp] theorem pc_ins252 : Artifact.submissionArtifact.instructionPC 254 = 0x19e :=
  by rw [scan_instruction_pc 254 (by decide) (by decide)]; rfl
@[simp] theorem pc_ins253 : Artifact.submissionArtifact.instructionPC 255 = 0x1b3 :=
  by rw [scan_instruction_pc 255 (by decide) (by decide)]; rfl
@[simp] theorem pc_ins255 : Artifact.submissionArtifact.instructionPC 257 = 0x1c9 :=
  by rw [scan_instruction_pc 257 (by decide) (by decide)]; rfl
@[simp] theorem pc_ins217 : Artifact.submissionArtifact.instructionPC 230 = 0x180 :=
  by rw [scan_instruction_pc 230 (by decide) (by decide)]; rfl
@[simp] theorem pc_ins218 : Artifact.submissionArtifact.instructionPC 231 = 0x181 :=
  by rw [scan_instruction_pc 231 (by decide) (by decide)]; rfl
@[simp] theorem pc_ins219 : Artifact.submissionArtifact.instructionPC 232 = 0x182 :=
  by rw [scan_instruction_pc 232 (by decide) (by decide)]; rfl
@[simp] theorem pc_ins220 : Artifact.submissionArtifact.instructionPC 233 = 0x183 :=
  by rw [scan_instruction_pc 233 (by decide) (by decide)]; rfl
@[simp] theorem pc_ins221 : Artifact.submissionArtifact.instructionPC 234 = 0x185 :=
  by rw [scan_instruction_pc 234 (by decide) (by decide)]; rfl
@[simp] theorem pc2983 : Artifact.submissionArtifact.instructionPC 256 = 0x1b4 :=
  by rw [scan_instruction_pc 256 (by decide) (by decide)]; rfl
@[simp] theorem pc2984 : Artifact.submissionArtifact.instructionPC 258 = 0x1ca :=
  by rw [scan_instruction_pc 258 (by decide) (by decide)]; rfl
@[simp] theorem pc2985 : Artifact.submissionArtifact.instructionPC 259 = 0x1cb :=
  by rw [scan_instruction_pc 259 (by decide) (by decide)]; rfl
@[simp] theorem pc2986 : Artifact.submissionArtifact.instructionPC 260 = 0x1cc :=
  by rw [scan_instruction_pc 260 (by decide) (by decide)]; rfl
@[simp] theorem pc2987 : Artifact.submissionArtifact.instructionPC 261 = 0x1cd :=
  by rw [scan_instruction_pc 261 (by decide) (by decide)]; rfl
@[simp] theorem pc2988 : Artifact.submissionArtifact.instructionPC 262 = 0x1ce :=
  by rw [scan_instruction_pc 262 (by decide) (by decide)]; rfl
@[simp] theorem pc2989 : Artifact.submissionArtifact.instructionPC 263 = 0x1cf :=
  by rw [scan_instruction_pc 263 (by decide) (by decide)]; rfl
@[simp] theorem pc2990 : Artifact.submissionArtifact.instructionPC 264 = 0x1d0 :=
  by rw [scan_instruction_pc 264 (by decide) (by decide)]; rfl
@[simp] theorem pc2991 : Artifact.submissionArtifact.instructionPC 265 = 0x1d1 :=
  by rw [scan_instruction_pc 265 (by decide) (by decide)]; rfl
@[simp] theorem pc2992 : Artifact.submissionArtifact.instructionPC 266 = 0x1d2 :=
  by rw [scan_instruction_pc 266 (by decide) (by decide)]; rfl
@[simp] theorem pc2993 : Artifact.submissionArtifact.instructionPC 267 = 0x1d4 :=
  by rw [scan_instruction_pc 267 (by decide) (by decide)]; rfl
@[simp] theorem pc2994 : Artifact.submissionArtifact.instructionPC 268 = 0x1d5 :=
  by rw [scan_instruction_pc 268 (by decide) (by decide)]; rfl
@[simp] theorem pc2995 : Artifact.submissionArtifact.instructionPC 269 = 0x1d7 :=
  by rw [scan_instruction_pc 269 (by decide) (by decide)]; rfl
@[simp] theorem pc2996 : Artifact.submissionArtifact.instructionPC 270 = 0x1d8 :=
  by rw [scan_instruction_pc 270 (by decide) (by decide)]; rfl
@[simp] theorem pc2997 : Artifact.submissionArtifact.instructionPC 271 = 0x1da :=
  by rw [scan_instruction_pc 271 (by decide) (by decide)]; rfl
@[simp] theorem pc2998 : Artifact.submissionArtifact.instructionPC 272 = 0x1db :=
  by rw [scan_instruction_pc 272 (by decide) (by decide)]; rfl
@[simp] theorem pc2999 : Artifact.submissionArtifact.instructionPC 273 = 0x1dd :=
  by rw [scan_instruction_pc 273 (by decide) (by decide)]; rfl
@[simp] theorem pc3000 : Artifact.submissionArtifact.instructionPC 274 = 0x1de :=
  by rw [scan_instruction_pc 274 (by decide) (by decide)]; rfl
@[simp] theorem pc3001 : Artifact.submissionArtifact.instructionPC 275 = 0x1df :=
  by rw [scan_instruction_pc 275 (by decide) (by decide)]; rfl
@[simp] theorem pc3002 : Artifact.submissionArtifact.instructionPC 276 = 0x1e1 :=
  by rw [scan_instruction_pc 276 (by decide) (by decide)]; rfl
@[simp] theorem pc3003 : Artifact.submissionArtifact.instructionPC 277 = 0x1e2 :=
  by rw [scan_instruction_pc 277 (by decide) (by decide)]; rfl
@[simp] theorem pc3004 : Artifact.submissionArtifact.instructionPC 278 = 0x1e3 :=
  by rw [scan_instruction_pc 278 (by decide) (by decide)]; rfl
@[simp] theorem pc3005 : Artifact.submissionArtifact.instructionPC 279 = 0x1e4 :=
  by rw [scan_instruction_pc 279 (by decide) (by decide)]; rfl
@[simp] theorem pc3006 : Artifact.submissionArtifact.instructionPC 280 = 0x1e5 :=
  by rw [scan_instruction_pc 280 (by decide) (by decide)]; rfl
@[simp] theorem pc3007 : Artifact.submissionArtifact.instructionPC 281 = 0x1e6 :=
  by rw [scan_instruction_pc 281 (by decide) (by decide)]; rfl
@[simp] theorem pc3008 : Artifact.submissionArtifact.instructionPC 282 = 0x1e7 :=
  by rw [scan_instruction_pc 282 (by decide) (by decide)]; rfl
@[simp] theorem pc3009 : Artifact.submissionArtifact.instructionPC 283 = 0x1e8 :=
  by rw [scan_instruction_pc 283 (by decide) (by decide)]; rfl
@[simp] theorem pc3010 : Artifact.submissionArtifact.instructionPC 284 = 0x1e9 :=
  by rw [scan_instruction_pc 284 (by decide) (by decide)]; rfl
@[simp] theorem pc3011 : Artifact.submissionArtifact.instructionPC 285 = 0x1ea :=
  by rw [scan_instruction_pc 285 (by decide) (by decide)]; rfl
@[simp] theorem pc3012 : Artifact.submissionArtifact.instructionPC 286 = 0x1eb :=
  by rw [scan_instruction_pc 286 (by decide) (by decide)]; rfl
@[simp] theorem pc3013 : Artifact.submissionArtifact.instructionPC 287 = 0x1ec :=
  by rw [scan_instruction_pc 287 (by decide) (by decide)]; rfl
@[simp] theorem pc3014 : Artifact.submissionArtifact.instructionPC 288 = 0x1ed :=
  by rw [scan_instruction_pc 288 (by decide) (by decide)]; rfl
@[simp] theorem pc3015 : Artifact.submissionArtifact.instructionPC 289 = 0x1ee :=
  by rw [scan_instruction_pc 289 (by decide) (by decide)]; rfl
@[simp] theorem pc3016 : Artifact.submissionArtifact.instructionPC 290 = 0x1ef :=
  by rw [scan_instruction_pc 290 (by decide) (by decide)]; rfl
@[simp] theorem pc3017 : Artifact.submissionArtifact.instructionPC 291 = 0x1f1 :=
  by rw [scan_instruction_pc 291 (by decide) (by decide)]; rfl
@[simp] theorem pc3018 : Artifact.submissionArtifact.instructionPC 292 = 0x1f2 :=
  by rw [scan_instruction_pc 292 (by decide) (by decide)]; rfl
@[simp] theorem pc3019 : Artifact.submissionArtifact.instructionPC 293 = 0x1f3 :=
  by rw [scan_instruction_pc 293 (by decide) (by decide)]; rfl
@[simp] theorem pc3020 : Artifact.submissionArtifact.instructionPC 294 = 0x1f4 :=
  by rw [scan_instruction_pc 294 (by decide) (by decide)]; rfl
@[simp] theorem pc3021 : Artifact.submissionArtifact.instructionPC 295 = 0x1f7 :=
  by rw [scan_instruction_pc 295 (by decide) (by decide)]; rfl
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
