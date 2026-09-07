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
  from Challenge.Ripemd160.Submission.Proofs.Bytecode.Artifact

private def scanPrefix : List YulEvmCompiler.Instr :=
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
    submissionInstructionsChunk15

private def scanBefore : List YulEvmCompiler.Instr :=
  scanPrefix ++ submissionInstructionsChunk16.take 124

private def scanSuffix : List YulEvmCompiler.Instr :=
  submissionInstructionsChunk16.drop 124 ++
    submissionInstructionsChunk17

private theorem scanBefore_length : scanBefore.length = 3324 := by
  simp [scanBefore, scanPrefix]

private theorem scanSuffix_length : scanSuffix.length = 127 := by
  simp [scanSuffix]

private theorem artifact_scan_split :
    Artifact.submissionArtifact.instructions = scanBefore ++ scanSuffix ++ [] := by
  change Artifact.submissionInstructions = _
  have hprefix : Artifact.submissionInstructions =
      scanPrefix ++ submissionInstructionsChunk16 ++
    submissionInstructionsChunk17 := by
    simp only [Artifact.submissionInstructions, scanPrefix, List.append_assoc]
  have hchunk : submissionInstructionsChunk16 =
      submissionInstructionsChunk16.take 124 ++ submissionInstructionsChunk16.drop 124 := by
    exact (List.take_append_drop 124 submissionInstructionsChunk16).symm
  rw [hprefix]
  conv_lhs => rw [hchunk]
  simp only [scanBefore, scanSuffix, List.append_assoc, List.append_nil]

private theorem scanBefore_pc :
    (YulEvmCompiler.assembleBytes scanBefore).length = 5150 := by rfl

private theorem artifact_instruction_projection :
    Artifact.submissionArtifact.instructions = Artifact.submissionInstructions := by rfl

private theorem scan_instruction_at (index : Nat)
    (hlo : 3324 ≤ index) (hhi : index < 3451) :
    Artifact.submissionInstructions[index]? = scanSuffix[index - 3324]? := by
  have hi : index - 3324 < scanSuffix.length := by
    rw [scanSuffix_length]
    omega
  have h := ArtifactSegment.getElem?_segment Artifact.submissionArtifact
    scanBefore scanSuffix [] artifact_scan_split (index - 3324) hi
  simpa only [artifact_instruction_projection, scanBefore_length,
    Nat.add_sub_of_le hlo] using h

private theorem scan_instruction_pc (index : Nat)
    (hlo : 3324 ≤ index) (hhi : index ≤ 3451) :
    Artifact.submissionArtifact.instructionPC index =
      5150 + (YulEvmCompiler.assembleBytes (scanSuffix.take (index - 3324))).length := by
  have hi : index - 3324 ≤ scanSuffix.length := by
    rw [scanSuffix_length]
    omega
  have h := ArtifactSegment.instructionPC_segment_of_bounds Artifact.submissionArtifact
    scanBefore scanSuffix [] 3324 5150 artifact_scan_split scanBefore_length
    scanBefore_pc (index - 3324) hi
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
  [opAt 3324 .JUMPDEST,
   pushAt 3325 1 255,
   pushAt 3326 0 0,
   opAt 3327 .NOT,
   opAt 3328 .DIV,
   pushAt 3329 32 3244493450063667868678674439968361782956185527883176199882357678282131398018,
   opAt 3330 (.Dup ⟨1, by decide⟩),
   pushAt 3331 1 7,
   opAt 3332 .SHL,
   opAt 3333 (.Dup ⟨0, by decide⟩),
   opAt 3334 .NOT,
   opAt 3335 (.Swap ⟨0, by decide⟩),
   opAt 3336 (.Swap ⟨2, by decide⟩),
   opAt 3337 (.Dup ⟨2, by decide⟩),
   opAt 3338 (.Dup ⟨2, by decide⟩),
   opAt 3339 .AND,
   pushAt 3340 0 0,
   pushAt 3341 0 0,
   pushAt 3342 0 0]

/-- Derive the expected word and test for a straddler. -/
def wordPath : List Located :=
  [opAt 3343 .JUMPDEST, opAt 3344 (.Dup ⟨0, by decide⟩),
   opAt 3345 (.Dup ⟨5, by decide⟩), opAt 3346 .MUL,
   opAt 3347 (.Dup ⟨0, by decide⟩), opAt 3348 (.Dup ⟨7, by decide⟩),
   opAt 3349 .AND, opAt 3350 (.Dup ⟨5, by decide⟩), opAt 3351 .ADD,
   opAt 3352 (.Dup ⟨1, by decide⟩), opAt 3353 (.Dup ⟨9, by decide⟩),
   opAt 3354 .XOR, opAt 3355 (.Dup ⟨10, by decide⟩), opAt 3356 .AND,
   opAt 3357 .XOR, opAt 3358 (.Dup ⟨3, by decide⟩), pushAt 3359 1 255,
   opAt 3360 .AND, pushAt 3361 1 224, opAt 3362 .EQ, pushAt 3363 2 5323,
   opAt 3364 .JUMPI]

/-- Fold one word into the accumulator and advance. -/
def comparePath : List Located :=
  [opAt 3365 .JUMPDEST, opAt 3366 (.Dup ⟨3, by decide⟩),
   opAt 3367 .CALLDATALOAD, opAt 3368 .XOR, opAt 3369 (.Dup ⟨4, by decide⟩),
   opAt 3370 .OR, opAt 3371 (.Swap ⟨3, by decide⟩), opAt 3372 .POP,
   opAt 3373 .POP, opAt 3374 .JUMPDEST, pushAt 3375 1 160,
   opAt 3376 .ADD, pushAt 3377 1 255, opAt 3378 .AND,
   opAt 3379 .JUMPDEST, opAt 3380 .JUMPDEST,
   opAt 3381 (.Swap ⟨0, by decide⟩), pushAt 3382 1 32, opAt 3383 .ADD,
   opAt 3384 (.Swap ⟨0, by decide⟩), opAt 3385 .JUMPDEST,
   opAt 3386 (.Dup ⟨1, by decide⟩), pushAt 3387 2 992, opAt 3388 .GT,
   pushAt 3389 2 5203, opAt 3390 .JUMPI]

/-- The padded tail word, the cleanup and the miss test. -/
def tailPath : List Located :=
  [pushAt 3391 2 992, opAt 3392 .CALLDATALOAD,
   pushAt 3393 8 9848759918901945995, pushAt 3394 1 192, opAt 3395 .SHL,
   opAt 3396 .XOR, opAt 3397 (.Dup ⟨3, by decide⟩), opAt 3398 .OR,
   opAt 3399 (.Swap ⟨2, by decide⟩), opAt 3400 .POP,
   opAt 3401 (.Swap ⟨1, by decide⟩), opAt 3402 (.Swap ⟨6, by decide⟩),
   opAt 3403 .POP, opAt 3404 .POP, opAt 3405 .POP, opAt 3406 .POP,
   opAt 3407 .POP, opAt 3408 .POP, opAt 3409 .POP, pushAt 3410 2 1011,
   opAt 3411 .JUMPI]

/-- Store and return the stored digest. -/
def returnPath : List Located :=
  [pushAt 3412 20 766350606435067737561421097975693824639675460820,
   pushAt 3413 0 0, opAt 3414 .MSTORE, pushAt 3415 1 32, pushAt 3416 0 0,
   opAt 3417 .RETURN]

/-- Shift the correction constant out of `M`. -/
def straddleCorrPath : List Located :=
  [opAt 3418 .JUMPDEST, opAt 3419 (.Dup ⟨6, by decide⟩),
   opAt 3420 (.Dup ⟨4, by decide⟩), pushAt 3421 1 8, opAt 3422 .SHR,
   pushAt 3423 1 5, opAt 3424 .MUL, pushAt 3425 1 27, opAt 3426 .SUB,
   pushAt 3427 1 8, opAt 3428 .MUL, opAt 3429 .SHR, pushAt 3430 1 11,
   opAt 3431 .MUL]

/-- Apply the correction to the expected word. -/
def straddleAddPath : List Located :=
  [opAt 3432 (.Dup ⟨1, by decide⟩), opAt 3433 (.Dup ⟨9, by decide⟩),
   opAt 3434 .AND, opAt 3435 (.Dup ⟨1, by decide⟩), opAt 3436 .ADD,
   opAt 3437 (.Dup ⟨2, by decide⟩), opAt 3438 (.Dup ⟨12, by decide⟩),
   opAt 3439 .AND, opAt 3440 .XOR, opAt 3441 (.Swap ⟨1, by decide⟩),
   opAt 3442 .POP, opAt 3443 .POP]

/-- Bump the scalar and rejoin the scan. -/
def straddleBackPath : List Located :=
  [opAt 3444 (.Dup ⟨2, by decide⟩), pushAt 3445 1 11, opAt 3446 .ADD,
   opAt 3447 (.Swap ⟨2, by decide⟩), opAt 3448 .POP, pushAt 3449 2 5229,
   opAt 3450 .JUMP]


@[simp] theorem pc2903 : Artifact.submissionArtifact.instructionPC 3324 = 0x141e :=
  by rw [scan_instruction_pc 3324 (by decide) (by decide)]; rfl
@[simp] theorem pc2904 : Artifact.submissionArtifact.instructionPC 3325 = 0x141f :=
  by rw [scan_instruction_pc 3325 (by decide) (by decide)]; rfl
@[simp] theorem pc2905 : Artifact.submissionArtifact.instructionPC 3329 = 0x1424 :=
  by rw [scan_instruction_pc 3329 (by decide) (by decide)]; rfl
@[simp] theorem pc2906 : Artifact.submissionArtifact.instructionPC 3334 = 0x144a :=
  by rw [scan_instruction_pc 3334 (by decide) (by decide)]; rfl
@[simp] theorem pc2907 : Artifact.submissionArtifact.instructionPC 3336 = 0x144c :=
  by rw [scan_instruction_pc 3336 (by decide) (by decide)]; rfl
@[simp] theorem pc2908 : Artifact.submissionArtifact.instructionPC 3337 = 0x144d :=
  by rw [scan_instruction_pc 3337 (by decide) (by decide)]; rfl
@[simp] theorem pc2909 : Artifact.submissionArtifact.instructionPC 3338 = 0x144e :=
  by rw [scan_instruction_pc 3338 (by decide) (by decide)]; rfl
@[simp] theorem pc2910 : Artifact.submissionArtifact.instructionPC 3339 = 0x144f :=
  by rw [scan_instruction_pc 3339 (by decide) (by decide)]; rfl
@[simp] theorem pc2911 : Artifact.submissionArtifact.instructionPC 3340 = 0x1450 :=
  by rw [scan_instruction_pc 3340 (by decide) (by decide)]; rfl
@[simp] theorem pc2912 : Artifact.submissionArtifact.instructionPC 3341 = 0x1451 :=
  by rw [scan_instruction_pc 3341 (by decide) (by decide)]; rfl
@[simp] theorem pc2913 : Artifact.submissionArtifact.instructionPC 3342 = 0x1452 :=
  by rw [scan_instruction_pc 3342 (by decide) (by decide)]; rfl
@[simp] theorem pc2914 : Artifact.submissionArtifact.instructionPC 3343 = 0x1453 :=
  by rw [scan_instruction_pc 3343 (by decide) (by decide)]; rfl
@[simp] theorem pc2915 : Artifact.submissionArtifact.instructionPC 3344 = 0x1454 :=
  by rw [scan_instruction_pc 3344 (by decide) (by decide)]; rfl
@[simp] theorem pc2916 : Artifact.submissionArtifact.instructionPC 3345 = 0x1455 :=
  by rw [scan_instruction_pc 3345 (by decide) (by decide)]; rfl
@[simp] theorem pc2917 : Artifact.submissionArtifact.instructionPC 3346 = 0x1456 :=
  by rw [scan_instruction_pc 3346 (by decide) (by decide)]; rfl
@[simp] theorem pc2918 : Artifact.submissionArtifact.instructionPC 3347 = 0x1457 :=
  by rw [scan_instruction_pc 3347 (by decide) (by decide)]; rfl
@[simp] theorem pc2919 : Artifact.submissionArtifact.instructionPC 3348 = 0x1458 :=
  by rw [scan_instruction_pc 3348 (by decide) (by decide)]; rfl
@[simp] theorem pc2920 : Artifact.submissionArtifact.instructionPC 3349 = 0x1459 :=
  by rw [scan_instruction_pc 3349 (by decide) (by decide)]; rfl
@[simp] theorem pc2921 : Artifact.submissionArtifact.instructionPC 3350 = 0x145a :=
  by rw [scan_instruction_pc 3350 (by decide) (by decide)]; rfl
@[simp] theorem pc2922 : Artifact.submissionArtifact.instructionPC 3351 = 0x145b :=
  by rw [scan_instruction_pc 3351 (by decide) (by decide)]; rfl
@[simp] theorem pc2923 : Artifact.submissionArtifact.instructionPC 3352 = 0x145c :=
  by rw [scan_instruction_pc 3352 (by decide) (by decide)]; rfl
@[simp] theorem pc2924 : Artifact.submissionArtifact.instructionPC 3353 = 0x145d :=
  by rw [scan_instruction_pc 3353 (by decide) (by decide)]; rfl
@[simp] theorem pc2925 : Artifact.submissionArtifact.instructionPC 3354 = 0x145e :=
  by rw [scan_instruction_pc 3354 (by decide) (by decide)]; rfl
@[simp] theorem pc2926 : Artifact.submissionArtifact.instructionPC 3355 = 0x145f :=
  by rw [scan_instruction_pc 3355 (by decide) (by decide)]; rfl
@[simp] theorem pc2927 : Artifact.submissionArtifact.instructionPC 3356 = 0x1460 :=
  by rw [scan_instruction_pc 3356 (by decide) (by decide)]; rfl
@[simp] theorem pc2928 : Artifact.submissionArtifact.instructionPC 3357 = 0x1461 :=
  by rw [scan_instruction_pc 3357 (by decide) (by decide)]; rfl
@[simp] theorem pc2929 : Artifact.submissionArtifact.instructionPC 3358 = 0x1462 :=
  by rw [scan_instruction_pc 3358 (by decide) (by decide)]; rfl
@[simp] theorem pc2930 : Artifact.submissionArtifact.instructionPC 3359 = 0x1463 :=
  by rw [scan_instruction_pc 3359 (by decide) (by decide)]; rfl
@[simp] theorem pc2931 : Artifact.submissionArtifact.instructionPC 3360 = 0x1465 :=
  by rw [scan_instruction_pc 3360 (by decide) (by decide)]; rfl
@[simp] theorem pc2932 : Artifact.submissionArtifact.instructionPC 3361 = 0x1466 :=
  by rw [scan_instruction_pc 3361 (by decide) (by decide)]; rfl
@[simp] theorem pc2933 : Artifact.submissionArtifact.instructionPC 3362 = 0x1468 :=
  by rw [scan_instruction_pc 3362 (by decide) (by decide)]; rfl
@[simp] theorem pc2934 : Artifact.submissionArtifact.instructionPC 3363 = 0x1469 :=
  by rw [scan_instruction_pc 3363 (by decide) (by decide)]; rfl
@[simp] theorem pc2935 : Artifact.submissionArtifact.instructionPC 3364 = 0x146c :=
  by rw [scan_instruction_pc 3364 (by decide) (by decide)]; rfl
@[simp] theorem pc2936 : Artifact.submissionArtifact.instructionPC 3365 = 0x146d :=
  by rw [scan_instruction_pc 3365 (by decide) (by decide)]; rfl
@[simp] theorem pc2937 : Artifact.submissionArtifact.instructionPC 3366 = 0x146e :=
  by rw [scan_instruction_pc 3366 (by decide) (by decide)]; rfl
@[simp] theorem pc2938 : Artifact.submissionArtifact.instructionPC 3367 = 0x146f :=
  by rw [scan_instruction_pc 3367 (by decide) (by decide)]; rfl
@[simp] theorem pc2939 : Artifact.submissionArtifact.instructionPC 3368 = 0x1470 :=
  by rw [scan_instruction_pc 3368 (by decide) (by decide)]; rfl
@[simp] theorem pc2940 : Artifact.submissionArtifact.instructionPC 3369 = 0x1471 :=
  by rw [scan_instruction_pc 3369 (by decide) (by decide)]; rfl
@[simp] theorem pc2941 : Artifact.submissionArtifact.instructionPC 3370 = 0x1472 :=
  by rw [scan_instruction_pc 3370 (by decide) (by decide)]; rfl
@[simp] theorem pc2942 : Artifact.submissionArtifact.instructionPC 3371 = 0x1473 :=
  by rw [scan_instruction_pc 3371 (by decide) (by decide)]; rfl
@[simp] theorem pc2943 : Artifact.submissionArtifact.instructionPC 3372 = 0x1474 :=
  by rw [scan_instruction_pc 3372 (by decide) (by decide)]; rfl
@[simp] theorem pc2944 : Artifact.submissionArtifact.instructionPC 3373 = 0x1475 :=
  by rw [scan_instruction_pc 3373 (by decide) (by decide)]; rfl
@[simp] theorem pc2945 : Artifact.submissionArtifact.instructionPC 3374 = 0x1476 :=
  by rw [scan_instruction_pc 3374 (by decide) (by decide)]; rfl
@[simp] theorem pc2946 : Artifact.submissionArtifact.instructionPC 3375 = 0x1477 :=
  by rw [scan_instruction_pc 3375 (by decide) (by decide)]; rfl
@[simp] theorem pc2947 : Artifact.submissionArtifact.instructionPC 3376 = 0x1479 :=
  by rw [scan_instruction_pc 3376 (by decide) (by decide)]; rfl
@[simp] theorem pc2948 : Artifact.submissionArtifact.instructionPC 3377 = 0x147a :=
  by rw [scan_instruction_pc 3377 (by decide) (by decide)]; rfl
@[simp] theorem pc2949 : Artifact.submissionArtifact.instructionPC 3378 = 0x147c :=
  by rw [scan_instruction_pc 3378 (by decide) (by decide)]; rfl
@[simp] theorem pc2950 : Artifact.submissionArtifact.instructionPC 3379 = 0x147d :=
  by rw [scan_instruction_pc 3379 (by decide) (by decide)]; rfl
@[simp] theorem pc2951 : Artifact.submissionArtifact.instructionPC 3380 = 0x147e :=
  by rw [scan_instruction_pc 3380 (by decide) (by decide)]; rfl
@[simp] theorem pc2952 : Artifact.submissionArtifact.instructionPC 3381 = 0x147f :=
  by rw [scan_instruction_pc 3381 (by decide) (by decide)]; rfl
@[simp] theorem pc2953 : Artifact.submissionArtifact.instructionPC 3382 = 0x1480 :=
  by rw [scan_instruction_pc 3382 (by decide) (by decide)]; rfl
@[simp] theorem pc2954 : Artifact.submissionArtifact.instructionPC 3383 = 0x1482 :=
  by rw [scan_instruction_pc 3383 (by decide) (by decide)]; rfl
@[simp] theorem pc2955 : Artifact.submissionArtifact.instructionPC 3384 = 0x1483 :=
  by rw [scan_instruction_pc 3384 (by decide) (by decide)]; rfl
@[simp] theorem pc2956 : Artifact.submissionArtifact.instructionPC 3385 = 0x1484 :=
  by rw [scan_instruction_pc 3385 (by decide) (by decide)]; rfl
@[simp] theorem pc2957 : Artifact.submissionArtifact.instructionPC 3386 = 0x1485 :=
  by rw [scan_instruction_pc 3386 (by decide) (by decide)]; rfl
@[simp] theorem pc2958 : Artifact.submissionArtifact.instructionPC 3387 = 0x1486 :=
  by rw [scan_instruction_pc 3387 (by decide) (by decide)]; rfl
@[simp] theorem pc2959 : Artifact.submissionArtifact.instructionPC 3388 = 0x1489 :=
  by rw [scan_instruction_pc 3388 (by decide) (by decide)]; rfl
@[simp] theorem pc2960 : Artifact.submissionArtifact.instructionPC 3389 = 0x148a :=
  by rw [scan_instruction_pc 3389 (by decide) (by decide)]; rfl
@[simp] theorem pc2961 : Artifact.submissionArtifact.instructionPC 3390 = 0x148d :=
  by rw [scan_instruction_pc 3390 (by decide) (by decide)]; rfl
@[simp] theorem pc2962 : Artifact.submissionArtifact.instructionPC 3391 = 0x148e :=
  by rw [scan_instruction_pc 3391 (by decide) (by decide)]; rfl
@[simp] theorem pc2963 : Artifact.submissionArtifact.instructionPC 3392 = 0x1491 :=
  by rw [scan_instruction_pc 3392 (by decide) (by decide)]; rfl
@[simp] theorem pc2964 : Artifact.submissionArtifact.instructionPC 3393 = 0x1492 :=
  by rw [scan_instruction_pc 3393 (by decide) (by decide)]; rfl
@[simp] theorem pc2965 : Artifact.submissionArtifact.instructionPC 3394 = 0x149b :=
  by rw [scan_instruction_pc 3394 (by decide) (by decide)]; rfl
@[simp] theorem pc2966 : Artifact.submissionArtifact.instructionPC 3395 = 0x149d :=
  by rw [scan_instruction_pc 3395 (by decide) (by decide)]; rfl
@[simp] theorem pc2967 : Artifact.submissionArtifact.instructionPC 3396 = 0x149e :=
  by rw [scan_instruction_pc 3396 (by decide) (by decide)]; rfl
@[simp] theorem pc2968 : Artifact.submissionArtifact.instructionPC 3397 = 0x149f :=
  by rw [scan_instruction_pc 3397 (by decide) (by decide)]; rfl
@[simp] theorem pc2969 : Artifact.submissionArtifact.instructionPC 3398 = 0x14a0 :=
  by rw [scan_instruction_pc 3398 (by decide) (by decide)]; rfl
@[simp] theorem pc2970 : Artifact.submissionArtifact.instructionPC 3399 = 0x14a1 :=
  by rw [scan_instruction_pc 3399 (by decide) (by decide)]; rfl
@[simp] theorem pc2971 : Artifact.submissionArtifact.instructionPC 3400 = 0x14a2 :=
  by rw [scan_instruction_pc 3400 (by decide) (by decide)]; rfl
@[simp] theorem pc2972 : Artifact.submissionArtifact.instructionPC 3401 = 0x14a3 :=
  by rw [scan_instruction_pc 3401 (by decide) (by decide)]; rfl
@[simp] theorem pc2973 : Artifact.submissionArtifact.instructionPC 3402 = 0x14a4 :=
  by rw [scan_instruction_pc 3402 (by decide) (by decide)]; rfl
@[simp] theorem pc2974 : Artifact.submissionArtifact.instructionPC 3403 = 0x14a5 :=
  by rw [scan_instruction_pc 3403 (by decide) (by decide)]; rfl
@[simp] theorem pc2975 : Artifact.submissionArtifact.instructionPC 3404 = 0x14a6 :=
  by rw [scan_instruction_pc 3404 (by decide) (by decide)]; rfl
@[simp] theorem pc2976 : Artifact.submissionArtifact.instructionPC 3405 = 0x14a7 :=
  by rw [scan_instruction_pc 3405 (by decide) (by decide)]; rfl
@[simp] theorem pc2977 : Artifact.submissionArtifact.instructionPC 3406 = 0x14a8 :=
  by rw [scan_instruction_pc 3406 (by decide) (by decide)]; rfl
@[simp] theorem pc2978 : Artifact.submissionArtifact.instructionPC 3407 = 0x14a9 :=
  by rw [scan_instruction_pc 3407 (by decide) (by decide)]; rfl
@[simp] theorem pc2979 : Artifact.submissionArtifact.instructionPC 3408 = 0x14aa :=
  by rw [scan_instruction_pc 3408 (by decide) (by decide)]; rfl
@[simp] theorem pc2980 : Artifact.submissionArtifact.instructionPC 3409 = 0x14ab :=
  by rw [scan_instruction_pc 3409 (by decide) (by decide)]; rfl
@[simp] theorem pc2981 : Artifact.submissionArtifact.instructionPC 3410 = 0x14ac :=
  by rw [scan_instruction_pc 3410 (by decide) (by decide)]; rfl
@[simp] theorem pc2982 : Artifact.submissionArtifact.instructionPC 3411 = 0x14af :=
  by rw [scan_instruction_pc 3411 (by decide) (by decide)]; rfl
@[simp] theorem pc2983 : Artifact.submissionArtifact.instructionPC 3412 = 0x14b0 :=
  by rw [scan_instruction_pc 3412 (by decide) (by decide)]; rfl
@[simp] theorem pc2984 : Artifact.submissionArtifact.instructionPC 3413 = 0x14c5 :=
  by rw [scan_instruction_pc 3413 (by decide) (by decide)]; rfl
@[simp] theorem pc2985 : Artifact.submissionArtifact.instructionPC 3414 = 0x14c6 :=
  by rw [scan_instruction_pc 3414 (by decide) (by decide)]; rfl
@[simp] theorem pc2986 : Artifact.submissionArtifact.instructionPC 3415 = 0x14c7 :=
  by rw [scan_instruction_pc 3415 (by decide) (by decide)]; rfl
@[simp] theorem pc2987 : Artifact.submissionArtifact.instructionPC 3416 = 0x14c9 :=
  by rw [scan_instruction_pc 3416 (by decide) (by decide)]; rfl
@[simp] theorem pc2988 : Artifact.submissionArtifact.instructionPC 3417 = 0x14ca :=
  by rw [scan_instruction_pc 3417 (by decide) (by decide)]; rfl
@[simp] theorem pc2989 : Artifact.submissionArtifact.instructionPC 3418 = 0x14cb :=
  by rw [scan_instruction_pc 3418 (by decide) (by decide)]; rfl
@[simp] theorem pc2990 : Artifact.submissionArtifact.instructionPC 3419 = 0x14cc :=
  by rw [scan_instruction_pc 3419 (by decide) (by decide)]; rfl
@[simp] theorem pc2991 : Artifact.submissionArtifact.instructionPC 3420 = 0x14cd :=
  by rw [scan_instruction_pc 3420 (by decide) (by decide)]; rfl
@[simp] theorem pc2992 : Artifact.submissionArtifact.instructionPC 3421 = 0x14ce :=
  by rw [scan_instruction_pc 3421 (by decide) (by decide)]; rfl
@[simp] theorem pc2993 : Artifact.submissionArtifact.instructionPC 3422 = 0x14d0 :=
  by rw [scan_instruction_pc 3422 (by decide) (by decide)]; rfl
@[simp] theorem pc2994 : Artifact.submissionArtifact.instructionPC 3423 = 0x14d1 :=
  by rw [scan_instruction_pc 3423 (by decide) (by decide)]; rfl
@[simp] theorem pc2995 : Artifact.submissionArtifact.instructionPC 3424 = 0x14d3 :=
  by rw [scan_instruction_pc 3424 (by decide) (by decide)]; rfl
@[simp] theorem pc2996 : Artifact.submissionArtifact.instructionPC 3425 = 0x14d4 :=
  by rw [scan_instruction_pc 3425 (by decide) (by decide)]; rfl
@[simp] theorem pc2997 : Artifact.submissionArtifact.instructionPC 3426 = 0x14d6 :=
  by rw [scan_instruction_pc 3426 (by decide) (by decide)]; rfl
@[simp] theorem pc2998 : Artifact.submissionArtifact.instructionPC 3427 = 0x14d7 :=
  by rw [scan_instruction_pc 3427 (by decide) (by decide)]; rfl
@[simp] theorem pc2999 : Artifact.submissionArtifact.instructionPC 3428 = 0x14d9 :=
  by rw [scan_instruction_pc 3428 (by decide) (by decide)]; rfl
@[simp] theorem pc3000 : Artifact.submissionArtifact.instructionPC 3429 = 0x14da :=
  by rw [scan_instruction_pc 3429 (by decide) (by decide)]; rfl
@[simp] theorem pc3001 : Artifact.submissionArtifact.instructionPC 3430 = 0x14db :=
  by rw [scan_instruction_pc 3430 (by decide) (by decide)]; rfl
@[simp] theorem pc3002 : Artifact.submissionArtifact.instructionPC 3431 = 0x14dd :=
  by rw [scan_instruction_pc 3431 (by decide) (by decide)]; rfl
@[simp] theorem pc3003 : Artifact.submissionArtifact.instructionPC 3432 = 0x14de :=
  by rw [scan_instruction_pc 3432 (by decide) (by decide)]; rfl
@[simp] theorem pc3004 : Artifact.submissionArtifact.instructionPC 3433 = 0x14df :=
  by rw [scan_instruction_pc 3433 (by decide) (by decide)]; rfl
@[simp] theorem pc3005 : Artifact.submissionArtifact.instructionPC 3434 = 0x14e0 :=
  by rw [scan_instruction_pc 3434 (by decide) (by decide)]; rfl
@[simp] theorem pc3006 : Artifact.submissionArtifact.instructionPC 3435 = 0x14e1 :=
  by rw [scan_instruction_pc 3435 (by decide) (by decide)]; rfl
@[simp] theorem pc3007 : Artifact.submissionArtifact.instructionPC 3436 = 0x14e2 :=
  by rw [scan_instruction_pc 3436 (by decide) (by decide)]; rfl
@[simp] theorem pc3008 : Artifact.submissionArtifact.instructionPC 3437 = 0x14e3 :=
  by rw [scan_instruction_pc 3437 (by decide) (by decide)]; rfl
@[simp] theorem pc3009 : Artifact.submissionArtifact.instructionPC 3438 = 0x14e4 :=
  by rw [scan_instruction_pc 3438 (by decide) (by decide)]; rfl
@[simp] theorem pc3010 : Artifact.submissionArtifact.instructionPC 3439 = 0x14e5 :=
  by rw [scan_instruction_pc 3439 (by decide) (by decide)]; rfl
@[simp] theorem pc3011 : Artifact.submissionArtifact.instructionPC 3440 = 0x14e6 :=
  by rw [scan_instruction_pc 3440 (by decide) (by decide)]; rfl
@[simp] theorem pc3012 : Artifact.submissionArtifact.instructionPC 3441 = 0x14e7 :=
  by rw [scan_instruction_pc 3441 (by decide) (by decide)]; rfl
@[simp] theorem pc3013 : Artifact.submissionArtifact.instructionPC 3442 = 0x14e8 :=
  by rw [scan_instruction_pc 3442 (by decide) (by decide)]; rfl
@[simp] theorem pc3014 : Artifact.submissionArtifact.instructionPC 3443 = 0x14e9 :=
  by rw [scan_instruction_pc 3443 (by decide) (by decide)]; rfl
@[simp] theorem pc3015 : Artifact.submissionArtifact.instructionPC 3444 = 0x14ea :=
  by rw [scan_instruction_pc 3444 (by decide) (by decide)]; rfl
@[simp] theorem pc3016 : Artifact.submissionArtifact.instructionPC 3445 = 0x14eb :=
  by rw [scan_instruction_pc 3445 (by decide) (by decide)]; rfl
@[simp] theorem pc3017 : Artifact.submissionArtifact.instructionPC 3446 = 0x14ed :=
  by rw [scan_instruction_pc 3446 (by decide) (by decide)]; rfl
@[simp] theorem pc3018 : Artifact.submissionArtifact.instructionPC 3447 = 0x14ee :=
  by rw [scan_instruction_pc 3447 (by decide) (by decide)]; rfl
@[simp] theorem pc3019 : Artifact.submissionArtifact.instructionPC 3448 = 0x14ef :=
  by rw [scan_instruction_pc 3448 (by decide) (by decide)]; rfl
@[simp] theorem pc3020 : Artifact.submissionArtifact.instructionPC 3449 = 0x14f0 :=
  by rw [scan_instruction_pc 3449 (by decide) (by decide)]; rfl
@[simp] theorem pc3021 : Artifact.submissionArtifact.instructionPC 3450 = 0x14f3 :=
  by rw [scan_instruction_pc 3450 (by decide) (by decide)]; rfl
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
