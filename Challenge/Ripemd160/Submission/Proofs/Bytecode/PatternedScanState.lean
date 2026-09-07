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
  scanPrefix ++ submissionInstructionsChunk16.take 166

private def scanSuffix : List YulEvmCompiler.Instr :=
  submissionInstructionsChunk16.drop 166 ++
    submissionInstructionsChunk17

private theorem scanBefore_length : scanBefore.length = 3366 := by
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
      submissionInstructionsChunk16.take 166 ++ submissionInstructionsChunk16.drop 166 := by
    exact (List.take_append_drop 166 submissionInstructionsChunk16).symm
  rw [hprefix]
  conv_lhs => rw [hchunk]
  simp only [scanBefore, scanSuffix, List.append_assoc, List.append_nil]

private theorem scanBefore_pc :
    (YulEvmCompiler.assembleBytes scanBefore).length = 5019 := by rfl

private theorem artifact_instruction_projection :
    Artifact.submissionArtifact.instructions = Artifact.submissionInstructions := by rfl

private theorem scan_instruction_at (index : Nat)
    (hlo : 3366 ≤ index) (hhi : index < 3493) :
    Artifact.submissionInstructions[index]? = scanSuffix[index - 3366]? := by
  have hi : index - 3366 < scanSuffix.length := by
    rw [scanSuffix_length]
    omega
  have h := ArtifactSegment.getElem?_segment Artifact.submissionArtifact
    scanBefore scanSuffix [] artifact_scan_split (index - 3366) hi
  simpa only [artifact_instruction_projection, scanBefore_length,
    Nat.add_sub_of_le hlo] using h

private theorem scan_instruction_pc (index : Nat)
    (hlo : 3366 ≤ index) (hhi : index ≤ 3493) :
    Artifact.submissionArtifact.instructionPC index =
      5019 + (YulEvmCompiler.assembleBytes (scanSuffix.take (index - 3366))).length := by
  have hi : index - 3366 ≤ scanSuffix.length := by
    rw [scanSuffix_length]
    omega
  have h := ArtifactSegment.instructionPC_segment_of_bounds Artifact.submissionArtifact
    scanBefore scanSuffix [] 3366 5019 artifact_scan_split scanBefore_length
    scanBefore_pc (index - 3366) hi
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
  [opAt 3366 .JUMPDEST,
   pushAt 3367 1 255,
   pushAt 3368 0 0,
   opAt 3369 .NOT,
   opAt 3370 .DIV,
   pushAt 3371 32 3244493450063667868678674439968361782956185527883176199882357678282131398018,
   opAt 3372 (.Dup ⟨1, by decide⟩),
   pushAt 3373 1 7,
   opAt 3374 .SHL,
   opAt 3375 (.Dup ⟨0, by decide⟩),
   opAt 3376 .NOT,
   opAt 3377 (.Swap ⟨0, by decide⟩),
   opAt 3378 (.Swap ⟨2, by decide⟩),
   opAt 3379 (.Dup ⟨2, by decide⟩),
   opAt 3380 (.Dup ⟨2, by decide⟩),
   opAt 3381 .AND,
   pushAt 3382 0 0,
   pushAt 3383 0 0,
   pushAt 3384 0 0]

/-- Derive the expected word and test for a straddler. -/
def wordPath : List Located :=
  [opAt 3385 .JUMPDEST, opAt 3386 (.Dup ⟨0, by decide⟩),
   opAt 3387 (.Dup ⟨5, by decide⟩), opAt 3388 .MUL,
   opAt 3389 (.Dup ⟨0, by decide⟩), opAt 3390 (.Dup ⟨7, by decide⟩),
   opAt 3391 .AND, opAt 3392 (.Dup ⟨5, by decide⟩), opAt 3393 .ADD,
   opAt 3394 (.Dup ⟨1, by decide⟩), opAt 3395 (.Dup ⟨9, by decide⟩),
   opAt 3396 .XOR, opAt 3397 (.Dup ⟨10, by decide⟩), opAt 3398 .AND,
   opAt 3399 .XOR, opAt 3400 (.Dup ⟨3, by decide⟩), pushAt 3401 1 255,
   opAt 3402 .AND, pushAt 3403 1 224, opAt 3404 .EQ, pushAt 3405 2 5192,
   opAt 3406 .JUMPI]

/-- Fold one word into the accumulator and advance. -/
def comparePath : List Located :=
  [opAt 3407 .JUMPDEST, opAt 3408 (.Dup ⟨3, by decide⟩),
   opAt 3409 .CALLDATALOAD, opAt 3410 .XOR, opAt 3411 (.Dup ⟨4, by decide⟩),
   opAt 3412 .OR, opAt 3413 (.Swap ⟨3, by decide⟩), opAt 3414 .POP,
   opAt 3415 .POP, opAt 3416 .JUMPDEST, pushAt 3417 1 160,
   opAt 3418 .ADD, pushAt 3419 1 255, opAt 3420 .AND,
   opAt 3421 .JUMPDEST, opAt 3422 .JUMPDEST,
   opAt 3423 (.Swap ⟨0, by decide⟩), pushAt 3424 1 32, opAt 3425 .ADD,
   opAt 3426 (.Swap ⟨0, by decide⟩), opAt 3427 .JUMPDEST,
   opAt 3428 (.Dup ⟨1, by decide⟩), pushAt 3429 2 992, opAt 3430 .GT,
   pushAt 3431 2 5072, opAt 3432 .JUMPI]

/-- The padded tail word, the cleanup and the miss test. -/
def tailPath : List Located :=
  [pushAt 3433 2 992, opAt 3434 .CALLDATALOAD,
   pushAt 3435 8 9848759918901945995, pushAt 3436 1 192, opAt 3437 .SHL,
   opAt 3438 .XOR, opAt 3439 (.Dup ⟨3, by decide⟩), opAt 3440 .OR,
   opAt 3441 (.Swap ⟨2, by decide⟩), opAt 3442 .POP,
   opAt 3443 (.Swap ⟨1, by decide⟩), opAt 3444 (.Swap ⟨6, by decide⟩),
   opAt 3445 .POP, opAt 3446 .POP, opAt 3447 .POP, opAt 3448 .POP,
   opAt 3449 .POP, opAt 3450 .POP, opAt 3451 .POP, pushAt 3452 2 972,
   opAt 3453 .JUMPI]

/-- Store and return the stored digest. -/
def returnPath : List Located :=
  [pushAt 3454 20 766350606435067737561421097975693824639675460820,
   pushAt 3455 0 0, opAt 3456 .MSTORE, pushAt 3457 1 32, pushAt 3458 0 0,
   opAt 3459 .RETURN]

/-- Shift the correction constant out of `M`. -/
def straddleCorrPath : List Located :=
  [opAt 3460 .JUMPDEST, opAt 3461 (.Dup ⟨6, by decide⟩),
   opAt 3462 (.Dup ⟨4, by decide⟩), pushAt 3463 1 8, opAt 3464 .SHR,
   pushAt 3465 1 5, opAt 3466 .MUL, pushAt 3467 1 27, opAt 3468 .SUB,
   pushAt 3469 1 8, opAt 3470 .MUL, opAt 3471 .SHR, pushAt 3472 1 11,
   opAt 3473 .MUL]

/-- Apply the correction to the expected word. -/
def straddleAddPath : List Located :=
  [opAt 3474 (.Dup ⟨1, by decide⟩), opAt 3475 (.Dup ⟨9, by decide⟩),
   opAt 3476 .AND, opAt 3477 (.Dup ⟨1, by decide⟩), opAt 3478 .ADD,
   opAt 3479 (.Dup ⟨2, by decide⟩), opAt 3480 (.Dup ⟨12, by decide⟩),
   opAt 3481 .AND, opAt 3482 .XOR, opAt 3483 (.Swap ⟨1, by decide⟩),
   opAt 3484 .POP, opAt 3485 .POP]

/-- Bump the scalar and rejoin the scan. -/
def straddleBackPath : List Located :=
  [opAt 3486 (.Dup ⟨2, by decide⟩), pushAt 3487 1 11, opAt 3488 .ADD,
   opAt 3489 (.Swap ⟨2, by decide⟩), opAt 3490 .POP, pushAt 3491 2 5098,
   opAt 3492 .JUMP]


@[simp] theorem pc2903 : Artifact.submissionArtifact.instructionPC 3366 = 0x139b :=
  by rw [scan_instruction_pc 3366 (by decide) (by decide)]; rfl
@[simp] theorem pc2904 : Artifact.submissionArtifact.instructionPC 3367 = 0x139c :=
  by rw [scan_instruction_pc 3367 (by decide) (by decide)]; rfl
@[simp] theorem pc2905 : Artifact.submissionArtifact.instructionPC 3371 = 0x13a1 :=
  by rw [scan_instruction_pc 3371 (by decide) (by decide)]; rfl
@[simp] theorem pc2906 : Artifact.submissionArtifact.instructionPC 3376 = 0x13c7 :=
  by rw [scan_instruction_pc 3376 (by decide) (by decide)]; rfl
@[simp] theorem pc2907 : Artifact.submissionArtifact.instructionPC 3378 = 0x13c9 :=
  by rw [scan_instruction_pc 3378 (by decide) (by decide)]; rfl
@[simp] theorem pc2908 : Artifact.submissionArtifact.instructionPC 3379 = 0x13ca :=
  by rw [scan_instruction_pc 3379 (by decide) (by decide)]; rfl
@[simp] theorem pc2909 : Artifact.submissionArtifact.instructionPC 3380 = 0x13cb :=
  by rw [scan_instruction_pc 3380 (by decide) (by decide)]; rfl
@[simp] theorem pc2910 : Artifact.submissionArtifact.instructionPC 3381 = 0x13cc :=
  by rw [scan_instruction_pc 3381 (by decide) (by decide)]; rfl
@[simp] theorem pc2911 : Artifact.submissionArtifact.instructionPC 3382 = 0x13cd :=
  by rw [scan_instruction_pc 3382 (by decide) (by decide)]; rfl
@[simp] theorem pc2912 : Artifact.submissionArtifact.instructionPC 3383 = 0x13ce :=
  by rw [scan_instruction_pc 3383 (by decide) (by decide)]; rfl
@[simp] theorem pc2913 : Artifact.submissionArtifact.instructionPC 3384 = 0x13cf :=
  by rw [scan_instruction_pc 3384 (by decide) (by decide)]; rfl
@[simp] theorem pc2914 : Artifact.submissionArtifact.instructionPC 3385 = 0x13d0 :=
  by rw [scan_instruction_pc 3385 (by decide) (by decide)]; rfl
@[simp] theorem pc2915 : Artifact.submissionArtifact.instructionPC 3386 = 0x13d1 :=
  by rw [scan_instruction_pc 3386 (by decide) (by decide)]; rfl
@[simp] theorem pc2916 : Artifact.submissionArtifact.instructionPC 3387 = 0x13d2 :=
  by rw [scan_instruction_pc 3387 (by decide) (by decide)]; rfl
@[simp] theorem pc2917 : Artifact.submissionArtifact.instructionPC 3388 = 0x13d3 :=
  by rw [scan_instruction_pc 3388 (by decide) (by decide)]; rfl
@[simp] theorem pc2918 : Artifact.submissionArtifact.instructionPC 3389 = 0x13d4 :=
  by rw [scan_instruction_pc 3389 (by decide) (by decide)]; rfl
@[simp] theorem pc2919 : Artifact.submissionArtifact.instructionPC 3390 = 0x13d5 :=
  by rw [scan_instruction_pc 3390 (by decide) (by decide)]; rfl
@[simp] theorem pc2920 : Artifact.submissionArtifact.instructionPC 3391 = 0x13d6 :=
  by rw [scan_instruction_pc 3391 (by decide) (by decide)]; rfl
@[simp] theorem pc2921 : Artifact.submissionArtifact.instructionPC 3392 = 0x13d7 :=
  by rw [scan_instruction_pc 3392 (by decide) (by decide)]; rfl
@[simp] theorem pc2922 : Artifact.submissionArtifact.instructionPC 3393 = 0x13d8 :=
  by rw [scan_instruction_pc 3393 (by decide) (by decide)]; rfl
@[simp] theorem pc2923 : Artifact.submissionArtifact.instructionPC 3394 = 0x13d9 :=
  by rw [scan_instruction_pc 3394 (by decide) (by decide)]; rfl
@[simp] theorem pc2924 : Artifact.submissionArtifact.instructionPC 3395 = 0x13da :=
  by rw [scan_instruction_pc 3395 (by decide) (by decide)]; rfl
@[simp] theorem pc2925 : Artifact.submissionArtifact.instructionPC 3396 = 0x13db :=
  by rw [scan_instruction_pc 3396 (by decide) (by decide)]; rfl
@[simp] theorem pc2926 : Artifact.submissionArtifact.instructionPC 3397 = 0x13dc :=
  by rw [scan_instruction_pc 3397 (by decide) (by decide)]; rfl
@[simp] theorem pc2927 : Artifact.submissionArtifact.instructionPC 3398 = 0x13dd :=
  by rw [scan_instruction_pc 3398 (by decide) (by decide)]; rfl
@[simp] theorem pc2928 : Artifact.submissionArtifact.instructionPC 3399 = 0x13de :=
  by rw [scan_instruction_pc 3399 (by decide) (by decide)]; rfl
@[simp] theorem pc2929 : Artifact.submissionArtifact.instructionPC 3400 = 0x13df :=
  by rw [scan_instruction_pc 3400 (by decide) (by decide)]; rfl
@[simp] theorem pc2930 : Artifact.submissionArtifact.instructionPC 3401 = 0x13e0 :=
  by rw [scan_instruction_pc 3401 (by decide) (by decide)]; rfl
@[simp] theorem pc2931 : Artifact.submissionArtifact.instructionPC 3402 = 0x13e2 :=
  by rw [scan_instruction_pc 3402 (by decide) (by decide)]; rfl
@[simp] theorem pc2932 : Artifact.submissionArtifact.instructionPC 3403 = 0x13e3 :=
  by rw [scan_instruction_pc 3403 (by decide) (by decide)]; rfl
@[simp] theorem pc2933 : Artifact.submissionArtifact.instructionPC 3404 = 0x13e5 :=
  by rw [scan_instruction_pc 3404 (by decide) (by decide)]; rfl
@[simp] theorem pc2934 : Artifact.submissionArtifact.instructionPC 3405 = 0x13e6 :=
  by rw [scan_instruction_pc 3405 (by decide) (by decide)]; rfl
@[simp] theorem pc2935 : Artifact.submissionArtifact.instructionPC 3406 = 0x13e9 :=
  by rw [scan_instruction_pc 3406 (by decide) (by decide)]; rfl
@[simp] theorem pc2936 : Artifact.submissionArtifact.instructionPC 3407 = 0x13ea :=
  by rw [scan_instruction_pc 3407 (by decide) (by decide)]; rfl
@[simp] theorem pc2937 : Artifact.submissionArtifact.instructionPC 3408 = 0x13eb :=
  by rw [scan_instruction_pc 3408 (by decide) (by decide)]; rfl
@[simp] theorem pc2938 : Artifact.submissionArtifact.instructionPC 3409 = 0x13ec :=
  by rw [scan_instruction_pc 3409 (by decide) (by decide)]; rfl
@[simp] theorem pc2939 : Artifact.submissionArtifact.instructionPC 3410 = 0x13ed :=
  by rw [scan_instruction_pc 3410 (by decide) (by decide)]; rfl
@[simp] theorem pc2940 : Artifact.submissionArtifact.instructionPC 3411 = 0x13ee :=
  by rw [scan_instruction_pc 3411 (by decide) (by decide)]; rfl
@[simp] theorem pc2941 : Artifact.submissionArtifact.instructionPC 3412 = 0x13ef :=
  by rw [scan_instruction_pc 3412 (by decide) (by decide)]; rfl
@[simp] theorem pc2942 : Artifact.submissionArtifact.instructionPC 3413 = 0x13f0 :=
  by rw [scan_instruction_pc 3413 (by decide) (by decide)]; rfl
@[simp] theorem pc2943 : Artifact.submissionArtifact.instructionPC 3414 = 0x13f1 :=
  by rw [scan_instruction_pc 3414 (by decide) (by decide)]; rfl
@[simp] theorem pc2944 : Artifact.submissionArtifact.instructionPC 3415 = 0x13f2 :=
  by rw [scan_instruction_pc 3415 (by decide) (by decide)]; rfl
@[simp] theorem pc2945 : Artifact.submissionArtifact.instructionPC 3416 = 0x13f3 :=
  by rw [scan_instruction_pc 3416 (by decide) (by decide)]; rfl
@[simp] theorem pc2946 : Artifact.submissionArtifact.instructionPC 3417 = 0x13f4 :=
  by rw [scan_instruction_pc 3417 (by decide) (by decide)]; rfl
@[simp] theorem pc2947 : Artifact.submissionArtifact.instructionPC 3418 = 0x13f6 :=
  by rw [scan_instruction_pc 3418 (by decide) (by decide)]; rfl
@[simp] theorem pc2948 : Artifact.submissionArtifact.instructionPC 3419 = 0x13f7 :=
  by rw [scan_instruction_pc 3419 (by decide) (by decide)]; rfl
@[simp] theorem pc2949 : Artifact.submissionArtifact.instructionPC 3420 = 0x13f9 :=
  by rw [scan_instruction_pc 3420 (by decide) (by decide)]; rfl
@[simp] theorem pc2950 : Artifact.submissionArtifact.instructionPC 3421 = 0x13fa :=
  by rw [scan_instruction_pc 3421 (by decide) (by decide)]; rfl
@[simp] theorem pc2951 : Artifact.submissionArtifact.instructionPC 3422 = 0x13fb :=
  by rw [scan_instruction_pc 3422 (by decide) (by decide)]; rfl
@[simp] theorem pc2952 : Artifact.submissionArtifact.instructionPC 3423 = 0x13fc :=
  by rw [scan_instruction_pc 3423 (by decide) (by decide)]; rfl
@[simp] theorem pc2953 : Artifact.submissionArtifact.instructionPC 3424 = 0x13fd :=
  by rw [scan_instruction_pc 3424 (by decide) (by decide)]; rfl
@[simp] theorem pc2954 : Artifact.submissionArtifact.instructionPC 3425 = 0x13ff :=
  by rw [scan_instruction_pc 3425 (by decide) (by decide)]; rfl
@[simp] theorem pc2955 : Artifact.submissionArtifact.instructionPC 3426 = 0x1400 :=
  by rw [scan_instruction_pc 3426 (by decide) (by decide)]; rfl
@[simp] theorem pc2956 : Artifact.submissionArtifact.instructionPC 3427 = 0x1401 :=
  by rw [scan_instruction_pc 3427 (by decide) (by decide)]; rfl
@[simp] theorem pc2957 : Artifact.submissionArtifact.instructionPC 3428 = 0x1402 :=
  by rw [scan_instruction_pc 3428 (by decide) (by decide)]; rfl
@[simp] theorem pc2958 : Artifact.submissionArtifact.instructionPC 3429 = 0x1403 :=
  by rw [scan_instruction_pc 3429 (by decide) (by decide)]; rfl
@[simp] theorem pc2959 : Artifact.submissionArtifact.instructionPC 3430 = 0x1406 :=
  by rw [scan_instruction_pc 3430 (by decide) (by decide)]; rfl
@[simp] theorem pc2960 : Artifact.submissionArtifact.instructionPC 3431 = 0x1407 :=
  by rw [scan_instruction_pc 3431 (by decide) (by decide)]; rfl
@[simp] theorem pc2961 : Artifact.submissionArtifact.instructionPC 3432 = 0x140a :=
  by rw [scan_instruction_pc 3432 (by decide) (by decide)]; rfl
@[simp] theorem pc2962 : Artifact.submissionArtifact.instructionPC 3433 = 0x140b :=
  by rw [scan_instruction_pc 3433 (by decide) (by decide)]; rfl
@[simp] theorem pc2963 : Artifact.submissionArtifact.instructionPC 3434 = 0x140e :=
  by rw [scan_instruction_pc 3434 (by decide) (by decide)]; rfl
@[simp] theorem pc2964 : Artifact.submissionArtifact.instructionPC 3435 = 0x140f :=
  by rw [scan_instruction_pc 3435 (by decide) (by decide)]; rfl
@[simp] theorem pc2965 : Artifact.submissionArtifact.instructionPC 3436 = 0x1418 :=
  by rw [scan_instruction_pc 3436 (by decide) (by decide)]; rfl
@[simp] theorem pc2966 : Artifact.submissionArtifact.instructionPC 3437 = 0x141a :=
  by rw [scan_instruction_pc 3437 (by decide) (by decide)]; rfl
@[simp] theorem pc2967 : Artifact.submissionArtifact.instructionPC 3438 = 0x141b :=
  by rw [scan_instruction_pc 3438 (by decide) (by decide)]; rfl
@[simp] theorem pc2968 : Artifact.submissionArtifact.instructionPC 3439 = 0x141c :=
  by rw [scan_instruction_pc 3439 (by decide) (by decide)]; rfl
@[simp] theorem pc2969 : Artifact.submissionArtifact.instructionPC 3440 = 0x141d :=
  by rw [scan_instruction_pc 3440 (by decide) (by decide)]; rfl
@[simp] theorem pc2970 : Artifact.submissionArtifact.instructionPC 3441 = 0x141e :=
  by rw [scan_instruction_pc 3441 (by decide) (by decide)]; rfl
@[simp] theorem pc2971 : Artifact.submissionArtifact.instructionPC 3442 = 0x141f :=
  by rw [scan_instruction_pc 3442 (by decide) (by decide)]; rfl
@[simp] theorem pc2972 : Artifact.submissionArtifact.instructionPC 3443 = 0x1420 :=
  by rw [scan_instruction_pc 3443 (by decide) (by decide)]; rfl
@[simp] theorem pc2973 : Artifact.submissionArtifact.instructionPC 3444 = 0x1421 :=
  by rw [scan_instruction_pc 3444 (by decide) (by decide)]; rfl
@[simp] theorem pc2974 : Artifact.submissionArtifact.instructionPC 3445 = 0x1422 :=
  by rw [scan_instruction_pc 3445 (by decide) (by decide)]; rfl
@[simp] theorem pc2975 : Artifact.submissionArtifact.instructionPC 3446 = 0x1423 :=
  by rw [scan_instruction_pc 3446 (by decide) (by decide)]; rfl
@[simp] theorem pc2976 : Artifact.submissionArtifact.instructionPC 3447 = 0x1424 :=
  by rw [scan_instruction_pc 3447 (by decide) (by decide)]; rfl
@[simp] theorem pc2977 : Artifact.submissionArtifact.instructionPC 3448 = 0x1425 :=
  by rw [scan_instruction_pc 3448 (by decide) (by decide)]; rfl
@[simp] theorem pc2978 : Artifact.submissionArtifact.instructionPC 3449 = 0x1426 :=
  by rw [scan_instruction_pc 3449 (by decide) (by decide)]; rfl
@[simp] theorem pc2979 : Artifact.submissionArtifact.instructionPC 3450 = 0x1427 :=
  by rw [scan_instruction_pc 3450 (by decide) (by decide)]; rfl
@[simp] theorem pc2980 : Artifact.submissionArtifact.instructionPC 3451 = 0x1428 :=
  by rw [scan_instruction_pc 3451 (by decide) (by decide)]; rfl
@[simp] theorem pc2981 : Artifact.submissionArtifact.instructionPC 3452 = 0x1429 :=
  by rw [scan_instruction_pc 3452 (by decide) (by decide)]; rfl
@[simp] theorem pc2982 : Artifact.submissionArtifact.instructionPC 3453 = 0x142c :=
  by rw [scan_instruction_pc 3453 (by decide) (by decide)]; rfl
@[simp] theorem pc2983 : Artifact.submissionArtifact.instructionPC 3454 = 0x142d :=
  by rw [scan_instruction_pc 3454 (by decide) (by decide)]; rfl
@[simp] theorem pc2984 : Artifact.submissionArtifact.instructionPC 3455 = 0x1442 :=
  by rw [scan_instruction_pc 3455 (by decide) (by decide)]; rfl
@[simp] theorem pc2985 : Artifact.submissionArtifact.instructionPC 3456 = 0x1443 :=
  by rw [scan_instruction_pc 3456 (by decide) (by decide)]; rfl
@[simp] theorem pc2986 : Artifact.submissionArtifact.instructionPC 3457 = 0x1444 :=
  by rw [scan_instruction_pc 3457 (by decide) (by decide)]; rfl
@[simp] theorem pc2987 : Artifact.submissionArtifact.instructionPC 3458 = 0x1446 :=
  by rw [scan_instruction_pc 3458 (by decide) (by decide)]; rfl
@[simp] theorem pc2988 : Artifact.submissionArtifact.instructionPC 3459 = 0x1447 :=
  by rw [scan_instruction_pc 3459 (by decide) (by decide)]; rfl
@[simp] theorem pc2989 : Artifact.submissionArtifact.instructionPC 3460 = 0x1448 :=
  by rw [scan_instruction_pc 3460 (by decide) (by decide)]; rfl
@[simp] theorem pc2990 : Artifact.submissionArtifact.instructionPC 3461 = 0x1449 :=
  by rw [scan_instruction_pc 3461 (by decide) (by decide)]; rfl
@[simp] theorem pc2991 : Artifact.submissionArtifact.instructionPC 3462 = 0x144a :=
  by rw [scan_instruction_pc 3462 (by decide) (by decide)]; rfl
@[simp] theorem pc2992 : Artifact.submissionArtifact.instructionPC 3463 = 0x144b :=
  by rw [scan_instruction_pc 3463 (by decide) (by decide)]; rfl
@[simp] theorem pc2993 : Artifact.submissionArtifact.instructionPC 3464 = 0x144d :=
  by rw [scan_instruction_pc 3464 (by decide) (by decide)]; rfl
@[simp] theorem pc2994 : Artifact.submissionArtifact.instructionPC 3465 = 0x144e :=
  by rw [scan_instruction_pc 3465 (by decide) (by decide)]; rfl
@[simp] theorem pc2995 : Artifact.submissionArtifact.instructionPC 3466 = 0x1450 :=
  by rw [scan_instruction_pc 3466 (by decide) (by decide)]; rfl
@[simp] theorem pc2996 : Artifact.submissionArtifact.instructionPC 3467 = 0x1451 :=
  by rw [scan_instruction_pc 3467 (by decide) (by decide)]; rfl
@[simp] theorem pc2997 : Artifact.submissionArtifact.instructionPC 3468 = 0x1453 :=
  by rw [scan_instruction_pc 3468 (by decide) (by decide)]; rfl
@[simp] theorem pc2998 : Artifact.submissionArtifact.instructionPC 3469 = 0x1454 :=
  by rw [scan_instruction_pc 3469 (by decide) (by decide)]; rfl
@[simp] theorem pc2999 : Artifact.submissionArtifact.instructionPC 3470 = 0x1456 :=
  by rw [scan_instruction_pc 3470 (by decide) (by decide)]; rfl
@[simp] theorem pc3000 : Artifact.submissionArtifact.instructionPC 3471 = 0x1457 :=
  by rw [scan_instruction_pc 3471 (by decide) (by decide)]; rfl
@[simp] theorem pc3001 : Artifact.submissionArtifact.instructionPC 3472 = 0x1458 :=
  by rw [scan_instruction_pc 3472 (by decide) (by decide)]; rfl
@[simp] theorem pc3002 : Artifact.submissionArtifact.instructionPC 3473 = 0x145a :=
  by rw [scan_instruction_pc 3473 (by decide) (by decide)]; rfl
@[simp] theorem pc3003 : Artifact.submissionArtifact.instructionPC 3474 = 0x145b :=
  by rw [scan_instruction_pc 3474 (by decide) (by decide)]; rfl
@[simp] theorem pc3004 : Artifact.submissionArtifact.instructionPC 3475 = 0x145c :=
  by rw [scan_instruction_pc 3475 (by decide) (by decide)]; rfl
@[simp] theorem pc3005 : Artifact.submissionArtifact.instructionPC 3476 = 0x145d :=
  by rw [scan_instruction_pc 3476 (by decide) (by decide)]; rfl
@[simp] theorem pc3006 : Artifact.submissionArtifact.instructionPC 3477 = 0x145e :=
  by rw [scan_instruction_pc 3477 (by decide) (by decide)]; rfl
@[simp] theorem pc3007 : Artifact.submissionArtifact.instructionPC 3478 = 0x145f :=
  by rw [scan_instruction_pc 3478 (by decide) (by decide)]; rfl
@[simp] theorem pc3008 : Artifact.submissionArtifact.instructionPC 3479 = 0x1460 :=
  by rw [scan_instruction_pc 3479 (by decide) (by decide)]; rfl
@[simp] theorem pc3009 : Artifact.submissionArtifact.instructionPC 3480 = 0x1461 :=
  by rw [scan_instruction_pc 3480 (by decide) (by decide)]; rfl
@[simp] theorem pc3010 : Artifact.submissionArtifact.instructionPC 3481 = 0x1462 :=
  by rw [scan_instruction_pc 3481 (by decide) (by decide)]; rfl
@[simp] theorem pc3011 : Artifact.submissionArtifact.instructionPC 3482 = 0x1463 :=
  by rw [scan_instruction_pc 3482 (by decide) (by decide)]; rfl
@[simp] theorem pc3012 : Artifact.submissionArtifact.instructionPC 3483 = 0x1464 :=
  by rw [scan_instruction_pc 3483 (by decide) (by decide)]; rfl
@[simp] theorem pc3013 : Artifact.submissionArtifact.instructionPC 3484 = 0x1465 :=
  by rw [scan_instruction_pc 3484 (by decide) (by decide)]; rfl
@[simp] theorem pc3014 : Artifact.submissionArtifact.instructionPC 3485 = 0x1466 :=
  by rw [scan_instruction_pc 3485 (by decide) (by decide)]; rfl
@[simp] theorem pc3015 : Artifact.submissionArtifact.instructionPC 3486 = 0x1467 :=
  by rw [scan_instruction_pc 3486 (by decide) (by decide)]; rfl
@[simp] theorem pc3016 : Artifact.submissionArtifact.instructionPC 3487 = 0x1468 :=
  by rw [scan_instruction_pc 3487 (by decide) (by decide)]; rfl
@[simp] theorem pc3017 : Artifact.submissionArtifact.instructionPC 3488 = 0x146a :=
  by rw [scan_instruction_pc 3488 (by decide) (by decide)]; rfl
@[simp] theorem pc3018 : Artifact.submissionArtifact.instructionPC 3489 = 0x146b :=
  by rw [scan_instruction_pc 3489 (by decide) (by decide)]; rfl
@[simp] theorem pc3019 : Artifact.submissionArtifact.instructionPC 3490 = 0x146c :=
  by rw [scan_instruction_pc 3490 (by decide) (by decide)]; rfl
@[simp] theorem pc3020 : Artifact.submissionArtifact.instructionPC 3491 = 0x146d :=
  by rw [scan_instruction_pc 3491 (by decide) (by decide)]; rfl
@[simp] theorem pc3021 : Artifact.submissionArtifact.instructionPC 3492 = 0x1470 :=
  by rw [scan_instruction_pc 3492 (by decide) (by decide)]; rfl
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
