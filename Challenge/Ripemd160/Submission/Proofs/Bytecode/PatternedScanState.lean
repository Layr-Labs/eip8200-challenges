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
    submissionInstructionsChunk15 ++
    submissionInstructionsChunk16

private def scanBefore : List YulEvmCompiler.Instr :=
  scanPrefix ++ submissionInstructionsChunk17.take 32

private def scanSuffix : List YulEvmCompiler.Instr :=
  submissionInstructionsChunk17.drop 32

private theorem scanBefore_length : scanBefore.length = 3432 := by
  simp [scanBefore, scanPrefix]

private theorem scanSuffix_length : scanSuffix.length = 127 := by
  simp [scanSuffix]

private theorem artifact_scan_split :
    Artifact.submissionArtifact.instructions = scanBefore ++ scanSuffix ++ [] := by
  change Artifact.submissionInstructions = _
  have hprefix : Artifact.submissionInstructions =
      scanPrefix ++ submissionInstructionsChunk17 := by
    simp only [Artifact.submissionInstructions, scanPrefix, List.append_assoc]
  have hchunk : submissionInstructionsChunk17 =
      submissionInstructionsChunk17.take 32 ++ submissionInstructionsChunk17.drop 32 := by
    exact (List.take_append_drop 32 submissionInstructionsChunk17).symm
  rw [hprefix]
  conv_lhs => rw [hchunk]
  simp only [scanBefore, scanSuffix, List.append_assoc, List.append_nil]

private theorem scanBefore_pc :
    (YulEvmCompiler.assembleBytes scanBefore).length = 5124 := by rfl

private theorem artifact_instruction_projection :
    Artifact.submissionArtifact.instructions = Artifact.submissionInstructions := by rfl

private theorem scan_instruction_at (index : Nat)
    (hlo : 3432 ≤ index) (hhi : index < 3559) :
    Artifact.submissionInstructions[index]? = scanSuffix[index - 3432]? := by
  have hi : index - 3432 < scanSuffix.length := by
    rw [scanSuffix_length]
    omega
  have h := ArtifactSegment.getElem?_segment Artifact.submissionArtifact
    scanBefore scanSuffix [] artifact_scan_split (index - 3432) hi
  simpa only [artifact_instruction_projection, scanBefore_length,
    Nat.add_sub_of_le hlo] using h

private theorem scan_instruction_pc (index : Nat)
    (hlo : 3432 ≤ index) (hhi : index ≤ 3559) :
    Artifact.submissionArtifact.instructionPC index =
      5124 + (YulEvmCompiler.assembleBytes (scanSuffix.take (index - 3432))).length := by
  have hi : index - 3432 ≤ scanSuffix.length := by
    rw [scanSuffix_length]
    omega
  have h := ArtifactSegment.instructionPC_segment_of_bounds Artifact.submissionArtifact
    scanBefore scanSuffix [] 3432 5124 artifact_scan_split scanBefore_length
    scanBefore_pc (index - 3432) hi
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
  [opAt 3432 .JUMPDEST,
   pushAt 3433 1 255,
   pushAt 3434 0 0,
   opAt 3435 .NOT,
   opAt 3436 .DIV,
   pushAt 3437 32 3244493450063667868678674439968361782956185527883176199882357678282131398018,
   opAt 3438 (.Dup ⟨1, by decide⟩),
   pushAt 3439 1 7,
   opAt 3440 .SHL,
   opAt 3441 (.Dup ⟨0, by decide⟩),
   opAt 3442 .NOT,
   opAt 3443 (.Swap ⟨0, by decide⟩),
   opAt 3444 (.Swap ⟨2, by decide⟩),
   opAt 3445 (.Dup ⟨2, by decide⟩),
   opAt 3446 (.Dup ⟨2, by decide⟩),
   opAt 3447 .AND,
   pushAt 3448 0 0,
   pushAt 3449 0 0,
   pushAt 3450 0 0]

/-- Derive the expected word and test for a straddler. -/
def wordPath : List Located :=
  [opAt 3451 .JUMPDEST, opAt 3452 (.Dup ⟨0, by decide⟩),
   opAt 3453 (.Dup ⟨5, by decide⟩), opAt 3454 .MUL,
   opAt 3455 (.Dup ⟨0, by decide⟩), opAt 3456 (.Dup ⟨7, by decide⟩),
   opAt 3457 .AND, opAt 3458 (.Dup ⟨5, by decide⟩), opAt 3459 .ADD,
   opAt 3460 (.Dup ⟨1, by decide⟩), opAt 3461 (.Dup ⟨9, by decide⟩),
   opAt 3462 .XOR, opAt 3463 (.Dup ⟨10, by decide⟩), opAt 3464 .AND,
   opAt 3465 .XOR, opAt 3466 (.Dup ⟨3, by decide⟩), pushAt 3467 1 255,
   opAt 3468 .AND, pushAt 3469 1 224, opAt 3470 .EQ, pushAt 3471 2 5297,
   opAt 3472 .JUMPI]

/-- Fold one word into the accumulator and advance. -/
def comparePath : List Located :=
  [opAt 3473 .JUMPDEST, opAt 3474 (.Dup ⟨3, by decide⟩),
   opAt 3475 .CALLDATALOAD, opAt 3476 .XOR, opAt 3477 (.Dup ⟨4, by decide⟩),
   opAt 3478 .OR, opAt 3479 (.Swap ⟨3, by decide⟩), opAt 3480 .POP,
   opAt 3481 .POP, opAt 3482 .JUMPDEST, pushAt 3483 1 160,
   opAt 3484 .ADD, pushAt 3485 1 255, opAt 3486 .AND,
   opAt 3487 .JUMPDEST, opAt 3488 .JUMPDEST,
   opAt 3489 (.Swap ⟨0, by decide⟩), pushAt 3490 1 32, opAt 3491 .ADD,
   opAt 3492 (.Swap ⟨0, by decide⟩), opAt 3493 .JUMPDEST,
   opAt 3494 (.Dup ⟨1, by decide⟩), pushAt 3495 2 992, opAt 3496 .GT,
   pushAt 3497 2 5177, opAt 3498 .JUMPI]

/-- The padded tail word, the cleanup and the miss test. -/
def tailPath : List Located :=
  [pushAt 3499 2 992, opAt 3500 .CALLDATALOAD,
   pushAt 3501 8 9848759918901945995, pushAt 3502 1 192, opAt 3503 .SHL,
   opAt 3504 .XOR, opAt 3505 (.Dup ⟨3, by decide⟩), opAt 3506 .OR,
   opAt 3507 (.Swap ⟨2, by decide⟩), opAt 3508 .POP,
   opAt 3509 (.Swap ⟨1, by decide⟩), opAt 3510 (.Swap ⟨6, by decide⟩),
   opAt 3511 .POP, opAt 3512 .POP, opAt 3513 .POP, opAt 3514 .POP,
   opAt 3515 .POP, opAt 3516 .POP, opAt 3517 .POP, pushAt 3518 2 1004,
   opAt 3519 .JUMPI]

/-- Store and return the stored digest. -/
def returnPath : List Located :=
  [pushAt 3520 20 766350606435067737561421097975693824639675460820,
   pushAt 3521 0 0, opAt 3522 .MSTORE, pushAt 3523 1 32, pushAt 3524 0 0,
   opAt 3525 .RETURN]

/-- Shift the correction constant out of `M`. -/
def straddleCorrPath : List Located :=
  [opAt 3526 .JUMPDEST, opAt 3527 (.Dup ⟨6, by decide⟩),
   opAt 3528 (.Dup ⟨4, by decide⟩), pushAt 3529 1 8, opAt 3530 .SHR,
   pushAt 3531 1 5, opAt 3532 .MUL, pushAt 3533 1 27, opAt 3534 .SUB,
   pushAt 3535 1 8, opAt 3536 .MUL, opAt 3537 .SHR, pushAt 3538 1 11,
   opAt 3539 .MUL]

/-- Apply the correction to the expected word. -/
def straddleAddPath : List Located :=
  [opAt 3540 (.Dup ⟨1, by decide⟩), opAt 3541 (.Dup ⟨9, by decide⟩),
   opAt 3542 .AND, opAt 3543 (.Dup ⟨1, by decide⟩), opAt 3544 .ADD,
   opAt 3545 (.Dup ⟨2, by decide⟩), opAt 3546 (.Dup ⟨12, by decide⟩),
   opAt 3547 .AND, opAt 3548 .XOR, opAt 3549 (.Swap ⟨1, by decide⟩),
   opAt 3550 .POP, opAt 3551 .POP]

/-- Bump the scalar and rejoin the scan. -/
def straddleBackPath : List Located :=
  [opAt 3552 (.Dup ⟨2, by decide⟩), pushAt 3553 1 11, opAt 3554 .ADD,
   opAt 3555 (.Swap ⟨2, by decide⟩), opAt 3556 .POP, pushAt 3557 2 5203,
   opAt 3558 .JUMP]


@[simp] theorem pc2903 : Artifact.submissionArtifact.instructionPC 3432 = 0x1404 :=
  by rw [scan_instruction_pc 3432 (by decide) (by decide)]; rfl
@[simp] theorem pc2904 : Artifact.submissionArtifact.instructionPC 3433 = 0x1405 :=
  by rw [scan_instruction_pc 3433 (by decide) (by decide)]; rfl
@[simp] theorem pc2905 : Artifact.submissionArtifact.instructionPC 3437 = 0x140a :=
  by rw [scan_instruction_pc 3437 (by decide) (by decide)]; rfl
@[simp] theorem pc2906 : Artifact.submissionArtifact.instructionPC 3442 = 0x1430 :=
  by rw [scan_instruction_pc 3442 (by decide) (by decide)]; rfl
@[simp] theorem pc2907 : Artifact.submissionArtifact.instructionPC 3444 = 0x1432 :=
  by rw [scan_instruction_pc 3444 (by decide) (by decide)]; rfl
@[simp] theorem pc2908 : Artifact.submissionArtifact.instructionPC 3445 = 0x1433 :=
  by rw [scan_instruction_pc 3445 (by decide) (by decide)]; rfl
@[simp] theorem pc2909 : Artifact.submissionArtifact.instructionPC 3446 = 0x1434 :=
  by rw [scan_instruction_pc 3446 (by decide) (by decide)]; rfl
@[simp] theorem pc2910 : Artifact.submissionArtifact.instructionPC 3447 = 0x1435 :=
  by rw [scan_instruction_pc 3447 (by decide) (by decide)]; rfl
@[simp] theorem pc2911 : Artifact.submissionArtifact.instructionPC 3448 = 0x1436 :=
  by rw [scan_instruction_pc 3448 (by decide) (by decide)]; rfl
@[simp] theorem pc2912 : Artifact.submissionArtifact.instructionPC 3449 = 0x1437 :=
  by rw [scan_instruction_pc 3449 (by decide) (by decide)]; rfl
@[simp] theorem pc2913 : Artifact.submissionArtifact.instructionPC 3450 = 0x1438 :=
  by rw [scan_instruction_pc 3450 (by decide) (by decide)]; rfl
@[simp] theorem pc2914 : Artifact.submissionArtifact.instructionPC 3451 = 0x1439 :=
  by rw [scan_instruction_pc 3451 (by decide) (by decide)]; rfl
@[simp] theorem pc2915 : Artifact.submissionArtifact.instructionPC 3452 = 0x143a :=
  by rw [scan_instruction_pc 3452 (by decide) (by decide)]; rfl
@[simp] theorem pc2916 : Artifact.submissionArtifact.instructionPC 3453 = 0x143b :=
  by rw [scan_instruction_pc 3453 (by decide) (by decide)]; rfl
@[simp] theorem pc2917 : Artifact.submissionArtifact.instructionPC 3454 = 0x143c :=
  by rw [scan_instruction_pc 3454 (by decide) (by decide)]; rfl
@[simp] theorem pc2918 : Artifact.submissionArtifact.instructionPC 3455 = 0x143d :=
  by rw [scan_instruction_pc 3455 (by decide) (by decide)]; rfl
@[simp] theorem pc2919 : Artifact.submissionArtifact.instructionPC 3456 = 0x143e :=
  by rw [scan_instruction_pc 3456 (by decide) (by decide)]; rfl
@[simp] theorem pc2920 : Artifact.submissionArtifact.instructionPC 3457 = 0x143f :=
  by rw [scan_instruction_pc 3457 (by decide) (by decide)]; rfl
@[simp] theorem pc2921 : Artifact.submissionArtifact.instructionPC 3458 = 0x1440 :=
  by rw [scan_instruction_pc 3458 (by decide) (by decide)]; rfl
@[simp] theorem pc2922 : Artifact.submissionArtifact.instructionPC 3459 = 0x1441 :=
  by rw [scan_instruction_pc 3459 (by decide) (by decide)]; rfl
@[simp] theorem pc2923 : Artifact.submissionArtifact.instructionPC 3460 = 0x1442 :=
  by rw [scan_instruction_pc 3460 (by decide) (by decide)]; rfl
@[simp] theorem pc2924 : Artifact.submissionArtifact.instructionPC 3461 = 0x1443 :=
  by rw [scan_instruction_pc 3461 (by decide) (by decide)]; rfl
@[simp] theorem pc2925 : Artifact.submissionArtifact.instructionPC 3462 = 0x1444 :=
  by rw [scan_instruction_pc 3462 (by decide) (by decide)]; rfl
@[simp] theorem pc2926 : Artifact.submissionArtifact.instructionPC 3463 = 0x1445 :=
  by rw [scan_instruction_pc 3463 (by decide) (by decide)]; rfl
@[simp] theorem pc2927 : Artifact.submissionArtifact.instructionPC 3464 = 0x1446 :=
  by rw [scan_instruction_pc 3464 (by decide) (by decide)]; rfl
@[simp] theorem pc2928 : Artifact.submissionArtifact.instructionPC 3465 = 0x1447 :=
  by rw [scan_instruction_pc 3465 (by decide) (by decide)]; rfl
@[simp] theorem pc2929 : Artifact.submissionArtifact.instructionPC 3466 = 0x1448 :=
  by rw [scan_instruction_pc 3466 (by decide) (by decide)]; rfl
@[simp] theorem pc2930 : Artifact.submissionArtifact.instructionPC 3467 = 0x1449 :=
  by rw [scan_instruction_pc 3467 (by decide) (by decide)]; rfl
@[simp] theorem pc2931 : Artifact.submissionArtifact.instructionPC 3468 = 0x144b :=
  by rw [scan_instruction_pc 3468 (by decide) (by decide)]; rfl
@[simp] theorem pc2932 : Artifact.submissionArtifact.instructionPC 3469 = 0x144c :=
  by rw [scan_instruction_pc 3469 (by decide) (by decide)]; rfl
@[simp] theorem pc2933 : Artifact.submissionArtifact.instructionPC 3470 = 0x144e :=
  by rw [scan_instruction_pc 3470 (by decide) (by decide)]; rfl
@[simp] theorem pc2934 : Artifact.submissionArtifact.instructionPC 3471 = 0x144f :=
  by rw [scan_instruction_pc 3471 (by decide) (by decide)]; rfl
@[simp] theorem pc2935 : Artifact.submissionArtifact.instructionPC 3472 = 0x1452 :=
  by rw [scan_instruction_pc 3472 (by decide) (by decide)]; rfl
@[simp] theorem pc2936 : Artifact.submissionArtifact.instructionPC 3473 = 0x1453 :=
  by rw [scan_instruction_pc 3473 (by decide) (by decide)]; rfl
@[simp] theorem pc2937 : Artifact.submissionArtifact.instructionPC 3474 = 0x1454 :=
  by rw [scan_instruction_pc 3474 (by decide) (by decide)]; rfl
@[simp] theorem pc2938 : Artifact.submissionArtifact.instructionPC 3475 = 0x1455 :=
  by rw [scan_instruction_pc 3475 (by decide) (by decide)]; rfl
@[simp] theorem pc2939 : Artifact.submissionArtifact.instructionPC 3476 = 0x1456 :=
  by rw [scan_instruction_pc 3476 (by decide) (by decide)]; rfl
@[simp] theorem pc2940 : Artifact.submissionArtifact.instructionPC 3477 = 0x1457 :=
  by rw [scan_instruction_pc 3477 (by decide) (by decide)]; rfl
@[simp] theorem pc2941 : Artifact.submissionArtifact.instructionPC 3478 = 0x1458 :=
  by rw [scan_instruction_pc 3478 (by decide) (by decide)]; rfl
@[simp] theorem pc2942 : Artifact.submissionArtifact.instructionPC 3479 = 0x1459 :=
  by rw [scan_instruction_pc 3479 (by decide) (by decide)]; rfl
@[simp] theorem pc2943 : Artifact.submissionArtifact.instructionPC 3480 = 0x145a :=
  by rw [scan_instruction_pc 3480 (by decide) (by decide)]; rfl
@[simp] theorem pc2944 : Artifact.submissionArtifact.instructionPC 3481 = 0x145b :=
  by rw [scan_instruction_pc 3481 (by decide) (by decide)]; rfl
@[simp] theorem pc2945 : Artifact.submissionArtifact.instructionPC 3482 = 0x145c :=
  by rw [scan_instruction_pc 3482 (by decide) (by decide)]; rfl
@[simp] theorem pc2946 : Artifact.submissionArtifact.instructionPC 3483 = 0x145d :=
  by rw [scan_instruction_pc 3483 (by decide) (by decide)]; rfl
@[simp] theorem pc2947 : Artifact.submissionArtifact.instructionPC 3484 = 0x145f :=
  by rw [scan_instruction_pc 3484 (by decide) (by decide)]; rfl
@[simp] theorem pc2948 : Artifact.submissionArtifact.instructionPC 3485 = 0x1460 :=
  by rw [scan_instruction_pc 3485 (by decide) (by decide)]; rfl
@[simp] theorem pc2949 : Artifact.submissionArtifact.instructionPC 3486 = 0x1462 :=
  by rw [scan_instruction_pc 3486 (by decide) (by decide)]; rfl
@[simp] theorem pc2950 : Artifact.submissionArtifact.instructionPC 3487 = 0x1463 :=
  by rw [scan_instruction_pc 3487 (by decide) (by decide)]; rfl
@[simp] theorem pc2951 : Artifact.submissionArtifact.instructionPC 3488 = 0x1464 :=
  by rw [scan_instruction_pc 3488 (by decide) (by decide)]; rfl
@[simp] theorem pc2952 : Artifact.submissionArtifact.instructionPC 3489 = 0x1465 :=
  by rw [scan_instruction_pc 3489 (by decide) (by decide)]; rfl
@[simp] theorem pc2953 : Artifact.submissionArtifact.instructionPC 3490 = 0x1466 :=
  by rw [scan_instruction_pc 3490 (by decide) (by decide)]; rfl
@[simp] theorem pc2954 : Artifact.submissionArtifact.instructionPC 3491 = 0x1468 :=
  by rw [scan_instruction_pc 3491 (by decide) (by decide)]; rfl
@[simp] theorem pc2955 : Artifact.submissionArtifact.instructionPC 3492 = 0x1469 :=
  by rw [scan_instruction_pc 3492 (by decide) (by decide)]; rfl
@[simp] theorem pc2956 : Artifact.submissionArtifact.instructionPC 3493 = 0x146a :=
  by rw [scan_instruction_pc 3493 (by decide) (by decide)]; rfl
@[simp] theorem pc2957 : Artifact.submissionArtifact.instructionPC 3494 = 0x146b :=
  by rw [scan_instruction_pc 3494 (by decide) (by decide)]; rfl
@[simp] theorem pc2958 : Artifact.submissionArtifact.instructionPC 3495 = 0x146c :=
  by rw [scan_instruction_pc 3495 (by decide) (by decide)]; rfl
@[simp] theorem pc2959 : Artifact.submissionArtifact.instructionPC 3496 = 0x146f :=
  by rw [scan_instruction_pc 3496 (by decide) (by decide)]; rfl
@[simp] theorem pc2960 : Artifact.submissionArtifact.instructionPC 3497 = 0x1470 :=
  by rw [scan_instruction_pc 3497 (by decide) (by decide)]; rfl
@[simp] theorem pc2961 : Artifact.submissionArtifact.instructionPC 3498 = 0x1473 :=
  by rw [scan_instruction_pc 3498 (by decide) (by decide)]; rfl
@[simp] theorem pc2962 : Artifact.submissionArtifact.instructionPC 3499 = 0x1474 :=
  by rw [scan_instruction_pc 3499 (by decide) (by decide)]; rfl
@[simp] theorem pc2963 : Artifact.submissionArtifact.instructionPC 3500 = 0x1477 :=
  by rw [scan_instruction_pc 3500 (by decide) (by decide)]; rfl
@[simp] theorem pc2964 : Artifact.submissionArtifact.instructionPC 3501 = 0x1478 :=
  by rw [scan_instruction_pc 3501 (by decide) (by decide)]; rfl
@[simp] theorem pc2965 : Artifact.submissionArtifact.instructionPC 3502 = 0x1481 :=
  by rw [scan_instruction_pc 3502 (by decide) (by decide)]; rfl
@[simp] theorem pc2966 : Artifact.submissionArtifact.instructionPC 3503 = 0x1483 :=
  by rw [scan_instruction_pc 3503 (by decide) (by decide)]; rfl
@[simp] theorem pc2967 : Artifact.submissionArtifact.instructionPC 3504 = 0x1484 :=
  by rw [scan_instruction_pc 3504 (by decide) (by decide)]; rfl
@[simp] theorem pc2968 : Artifact.submissionArtifact.instructionPC 3505 = 0x1485 :=
  by rw [scan_instruction_pc 3505 (by decide) (by decide)]; rfl
@[simp] theorem pc2969 : Artifact.submissionArtifact.instructionPC 3506 = 0x1486 :=
  by rw [scan_instruction_pc 3506 (by decide) (by decide)]; rfl
@[simp] theorem pc2970 : Artifact.submissionArtifact.instructionPC 3507 = 0x1487 :=
  by rw [scan_instruction_pc 3507 (by decide) (by decide)]; rfl
@[simp] theorem pc2971 : Artifact.submissionArtifact.instructionPC 3508 = 0x1488 :=
  by rw [scan_instruction_pc 3508 (by decide) (by decide)]; rfl
@[simp] theorem pc2972 : Artifact.submissionArtifact.instructionPC 3509 = 0x1489 :=
  by rw [scan_instruction_pc 3509 (by decide) (by decide)]; rfl
@[simp] theorem pc2973 : Artifact.submissionArtifact.instructionPC 3510 = 0x148a :=
  by rw [scan_instruction_pc 3510 (by decide) (by decide)]; rfl
@[simp] theorem pc2974 : Artifact.submissionArtifact.instructionPC 3511 = 0x148b :=
  by rw [scan_instruction_pc 3511 (by decide) (by decide)]; rfl
@[simp] theorem pc2975 : Artifact.submissionArtifact.instructionPC 3512 = 0x148c :=
  by rw [scan_instruction_pc 3512 (by decide) (by decide)]; rfl
@[simp] theorem pc2976 : Artifact.submissionArtifact.instructionPC 3513 = 0x148d :=
  by rw [scan_instruction_pc 3513 (by decide) (by decide)]; rfl
@[simp] theorem pc2977 : Artifact.submissionArtifact.instructionPC 3514 = 0x148e :=
  by rw [scan_instruction_pc 3514 (by decide) (by decide)]; rfl
@[simp] theorem pc2978 : Artifact.submissionArtifact.instructionPC 3515 = 0x148f :=
  by rw [scan_instruction_pc 3515 (by decide) (by decide)]; rfl
@[simp] theorem pc2979 : Artifact.submissionArtifact.instructionPC 3516 = 0x1490 :=
  by rw [scan_instruction_pc 3516 (by decide) (by decide)]; rfl
@[simp] theorem pc2980 : Artifact.submissionArtifact.instructionPC 3517 = 0x1491 :=
  by rw [scan_instruction_pc 3517 (by decide) (by decide)]; rfl
@[simp] theorem pc2981 : Artifact.submissionArtifact.instructionPC 3518 = 0x1492 :=
  by rw [scan_instruction_pc 3518 (by decide) (by decide)]; rfl
@[simp] theorem pc2982 : Artifact.submissionArtifact.instructionPC 3519 = 0x1495 :=
  by rw [scan_instruction_pc 3519 (by decide) (by decide)]; rfl
@[simp] theorem pc2983 : Artifact.submissionArtifact.instructionPC 3520 = 0x1496 :=
  by rw [scan_instruction_pc 3520 (by decide) (by decide)]; rfl
@[simp] theorem pc2984 : Artifact.submissionArtifact.instructionPC 3521 = 0x14ab :=
  by rw [scan_instruction_pc 3521 (by decide) (by decide)]; rfl
@[simp] theorem pc2985 : Artifact.submissionArtifact.instructionPC 3522 = 0x14ac :=
  by rw [scan_instruction_pc 3522 (by decide) (by decide)]; rfl
@[simp] theorem pc2986 : Artifact.submissionArtifact.instructionPC 3523 = 0x14ad :=
  by rw [scan_instruction_pc 3523 (by decide) (by decide)]; rfl
@[simp] theorem pc2987 : Artifact.submissionArtifact.instructionPC 3524 = 0x14af :=
  by rw [scan_instruction_pc 3524 (by decide) (by decide)]; rfl
@[simp] theorem pc2988 : Artifact.submissionArtifact.instructionPC 3525 = 0x14b0 :=
  by rw [scan_instruction_pc 3525 (by decide) (by decide)]; rfl
@[simp] theorem pc2989 : Artifact.submissionArtifact.instructionPC 3526 = 0x14b1 :=
  by rw [scan_instruction_pc 3526 (by decide) (by decide)]; rfl
@[simp] theorem pc2990 : Artifact.submissionArtifact.instructionPC 3527 = 0x14b2 :=
  by rw [scan_instruction_pc 3527 (by decide) (by decide)]; rfl
@[simp] theorem pc2991 : Artifact.submissionArtifact.instructionPC 3528 = 0x14b3 :=
  by rw [scan_instruction_pc 3528 (by decide) (by decide)]; rfl
@[simp] theorem pc2992 : Artifact.submissionArtifact.instructionPC 3529 = 0x14b4 :=
  by rw [scan_instruction_pc 3529 (by decide) (by decide)]; rfl
@[simp] theorem pc2993 : Artifact.submissionArtifact.instructionPC 3530 = 0x14b6 :=
  by rw [scan_instruction_pc 3530 (by decide) (by decide)]; rfl
@[simp] theorem pc2994 : Artifact.submissionArtifact.instructionPC 3531 = 0x14b7 :=
  by rw [scan_instruction_pc 3531 (by decide) (by decide)]; rfl
@[simp] theorem pc2995 : Artifact.submissionArtifact.instructionPC 3532 = 0x14b9 :=
  by rw [scan_instruction_pc 3532 (by decide) (by decide)]; rfl
@[simp] theorem pc2996 : Artifact.submissionArtifact.instructionPC 3533 = 0x14ba :=
  by rw [scan_instruction_pc 3533 (by decide) (by decide)]; rfl
@[simp] theorem pc2997 : Artifact.submissionArtifact.instructionPC 3534 = 0x14bc :=
  by rw [scan_instruction_pc 3534 (by decide) (by decide)]; rfl
@[simp] theorem pc2998 : Artifact.submissionArtifact.instructionPC 3535 = 0x14bd :=
  by rw [scan_instruction_pc 3535 (by decide) (by decide)]; rfl
@[simp] theorem pc2999 : Artifact.submissionArtifact.instructionPC 3536 = 0x14bf :=
  by rw [scan_instruction_pc 3536 (by decide) (by decide)]; rfl
@[simp] theorem pc3000 : Artifact.submissionArtifact.instructionPC 3537 = 0x14c0 :=
  by rw [scan_instruction_pc 3537 (by decide) (by decide)]; rfl
@[simp] theorem pc3001 : Artifact.submissionArtifact.instructionPC 3538 = 0x14c1 :=
  by rw [scan_instruction_pc 3538 (by decide) (by decide)]; rfl
@[simp] theorem pc3002 : Artifact.submissionArtifact.instructionPC 3539 = 0x14c3 :=
  by rw [scan_instruction_pc 3539 (by decide) (by decide)]; rfl
@[simp] theorem pc3003 : Artifact.submissionArtifact.instructionPC 3540 = 0x14c4 :=
  by rw [scan_instruction_pc 3540 (by decide) (by decide)]; rfl
@[simp] theorem pc3004 : Artifact.submissionArtifact.instructionPC 3541 = 0x14c5 :=
  by rw [scan_instruction_pc 3541 (by decide) (by decide)]; rfl
@[simp] theorem pc3005 : Artifact.submissionArtifact.instructionPC 3542 = 0x14c6 :=
  by rw [scan_instruction_pc 3542 (by decide) (by decide)]; rfl
@[simp] theorem pc3006 : Artifact.submissionArtifact.instructionPC 3543 = 0x14c7 :=
  by rw [scan_instruction_pc 3543 (by decide) (by decide)]; rfl
@[simp] theorem pc3007 : Artifact.submissionArtifact.instructionPC 3544 = 0x14c8 :=
  by rw [scan_instruction_pc 3544 (by decide) (by decide)]; rfl
@[simp] theorem pc3008 : Artifact.submissionArtifact.instructionPC 3545 = 0x14c9 :=
  by rw [scan_instruction_pc 3545 (by decide) (by decide)]; rfl
@[simp] theorem pc3009 : Artifact.submissionArtifact.instructionPC 3546 = 0x14ca :=
  by rw [scan_instruction_pc 3546 (by decide) (by decide)]; rfl
@[simp] theorem pc3010 : Artifact.submissionArtifact.instructionPC 3547 = 0x14cb :=
  by rw [scan_instruction_pc 3547 (by decide) (by decide)]; rfl
@[simp] theorem pc3011 : Artifact.submissionArtifact.instructionPC 3548 = 0x14cc :=
  by rw [scan_instruction_pc 3548 (by decide) (by decide)]; rfl
@[simp] theorem pc3012 : Artifact.submissionArtifact.instructionPC 3549 = 0x14cd :=
  by rw [scan_instruction_pc 3549 (by decide) (by decide)]; rfl
@[simp] theorem pc3013 : Artifact.submissionArtifact.instructionPC 3550 = 0x14ce :=
  by rw [scan_instruction_pc 3550 (by decide) (by decide)]; rfl
@[simp] theorem pc3014 : Artifact.submissionArtifact.instructionPC 3551 = 0x14cf :=
  by rw [scan_instruction_pc 3551 (by decide) (by decide)]; rfl
@[simp] theorem pc3015 : Artifact.submissionArtifact.instructionPC 3552 = 0x14d0 :=
  by rw [scan_instruction_pc 3552 (by decide) (by decide)]; rfl
@[simp] theorem pc3016 : Artifact.submissionArtifact.instructionPC 3553 = 0x14d1 :=
  by rw [scan_instruction_pc 3553 (by decide) (by decide)]; rfl
@[simp] theorem pc3017 : Artifact.submissionArtifact.instructionPC 3554 = 0x14d3 :=
  by rw [scan_instruction_pc 3554 (by decide) (by decide)]; rfl
@[simp] theorem pc3018 : Artifact.submissionArtifact.instructionPC 3555 = 0x14d4 :=
  by rw [scan_instruction_pc 3555 (by decide) (by decide)]; rfl
@[simp] theorem pc3019 : Artifact.submissionArtifact.instructionPC 3556 = 0x14d5 :=
  by rw [scan_instruction_pc 3556 (by decide) (by decide)]; rfl
@[simp] theorem pc3020 : Artifact.submissionArtifact.instructionPC 3557 = 0x14d6 :=
  by rw [scan_instruction_pc 3557 (by decide) (by decide)]; rfl
@[simp] theorem pc3021 : Artifact.submissionArtifact.instructionPC 3558 = 0x14d9 :=
  by rw [scan_instruction_pc 3558 (by decide) (by decide)]; rfl
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
