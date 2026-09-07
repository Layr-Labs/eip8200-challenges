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

private theorem scanBefore_length : scanBefore.length = 3464 := by
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
    (YulEvmCompiler.assembleBytes scanBefore).length = 5078 := by rfl

private theorem artifact_instruction_projection :
    Artifact.submissionArtifact.instructions = Artifact.submissionInstructions := by rfl

private theorem scan_instruction_at (index : Nat)
    (hlo : 3464 ≤ index) (hhi : index < 3591) :
    Artifact.submissionInstructions[index]? = scanSuffix[index - 3464]? := by
  have hi : index - 3464 < scanSuffix.length := by
    rw [scanSuffix_length]
    omega
  have h := ArtifactSegment.getElem?_segment Artifact.submissionArtifact
    scanBefore scanSuffix [] artifact_scan_split (index - 3464) hi
  simpa only [artifact_instruction_projection, scanBefore_length,
    Nat.add_sub_of_le hlo] using h

private theorem scan_instruction_pc (index : Nat)
    (hlo : 3464 ≤ index) (hhi : index ≤ 3591) :
    Artifact.submissionArtifact.instructionPC index =
      5078 + (YulEvmCompiler.assembleBytes (scanSuffix.take (index - 3464))).length := by
  have hi : index - 3464 ≤ scanSuffix.length := by
    rw [scanSuffix_length]
    omega
  have h := ArtifactSegment.instructionPC_segment_of_bounds Artifact.submissionArtifact
    scanBefore scanSuffix [] 3464 5078 artifact_scan_split scanBefore_length
    scanBefore_pc (index - 3464) hi
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
  [opAt 3464 .JUMPDEST,
   pushAt 3465 1 255,
   pushAt 3466 0 0,
   opAt 3467 .NOT,
   opAt 3468 .DIV,
   pushAt 3469 32 3244493450063667868678674439968361782956185527883176199882357678282131398018,
   opAt 3470 (.Dup ⟨1, by decide⟩),
   pushAt 3471 1 7,
   opAt 3472 .SHL,
   opAt 3473 (.Dup ⟨0, by decide⟩),
   opAt 3474 .NOT,
   opAt 3475 (.Swap ⟨0, by decide⟩),
   opAt 3476 (.Swap ⟨2, by decide⟩),
   opAt 3477 (.Dup ⟨2, by decide⟩),
   opAt 3478 (.Dup ⟨2, by decide⟩),
   opAt 3479 .AND,
   pushAt 3480 0 0,
   pushAt 3481 0 0,
   pushAt 3482 0 0]

/-- Derive the expected word and test for a straddler. -/
def wordPath : List Located :=
  [opAt 3483 .JUMPDEST, opAt 3484 (.Dup ⟨0, by decide⟩),
   opAt 3485 (.Dup ⟨5, by decide⟩), opAt 3486 .MUL,
   opAt 3487 (.Dup ⟨0, by decide⟩), opAt 3488 (.Dup ⟨7, by decide⟩),
   opAt 3489 .AND, opAt 3490 (.Dup ⟨5, by decide⟩), opAt 3491 .ADD,
   opAt 3492 (.Dup ⟨1, by decide⟩), opAt 3493 (.Dup ⟨9, by decide⟩),
   opAt 3494 .XOR, opAt 3495 (.Dup ⟨10, by decide⟩), opAt 3496 .AND,
   opAt 3497 .XOR, opAt 3498 (.Dup ⟨3, by decide⟩), pushAt 3499 1 255,
   opAt 3500 .AND, pushAt 3501 1 224, opAt 3502 .EQ, pushAt 3503 2 5251,
   opAt 3504 .JUMPI]

/-- Fold one word into the accumulator and advance. -/
def comparePath : List Located :=
  [opAt 3505 .JUMPDEST, opAt 3506 (.Dup ⟨3, by decide⟩),
   opAt 3507 .CALLDATALOAD, opAt 3508 .XOR, opAt 3509 (.Dup ⟨4, by decide⟩),
   opAt 3510 .OR, opAt 3511 (.Swap ⟨3, by decide⟩), opAt 3512 .POP,
   opAt 3513 .POP, opAt 3514 .JUMPDEST, pushAt 3515 1 160,
   opAt 3516 .ADD, pushAt 3517 1 255, opAt 3518 .AND,
   opAt 3519 .JUMPDEST, opAt 3520 .JUMPDEST,
   opAt 3521 (.Swap ⟨0, by decide⟩), pushAt 3522 1 32, opAt 3523 .ADD,
   opAt 3524 (.Swap ⟨0, by decide⟩), opAt 3525 .JUMPDEST,
   opAt 3526 (.Dup ⟨1, by decide⟩), pushAt 3527 2 992, opAt 3528 .GT,
   pushAt 3529 2 5131, opAt 3530 .JUMPI]

/-- The padded tail word, the cleanup and the miss test. -/
def tailPath : List Located :=
  [pushAt 3531 2 992, opAt 3532 .CALLDATALOAD,
   pushAt 3533 8 9848759918901945995, pushAt 3534 1 192, opAt 3535 .SHL,
   opAt 3536 .XOR, opAt 3537 (.Dup ⟨3, by decide⟩), opAt 3538 .OR,
   opAt 3539 (.Swap ⟨2, by decide⟩), opAt 3540 .POP,
   opAt 3541 (.Swap ⟨1, by decide⟩), opAt 3542 (.Swap ⟨6, by decide⟩),
   opAt 3543 .POP, opAt 3544 .POP, opAt 3545 .POP, opAt 3546 .POP,
   opAt 3547 .POP, opAt 3548 .POP, opAt 3549 .POP, pushAt 3550 2 1004,
   opAt 3551 .JUMPI]

/-- Store and return the stored digest. -/
def returnPath : List Located :=
  [pushAt 3552 20 766350606435067737561421097975693824639675460820,
   pushAt 3553 0 0, opAt 3554 .MSTORE, pushAt 3555 1 32, pushAt 3556 0 0,
   opAt 3557 .RETURN]

/-- Shift the correction constant out of `M`. -/
def straddleCorrPath : List Located :=
  [opAt 3558 .JUMPDEST, opAt 3559 (.Dup ⟨6, by decide⟩),
   opAt 3560 (.Dup ⟨4, by decide⟩), pushAt 3561 1 8, opAt 3562 .SHR,
   pushAt 3563 1 5, opAt 3564 .MUL, pushAt 3565 1 27, opAt 3566 .SUB,
   pushAt 3567 1 8, opAt 3568 .MUL, opAt 3569 .SHR, pushAt 3570 1 11,
   opAt 3571 .MUL]

/-- Apply the correction to the expected word. -/
def straddleAddPath : List Located :=
  [opAt 3572 (.Dup ⟨1, by decide⟩), opAt 3573 (.Dup ⟨9, by decide⟩),
   opAt 3574 .AND, opAt 3575 (.Dup ⟨1, by decide⟩), opAt 3576 .ADD,
   opAt 3577 (.Dup ⟨2, by decide⟩), opAt 3578 (.Dup ⟨12, by decide⟩),
   opAt 3579 .AND, opAt 3580 .XOR, opAt 3581 (.Swap ⟨1, by decide⟩),
   opAt 3582 .POP, opAt 3583 .POP]

/-- Bump the scalar and rejoin the scan. -/
def straddleBackPath : List Located :=
  [opAt 3584 (.Dup ⟨2, by decide⟩), pushAt 3585 1 11, opAt 3586 .ADD,
   opAt 3587 (.Swap ⟨2, by decide⟩), opAt 3588 .POP, pushAt 3589 2 5157,
   opAt 3590 .JUMP]


@[simp] theorem pc2903 : Artifact.submissionArtifact.instructionPC 3464 = 0x13d6 :=
  by rw [scan_instruction_pc 3464 (by decide) (by decide)]; rfl
@[simp] theorem pc2904 : Artifact.submissionArtifact.instructionPC 3465 = 0x13d7 :=
  by rw [scan_instruction_pc 3465 (by decide) (by decide)]; rfl
@[simp] theorem pc2905 : Artifact.submissionArtifact.instructionPC 3469 = 0x13dc :=
  by rw [scan_instruction_pc 3469 (by decide) (by decide)]; rfl
@[simp] theorem pc2906 : Artifact.submissionArtifact.instructionPC 3474 = 0x1402 :=
  by rw [scan_instruction_pc 3474 (by decide) (by decide)]; rfl
@[simp] theorem pc2907 : Artifact.submissionArtifact.instructionPC 3476 = 0x1404 :=
  by rw [scan_instruction_pc 3476 (by decide) (by decide)]; rfl
@[simp] theorem pc2908 : Artifact.submissionArtifact.instructionPC 3477 = 0x1405 :=
  by rw [scan_instruction_pc 3477 (by decide) (by decide)]; rfl
@[simp] theorem pc2909 : Artifact.submissionArtifact.instructionPC 3478 = 0x1406 :=
  by rw [scan_instruction_pc 3478 (by decide) (by decide)]; rfl
@[simp] theorem pc2910 : Artifact.submissionArtifact.instructionPC 3479 = 0x1407 :=
  by rw [scan_instruction_pc 3479 (by decide) (by decide)]; rfl
@[simp] theorem pc2911 : Artifact.submissionArtifact.instructionPC 3480 = 0x1408 :=
  by rw [scan_instruction_pc 3480 (by decide) (by decide)]; rfl
@[simp] theorem pc2912 : Artifact.submissionArtifact.instructionPC 3481 = 0x1409 :=
  by rw [scan_instruction_pc 3481 (by decide) (by decide)]; rfl
@[simp] theorem pc2913 : Artifact.submissionArtifact.instructionPC 3482 = 0x140a :=
  by rw [scan_instruction_pc 3482 (by decide) (by decide)]; rfl
@[simp] theorem pc2914 : Artifact.submissionArtifact.instructionPC 3483 = 0x140b :=
  by rw [scan_instruction_pc 3483 (by decide) (by decide)]; rfl
@[simp] theorem pc2915 : Artifact.submissionArtifact.instructionPC 3484 = 0x140c :=
  by rw [scan_instruction_pc 3484 (by decide) (by decide)]; rfl
@[simp] theorem pc2916 : Artifact.submissionArtifact.instructionPC 3485 = 0x140d :=
  by rw [scan_instruction_pc 3485 (by decide) (by decide)]; rfl
@[simp] theorem pc2917 : Artifact.submissionArtifact.instructionPC 3486 = 0x140e :=
  by rw [scan_instruction_pc 3486 (by decide) (by decide)]; rfl
@[simp] theorem pc2918 : Artifact.submissionArtifact.instructionPC 3487 = 0x140f :=
  by rw [scan_instruction_pc 3487 (by decide) (by decide)]; rfl
@[simp] theorem pc2919 : Artifact.submissionArtifact.instructionPC 3488 = 0x1410 :=
  by rw [scan_instruction_pc 3488 (by decide) (by decide)]; rfl
@[simp] theorem pc2920 : Artifact.submissionArtifact.instructionPC 3489 = 0x1411 :=
  by rw [scan_instruction_pc 3489 (by decide) (by decide)]; rfl
@[simp] theorem pc2921 : Artifact.submissionArtifact.instructionPC 3490 = 0x1412 :=
  by rw [scan_instruction_pc 3490 (by decide) (by decide)]; rfl
@[simp] theorem pc2922 : Artifact.submissionArtifact.instructionPC 3491 = 0x1413 :=
  by rw [scan_instruction_pc 3491 (by decide) (by decide)]; rfl
@[simp] theorem pc2923 : Artifact.submissionArtifact.instructionPC 3492 = 0x1414 :=
  by rw [scan_instruction_pc 3492 (by decide) (by decide)]; rfl
@[simp] theorem pc2924 : Artifact.submissionArtifact.instructionPC 3493 = 0x1415 :=
  by rw [scan_instruction_pc 3493 (by decide) (by decide)]; rfl
@[simp] theorem pc2925 : Artifact.submissionArtifact.instructionPC 3494 = 0x1416 :=
  by rw [scan_instruction_pc 3494 (by decide) (by decide)]; rfl
@[simp] theorem pc2926 : Artifact.submissionArtifact.instructionPC 3495 = 0x1417 :=
  by rw [scan_instruction_pc 3495 (by decide) (by decide)]; rfl
@[simp] theorem pc2927 : Artifact.submissionArtifact.instructionPC 3496 = 0x1418 :=
  by rw [scan_instruction_pc 3496 (by decide) (by decide)]; rfl
@[simp] theorem pc2928 : Artifact.submissionArtifact.instructionPC 3497 = 0x1419 :=
  by rw [scan_instruction_pc 3497 (by decide) (by decide)]; rfl
@[simp] theorem pc2929 : Artifact.submissionArtifact.instructionPC 3498 = 0x141a :=
  by rw [scan_instruction_pc 3498 (by decide) (by decide)]; rfl
@[simp] theorem pc2930 : Artifact.submissionArtifact.instructionPC 3499 = 0x141b :=
  by rw [scan_instruction_pc 3499 (by decide) (by decide)]; rfl
@[simp] theorem pc2931 : Artifact.submissionArtifact.instructionPC 3500 = 0x141d :=
  by rw [scan_instruction_pc 3500 (by decide) (by decide)]; rfl
@[simp] theorem pc2932 : Artifact.submissionArtifact.instructionPC 3501 = 0x141e :=
  by rw [scan_instruction_pc 3501 (by decide) (by decide)]; rfl
@[simp] theorem pc2933 : Artifact.submissionArtifact.instructionPC 3502 = 0x1420 :=
  by rw [scan_instruction_pc 3502 (by decide) (by decide)]; rfl
@[simp] theorem pc2934 : Artifact.submissionArtifact.instructionPC 3503 = 0x1421 :=
  by rw [scan_instruction_pc 3503 (by decide) (by decide)]; rfl
@[simp] theorem pc2935 : Artifact.submissionArtifact.instructionPC 3504 = 0x1424 :=
  by rw [scan_instruction_pc 3504 (by decide) (by decide)]; rfl
@[simp] theorem pc2936 : Artifact.submissionArtifact.instructionPC 3505 = 0x1425 :=
  by rw [scan_instruction_pc 3505 (by decide) (by decide)]; rfl
@[simp] theorem pc2937 : Artifact.submissionArtifact.instructionPC 3506 = 0x1426 :=
  by rw [scan_instruction_pc 3506 (by decide) (by decide)]; rfl
@[simp] theorem pc2938 : Artifact.submissionArtifact.instructionPC 3507 = 0x1427 :=
  by rw [scan_instruction_pc 3507 (by decide) (by decide)]; rfl
@[simp] theorem pc2939 : Artifact.submissionArtifact.instructionPC 3508 = 0x1428 :=
  by rw [scan_instruction_pc 3508 (by decide) (by decide)]; rfl
@[simp] theorem pc2940 : Artifact.submissionArtifact.instructionPC 3509 = 0x1429 :=
  by rw [scan_instruction_pc 3509 (by decide) (by decide)]; rfl
@[simp] theorem pc2941 : Artifact.submissionArtifact.instructionPC 3510 = 0x142a :=
  by rw [scan_instruction_pc 3510 (by decide) (by decide)]; rfl
@[simp] theorem pc2942 : Artifact.submissionArtifact.instructionPC 3511 = 0x142b :=
  by rw [scan_instruction_pc 3511 (by decide) (by decide)]; rfl
@[simp] theorem pc2943 : Artifact.submissionArtifact.instructionPC 3512 = 0x142c :=
  by rw [scan_instruction_pc 3512 (by decide) (by decide)]; rfl
@[simp] theorem pc2944 : Artifact.submissionArtifact.instructionPC 3513 = 0x142d :=
  by rw [scan_instruction_pc 3513 (by decide) (by decide)]; rfl
@[simp] theorem pc2945 : Artifact.submissionArtifact.instructionPC 3514 = 0x142e :=
  by rw [scan_instruction_pc 3514 (by decide) (by decide)]; rfl
@[simp] theorem pc2946 : Artifact.submissionArtifact.instructionPC 3515 = 0x142f :=
  by rw [scan_instruction_pc 3515 (by decide) (by decide)]; rfl
@[simp] theorem pc2947 : Artifact.submissionArtifact.instructionPC 3516 = 0x1431 :=
  by rw [scan_instruction_pc 3516 (by decide) (by decide)]; rfl
@[simp] theorem pc2948 : Artifact.submissionArtifact.instructionPC 3517 = 0x1432 :=
  by rw [scan_instruction_pc 3517 (by decide) (by decide)]; rfl
@[simp] theorem pc2949 : Artifact.submissionArtifact.instructionPC 3518 = 0x1434 :=
  by rw [scan_instruction_pc 3518 (by decide) (by decide)]; rfl
@[simp] theorem pc2950 : Artifact.submissionArtifact.instructionPC 3519 = 0x1435 :=
  by rw [scan_instruction_pc 3519 (by decide) (by decide)]; rfl
@[simp] theorem pc2951 : Artifact.submissionArtifact.instructionPC 3520 = 0x1436 :=
  by rw [scan_instruction_pc 3520 (by decide) (by decide)]; rfl
@[simp] theorem pc2952 : Artifact.submissionArtifact.instructionPC 3521 = 0x1437 :=
  by rw [scan_instruction_pc 3521 (by decide) (by decide)]; rfl
@[simp] theorem pc2953 : Artifact.submissionArtifact.instructionPC 3522 = 0x1438 :=
  by rw [scan_instruction_pc 3522 (by decide) (by decide)]; rfl
@[simp] theorem pc2954 : Artifact.submissionArtifact.instructionPC 3523 = 0x143a :=
  by rw [scan_instruction_pc 3523 (by decide) (by decide)]; rfl
@[simp] theorem pc2955 : Artifact.submissionArtifact.instructionPC 3524 = 0x143b :=
  by rw [scan_instruction_pc 3524 (by decide) (by decide)]; rfl
@[simp] theorem pc2956 : Artifact.submissionArtifact.instructionPC 3525 = 0x143c :=
  by rw [scan_instruction_pc 3525 (by decide) (by decide)]; rfl
@[simp] theorem pc2957 : Artifact.submissionArtifact.instructionPC 3526 = 0x143d :=
  by rw [scan_instruction_pc 3526 (by decide) (by decide)]; rfl
@[simp] theorem pc2958 : Artifact.submissionArtifact.instructionPC 3527 = 0x143e :=
  by rw [scan_instruction_pc 3527 (by decide) (by decide)]; rfl
@[simp] theorem pc2959 : Artifact.submissionArtifact.instructionPC 3528 = 0x1441 :=
  by rw [scan_instruction_pc 3528 (by decide) (by decide)]; rfl
@[simp] theorem pc2960 : Artifact.submissionArtifact.instructionPC 3529 = 0x1442 :=
  by rw [scan_instruction_pc 3529 (by decide) (by decide)]; rfl
@[simp] theorem pc2961 : Artifact.submissionArtifact.instructionPC 3530 = 0x1445 :=
  by rw [scan_instruction_pc 3530 (by decide) (by decide)]; rfl
@[simp] theorem pc2962 : Artifact.submissionArtifact.instructionPC 3531 = 0x1446 :=
  by rw [scan_instruction_pc 3531 (by decide) (by decide)]; rfl
@[simp] theorem pc2963 : Artifact.submissionArtifact.instructionPC 3532 = 0x1449 :=
  by rw [scan_instruction_pc 3532 (by decide) (by decide)]; rfl
@[simp] theorem pc2964 : Artifact.submissionArtifact.instructionPC 3533 = 0x144a :=
  by rw [scan_instruction_pc 3533 (by decide) (by decide)]; rfl
@[simp] theorem pc2965 : Artifact.submissionArtifact.instructionPC 3534 = 0x1453 :=
  by rw [scan_instruction_pc 3534 (by decide) (by decide)]; rfl
@[simp] theorem pc2966 : Artifact.submissionArtifact.instructionPC 3535 = 0x1455 :=
  by rw [scan_instruction_pc 3535 (by decide) (by decide)]; rfl
@[simp] theorem pc2967 : Artifact.submissionArtifact.instructionPC 3536 = 0x1456 :=
  by rw [scan_instruction_pc 3536 (by decide) (by decide)]; rfl
@[simp] theorem pc2968 : Artifact.submissionArtifact.instructionPC 3537 = 0x1457 :=
  by rw [scan_instruction_pc 3537 (by decide) (by decide)]; rfl
@[simp] theorem pc2969 : Artifact.submissionArtifact.instructionPC 3538 = 0x1458 :=
  by rw [scan_instruction_pc 3538 (by decide) (by decide)]; rfl
@[simp] theorem pc2970 : Artifact.submissionArtifact.instructionPC 3539 = 0x1459 :=
  by rw [scan_instruction_pc 3539 (by decide) (by decide)]; rfl
@[simp] theorem pc2971 : Artifact.submissionArtifact.instructionPC 3540 = 0x145a :=
  by rw [scan_instruction_pc 3540 (by decide) (by decide)]; rfl
@[simp] theorem pc2972 : Artifact.submissionArtifact.instructionPC 3541 = 0x145b :=
  by rw [scan_instruction_pc 3541 (by decide) (by decide)]; rfl
@[simp] theorem pc2973 : Artifact.submissionArtifact.instructionPC 3542 = 0x145c :=
  by rw [scan_instruction_pc 3542 (by decide) (by decide)]; rfl
@[simp] theorem pc2974 : Artifact.submissionArtifact.instructionPC 3543 = 0x145d :=
  by rw [scan_instruction_pc 3543 (by decide) (by decide)]; rfl
@[simp] theorem pc2975 : Artifact.submissionArtifact.instructionPC 3544 = 0x145e :=
  by rw [scan_instruction_pc 3544 (by decide) (by decide)]; rfl
@[simp] theorem pc2976 : Artifact.submissionArtifact.instructionPC 3545 = 0x145f :=
  by rw [scan_instruction_pc 3545 (by decide) (by decide)]; rfl
@[simp] theorem pc2977 : Artifact.submissionArtifact.instructionPC 3546 = 0x1460 :=
  by rw [scan_instruction_pc 3546 (by decide) (by decide)]; rfl
@[simp] theorem pc2978 : Artifact.submissionArtifact.instructionPC 3547 = 0x1461 :=
  by rw [scan_instruction_pc 3547 (by decide) (by decide)]; rfl
@[simp] theorem pc2979 : Artifact.submissionArtifact.instructionPC 3548 = 0x1462 :=
  by rw [scan_instruction_pc 3548 (by decide) (by decide)]; rfl
@[simp] theorem pc2980 : Artifact.submissionArtifact.instructionPC 3549 = 0x1463 :=
  by rw [scan_instruction_pc 3549 (by decide) (by decide)]; rfl
@[simp] theorem pc2981 : Artifact.submissionArtifact.instructionPC 3550 = 0x1464 :=
  by rw [scan_instruction_pc 3550 (by decide) (by decide)]; rfl
@[simp] theorem pc2982 : Artifact.submissionArtifact.instructionPC 3551 = 0x1467 :=
  by rw [scan_instruction_pc 3551 (by decide) (by decide)]; rfl
@[simp] theorem pc2983 : Artifact.submissionArtifact.instructionPC 3552 = 0x1468 :=
  by rw [scan_instruction_pc 3552 (by decide) (by decide)]; rfl
@[simp] theorem pc2984 : Artifact.submissionArtifact.instructionPC 3553 = 0x147d :=
  by rw [scan_instruction_pc 3553 (by decide) (by decide)]; rfl
@[simp] theorem pc2985 : Artifact.submissionArtifact.instructionPC 3554 = 0x147e :=
  by rw [scan_instruction_pc 3554 (by decide) (by decide)]; rfl
@[simp] theorem pc2986 : Artifact.submissionArtifact.instructionPC 3555 = 0x147f :=
  by rw [scan_instruction_pc 3555 (by decide) (by decide)]; rfl
@[simp] theorem pc2987 : Artifact.submissionArtifact.instructionPC 3556 = 0x1481 :=
  by rw [scan_instruction_pc 3556 (by decide) (by decide)]; rfl
@[simp] theorem pc2988 : Artifact.submissionArtifact.instructionPC 3557 = 0x1482 :=
  by rw [scan_instruction_pc 3557 (by decide) (by decide)]; rfl
@[simp] theorem pc2989 : Artifact.submissionArtifact.instructionPC 3558 = 0x1483 :=
  by rw [scan_instruction_pc 3558 (by decide) (by decide)]; rfl
@[simp] theorem pc2990 : Artifact.submissionArtifact.instructionPC 3559 = 0x1484 :=
  by rw [scan_instruction_pc 3559 (by decide) (by decide)]; rfl
@[simp] theorem pc2991 : Artifact.submissionArtifact.instructionPC 3560 = 0x1485 :=
  by rw [scan_instruction_pc 3560 (by decide) (by decide)]; rfl
@[simp] theorem pc2992 : Artifact.submissionArtifact.instructionPC 3561 = 0x1486 :=
  by rw [scan_instruction_pc 3561 (by decide) (by decide)]; rfl
@[simp] theorem pc2993 : Artifact.submissionArtifact.instructionPC 3562 = 0x1488 :=
  by rw [scan_instruction_pc 3562 (by decide) (by decide)]; rfl
@[simp] theorem pc2994 : Artifact.submissionArtifact.instructionPC 3563 = 0x1489 :=
  by rw [scan_instruction_pc 3563 (by decide) (by decide)]; rfl
@[simp] theorem pc2995 : Artifact.submissionArtifact.instructionPC 3564 = 0x148b :=
  by rw [scan_instruction_pc 3564 (by decide) (by decide)]; rfl
@[simp] theorem pc2996 : Artifact.submissionArtifact.instructionPC 3565 = 0x148c :=
  by rw [scan_instruction_pc 3565 (by decide) (by decide)]; rfl
@[simp] theorem pc2997 : Artifact.submissionArtifact.instructionPC 3566 = 0x148e :=
  by rw [scan_instruction_pc 3566 (by decide) (by decide)]; rfl
@[simp] theorem pc2998 : Artifact.submissionArtifact.instructionPC 3567 = 0x148f :=
  by rw [scan_instruction_pc 3567 (by decide) (by decide)]; rfl
@[simp] theorem pc2999 : Artifact.submissionArtifact.instructionPC 3568 = 0x1491 :=
  by rw [scan_instruction_pc 3568 (by decide) (by decide)]; rfl
@[simp] theorem pc3000 : Artifact.submissionArtifact.instructionPC 3569 = 0x1492 :=
  by rw [scan_instruction_pc 3569 (by decide) (by decide)]; rfl
@[simp] theorem pc3001 : Artifact.submissionArtifact.instructionPC 3570 = 0x1493 :=
  by rw [scan_instruction_pc 3570 (by decide) (by decide)]; rfl
@[simp] theorem pc3002 : Artifact.submissionArtifact.instructionPC 3571 = 0x1495 :=
  by rw [scan_instruction_pc 3571 (by decide) (by decide)]; rfl
@[simp] theorem pc3003 : Artifact.submissionArtifact.instructionPC 3572 = 0x1496 :=
  by rw [scan_instruction_pc 3572 (by decide) (by decide)]; rfl
@[simp] theorem pc3004 : Artifact.submissionArtifact.instructionPC 3573 = 0x1497 :=
  by rw [scan_instruction_pc 3573 (by decide) (by decide)]; rfl
@[simp] theorem pc3005 : Artifact.submissionArtifact.instructionPC 3574 = 0x1498 :=
  by rw [scan_instruction_pc 3574 (by decide) (by decide)]; rfl
@[simp] theorem pc3006 : Artifact.submissionArtifact.instructionPC 3575 = 0x1499 :=
  by rw [scan_instruction_pc 3575 (by decide) (by decide)]; rfl
@[simp] theorem pc3007 : Artifact.submissionArtifact.instructionPC 3576 = 0x149a :=
  by rw [scan_instruction_pc 3576 (by decide) (by decide)]; rfl
@[simp] theorem pc3008 : Artifact.submissionArtifact.instructionPC 3577 = 0x149b :=
  by rw [scan_instruction_pc 3577 (by decide) (by decide)]; rfl
@[simp] theorem pc3009 : Artifact.submissionArtifact.instructionPC 3578 = 0x149c :=
  by rw [scan_instruction_pc 3578 (by decide) (by decide)]; rfl
@[simp] theorem pc3010 : Artifact.submissionArtifact.instructionPC 3579 = 0x149d :=
  by rw [scan_instruction_pc 3579 (by decide) (by decide)]; rfl
@[simp] theorem pc3011 : Artifact.submissionArtifact.instructionPC 3580 = 0x149e :=
  by rw [scan_instruction_pc 3580 (by decide) (by decide)]; rfl
@[simp] theorem pc3012 : Artifact.submissionArtifact.instructionPC 3581 = 0x149f :=
  by rw [scan_instruction_pc 3581 (by decide) (by decide)]; rfl
@[simp] theorem pc3013 : Artifact.submissionArtifact.instructionPC 3582 = 0x14a0 :=
  by rw [scan_instruction_pc 3582 (by decide) (by decide)]; rfl
@[simp] theorem pc3014 : Artifact.submissionArtifact.instructionPC 3583 = 0x14a1 :=
  by rw [scan_instruction_pc 3583 (by decide) (by decide)]; rfl
@[simp] theorem pc3015 : Artifact.submissionArtifact.instructionPC 3584 = 0x14a2 :=
  by rw [scan_instruction_pc 3584 (by decide) (by decide)]; rfl
@[simp] theorem pc3016 : Artifact.submissionArtifact.instructionPC 3585 = 0x14a3 :=
  by rw [scan_instruction_pc 3585 (by decide) (by decide)]; rfl
@[simp] theorem pc3017 : Artifact.submissionArtifact.instructionPC 3586 = 0x14a5 :=
  by rw [scan_instruction_pc 3586 (by decide) (by decide)]; rfl
@[simp] theorem pc3018 : Artifact.submissionArtifact.instructionPC 3587 = 0x14a6 :=
  by rw [scan_instruction_pc 3587 (by decide) (by decide)]; rfl
@[simp] theorem pc3019 : Artifact.submissionArtifact.instructionPC 3588 = 0x14a7 :=
  by rw [scan_instruction_pc 3588 (by decide) (by decide)]; rfl
@[simp] theorem pc3020 : Artifact.submissionArtifact.instructionPC 3589 = 0x14a8 :=
  by rw [scan_instruction_pc 3589 (by decide) (by decide)]; rfl
@[simp] theorem pc3021 : Artifact.submissionArtifact.instructionPC 3590 = 0x14ab :=
  by rw [scan_instruction_pc 3590 (by decide) (by decide)]; rfl
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
