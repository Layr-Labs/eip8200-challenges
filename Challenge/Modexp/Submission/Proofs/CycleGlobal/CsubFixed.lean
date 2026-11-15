import Challenge.Modexp.Submission.Proofs.CycleGlobal.PCCertificate
import Challenge.Modexp.Submission.Proofs.Prepared.StackArgs
import Challenge.Modexp.Submission.Proofs.CycleGlobal.PrefixPC
import Challenge.Modexp.Submission.Proofs.CycleGlobal.Binding
import Challenge.Modexp.Submission.Proofs.Bytecode.PCFast
import Challenge.Modexp.Submission.Proofs.CycleGlobal.FastDefs
open CycleSubmission.SharedStackArgs
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
namespace CycleSubmission.Global.Fast
private abbrev runtimeArtifact := CycleSubmission.Artifact.artifact
open Challenge.Modexp
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode
open YulEvmCompiler
private theorem instructionPC_succ
    (p : Challenge.EvmProof.ProgramArtifact) (index : Nat) (instr : Instr)
    (hget : p.instructions[index]? = some instr) :
    p.instructionPC (index + 1) =
      p.instructionPC index + instr.bytes.length := by
  simp only [Challenge.EvmProof.ProgramArtifact.instructionPC,
    List.take_add_one,hget,Option.toList_some,assembleBytes_append,
    assembleBytes_cons,assembleBytes_nil,List.append_nil,List.length_append]
def csFixedEntry8 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 478 2 2688,
   opAt 479 .MLOAD,
   pushAt 480 1 128,
   opAt 481 .EQ,
   pushAt 482 2 10508,
   opAt 483 .JUMPI]
def csFixedEntry4 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 478 2 2688,
   opAt 479 .MLOAD,
   pushAt 480 1 128,
   opAt 481 .EQ,
   pushAt 482 2 10508,
   opAt 483 .JUMPI,
   opAt 7945 .JUMPDEST]
/-- rarej: the eight-limb subtraction starts at the `s8` `JUMPDEST` (pc 4362), the target of the
square exit's carry continuation; the entry block falls into it. -/
def csFixedStep8_0 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 484 2 2336,
   opAt 485 .MLOAD,
   pushAt 486 1 224,
   opAt 487 .MLOAD,
   opAt 488 (.Dup ⟨0,by decide⟩),
   opAt 489 (.Dup ⟨2,by decide⟩),
   opAt 490 .SUB,
   pushAt 491 2 2016,
   opAt 492 .MSTORE,
   opAt 493 .GT]
def csFixedStep8_1 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 494 (.Dup ⟨0,by decide⟩),
   pushAt 495 1 192,
   opAt 496 .MLOAD,
   opAt 497 .ADD,
   opAt 498 (.Dup ⟨0,by decide⟩),
   pushAt 499 2 2304,
   opAt 500 .MLOAD,
   opAt 501 (.Dup ⟨1,by decide⟩),
   opAt 502 (.Dup ⟨1,by decide⟩),
   opAt 503 .SUB,
   pushAt 504 2 1984,
   opAt 505 .MSTORE,
   opAt 506 .LT,
   opAt 507 (.Swap ⟨1,by decide⟩),
   opAt 508 .GT,
   opAt 509 .OR]
def csFixedStep8_2 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 510 (.Dup ⟨0,by decide⟩),
   pushAt 511 1 160,
   opAt 512 .MLOAD,
   opAt 513 .ADD,
   opAt 514 (.Dup ⟨0,by decide⟩),
   pushAt 515 2 2272,
   opAt 516 .MLOAD,
   opAt 517 (.Dup ⟨1,by decide⟩),
   opAt 518 (.Dup ⟨1,by decide⟩),
   opAt 519 .SUB,
   pushAt 520 2 1952,
   opAt 521 .MSTORE,
   opAt 522 .LT,
   opAt 523 (.Swap ⟨1,by decide⟩),
   opAt 524 .GT,
   opAt 525 .OR]
def csFixedStep8_3 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 526 (.Dup ⟨0,by decide⟩),
   pushAt 527 1 128,
   opAt 528 .MLOAD,
   opAt 529 .ADD,
   opAt 530 (.Dup ⟨0,by decide⟩),
   pushAt 531 2 2240,
   opAt 532 .MLOAD,
   opAt 533 (.Dup ⟨1,by decide⟩),
   opAt 534 (.Dup ⟨1,by decide⟩),
   opAt 535 .SUB,
   pushAt 536 2 1920,
   opAt 537 .MSTORE,
   opAt 538 .LT,
   opAt 539 (.Swap ⟨1,by decide⟩),
   opAt 540 .GT,
   opAt 541 .OR]
def csFixedStep8_4 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 542 (.Dup ⟨0,by decide⟩),
   pushAt 543 1 96,
   opAt 544 .MLOAD,
   opAt 545 .ADD,
   opAt 546 (.Dup ⟨0,by decide⟩),
   pushAt 547 2 2208,
   opAt 548 .MLOAD,
   opAt 549 (.Dup ⟨1,by decide⟩),
   opAt 550 (.Dup ⟨1,by decide⟩),
   opAt 551 .SUB,
   pushAt 552 2 1888,
   opAt 553 .MSTORE,
   opAt 554 .LT,
   opAt 555 (.Swap ⟨1,by decide⟩),
   opAt 556 .GT,
   opAt 557 .OR]
def csFixedStep8_5 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 558 .JUMPDEST,
   opAt 559 (.Dup ⟨0,by decide⟩),
   pushAt 560 1 64,
   opAt 561 .MLOAD,
   opAt 562 .ADD,
   opAt 563 (.Dup ⟨0,by decide⟩),
   pushAt 564 2 2176,
   opAt 565 .MLOAD,
   opAt 566 (.Dup ⟨1,by decide⟩),
   opAt 567 (.Dup ⟨1,by decide⟩),
   opAt 568 .SUB,
   pushAt 569 2 1856,
   opAt 570 .MSTORE,
   opAt 571 .LT,
   opAt 572 (.Swap ⟨1,by decide⟩),
   opAt 573 .GT,
   opAt 574 .OR]
def csFixedStep8_6 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 575 (.Dup ⟨0,by decide⟩),
   pushAt 576 1 32,
   opAt 577 .MLOAD,
   opAt 578 .ADD,
   opAt 579 (.Dup ⟨0,by decide⟩),
   pushAt 580 2 2144,
   opAt 581 .MLOAD,
   opAt 582 (.Dup ⟨1,by decide⟩),
   opAt 583 (.Dup ⟨1,by decide⟩),
   opAt 584 .SUB,
   pushAt 585 2 1824,
   opAt 586 .MSTORE,
   opAt 587 .LT,
   opAt 588 (.Swap ⟨1,by decide⟩),
   opAt 589 .GT,
   opAt 590 .OR]
def csFixedStep8_7 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 591 (.Dup ⟨0,by decide⟩),
   pushAt 592 0 0,
   opAt 593 .MLOAD,
   opAt 594 .ADD,
   opAt 595 (.Dup ⟨0,by decide⟩),
   pushAt 596 2 2112,
   opAt 597 .MLOAD,
   opAt 598 (.Dup ⟨1,by decide⟩),
   opAt 599 (.Dup ⟨1,by decide⟩),
   opAt 600 .SUB,
   pushAt 601 2 1792,
   opAt 602 .MSTORE,
   opAt 603 .LT,
   opAt 604 (.Swap ⟨1,by decide⟩),
   opAt 605 .GT,
   opAt 606 .OR]
/-- Selection tail when `use ≠ 0` (`t ≥ m`): `JUMPI` to pc 4526, which copies the
difference block at `SUBB` (1792) to the destination and returns. -/
def csFixedTailSub : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 607 .ISZERO,
   pushAt 608 2 2080,
   opAt 609 .MLOAD,
   opAt 610 .OR,
   pushAt 611 2 883,
   opAt 612 .JUMPI,
   opAt 622 .JUMPDEST,
   pushAt 623 2 1792,
   pushAt 624 2 2688,
   opAt 625 .MLOAD,
   opAt 626 (.Swap ⟨1,by decide⟩),
   opAt 627 .MCOPY,
   opAt 628 .JUMP]
/-- Selection tail when `use = 0` (`t < m`): fall through the `JUMPI` and jump to the
shared copy block at pc 4515, which copies `t` (2112) to the destination and returns. -/
def csFixedTailKeep : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 607 .ISZERO,
   pushAt 608 2 2080,
   opAt 609 .MLOAD,
   opAt 610 .OR,
   pushAt 611 2 883,
   opAt 612 .JUMPI,
   pushAt 613 2 872,
   opAt 614 .JUMP,
   opAt 615 .JUMPDEST,
   pushAt 616 2 2112,
   pushAt 617 2 2688,
   opAt 618 .MLOAD,
   opAt 619 (.Swap ⟨1,by decide⟩),
   opAt 620 .MCOPY,
   opAt 621 .JUMP]
def csFixedStep4_0 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 7946 2 2208,
   opAt 7947 .MLOAD,
   pushAt 7948 1 96,
   opAt 7949 .MLOAD,
   opAt 7950 (.Dup ⟨0,by decide⟩),
   opAt 7951 (.Dup ⟨2,by decide⟩),
   opAt 7952 .SUB,
   pushAt 7953 2 1888,
   opAt 7954 .MSTORE,
   opAt 7955 .GT,
   pushAt 7956 2 795,
   opAt 7957 .JUMP]
def csFixedStep4_1 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 558 .JUMPDEST,
   opAt 559 (.Dup ⟨0,by decide⟩),
   pushAt 560 1 64,
   opAt 561 .MLOAD,
   opAt 562 .ADD,
   opAt 563 (.Dup ⟨0,by decide⟩),
   pushAt 564 2 2176,
   opAt 565 .MLOAD,
   opAt 566 (.Dup ⟨1,by decide⟩),
   opAt 567 (.Dup ⟨1,by decide⟩),
   opAt 568 .SUB,
   pushAt 569 2 1856,
   opAt 570 .MSTORE,
   opAt 571 .LT,
   opAt 572 (.Swap ⟨1,by decide⟩),
   opAt 573 .GT,
   opAt 574 .OR]
def csFixedStep4_2 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 575 (.Dup ⟨0,by decide⟩),
   pushAt 576 1 32,
   opAt 577 .MLOAD,
   opAt 578 .ADD,
   opAt 579 (.Dup ⟨0,by decide⟩),
   pushAt 580 2 2144,
   opAt 581 .MLOAD,
   opAt 582 (.Dup ⟨1,by decide⟩),
   opAt 583 (.Dup ⟨1,by decide⟩),
   opAt 584 .SUB,
   pushAt 585 2 1824,
   opAt 586 .MSTORE,
   opAt 587 .LT,
   opAt 588 (.Swap ⟨1,by decide⟩),
   opAt 589 .GT,
   opAt 590 .OR]
def csFixedStep4_3 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 591 (.Dup ⟨0,by decide⟩),
   pushAt 592 0 0,
   opAt 593 .MLOAD,
   opAt 594 .ADD,
   opAt 595 (.Dup ⟨0,by decide⟩),
   pushAt 596 2 2112,
   opAt 597 .MLOAD,
   opAt 598 (.Dup ⟨1,by decide⟩),
   opAt 599 (.Dup ⟨1,by decide⟩),
   opAt 600 .SUB,
   pushAt 601 2 1792,
   opAt 602 .MSTORE,
   opAt 603 .LT,
   opAt 604 (.Swap ⟨1,by decide⟩),
   opAt 605 .GT,
   opAt 606 .OR]
@[simp] theorem cycleAnchor : runtimeArtifact.instructionPC 7779 = 10290 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3777 : runtimeArtifact.instructionPC 473 = 674 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3778 : runtimeArtifact.instructionPC 613 = 868 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3779 : runtimeArtifact.instructionPC 614 = 871 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3787 : runtimeArtifact.instructionPC 615 = 872 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3788 : runtimeArtifact.instructionPC 615 = 872 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3789 : runtimeArtifact.instructionPC 615 = 872 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3790 : runtimeArtifact.instructionPC 615 = 872 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3791 : runtimeArtifact.instructionPC 615 = 872 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3792 : runtimeArtifact.instructionPC 615 = 872 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3793 : runtimeArtifact.instructionPC 616 = 873 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3794 : runtimeArtifact.instructionPC 617 = 876 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3795 : runtimeArtifact.instructionPC 618 = 879 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3796 : runtimeArtifact.instructionPC 619 = 880 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3797 : runtimeArtifact.instructionPC 620 = 881 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3798 : runtimeArtifact.instructionPC 620 = 881 := fixedPC3797
@[simp] theorem fixedPC3799 : runtimeArtifact.instructionPC 620 = 881 := fixedPC3797
@[simp] theorem fixedPC3800 : runtimeArtifact.instructionPC 621 = 882 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3801 : runtimeArtifact.instructionPC 622 = 883 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3802 : runtimeArtifact.instructionPC 623 = 884 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3803 : runtimeArtifact.instructionPC 624 = 887 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3804 : runtimeArtifact.instructionPC 625 = 890 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
/-! The rewritten conditional-subtraction dispatch occupies rows 3113..3119; its interior rows had
no pc certificates, so the block could not step. -/
@[simp] theorem fixedPC3114 : runtimeArtifact.instructionPC 474 = 675 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3115 : runtimeArtifact.instructionPC 475 = 678 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3116 : runtimeArtifact.instructionPC 476 = 679 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3117 : runtimeArtifact.instructionPC 477 = 682 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3118 : runtimeArtifact.instructionPC 478 = 685 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3119 : runtimeArtifact.instructionPC 479 = 688 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
/-- The four-limb landing of the rewritten conditional-subtraction dispatch. The old claim here named
pc 4359 through index 3261, which is now an `MCOPY` at 4380, so it was false and cost a `whnf` runaway
rather than an honest error. -/
@[simp] theorem fixedPC3009 : runtimeArtifact.instructionPC 7785 = 10299 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedJump3984 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10508 = true := by
  have h : runtimeArtifact.instructionPC 7945 = 10508 := by
    rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
    rfl
  simpa only [h] using CycleSubmission.Global.Binding.jumpDest 7945 (by rfl)
@[simp] theorem fixedPC3805 : runtimeArtifact.instructionPC 480 = 689 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3806 : runtimeArtifact.instructionPC 481 = 691 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3807 : runtimeArtifact.instructionPC 482 = 692 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3808 : runtimeArtifact.instructionPC 483 = 695 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPCs8 : runtimeArtifact.instructionPC 484 = 696 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3809 : runtimeArtifact.instructionPC 484 = 696 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3810 : runtimeArtifact.instructionPC 485 = 699 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3811 : runtimeArtifact.instructionPC 486 = 700 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3812 : runtimeArtifact.instructionPC 487 = 702 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3813 : runtimeArtifact.instructionPC 488 = 703 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3814 : runtimeArtifact.instructionPC 489 = 704 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3815 : runtimeArtifact.instructionPC 490 = 705 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3816 : runtimeArtifact.instructionPC 490 = 705 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3817 : runtimeArtifact.instructionPC 491 = 706 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3818 : runtimeArtifact.instructionPC 492 = 709 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3819 : runtimeArtifact.instructionPC 493 = 710 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3820 : runtimeArtifact.instructionPC 494 = 711 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3821 : runtimeArtifact.instructionPC 495 = 712 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3822 : runtimeArtifact.instructionPC 496 = 714 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3823 : runtimeArtifact.instructionPC 497 = 715 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3824 : runtimeArtifact.instructionPC 498 = 716 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3825 : runtimeArtifact.instructionPC 499 = 717 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3826 : runtimeArtifact.instructionPC 500 = 720 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3827 : runtimeArtifact.instructionPC 501 = 721 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3828 : runtimeArtifact.instructionPC 502 = 722 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3829 : runtimeArtifact.instructionPC 503 = 723 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3830 : runtimeArtifact.instructionPC 504 = 724 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3831 : runtimeArtifact.instructionPC 505 = 727 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3832 : runtimeArtifact.instructionPC 506 = 728 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3833 : runtimeArtifact.instructionPC 507 = 729 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3834 : runtimeArtifact.instructionPC 507 = 729 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3835 : runtimeArtifact.instructionPC 508 = 730 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3836 : runtimeArtifact.instructionPC 509 = 731 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3837 : runtimeArtifact.instructionPC 510 = 732 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3838 : runtimeArtifact.instructionPC 511 = 733 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3839 : runtimeArtifact.instructionPC 512 = 735 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3840 : runtimeArtifact.instructionPC 513 = 736 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3841 : runtimeArtifact.instructionPC 514 = 737 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3842 : runtimeArtifact.instructionPC 515 = 738 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3843 : runtimeArtifact.instructionPC 516 = 741 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3844 : runtimeArtifact.instructionPC 517 = 742 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3845 : runtimeArtifact.instructionPC 518 = 743 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3846 : runtimeArtifact.instructionPC 519 = 744 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3847 : runtimeArtifact.instructionPC 520 = 745 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3848 : runtimeArtifact.instructionPC 521 = 748 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3849 : runtimeArtifact.instructionPC 522 = 749 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3850 : runtimeArtifact.instructionPC 523 = 750 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3851 : runtimeArtifact.instructionPC 524 = 751 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3852 : runtimeArtifact.instructionPC 524 = 751 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3853 : runtimeArtifact.instructionPC 525 = 752 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3854 : runtimeArtifact.instructionPC 526 = 753 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3855 : runtimeArtifact.instructionPC 527 = 754 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3856 : runtimeArtifact.instructionPC 528 = 756 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3857 : runtimeArtifact.instructionPC 529 = 757 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3858 : runtimeArtifact.instructionPC 530 = 758 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3859 : runtimeArtifact.instructionPC 531 = 759 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3860 : runtimeArtifact.instructionPC 532 = 762 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3861 : runtimeArtifact.instructionPC 533 = 763 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3862 : runtimeArtifact.instructionPC 534 = 764 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3863 : runtimeArtifact.instructionPC 535 = 765 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3864 : runtimeArtifact.instructionPC 536 = 766 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3865 : runtimeArtifact.instructionPC 537 = 769 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3866 : runtimeArtifact.instructionPC 538 = 770 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3867 : runtimeArtifact.instructionPC 539 = 771 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3868 : runtimeArtifact.instructionPC 540 = 772 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3869 : runtimeArtifact.instructionPC 541 = 773 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3871 : runtimeArtifact.instructionPC 541 = 773 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3872 : runtimeArtifact.instructionPC 542 = 774 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3873 : runtimeArtifact.instructionPC 543 = 775 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3874 : runtimeArtifact.instructionPC 544 = 777 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3875 : runtimeArtifact.instructionPC 545 = 778 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3876 : runtimeArtifact.instructionPC 546 = 779 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3877 : runtimeArtifact.instructionPC 547 = 780 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3878 : runtimeArtifact.instructionPC 548 = 783 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3879 : runtimeArtifact.instructionPC 549 = 784 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3880 : runtimeArtifact.instructionPC 550 = 785 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3881 : runtimeArtifact.instructionPC 551 = 786 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3882 : runtimeArtifact.instructionPC 552 = 787 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3883 : runtimeArtifact.instructionPC 553 = 790 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3884 : runtimeArtifact.instructionPC 554 = 791 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3885 : runtimeArtifact.instructionPC 555 = 792 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3886 : runtimeArtifact.instructionPC 556 = 793 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3887 : runtimeArtifact.instructionPC 557 = 794 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3888 : runtimeArtifact.instructionPC 558 = 795 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3889 : runtimeArtifact.instructionPC 558 = 795 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedJump5133 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 795 = true := by
  have h : runtimeArtifact.instructionPC 558 = 795 := by
    rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
    rfl
  simpa only [h] using CycleSubmission.Global.Binding.jumpDest 558 (by rfl)
@[simp] theorem fixedPC3890 : runtimeArtifact.instructionPC 559 = 796 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3891 : runtimeArtifact.instructionPC 560 = 797 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3892 : runtimeArtifact.instructionPC 561 = 799 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3893 : runtimeArtifact.instructionPC 562 = 800 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3894 : runtimeArtifact.instructionPC 563 = 801 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3895 : runtimeArtifact.instructionPC 564 = 802 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3896 : runtimeArtifact.instructionPC 565 = 805 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3897 : runtimeArtifact.instructionPC 566 = 806 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3898 : runtimeArtifact.instructionPC 567 = 807 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3899 : runtimeArtifact.instructionPC 568 = 808 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3900 : runtimeArtifact.instructionPC 569 = 809 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3901 : runtimeArtifact.instructionPC 570 = 812 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3902 : runtimeArtifact.instructionPC 571 = 813 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3903 : runtimeArtifact.instructionPC 572 = 814 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3904 : runtimeArtifact.instructionPC 573 = 815 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3905 : runtimeArtifact.instructionPC 574 = 816 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3906 : runtimeArtifact.instructionPC 575 = 817 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3907 : runtimeArtifact.instructionPC 576 = 818 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3908 : runtimeArtifact.instructionPC 576 = 818 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3909 : runtimeArtifact.instructionPC 577 = 820 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3910 : runtimeArtifact.instructionPC 578 = 821 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3911 : runtimeArtifact.instructionPC 579 = 822 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3912 : runtimeArtifact.instructionPC 580 = 823 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3913 : runtimeArtifact.instructionPC 581 = 826 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3914 : runtimeArtifact.instructionPC 582 = 827 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3915 : runtimeArtifact.instructionPC 583 = 828 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3916 : runtimeArtifact.instructionPC 584 = 829 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3917 : runtimeArtifact.instructionPC 585 = 830 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3918 : runtimeArtifact.instructionPC 586 = 833 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3919 : runtimeArtifact.instructionPC 587 = 834 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3920 : runtimeArtifact.instructionPC 588 = 835 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3921 : runtimeArtifact.instructionPC 589 = 836 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3922 : runtimeArtifact.instructionPC 590 = 837 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3923 : runtimeArtifact.instructionPC 591 = 838 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3924 : runtimeArtifact.instructionPC 592 = 839 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3925 : runtimeArtifact.instructionPC 593 = 840 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3926 : runtimeArtifact.instructionPC 593 = 840 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3927 : runtimeArtifact.instructionPC 594 = 841 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3928 : runtimeArtifact.instructionPC 595 = 842 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3929 : runtimeArtifact.instructionPC 596 = 843 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3930 : runtimeArtifact.instructionPC 597 = 846 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3931 : runtimeArtifact.instructionPC 598 = 847 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3932 : runtimeArtifact.instructionPC 599 = 848 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3933 : runtimeArtifact.instructionPC 600 = 849 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3934 : runtimeArtifact.instructionPC 601 = 850 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3935 : runtimeArtifact.instructionPC 602 = 853 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3936 : runtimeArtifact.instructionPC 603 = 854 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3937 : runtimeArtifact.instructionPC 604 = 855 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3938 : runtimeArtifact.instructionPC 605 = 856 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3939 : runtimeArtifact.instructionPC 606 = 857 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3940 : runtimeArtifact.instructionPC 607 = 858 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3941 : runtimeArtifact.instructionPC 608 = 859 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3942 : runtimeArtifact.instructionPC 609 = 862 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3943 : runtimeArtifact.instructionPC 610 = 863 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3944 : runtimeArtifact.instructionPC 610 = 863 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3945 : runtimeArtifact.instructionPC 611 = 864 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3946 : runtimeArtifact.instructionPC 612 = 867 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3947 : runtimeArtifact.instructionPC 613 = 868 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3948 : runtimeArtifact.instructionPC 614 = 871 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3949 : runtimeArtifact.instructionPC 619 = 880 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3950 : runtimeArtifact.instructionPC 619 = 880 :=
  fixedPC3949
@[simp] theorem fixedPC3951 : runtimeArtifact.instructionPC 620 = 881 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3952 : runtimeArtifact.instructionPC 621 = 882 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3953 : runtimeArtifact.instructionPC 622 = 883 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3954 : runtimeArtifact.instructionPC 623 = 884 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3955 : runtimeArtifact.instructionPC 624 = 887 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3956 : runtimeArtifact.instructionPC 625 = 890 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3957 : runtimeArtifact.instructionPC 626 = 891 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedJump5280 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10508 = true := by
  have h : runtimeArtifact.instructionPC 7945 = 10508 := by
    rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
    rfl
  simpa only [h] using CycleSubmission.Global.Binding.jumpDest 7945 (by rfl)
@[simp] theorem fixedPC4000 : runtimeArtifact.instructionPC 7785 = 10299 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC4001 : runtimeArtifact.instructionPC 7785 = 10299 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC4002 : runtimeArtifact.instructionPC 7804 = 10322 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC4003 : runtimeArtifact.instructionPC 7945 = 10508 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC4004 : runtimeArtifact.instructionPC 7946 = 10509 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC4005 : runtimeArtifact.instructionPC 7947 = 10512 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC4006 : runtimeArtifact.instructionPC 7948 = 10513 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC4007 : runtimeArtifact.instructionPC 7949 = 10515 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC4008 : runtimeArtifact.instructionPC 7950 = 10516 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC4009 : runtimeArtifact.instructionPC 7951 = 10517 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC4010 : runtimeArtifact.instructionPC 7952 = 10518 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC4011 : runtimeArtifact.instructionPC 7953 = 10519 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC4012 : runtimeArtifact.instructionPC 7954 = 10522 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2883 : runtimeArtifact.instructionPC 7297 = 9712 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2884 : runtimeArtifact.instructionPC 7298 = 9713 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2885 : runtimeArtifact.instructionPC 7299 = 9714 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2886 : runtimeArtifact.instructionPC 7300 = 9715 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2888 : runtimeArtifact.instructionPC 7301 = 9716 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2889 : runtimeArtifact.instructionPC 7302 = 9717 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2890 : runtimeArtifact.instructionPC 7303 = 9718 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2891 : runtimeArtifact.instructionPC 7304 = 9721 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2892 : runtimeArtifact.instructionPC 7305 = 9722 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2893 : runtimeArtifact.instructionPC 7305 = 9722 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2894 : runtimeArtifact.instructionPC 7305 = 9722 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2895 : runtimeArtifact.instructionPC 7773 = 10280 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2896 : runtimeArtifact.instructionPC 7785 = 10299 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2930 : runtimeArtifact.instructionPC 7785 = 10299 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2931 : runtimeArtifact.instructionPC 7785 = 10299 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2932 : runtimeArtifact.instructionPC 7785 = 10299 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2933 : runtimeArtifact.instructionPC 7804 = 10322 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2934 : runtimeArtifact.instructionPC 7945 = 10508 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2935 : runtimeArtifact.instructionPC 7946 = 10509 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2936 : runtimeArtifact.instructionPC 7947 = 10512 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2937 : runtimeArtifact.instructionPC 7948 = 10513 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2938 : runtimeArtifact.instructionPC 7949 = 10515 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2939 : runtimeArtifact.instructionPC 7950 = 10516 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2940 : runtimeArtifact.instructionPC 7951 = 10517 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2941 : runtimeArtifact.instructionPC 7952 = 10518 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2942 : runtimeArtifact.instructionPC 7953 = 10519 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2943 : runtimeArtifact.instructionPC 7954 = 10522 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC3921 : runtimeArtifact.instructionPC 615 = 872 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC3922 : runtimeArtifact.instructionPC 615 = 872 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC3923 : runtimeArtifact.instructionPC 615 = 872 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC3924 : runtimeArtifact.instructionPC 615 = 872 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC3925 : runtimeArtifact.instructionPC 615 = 872 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC3926 : runtimeArtifact.instructionPC 616 = 873 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC3927 : runtimeArtifact.instructionPC 617 = 876 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC3928 : runtimeArtifact.instructionPC 618 = 879 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
end CycleSubmission.Global.Fast
