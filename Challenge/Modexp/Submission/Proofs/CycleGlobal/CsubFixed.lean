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
  [pushAt 481 2 2688,
   opAt 482 .MLOAD,
   pushAt 483 1 128,
   opAt 484 .EQ,
   pushAt 485 2 10508,
   opAt 486 .JUMPI]
def csFixedEntry4 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 481 2 2688,
   opAt 482 .MLOAD,
   pushAt 483 1 128,
   opAt 484 .EQ,
   pushAt 485 2 10508,
   opAt 486 .JUMPI,
   opAt 7946 .JUMPDEST]
/-- rarej: the eight-limb subtraction starts at the `s8` `JUMPDEST` (pc 4362), the target of the
square exit's carry continuation; the entry block falls into it. -/
def csFixedStep8_0 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 487 2 2336,
   opAt 488 .MLOAD,
   pushAt 489 1 224,
   opAt 490 .MLOAD,
   opAt 491 (.Dup ⟨0,by decide⟩),
   opAt 492 (.Dup ⟨2,by decide⟩),
   opAt 493 .SUB,
   pushAt 494 2 2016,
   opAt 495 .MSTORE,
   opAt 496 .GT]
def csFixedStep8_1 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 497 (.Dup ⟨0,by decide⟩),
   pushAt 498 1 192,
   opAt 499 .MLOAD,
   opAt 500 .ADD,
   opAt 501 (.Dup ⟨0,by decide⟩),
   pushAt 502 2 2304,
   opAt 503 .MLOAD,
   opAt 504 (.Dup ⟨1,by decide⟩),
   opAt 505 (.Dup ⟨1,by decide⟩),
   opAt 506 .SUB,
   pushAt 507 2 1984,
   opAt 508 .MSTORE,
   opAt 509 .LT,
   opAt 510 (.Swap ⟨1,by decide⟩),
   opAt 511 .GT,
   opAt 512 .OR]
def csFixedStep8_2 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 513 (.Dup ⟨0,by decide⟩),
   pushAt 514 1 160,
   opAt 515 .MLOAD,
   opAt 516 .ADD,
   opAt 517 (.Dup ⟨0,by decide⟩),
   pushAt 518 2 2272,
   opAt 519 .MLOAD,
   opAt 520 (.Dup ⟨1,by decide⟩),
   opAt 521 (.Dup ⟨1,by decide⟩),
   opAt 522 .SUB,
   pushAt 523 2 1952,
   opAt 524 .MSTORE,
   opAt 525 .LT,
   opAt 526 (.Swap ⟨1,by decide⟩),
   opAt 527 .GT,
   opAt 528 .OR]
def csFixedStep8_3 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 529 (.Dup ⟨0,by decide⟩),
   pushAt 530 1 128,
   opAt 531 .MLOAD,
   opAt 532 .ADD,
   opAt 533 (.Dup ⟨0,by decide⟩),
   pushAt 534 2 2240,
   opAt 535 .MLOAD,
   opAt 536 (.Dup ⟨1,by decide⟩),
   opAt 537 (.Dup ⟨1,by decide⟩),
   opAt 538 .SUB,
   pushAt 539 2 1920,
   opAt 540 .MSTORE,
   opAt 541 .LT,
   opAt 542 (.Swap ⟨1,by decide⟩),
   opAt 543 .GT,
   opAt 544 .OR]
def csFixedStep8_4 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 545 (.Dup ⟨0,by decide⟩),
   pushAt 546 1 96,
   opAt 547 .MLOAD,
   opAt 548 .ADD,
   opAt 549 (.Dup ⟨0,by decide⟩),
   pushAt 550 2 2208,
   opAt 551 .MLOAD,
   opAt 552 (.Dup ⟨1,by decide⟩),
   opAt 553 (.Dup ⟨1,by decide⟩),
   opAt 554 .SUB,
   pushAt 555 2 1888,
   opAt 556 .MSTORE,
   opAt 557 .LT,
   opAt 558 (.Swap ⟨1,by decide⟩),
   opAt 559 .GT,
   opAt 560 .OR]
def csFixedStep8_5 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 561 .JUMPDEST,
   opAt 562 (.Dup ⟨0,by decide⟩),
   pushAt 563 1 64,
   opAt 564 .MLOAD,
   opAt 565 .ADD,
   opAt 566 (.Dup ⟨0,by decide⟩),
   pushAt 567 2 2176,
   opAt 568 .MLOAD,
   opAt 569 (.Dup ⟨1,by decide⟩),
   opAt 570 (.Dup ⟨1,by decide⟩),
   opAt 571 .SUB,
   pushAt 572 2 1856,
   opAt 573 .MSTORE,
   opAt 574 .LT,
   opAt 575 (.Swap ⟨1,by decide⟩),
   opAt 576 .GT,
   opAt 577 .OR]
def csFixedStep8_6 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 578 (.Dup ⟨0,by decide⟩),
   pushAt 579 1 32,
   opAt 580 .MLOAD,
   opAt 581 .ADD,
   opAt 582 (.Dup ⟨0,by decide⟩),
   pushAt 583 2 2144,
   opAt 584 .MLOAD,
   opAt 585 (.Dup ⟨1,by decide⟩),
   opAt 586 (.Dup ⟨1,by decide⟩),
   opAt 587 .SUB,
   pushAt 588 2 1824,
   opAt 589 .MSTORE,
   opAt 590 .LT,
   opAt 591 (.Swap ⟨1,by decide⟩),
   opAt 592 .GT,
   opAt 593 .OR]
def csFixedStep8_7 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 594 (.Dup ⟨0,by decide⟩),
   pushAt 595 0 0,
   opAt 596 .MLOAD,
   opAt 597 .ADD,
   opAt 598 (.Dup ⟨0,by decide⟩),
   pushAt 599 2 2112,
   opAt 600 .MLOAD,
   opAt 601 (.Dup ⟨1,by decide⟩),
   opAt 602 (.Dup ⟨1,by decide⟩),
   opAt 603 .SUB,
   pushAt 604 2 1792,
   opAt 605 .MSTORE,
   opAt 606 .LT,
   opAt 607 (.Swap ⟨1,by decide⟩),
   opAt 608 .GT,
   opAt 609 .OR]
/-- Selection tail when `use ≠ 0` (`t ≥ m`): `JUMPI` to pc 4526, which copies the
difference block at `SUBB` (1792) to the destination and returns. -/
def csFixedTailSub : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 610 .ISZERO,
   pushAt 611 2 2080,
   opAt 612 .MLOAD,
   opAt 613 .OR,
   pushAt 614 2 854,
   opAt 615 .JUMPI,
   opAt 625 .JUMPDEST,
   pushAt 626 2 1792,
   pushAt 627 2 2688,
   opAt 628 .MLOAD,
   opAt 629 (.Swap ⟨1,by decide⟩),
   opAt 630 .MCOPY,
   opAt 631 .JUMP]
/-- Selection tail when `use = 0` (`t < m`): fall through the `JUMPI` and jump to the
shared copy block at pc 4515, which copies `t` (2112) to the destination and returns. -/
def csFixedTailKeep : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 610 .ISZERO,
   pushAt 611 2 2080,
   opAt 612 .MLOAD,
   opAt 613 .OR,
   pushAt 614 2 854,
   opAt 615 .JUMPI,
   pushAt 616 2 843,
   opAt 617 .JUMP,
   opAt 618 .JUMPDEST,
   pushAt 619 2 2112,
   pushAt 620 2 2688,
   opAt 621 .MLOAD,
   opAt 622 (.Swap ⟨1,by decide⟩),
   opAt 623 .MCOPY,
   opAt 624 .JUMP]
def csFixedStep4_0 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 7947 2 2208,
   opAt 7948 .MLOAD,
   pushAt 7949 1 96,
   opAt 7950 .MLOAD,
   opAt 7951 (.Dup ⟨0,by decide⟩),
   opAt 7952 (.Dup ⟨2,by decide⟩),
   opAt 7953 .SUB,
   pushAt 7954 2 1888,
   opAt 7955 .MSTORE,
   opAt 7956 .GT,
   pushAt 7957 2 766,
   opAt 7958 .JUMP]
def csFixedStep4_1 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 561 .JUMPDEST,
   opAt 562 (.Dup ⟨0,by decide⟩),
   pushAt 563 1 64,
   opAt 564 .MLOAD,
   opAt 565 .ADD,
   opAt 566 (.Dup ⟨0,by decide⟩),
   pushAt 567 2 2176,
   opAt 568 .MLOAD,
   opAt 569 (.Dup ⟨1,by decide⟩),
   opAt 570 (.Dup ⟨1,by decide⟩),
   opAt 571 .SUB,
   pushAt 572 2 1856,
   opAt 573 .MSTORE,
   opAt 574 .LT,
   opAt 575 (.Swap ⟨1,by decide⟩),
   opAt 576 .GT,
   opAt 577 .OR]
def csFixedStep4_2 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 578 (.Dup ⟨0,by decide⟩),
   pushAt 579 1 32,
   opAt 580 .MLOAD,
   opAt 581 .ADD,
   opAt 582 (.Dup ⟨0,by decide⟩),
   pushAt 583 2 2144,
   opAt 584 .MLOAD,
   opAt 585 (.Dup ⟨1,by decide⟩),
   opAt 586 (.Dup ⟨1,by decide⟩),
   opAt 587 .SUB,
   pushAt 588 2 1824,
   opAt 589 .MSTORE,
   opAt 590 .LT,
   opAt 591 (.Swap ⟨1,by decide⟩),
   opAt 592 .GT,
   opAt 593 .OR]
def csFixedStep4_3 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 594 (.Dup ⟨0,by decide⟩),
   pushAt 595 0 0,
   opAt 596 .MLOAD,
   opAt 597 .ADD,
   opAt 598 (.Dup ⟨0,by decide⟩),
   pushAt 599 2 2112,
   opAt 600 .MLOAD,
   opAt 601 (.Dup ⟨1,by decide⟩),
   opAt 602 (.Dup ⟨1,by decide⟩),
   opAt 603 .SUB,
   pushAt 604 2 1792,
   opAt 605 .MSTORE,
   opAt 606 .LT,
   opAt 607 (.Swap ⟨1,by decide⟩),
   opAt 608 .GT,
   opAt 609 .OR]
@[simp] theorem cycleAnchor : runtimeArtifact.instructionPC 7780 = 10290 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3777 : runtimeArtifact.instructionPC 476 = 645 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3778 : runtimeArtifact.instructionPC 616 = 839 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3779 : runtimeArtifact.instructionPC 617 = 842 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3787 : runtimeArtifact.instructionPC 618 = 843 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3788 : runtimeArtifact.instructionPC 618 = 843 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3789 : runtimeArtifact.instructionPC 618 = 843 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3790 : runtimeArtifact.instructionPC 618 = 843 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3791 : runtimeArtifact.instructionPC 618 = 843 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3792 : runtimeArtifact.instructionPC 618 = 843 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3793 : runtimeArtifact.instructionPC 619 = 844 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3794 : runtimeArtifact.instructionPC 620 = 847 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3795 : runtimeArtifact.instructionPC 621 = 850 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3796 : runtimeArtifact.instructionPC 622 = 851 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3797 : runtimeArtifact.instructionPC 623 = 852 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3798 : runtimeArtifact.instructionPC 623 = 852 := fixedPC3797
@[simp] theorem fixedPC3799 : runtimeArtifact.instructionPC 623 = 852 := fixedPC3797
@[simp] theorem fixedPC3800 : runtimeArtifact.instructionPC 624 = 853 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3801 : runtimeArtifact.instructionPC 625 = 854 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3802 : runtimeArtifact.instructionPC 626 = 855 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3803 : runtimeArtifact.instructionPC 627 = 858 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3804 : runtimeArtifact.instructionPC 628 = 861 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
/-! The rewritten conditional-subtraction dispatch occupies rows 3113..3119; its interior rows had
no pc certificates, so the block could not step. -/
@[simp] theorem fixedPC3114 : runtimeArtifact.instructionPC 477 = 646 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3115 : runtimeArtifact.instructionPC 478 = 649 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3116 : runtimeArtifact.instructionPC 479 = 650 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3117 : runtimeArtifact.instructionPC 480 = 653 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3118 : runtimeArtifact.instructionPC 481 = 656 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3119 : runtimeArtifact.instructionPC 482 = 659 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
/-- The four-limb landing of the rewritten conditional-subtraction dispatch. The old claim here named
pc 4359 through index 3261, which is now an `MCOPY` at 4380, so it was false and cost a `whnf` runaway
rather than an honest error. -/
@[simp] theorem fixedPC3009 : runtimeArtifact.instructionPC 7786 = 10299 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedJump3984 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10508 = true := by
  have h : runtimeArtifact.instructionPC 7946 = 10508 := by
    rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
    rfl
  simpa only [h] using CycleSubmission.Global.Binding.jumpDest 7946 (by rfl)
@[simp] theorem fixedPC3805 : runtimeArtifact.instructionPC 483 = 660 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3806 : runtimeArtifact.instructionPC 484 = 662 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3807 : runtimeArtifact.instructionPC 485 = 663 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3808 : runtimeArtifact.instructionPC 486 = 666 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPCs8 : runtimeArtifact.instructionPC 487 = 667 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3809 : runtimeArtifact.instructionPC 487 = 667 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3810 : runtimeArtifact.instructionPC 488 = 670 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3811 : runtimeArtifact.instructionPC 489 = 671 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3812 : runtimeArtifact.instructionPC 490 = 673 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3813 : runtimeArtifact.instructionPC 491 = 674 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3814 : runtimeArtifact.instructionPC 492 = 675 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3815 : runtimeArtifact.instructionPC 493 = 676 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3816 : runtimeArtifact.instructionPC 493 = 676 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3817 : runtimeArtifact.instructionPC 494 = 677 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3818 : runtimeArtifact.instructionPC 495 = 680 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3819 : runtimeArtifact.instructionPC 496 = 681 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3820 : runtimeArtifact.instructionPC 497 = 682 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3821 : runtimeArtifact.instructionPC 498 = 683 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3822 : runtimeArtifact.instructionPC 499 = 685 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3823 : runtimeArtifact.instructionPC 500 = 686 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3824 : runtimeArtifact.instructionPC 501 = 687 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3825 : runtimeArtifact.instructionPC 502 = 688 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3826 : runtimeArtifact.instructionPC 503 = 691 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3827 : runtimeArtifact.instructionPC 504 = 692 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3828 : runtimeArtifact.instructionPC 505 = 693 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3829 : runtimeArtifact.instructionPC 506 = 694 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3830 : runtimeArtifact.instructionPC 507 = 695 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3831 : runtimeArtifact.instructionPC 508 = 698 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3832 : runtimeArtifact.instructionPC 509 = 699 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3833 : runtimeArtifact.instructionPC 510 = 700 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3834 : runtimeArtifact.instructionPC 510 = 700 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3835 : runtimeArtifact.instructionPC 511 = 701 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3836 : runtimeArtifact.instructionPC 512 = 702 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3837 : runtimeArtifact.instructionPC 513 = 703 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3838 : runtimeArtifact.instructionPC 514 = 704 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3839 : runtimeArtifact.instructionPC 515 = 706 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3840 : runtimeArtifact.instructionPC 516 = 707 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3841 : runtimeArtifact.instructionPC 517 = 708 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3842 : runtimeArtifact.instructionPC 518 = 709 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3843 : runtimeArtifact.instructionPC 519 = 712 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3844 : runtimeArtifact.instructionPC 520 = 713 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3845 : runtimeArtifact.instructionPC 521 = 714 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3846 : runtimeArtifact.instructionPC 522 = 715 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3847 : runtimeArtifact.instructionPC 523 = 716 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3848 : runtimeArtifact.instructionPC 524 = 719 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3849 : runtimeArtifact.instructionPC 525 = 720 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3850 : runtimeArtifact.instructionPC 526 = 721 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3851 : runtimeArtifact.instructionPC 527 = 722 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3852 : runtimeArtifact.instructionPC 527 = 722 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3853 : runtimeArtifact.instructionPC 528 = 723 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3854 : runtimeArtifact.instructionPC 529 = 724 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3855 : runtimeArtifact.instructionPC 530 = 725 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3856 : runtimeArtifact.instructionPC 531 = 727 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3857 : runtimeArtifact.instructionPC 532 = 728 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3858 : runtimeArtifact.instructionPC 533 = 729 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3859 : runtimeArtifact.instructionPC 534 = 730 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3860 : runtimeArtifact.instructionPC 535 = 733 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3861 : runtimeArtifact.instructionPC 536 = 734 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3862 : runtimeArtifact.instructionPC 537 = 735 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3863 : runtimeArtifact.instructionPC 538 = 736 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3864 : runtimeArtifact.instructionPC 539 = 737 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3865 : runtimeArtifact.instructionPC 540 = 740 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3866 : runtimeArtifact.instructionPC 541 = 741 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3867 : runtimeArtifact.instructionPC 542 = 742 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3868 : runtimeArtifact.instructionPC 543 = 743 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3869 : runtimeArtifact.instructionPC 544 = 744 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3871 : runtimeArtifact.instructionPC 544 = 744 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3872 : runtimeArtifact.instructionPC 545 = 745 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3873 : runtimeArtifact.instructionPC 546 = 746 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3874 : runtimeArtifact.instructionPC 547 = 748 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3875 : runtimeArtifact.instructionPC 548 = 749 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3876 : runtimeArtifact.instructionPC 549 = 750 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3877 : runtimeArtifact.instructionPC 550 = 751 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3878 : runtimeArtifact.instructionPC 551 = 754 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3879 : runtimeArtifact.instructionPC 552 = 755 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3880 : runtimeArtifact.instructionPC 553 = 756 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3881 : runtimeArtifact.instructionPC 554 = 757 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3882 : runtimeArtifact.instructionPC 555 = 758 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3883 : runtimeArtifact.instructionPC 556 = 761 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3884 : runtimeArtifact.instructionPC 557 = 762 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3885 : runtimeArtifact.instructionPC 558 = 763 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3886 : runtimeArtifact.instructionPC 559 = 764 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3887 : runtimeArtifact.instructionPC 560 = 765 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3888 : runtimeArtifact.instructionPC 561 = 766 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3889 : runtimeArtifact.instructionPC 561 = 766 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedJump5133 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 766 = true := by
  have h : runtimeArtifact.instructionPC 561 = 766 := by
    rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
    rfl
  simpa only [h] using CycleSubmission.Global.Binding.jumpDest 561 (by rfl)
@[simp] theorem fixedPC3890 : runtimeArtifact.instructionPC 562 = 767 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3891 : runtimeArtifact.instructionPC 563 = 768 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3892 : runtimeArtifact.instructionPC 564 = 770 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3893 : runtimeArtifact.instructionPC 565 = 771 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3894 : runtimeArtifact.instructionPC 566 = 772 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3895 : runtimeArtifact.instructionPC 567 = 773 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3896 : runtimeArtifact.instructionPC 568 = 776 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3897 : runtimeArtifact.instructionPC 569 = 777 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3898 : runtimeArtifact.instructionPC 570 = 778 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3899 : runtimeArtifact.instructionPC 571 = 779 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3900 : runtimeArtifact.instructionPC 572 = 780 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3901 : runtimeArtifact.instructionPC 573 = 783 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3902 : runtimeArtifact.instructionPC 574 = 784 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3903 : runtimeArtifact.instructionPC 575 = 785 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3904 : runtimeArtifact.instructionPC 576 = 786 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3905 : runtimeArtifact.instructionPC 577 = 787 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3906 : runtimeArtifact.instructionPC 578 = 788 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3907 : runtimeArtifact.instructionPC 579 = 789 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3908 : runtimeArtifact.instructionPC 579 = 789 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3909 : runtimeArtifact.instructionPC 580 = 791 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3910 : runtimeArtifact.instructionPC 581 = 792 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3911 : runtimeArtifact.instructionPC 582 = 793 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3912 : runtimeArtifact.instructionPC 583 = 794 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3913 : runtimeArtifact.instructionPC 584 = 797 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3914 : runtimeArtifact.instructionPC 585 = 798 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3915 : runtimeArtifact.instructionPC 586 = 799 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3916 : runtimeArtifact.instructionPC 587 = 800 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3917 : runtimeArtifact.instructionPC 588 = 801 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3918 : runtimeArtifact.instructionPC 589 = 804 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3919 : runtimeArtifact.instructionPC 590 = 805 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3920 : runtimeArtifact.instructionPC 591 = 806 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3921 : runtimeArtifact.instructionPC 592 = 807 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3922 : runtimeArtifact.instructionPC 593 = 808 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3923 : runtimeArtifact.instructionPC 594 = 809 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3924 : runtimeArtifact.instructionPC 595 = 810 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3925 : runtimeArtifact.instructionPC 596 = 811 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3926 : runtimeArtifact.instructionPC 596 = 811 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3927 : runtimeArtifact.instructionPC 597 = 812 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3928 : runtimeArtifact.instructionPC 598 = 813 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3929 : runtimeArtifact.instructionPC 599 = 814 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3930 : runtimeArtifact.instructionPC 600 = 817 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3931 : runtimeArtifact.instructionPC 601 = 818 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3932 : runtimeArtifact.instructionPC 602 = 819 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3933 : runtimeArtifact.instructionPC 603 = 820 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3934 : runtimeArtifact.instructionPC 604 = 821 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3935 : runtimeArtifact.instructionPC 605 = 824 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3936 : runtimeArtifact.instructionPC 606 = 825 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3937 : runtimeArtifact.instructionPC 607 = 826 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3938 : runtimeArtifact.instructionPC 608 = 827 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3939 : runtimeArtifact.instructionPC 609 = 828 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3940 : runtimeArtifact.instructionPC 610 = 829 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3941 : runtimeArtifact.instructionPC 611 = 830 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3942 : runtimeArtifact.instructionPC 612 = 833 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3943 : runtimeArtifact.instructionPC 613 = 834 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3944 : runtimeArtifact.instructionPC 613 = 834 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3945 : runtimeArtifact.instructionPC 614 = 835 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3946 : runtimeArtifact.instructionPC 615 = 838 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3947 : runtimeArtifact.instructionPC 616 = 839 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3948 : runtimeArtifact.instructionPC 617 = 842 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3949 : runtimeArtifact.instructionPC 622 = 851 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3950 : runtimeArtifact.instructionPC 622 = 851 :=
  fixedPC3949
@[simp] theorem fixedPC3951 : runtimeArtifact.instructionPC 623 = 852 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3952 : runtimeArtifact.instructionPC 624 = 853 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3953 : runtimeArtifact.instructionPC 625 = 854 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3954 : runtimeArtifact.instructionPC 626 = 855 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3955 : runtimeArtifact.instructionPC 627 = 858 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3956 : runtimeArtifact.instructionPC 628 = 861 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3957 : runtimeArtifact.instructionPC 629 = 862 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedJump5280 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10508 = true := by
  have h : runtimeArtifact.instructionPC 7946 = 10508 := by
    rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
    rfl
  simpa only [h] using CycleSubmission.Global.Binding.jumpDest 7946 (by rfl)
@[simp] theorem fixedPC4000 : runtimeArtifact.instructionPC 7786 = 10299 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC4001 : runtimeArtifact.instructionPC 7786 = 10299 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC4002 : runtimeArtifact.instructionPC 7805 = 10322 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC4003 : runtimeArtifact.instructionPC 7946 = 10508 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC4004 : runtimeArtifact.instructionPC 7947 = 10509 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC4005 : runtimeArtifact.instructionPC 7948 = 10512 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC4006 : runtimeArtifact.instructionPC 7949 = 10513 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC4007 : runtimeArtifact.instructionPC 7950 = 10515 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC4008 : runtimeArtifact.instructionPC 7951 = 10516 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC4009 : runtimeArtifact.instructionPC 7952 = 10517 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC4010 : runtimeArtifact.instructionPC 7953 = 10518 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC4011 : runtimeArtifact.instructionPC 7954 = 10519 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC4012 : runtimeArtifact.instructionPC 7955 = 10522 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2883 : runtimeArtifact.instructionPC 7298 = 9712 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2884 : runtimeArtifact.instructionPC 7299 = 9713 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2885 : runtimeArtifact.instructionPC 7300 = 9714 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2886 : runtimeArtifact.instructionPC 7301 = 9715 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2888 : runtimeArtifact.instructionPC 7302 = 9716 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2889 : runtimeArtifact.instructionPC 7303 = 9717 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2890 : runtimeArtifact.instructionPC 7304 = 9718 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2891 : runtimeArtifact.instructionPC 7305 = 9721 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2892 : runtimeArtifact.instructionPC 7306 = 9722 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2893 : runtimeArtifact.instructionPC 7306 = 9722 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2894 : runtimeArtifact.instructionPC 7306 = 9722 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2895 : runtimeArtifact.instructionPC 7774 = 10280 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2896 : runtimeArtifact.instructionPC 7786 = 10299 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2930 : runtimeArtifact.instructionPC 7786 = 10299 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2931 : runtimeArtifact.instructionPC 7786 = 10299 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2932 : runtimeArtifact.instructionPC 7786 = 10299 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2933 : runtimeArtifact.instructionPC 7805 = 10322 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2934 : runtimeArtifact.instructionPC 7946 = 10508 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2935 : runtimeArtifact.instructionPC 7947 = 10509 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2936 : runtimeArtifact.instructionPC 7948 = 10512 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2937 : runtimeArtifact.instructionPC 7949 = 10513 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2938 : runtimeArtifact.instructionPC 7950 = 10515 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2939 : runtimeArtifact.instructionPC 7951 = 10516 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2940 : runtimeArtifact.instructionPC 7952 = 10517 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2941 : runtimeArtifact.instructionPC 7953 = 10518 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2942 : runtimeArtifact.instructionPC 7954 = 10519 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2943 : runtimeArtifact.instructionPC 7955 = 10522 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC3921 : runtimeArtifact.instructionPC 618 = 843 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC3922 : runtimeArtifact.instructionPC 618 = 843 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC3923 : runtimeArtifact.instructionPC 618 = 843 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC3924 : runtimeArtifact.instructionPC 618 = 843 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC3925 : runtimeArtifact.instructionPC 618 = 843 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC3926 : runtimeArtifact.instructionPC 619 = 844 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC3927 : runtimeArtifact.instructionPC 620 = 847 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC3928 : runtimeArtifact.instructionPC 621 = 850 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
end CycleSubmission.Global.Fast
