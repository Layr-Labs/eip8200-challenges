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
    List.take_add_one, hget, Option.toList_some, assembleBytes_append,
    assembleBytes_cons, assembleBytes_nil, List.append_nil, List.length_append]

def csFixedEntry8 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 486 2 2688,
   opAt 487 .MLOAD,
   pushAt 488 1 128,
   opAt 489 .EQ,
   pushAt 490 2 9847,
   opAt 491 .JUMPI]

def csFixedEntry4 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 486 2 2688,
   opAt 487 .MLOAD,
   pushAt 488 1 128,
   opAt 489 .EQ,
   pushAt 490 2 9847,
   opAt 491 .JUMPI,
   opAt 7676 .JUMPDEST]

/-- rarej: the eight-limb subtraction starts at the `s8` `JUMPDEST` (pc 4374), the target of the
square exit's carry continuation; the entry block falls into it. -/
def csFixedStep8_0 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 492 2 2336,
   opAt 493 .MLOAD,
   pushAt 494 1 224,
   opAt 495 .MLOAD,
   opAt 496 (.Dup dA0),
   opAt 497 (.Dup dA2),
   opAt 498 .SUB,
   pushAt 499 2 2016,
   opAt 500 .MSTORE,
   opAt 501 .GT]

def csFixedStep8_1 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 502 (.Dup dA0),
   pushAt 503 1 192,
   opAt 504 .MLOAD,
   opAt 505 .ADD,
   opAt 506 (.Dup dA0),
   pushAt 507 2 2304,
   opAt 508 .MLOAD,
   opAt 509 (.Dup dA1),
   opAt 510 (.Dup dA1),
   opAt 511 .SUB,
   pushAt 512 2 1984,
   opAt 513 .MSTORE,
   opAt 514 .LT,
   opAt 515 (.Swap sA1),
   opAt 516 .GT,
   opAt 517 .OR]

def csFixedStep8_2 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 518 (.Dup dA0),
   pushAt 519 1 160,
   opAt 520 .MLOAD,
   opAt 521 .ADD,
   opAt 522 (.Dup dA0),
   pushAt 523 2 2272,
   opAt 524 .MLOAD,
   opAt 525 (.Dup dA1),
   opAt 526 (.Dup dA1),
   opAt 527 .SUB,
   pushAt 528 2 1952,
   opAt 529 .MSTORE,
   opAt 530 .LT,
   opAt 531 (.Swap sA1),
   opAt 532 .GT,
   opAt 533 .OR]

def csFixedStep8_3 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 534 (.Dup dA0),
   pushAt 535 1 128,
   opAt 536 .MLOAD,
   opAt 537 .ADD,
   opAt 538 (.Dup dA0),
   pushAt 539 2 2240,
   opAt 540 .MLOAD,
   opAt 541 (.Dup dA1),
   opAt 542 (.Dup dA1),
   opAt 543 .SUB,
   pushAt 544 2 1920,
   opAt 545 .MSTORE,
   opAt 546 .LT,
   opAt 547 (.Swap sA1),
   opAt 548 .GT,
   opAt 549 .OR]

def csFixedStep8_4 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 550 (.Dup dA0),
   pushAt 551 1 96,
   opAt 552 .MLOAD,
   opAt 553 .ADD,
   opAt 554 (.Dup dA0),
   pushAt 555 2 2208,
   opAt 556 .MLOAD,
   opAt 557 (.Dup dA1),
   opAt 558 (.Dup dA1),
   opAt 559 .SUB,
   pushAt 560 2 1888,
   opAt 561 .MSTORE,
   opAt 562 .LT,
   opAt 563 (.Swap sA1),
   opAt 564 .GT,
   opAt 565 .OR]

def csFixedStep8_5 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 566 .JUMPDEST,
   opAt 567 (.Dup dA0),
   pushAt 568 1 64,
   opAt 569 .MLOAD,
   opAt 570 .ADD,
   opAt 571 (.Dup dA0),
   pushAt 572 2 2176,
   opAt 573 .MLOAD,
   opAt 574 (.Dup dA1),
   opAt 575 (.Dup dA1),
   opAt 576 .SUB,
   pushAt 577 2 1856,
   opAt 578 .MSTORE,
   opAt 579 .LT,
   opAt 580 (.Swap sA1),
   opAt 581 .GT,
   opAt 582 .OR]

def csFixedStep8_6 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 583 (.Dup dA0),
   pushAt 584 1 32,
   opAt 585 .MLOAD,
   opAt 586 .ADD,
   opAt 587 (.Dup dA0),
   pushAt 588 2 2144,
   opAt 589 .MLOAD,
   opAt 590 (.Dup dA1),
   opAt 591 (.Dup dA1),
   opAt 592 .SUB,
   pushAt 593 2 1824,
   opAt 594 .MSTORE,
   opAt 595 .LT,
   opAt 596 (.Swap sA1),
   opAt 597 .GT,
   opAt 598 .OR]

def csFixedStep8_7 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 599 (.Dup dA0),
   pushAt 600 0 0,
   opAt 601 .MLOAD,
   opAt 602 .ADD,
   opAt 603 (.Dup dA0),
   pushAt 604 2 2112,
   opAt 605 .MLOAD,
   opAt 606 (.Dup dA1),
   opAt 607 (.Dup dA1),
   opAt 608 .SUB,
   pushAt 609 2 1792,
   opAt 610 .MSTORE,
   opAt 611 .LT,
   opAt 612 (.Swap sA1),
   opAt 613 .GT,
   opAt 614 .OR]

/-- Selection tail when `use ≠ 0` (`t ≥ m`): `JUMPI` to pc 4538, which copies the
difference block at `SUBB` (1792) to the destination and returns. -/
def csFixedTailSub : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 615 .ISZERO,
   pushAt 616 2 2080,
   opAt 617 .MLOAD,
   opAt 618 .OR,
   pushAt 619 2 891,
   opAt 620 .JUMPI,
   opAt 630 .JUMPDEST,
   pushAt 631 2 1792,
   pushAt 632 2 2688,
   opAt 633 .MLOAD,
   opAt 634 (.Swap sA1),
   opAt 635 .MCOPY,
   opAt 636 .JUMP]

/-- Selection tail when `use = 0` (`t < m`): fall through the `JUMPI` and jump to the
shared copy block at pc 4527, which copies `t` (2112) to the destination and returns. -/
def csFixedTailKeep : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 615 .ISZERO,
   pushAt 616 2 2080,
   opAt 617 .MLOAD,
   opAt 618 .OR,
   pushAt 619 2 891,
   opAt 620 .JUMPI,
   pushAt 621 2 880,
   opAt 622 .JUMP,
   opAt 623 .JUMPDEST,
   pushAt 624 2 2112,
   pushAt 625 2 2688,
   opAt 626 .MLOAD,
   opAt 627 (.Swap sA1),
   opAt 628 .MCOPY,
   opAt 629 .JUMP]

def csFixedStep4_0 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 7677 2 2208,
   opAt 7678 .MLOAD,
   pushAt 7679 1 96,
   opAt 7680 .MLOAD,
   opAt 7681 (.Dup dA0),
   opAt 7682 (.Dup dA2),
   opAt 7683 .SUB,
   pushAt 7684 2 1888,
   opAt 7685 .MSTORE,
   opAt 7686 .GT,
   pushAt 7687 2 803,
   opAt 7688 .JUMP]

def csFixedStep4_1 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 566 .JUMPDEST,
   opAt 567 (.Dup dA0),
   pushAt 568 1 64,
   opAt 569 .MLOAD,
   opAt 570 .ADD,
   opAt 571 (.Dup dA0),
   pushAt 572 2 2176,
   opAt 573 .MLOAD,
   opAt 574 (.Dup dA1),
   opAt 575 (.Dup dA1),
   opAt 576 .SUB,
   pushAt 577 2 1856,
   opAt 578 .MSTORE,
   opAt 579 .LT,
   opAt 580 (.Swap sA1),
   opAt 581 .GT,
   opAt 582 .OR]

def csFixedStep4_2 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 583 (.Dup dA0),
   pushAt 584 1 32,
   opAt 585 .MLOAD,
   opAt 586 .ADD,
   opAt 587 (.Dup dA0),
   pushAt 588 2 2144,
   opAt 589 .MLOAD,
   opAt 590 (.Dup dA1),
   opAt 591 (.Dup dA1),
   opAt 592 .SUB,
   pushAt 593 2 1824,
   opAt 594 .MSTORE,
   opAt 595 .LT,
   opAt 596 (.Swap sA1),
   opAt 597 .GT,
   opAt 598 .OR]

def csFixedStep4_3 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 599 (.Dup dA0),
   pushAt 600 0 0,
   opAt 601 .MLOAD,
   opAt 602 .ADD,
   opAt 603 (.Dup dA0),
   pushAt 604 2 2112,
   opAt 605 .MLOAD,
   opAt 606 (.Dup dA1),
   opAt 607 (.Dup dA1),
   opAt 608 .SUB,
   pushAt 609 2 1792,
   opAt 610 .MSTORE,
   opAt 611 .LT,
   opAt 612 (.Swap sA1),
   opAt 613 .GT,
   opAt 614 .OR]

@[simp] theorem cycleAnchor : runtimeArtifact.instructionPC 7397 = 9500 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3777 : runtimeArtifact.instructionPC 481 = 684 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3778 : runtimeArtifact.instructionPC 621 = 876 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3779 : runtimeArtifact.instructionPC 622 = 879 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3787 : runtimeArtifact.instructionPC 623 = 880 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3788 : runtimeArtifact.instructionPC 623 = 880 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3789 : runtimeArtifact.instructionPC 623 = 880 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3790 : runtimeArtifact.instructionPC 623 = 880 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3791 : runtimeArtifact.instructionPC 623 = 880 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3792 : runtimeArtifact.instructionPC 623 = 880 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3793 : runtimeArtifact.instructionPC 624 = 881 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3794 : runtimeArtifact.instructionPC 625 = 884 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3795 : runtimeArtifact.instructionPC 626 = 887 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3796 : runtimeArtifact.instructionPC 627 = 888 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3797 : runtimeArtifact.instructionPC 628 = 889 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3798 : runtimeArtifact.instructionPC 628 = 889 := fixedPC3797

@[simp] theorem fixedPC3799 : runtimeArtifact.instructionPC 628 = 889 := fixedPC3797

@[simp] theorem fixedPC3800 : runtimeArtifact.instructionPC 629 = 890 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3801 : runtimeArtifact.instructionPC 630 = 891 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3802 : runtimeArtifact.instructionPC 631 = 892 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3803 : runtimeArtifact.instructionPC 632 = 895 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3804 : runtimeArtifact.instructionPC 633 = 898 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

/-! The rewritten conditional-subtraction dispatch occupies rows 3113..3119; its interior rows had
no pc certificates, so the block could not step. -/
@[simp] theorem fixedPC3114 : runtimeArtifact.instructionPC 482 = 685 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3115 : runtimeArtifact.instructionPC 483 = 686 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3116 : runtimeArtifact.instructionPC 484 = 687 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3117 : runtimeArtifact.instructionPC 485 = 690 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3118 : runtimeArtifact.instructionPC 486 = 693 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3119 : runtimeArtifact.instructionPC 487 = 696 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

/-- The four-limb landing of the rewritten conditional-subtraction dispatch. The old claim here named
pc 4371 through index 3273, which is now an `MCOPY` at 4392, so it was false and cost a `whnf` runaway
rather than an honest error. -/
@[simp] theorem fixedPC3009 : runtimeArtifact.instructionPC 7403 = 9509 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedJump3984 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 9847 = true := by
  have h : runtimeArtifact.instructionPC 7676 = 9847 := by
    rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
    rfl
  simpa only [h] using CycleSubmission.Global.Binding.jumpDest 7676 (by rfl)

@[simp] theorem fixedPC3805 : runtimeArtifact.instructionPC 488 = 697 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3806 : runtimeArtifact.instructionPC 489 = 699 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3807 : runtimeArtifact.instructionPC 490 = 700 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3808 : runtimeArtifact.instructionPC 491 = 703 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPCs8 : runtimeArtifact.instructionPC 492 = 704 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3809 : runtimeArtifact.instructionPC 492 = 704 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3810 : runtimeArtifact.instructionPC 493 = 707 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3811 : runtimeArtifact.instructionPC 494 = 708 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3812 : runtimeArtifact.instructionPC 495 = 710 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3813 : runtimeArtifact.instructionPC 496 = 711 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3814 : runtimeArtifact.instructionPC 497 = 712 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3815 : runtimeArtifact.instructionPC 498 = 713 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3816 : runtimeArtifact.instructionPC 498 = 713 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3817 : runtimeArtifact.instructionPC 499 = 714 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3818 : runtimeArtifact.instructionPC 500 = 717 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3819 : runtimeArtifact.instructionPC 501 = 718 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3820 : runtimeArtifact.instructionPC 502 = 719 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3821 : runtimeArtifact.instructionPC 503 = 720 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3822 : runtimeArtifact.instructionPC 504 = 722 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3823 : runtimeArtifact.instructionPC 505 = 723 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3824 : runtimeArtifact.instructionPC 506 = 724 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3825 : runtimeArtifact.instructionPC 507 = 725 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3826 : runtimeArtifact.instructionPC 508 = 728 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3827 : runtimeArtifact.instructionPC 509 = 729 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3828 : runtimeArtifact.instructionPC 510 = 730 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3829 : runtimeArtifact.instructionPC 511 = 731 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3830 : runtimeArtifact.instructionPC 512 = 732 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3831 : runtimeArtifact.instructionPC 513 = 735 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3832 : runtimeArtifact.instructionPC 514 = 736 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3833 : runtimeArtifact.instructionPC 515 = 737 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3834 : runtimeArtifact.instructionPC 515 = 737 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3835 : runtimeArtifact.instructionPC 516 = 738 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3836 : runtimeArtifact.instructionPC 517 = 739 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3837 : runtimeArtifact.instructionPC 518 = 740 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3838 : runtimeArtifact.instructionPC 519 = 741 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3839 : runtimeArtifact.instructionPC 520 = 743 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3840 : runtimeArtifact.instructionPC 521 = 744 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3841 : runtimeArtifact.instructionPC 522 = 745 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3842 : runtimeArtifact.instructionPC 523 = 746 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3843 : runtimeArtifact.instructionPC 524 = 749 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3844 : runtimeArtifact.instructionPC 525 = 750 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3845 : runtimeArtifact.instructionPC 526 = 751 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3846 : runtimeArtifact.instructionPC 527 = 752 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3847 : runtimeArtifact.instructionPC 528 = 753 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3848 : runtimeArtifact.instructionPC 529 = 756 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3849 : runtimeArtifact.instructionPC 530 = 757 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3850 : runtimeArtifact.instructionPC 531 = 758 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3851 : runtimeArtifact.instructionPC 532 = 759 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3852 : runtimeArtifact.instructionPC 532 = 759 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3853 : runtimeArtifact.instructionPC 533 = 760 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3854 : runtimeArtifact.instructionPC 534 = 761 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3855 : runtimeArtifact.instructionPC 535 = 762 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3856 : runtimeArtifact.instructionPC 536 = 764 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3857 : runtimeArtifact.instructionPC 537 = 765 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3858 : runtimeArtifact.instructionPC 538 = 766 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3859 : runtimeArtifact.instructionPC 539 = 767 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3860 : runtimeArtifact.instructionPC 540 = 770 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3861 : runtimeArtifact.instructionPC 541 = 771 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3862 : runtimeArtifact.instructionPC 542 = 772 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3863 : runtimeArtifact.instructionPC 543 = 773 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3864 : runtimeArtifact.instructionPC 544 = 774 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3865 : runtimeArtifact.instructionPC 545 = 777 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3866 : runtimeArtifact.instructionPC 546 = 778 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3867 : runtimeArtifact.instructionPC 547 = 779 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3868 : runtimeArtifact.instructionPC 548 = 780 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3869 : runtimeArtifact.instructionPC 549 = 781 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3871 : runtimeArtifact.instructionPC 549 = 781 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3872 : runtimeArtifact.instructionPC 550 = 782 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3873 : runtimeArtifact.instructionPC 551 = 783 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3874 : runtimeArtifact.instructionPC 552 = 785 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3875 : runtimeArtifact.instructionPC 553 = 786 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3876 : runtimeArtifact.instructionPC 554 = 787 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3877 : runtimeArtifact.instructionPC 555 = 788 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3878 : runtimeArtifact.instructionPC 556 = 791 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3879 : runtimeArtifact.instructionPC 557 = 792 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3880 : runtimeArtifact.instructionPC 558 = 793 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3881 : runtimeArtifact.instructionPC 559 = 794 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3882 : runtimeArtifact.instructionPC 560 = 795 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3883 : runtimeArtifact.instructionPC 561 = 798 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3884 : runtimeArtifact.instructionPC 562 = 799 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3885 : runtimeArtifact.instructionPC 563 = 800 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3886 : runtimeArtifact.instructionPC 564 = 801 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3887 : runtimeArtifact.instructionPC 565 = 802 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3888 : runtimeArtifact.instructionPC 566 = 803 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3889 : runtimeArtifact.instructionPC 566 = 803 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedJump5133 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 803 = true := by
  have h : runtimeArtifact.instructionPC 566 = 803 := by
    rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
    rfl
  simpa only [h] using CycleSubmission.Global.Binding.jumpDest 566 (by rfl)

@[simp] theorem fixedPC3890 : runtimeArtifact.instructionPC 567 = 804 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3891 : runtimeArtifact.instructionPC 568 = 805 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3892 : runtimeArtifact.instructionPC 569 = 807 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3893 : runtimeArtifact.instructionPC 570 = 808 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3894 : runtimeArtifact.instructionPC 571 = 809 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3895 : runtimeArtifact.instructionPC 572 = 810 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3896 : runtimeArtifact.instructionPC 573 = 813 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3897 : runtimeArtifact.instructionPC 574 = 814 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3898 : runtimeArtifact.instructionPC 575 = 815 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3899 : runtimeArtifact.instructionPC 576 = 816 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3900 : runtimeArtifact.instructionPC 577 = 817 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3901 : runtimeArtifact.instructionPC 578 = 820 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3902 : runtimeArtifact.instructionPC 579 = 821 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3903 : runtimeArtifact.instructionPC 580 = 822 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3904 : runtimeArtifact.instructionPC 581 = 823 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3905 : runtimeArtifact.instructionPC 582 = 824 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3906 : runtimeArtifact.instructionPC 583 = 825 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3907 : runtimeArtifact.instructionPC 584 = 826 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3908 : runtimeArtifact.instructionPC 584 = 826 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3909 : runtimeArtifact.instructionPC 585 = 828 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3910 : runtimeArtifact.instructionPC 586 = 829 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3911 : runtimeArtifact.instructionPC 587 = 830 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3912 : runtimeArtifact.instructionPC 588 = 831 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3913 : runtimeArtifact.instructionPC 589 = 834 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3914 : runtimeArtifact.instructionPC 590 = 835 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3915 : runtimeArtifact.instructionPC 591 = 836 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3916 : runtimeArtifact.instructionPC 592 = 837 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3917 : runtimeArtifact.instructionPC 593 = 838 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3918 : runtimeArtifact.instructionPC 594 = 841 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3919 : runtimeArtifact.instructionPC 595 = 842 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3920 : runtimeArtifact.instructionPC 596 = 843 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3921 : runtimeArtifact.instructionPC 597 = 844 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3922 : runtimeArtifact.instructionPC 598 = 845 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3923 : runtimeArtifact.instructionPC 599 = 846 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3924 : runtimeArtifact.instructionPC 600 = 847 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3925 : runtimeArtifact.instructionPC 601 = 848 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3926 : runtimeArtifact.instructionPC 601 = 848 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3927 : runtimeArtifact.instructionPC 602 = 849 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3928 : runtimeArtifact.instructionPC 603 = 850 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3929 : runtimeArtifact.instructionPC 604 = 851 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3930 : runtimeArtifact.instructionPC 605 = 854 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3931 : runtimeArtifact.instructionPC 606 = 855 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3932 : runtimeArtifact.instructionPC 607 = 856 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3933 : runtimeArtifact.instructionPC 608 = 857 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3934 : runtimeArtifact.instructionPC 609 = 858 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3935 : runtimeArtifact.instructionPC 610 = 861 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3936 : runtimeArtifact.instructionPC 611 = 862 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3937 : runtimeArtifact.instructionPC 612 = 863 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3938 : runtimeArtifact.instructionPC 613 = 864 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3939 : runtimeArtifact.instructionPC 614 = 865 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3940 : runtimeArtifact.instructionPC 615 = 866 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3941 : runtimeArtifact.instructionPC 616 = 867 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3942 : runtimeArtifact.instructionPC 617 = 870 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3943 : runtimeArtifact.instructionPC 618 = 871 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3944 : runtimeArtifact.instructionPC 618 = 871 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3945 : runtimeArtifact.instructionPC 619 = 872 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3946 : runtimeArtifact.instructionPC 620 = 875 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3947 : runtimeArtifact.instructionPC 621 = 876 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3948 : runtimeArtifact.instructionPC 622 = 879 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3949 : runtimeArtifact.instructionPC 627 = 888 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3950 : runtimeArtifact.instructionPC 627 = 888 :=
  fixedPC3949

@[simp] theorem fixedPC3951 : runtimeArtifact.instructionPC 628 = 889 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3952 : runtimeArtifact.instructionPC 629 = 890 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3953 : runtimeArtifact.instructionPC 630 = 891 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3954 : runtimeArtifact.instructionPC 631 = 892 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3955 : runtimeArtifact.instructionPC 632 = 895 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3956 : runtimeArtifact.instructionPC 633 = 898 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC3957 : runtimeArtifact.instructionPC 634 = 899 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedJump5280 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 9847 = true := by
  have h : runtimeArtifact.instructionPC 7676 = 9847 := by
    rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
    rfl
  simpa only [h] using CycleSubmission.Global.Binding.jumpDest 7676 (by rfl)

@[simp] theorem fixedPC4000 : runtimeArtifact.instructionPC 7403 = 9509 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC4001 : runtimeArtifact.instructionPC 7403 = 9509 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC4002 : runtimeArtifact.instructionPC 7422 = 9532 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC4003 : runtimeArtifact.instructionPC 7676 = 9847 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC4004 : runtimeArtifact.instructionPC 7677 = 9848 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC4005 : runtimeArtifact.instructionPC 7678 = 9851 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC4006 : runtimeArtifact.instructionPC 7679 = 9852 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC4007 : runtimeArtifact.instructionPC 7680 = 9854 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC4008 : runtimeArtifact.instructionPC 7681 = 9855 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC4009 : runtimeArtifact.instructionPC 7682 = 9856 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC4010 : runtimeArtifact.instructionPC 7683 = 9857 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC4011 : runtimeArtifact.instructionPC 7684 = 9858 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem fixedPC4012 : runtimeArtifact.instructionPC 7685 = 9861 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC2883 : runtimeArtifact.instructionPC 7381 = 9476 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC2884 : runtimeArtifact.instructionPC 7382 = 9477 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC2885 : runtimeArtifact.instructionPC 7383 = 9478 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC2886 : runtimeArtifact.instructionPC 7384 = 9479 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC2888 : runtimeArtifact.instructionPC 7385 = 9480 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC2889 : runtimeArtifact.instructionPC 7386 = 9481 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC2890 : runtimeArtifact.instructionPC 7387 = 9482 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC2891 : runtimeArtifact.instructionPC 7388 = 9485 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC2892 : runtimeArtifact.instructionPC 7389 = 9486 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC2893 : runtimeArtifact.instructionPC 7389 = 9486 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC2894 : runtimeArtifact.instructionPC 7390 = 9489 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC2895 : runtimeArtifact.instructionPC 7391 = 9490 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC2896 : runtimeArtifact.instructionPC 7403 = 9509 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC2930 : runtimeArtifact.instructionPC 7403 = 9509 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC2931 : runtimeArtifact.instructionPC 7403 = 9509 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC2932 : runtimeArtifact.instructionPC 7403 = 9509 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC2933 : runtimeArtifact.instructionPC 7422 = 9532 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC2934 : runtimeArtifact.instructionPC 7676 = 9847 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC2935 : runtimeArtifact.instructionPC 7677 = 9848 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC2936 : runtimeArtifact.instructionPC 7678 = 9851 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC2937 : runtimeArtifact.instructionPC 7679 = 9852 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC2938 : runtimeArtifact.instructionPC 7680 = 9854 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC2939 : runtimeArtifact.instructionPC 7681 = 9855 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC2940 : runtimeArtifact.instructionPC 7682 = 9856 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC2941 : runtimeArtifact.instructionPC 7683 = 9857 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC2942 : runtimeArtifact.instructionPC 7684 = 9858 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC2943 : runtimeArtifact.instructionPC 7685 = 9861 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC3921 : runtimeArtifact.instructionPC 623 = 880 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC3922 : runtimeArtifact.instructionPC 623 = 880 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC3923 : runtimeArtifact.instructionPC 623 = 880 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC3924 : runtimeArtifact.instructionPC 623 = 880 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC3925 : runtimeArtifact.instructionPC 623 = 880 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC3926 : runtimeArtifact.instructionPC 624 = 881 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC3927 : runtimeArtifact.instructionPC 625 = 884 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

@[simp] theorem earlyExtraPC3928 : runtimeArtifact.instructionPC 626 = 887 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl

end CycleSubmission.Global.Fast
