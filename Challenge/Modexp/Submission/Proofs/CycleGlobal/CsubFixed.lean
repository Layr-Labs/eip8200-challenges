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
  [pushAt 483 2 2688,
   opAt 484 .MLOAD,
   pushAt 485 1 128,
   opAt 486 .EQ,
   pushAt 487 2 10531,
   opAt 488 .JUMPI]
def csFixedEntry4 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 483 2 2688,
   opAt 484 .MLOAD,
   pushAt 485 1 128,
   opAt 486 .EQ,
   pushAt 487 2 10531,
   opAt 488 .JUMPI,
   opAt 7969 .JUMPDEST]
/-- rarej: the eight-limb subtraction starts at the `s8` `JUMPDEST` (pc 4374), the target of the
square exit's carry continuation; the entry block falls into it. -/
def csFixedStep8_0 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 489 2 2336,
   opAt 490 .MLOAD,
   pushAt 491 1 224,
   opAt 492 .MLOAD,
   opAt 493 (.Dup ⟨0,by decide⟩),
   opAt 494 (.Dup ⟨2,by decide⟩),
   opAt 495 .SUB,
   pushAt 496 2 2016,
   opAt 497 .MSTORE,
   opAt 498 .GT]
def csFixedStep8_1 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 499 (.Dup ⟨0,by decide⟩),
   pushAt 500 1 192,
   opAt 501 .MLOAD,
   opAt 502 .ADD,
   opAt 503 (.Dup ⟨0,by decide⟩),
   pushAt 504 2 2304,
   opAt 505 .MLOAD,
   opAt 506 (.Dup ⟨1,by decide⟩),
   opAt 507 (.Dup ⟨1,by decide⟩),
   opAt 508 .SUB,
   pushAt 509 2 1984,
   opAt 510 .MSTORE,
   opAt 511 .LT,
   opAt 512 (.Swap ⟨1,by decide⟩),
   opAt 513 .GT,
   opAt 514 .OR]
def csFixedStep8_2 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 515 (.Dup ⟨0,by decide⟩),
   pushAt 516 1 160,
   opAt 517 .MLOAD,
   opAt 518 .ADD,
   opAt 519 (.Dup ⟨0,by decide⟩),
   pushAt 520 2 2272,
   opAt 521 .MLOAD,
   opAt 522 (.Dup ⟨1,by decide⟩),
   opAt 523 (.Dup ⟨1,by decide⟩),
   opAt 524 .SUB,
   pushAt 525 2 1952,
   opAt 526 .MSTORE,
   opAt 527 .LT,
   opAt 528 (.Swap ⟨1,by decide⟩),
   opAt 529 .GT,
   opAt 530 .OR]
def csFixedStep8_3 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 531 (.Dup ⟨0,by decide⟩),
   pushAt 532 1 128,
   opAt 533 .MLOAD,
   opAt 534 .ADD,
   opAt 535 (.Dup ⟨0,by decide⟩),
   pushAt 536 2 2240,
   opAt 537 .MLOAD,
   opAt 538 (.Dup ⟨1,by decide⟩),
   opAt 539 (.Dup ⟨1,by decide⟩),
   opAt 540 .SUB,
   pushAt 541 2 1920,
   opAt 542 .MSTORE,
   opAt 543 .LT,
   opAt 544 (.Swap ⟨1,by decide⟩),
   opAt 545 .GT,
   opAt 546 .OR]
def csFixedStep8_4 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 547 (.Dup ⟨0,by decide⟩),
   pushAt 548 1 96,
   opAt 549 .MLOAD,
   opAt 550 .ADD,
   opAt 551 (.Dup ⟨0,by decide⟩),
   pushAt 552 2 2208,
   opAt 553 .MLOAD,
   opAt 554 (.Dup ⟨1,by decide⟩),
   opAt 555 (.Dup ⟨1,by decide⟩),
   opAt 556 .SUB,
   pushAt 557 2 1888,
   opAt 558 .MSTORE,
   opAt 559 .LT,
   opAt 560 (.Swap ⟨1,by decide⟩),
   opAt 561 .GT,
   opAt 562 .OR]
def csFixedStep8_5 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 563 .JUMPDEST,
   opAt 564 (.Dup ⟨0,by decide⟩),
   pushAt 565 1 64,
   opAt 566 .MLOAD,
   opAt 567 .ADD,
   opAt 568 (.Dup ⟨0,by decide⟩),
   pushAt 569 2 2176,
   opAt 570 .MLOAD,
   opAt 571 (.Dup ⟨1,by decide⟩),
   opAt 572 (.Dup ⟨1,by decide⟩),
   opAt 573 .SUB,
   pushAt 574 2 1856,
   opAt 575 .MSTORE,
   opAt 576 .LT,
   opAt 577 (.Swap ⟨1,by decide⟩),
   opAt 578 .GT,
   opAt 579 .OR]
def csFixedStep8_6 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 580 (.Dup ⟨0,by decide⟩),
   pushAt 581 1 32,
   opAt 582 .MLOAD,
   opAt 583 .ADD,
   opAt 584 (.Dup ⟨0,by decide⟩),
   pushAt 585 2 2144,
   opAt 586 .MLOAD,
   opAt 587 (.Dup ⟨1,by decide⟩),
   opAt 588 (.Dup ⟨1,by decide⟩),
   opAt 589 .SUB,
   pushAt 590 2 1824,
   opAt 591 .MSTORE,
   opAt 592 .LT,
   opAt 593 (.Swap ⟨1,by decide⟩),
   opAt 594 .GT,
   opAt 595 .OR]
def csFixedStep8_7 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 596 (.Dup ⟨0,by decide⟩),
   pushAt 597 0 0,
   opAt 598 .MLOAD,
   opAt 599 .ADD,
   opAt 600 (.Dup ⟨0,by decide⟩),
   pushAt 601 2 2112,
   opAt 602 .MLOAD,
   opAt 603 (.Dup ⟨1,by decide⟩),
   opAt 604 (.Dup ⟨1,by decide⟩),
   opAt 605 .SUB,
   pushAt 606 2 1792,
   opAt 607 .MSTORE,
   opAt 608 .LT,
   opAt 609 (.Swap ⟨1,by decide⟩),
   opAt 610 .GT,
   opAt 611 .OR]
/-- Selection tail when `use ≠ 0` (`t ≥ m`): `JUMPI` to pc 4538, which copies the
difference block at `SUBB` (1792) to the destination and returns. -/
def csFixedTailSub : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 612 .ISZERO,
   pushAt 613 2 2080,
   opAt 614 .MLOAD,
   opAt 615 .OR,
   pushAt 616 2 888,
   opAt 617 .JUMPI,
   opAt 627 .JUMPDEST,
   pushAt 628 2 1792,
   pushAt 629 2 2688,
   opAt 630 .MLOAD,
   opAt 631 (.Swap ⟨1,by decide⟩),
   opAt 632 .MCOPY,
   opAt 633 .JUMP]
/-- Selection tail when `use = 0` (`t < m`): fall through the `JUMPI` and jump to the
shared copy block at pc 4527, which copies `t` (2112) to the destination and returns. -/
def csFixedTailKeep : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 612 .ISZERO,
   pushAt 613 2 2080,
   opAt 614 .MLOAD,
   opAt 615 .OR,
   pushAt 616 2 888,
   opAt 617 .JUMPI,
   pushAt 618 2 877,
   opAt 619 .JUMP,
   opAt 620 .JUMPDEST,
   pushAt 621 2 2112,
   pushAt 622 2 2688,
   opAt 623 .MLOAD,
   opAt 624 (.Swap ⟨1,by decide⟩),
   opAt 625 .MCOPY,
   opAt 626 .JUMP]
def csFixedStep4_0 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 7970 2 2208,
   opAt 7971 .MLOAD,
   pushAt 7972 1 96,
   opAt 7973 .MLOAD,
   opAt 7974 (.Dup ⟨0,by decide⟩),
   opAt 7975 (.Dup ⟨2,by decide⟩),
   opAt 7976 .SUB,
   pushAt 7977 2 1888,
   opAt 7978 .MSTORE,
   opAt 7979 .GT,
   pushAt 7980 2 800,
   opAt 7981 .JUMP]
def csFixedStep4_1 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 563 .JUMPDEST,
   opAt 564 (.Dup ⟨0,by decide⟩),
   pushAt 565 1 64,
   opAt 566 .MLOAD,
   opAt 567 .ADD,
   opAt 568 (.Dup ⟨0,by decide⟩),
   pushAt 569 2 2176,
   opAt 570 .MLOAD,
   opAt 571 (.Dup ⟨1,by decide⟩),
   opAt 572 (.Dup ⟨1,by decide⟩),
   opAt 573 .SUB,
   pushAt 574 2 1856,
   opAt 575 .MSTORE,
   opAt 576 .LT,
   opAt 577 (.Swap ⟨1,by decide⟩),
   opAt 578 .GT,
   opAt 579 .OR]
def csFixedStep4_2 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 580 (.Dup ⟨0,by decide⟩),
   pushAt 581 1 32,
   opAt 582 .MLOAD,
   opAt 583 .ADD,
   opAt 584 (.Dup ⟨0,by decide⟩),
   pushAt 585 2 2144,
   opAt 586 .MLOAD,
   opAt 587 (.Dup ⟨1,by decide⟩),
   opAt 588 (.Dup ⟨1,by decide⟩),
   opAt 589 .SUB,
   pushAt 590 2 1824,
   opAt 591 .MSTORE,
   opAt 592 .LT,
   opAt 593 (.Swap ⟨1,by decide⟩),
   opAt 594 .GT,
   opAt 595 .OR]
def csFixedStep4_3 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 596 (.Dup ⟨0,by decide⟩),
   pushAt 597 0 0,
   opAt 598 .MLOAD,
   opAt 599 .ADD,
   opAt 600 (.Dup ⟨0,by decide⟩),
   pushAt 601 2 2112,
   opAt 602 .MLOAD,
   opAt 603 (.Dup ⟨1,by decide⟩),
   opAt 604 (.Dup ⟨1,by decide⟩),
   opAt 605 .SUB,
   pushAt 606 2 1792,
   opAt 607 .MSTORE,
   opAt 608 .LT,
   opAt 609 (.Swap ⟨1,by decide⟩),
   opAt 610 .GT,
   opAt 611 .OR]
@[simp] theorem cycleAnchor : runtimeArtifact.instructionPC 7803 = 10312 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3777 : runtimeArtifact.instructionPC 478 = 679 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3778 : runtimeArtifact.instructionPC 618 = 873 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3779 : runtimeArtifact.instructionPC 619 = 876 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3787 : runtimeArtifact.instructionPC 620 = 877 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3788 : runtimeArtifact.instructionPC 620 = 877 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3789 : runtimeArtifact.instructionPC 620 = 877 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3790 : runtimeArtifact.instructionPC 620 = 877 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3791 : runtimeArtifact.instructionPC 620 = 877 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3792 : runtimeArtifact.instructionPC 620 = 877 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3793 : runtimeArtifact.instructionPC 621 = 878 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3794 : runtimeArtifact.instructionPC 622 = 881 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3795 : runtimeArtifact.instructionPC 623 = 884 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3796 : runtimeArtifact.instructionPC 624 = 885 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3797 : runtimeArtifact.instructionPC 625 = 886 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3798 : runtimeArtifact.instructionPC 625 = 886 := fixedPC3797
@[simp] theorem fixedPC3799 : runtimeArtifact.instructionPC 625 = 886 := fixedPC3797
@[simp] theorem fixedPC3800 : runtimeArtifact.instructionPC 626 = 887 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3801 : runtimeArtifact.instructionPC 627 = 888 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3802 : runtimeArtifact.instructionPC 628 = 889 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3803 : runtimeArtifact.instructionPC 629 = 892 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3804 : runtimeArtifact.instructionPC 630 = 895 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
/-! The rewritten conditional-subtraction dispatch occupies rows 3113..3119; its interior rows had
no pc certificates, so the block could not step. -/
@[simp] theorem fixedPC3114 : runtimeArtifact.instructionPC 479 = 680 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3115 : runtimeArtifact.instructionPC 480 = 683 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3116 : runtimeArtifact.instructionPC 481 = 684 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3117 : runtimeArtifact.instructionPC 482 = 687 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3118 : runtimeArtifact.instructionPC 483 = 690 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3119 : runtimeArtifact.instructionPC 484 = 693 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
/-- The four-limb landing of the rewritten conditional-subtraction dispatch. The old claim here named
pc 4371 through index 3273, which is now an `MCOPY` at 4392, so it was false and cost a `whnf` runaway
rather than an honest error. -/
@[simp] theorem fixedPC3009 : runtimeArtifact.instructionPC 7809 = 10321 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedJump3984 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10531 = true := by
  have h : runtimeArtifact.instructionPC 7969 = 10531 := by
    rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
    rfl
  simpa only [h] using CycleSubmission.Global.Binding.jumpDest 7969 (by rfl)
@[simp] theorem fixedPC3805 : runtimeArtifact.instructionPC 485 = 694 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3806 : runtimeArtifact.instructionPC 486 = 696 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3807 : runtimeArtifact.instructionPC 487 = 697 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3808 : runtimeArtifact.instructionPC 488 = 700 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPCs8 : runtimeArtifact.instructionPC 489 = 701 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3809 : runtimeArtifact.instructionPC 489 = 701 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3810 : runtimeArtifact.instructionPC 490 = 704 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3811 : runtimeArtifact.instructionPC 491 = 705 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3812 : runtimeArtifact.instructionPC 492 = 707 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3813 : runtimeArtifact.instructionPC 493 = 708 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3814 : runtimeArtifact.instructionPC 494 = 709 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3815 : runtimeArtifact.instructionPC 495 = 710 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3816 : runtimeArtifact.instructionPC 495 = 710 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3817 : runtimeArtifact.instructionPC 496 = 711 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3818 : runtimeArtifact.instructionPC 497 = 714 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3819 : runtimeArtifact.instructionPC 498 = 715 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3820 : runtimeArtifact.instructionPC 499 = 716 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3821 : runtimeArtifact.instructionPC 500 = 717 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3822 : runtimeArtifact.instructionPC 501 = 719 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3823 : runtimeArtifact.instructionPC 502 = 720 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3824 : runtimeArtifact.instructionPC 503 = 721 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3825 : runtimeArtifact.instructionPC 504 = 722 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3826 : runtimeArtifact.instructionPC 505 = 725 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3827 : runtimeArtifact.instructionPC 506 = 726 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3828 : runtimeArtifact.instructionPC 507 = 727 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3829 : runtimeArtifact.instructionPC 508 = 728 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3830 : runtimeArtifact.instructionPC 509 = 729 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3831 : runtimeArtifact.instructionPC 510 = 732 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3832 : runtimeArtifact.instructionPC 511 = 733 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3833 : runtimeArtifact.instructionPC 512 = 734 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3834 : runtimeArtifact.instructionPC 512 = 734 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3835 : runtimeArtifact.instructionPC 513 = 735 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3836 : runtimeArtifact.instructionPC 514 = 736 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3837 : runtimeArtifact.instructionPC 515 = 737 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3838 : runtimeArtifact.instructionPC 516 = 738 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3839 : runtimeArtifact.instructionPC 517 = 740 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3840 : runtimeArtifact.instructionPC 518 = 741 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3841 : runtimeArtifact.instructionPC 519 = 742 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3842 : runtimeArtifact.instructionPC 520 = 743 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3843 : runtimeArtifact.instructionPC 521 = 746 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3844 : runtimeArtifact.instructionPC 522 = 747 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3845 : runtimeArtifact.instructionPC 523 = 748 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3846 : runtimeArtifact.instructionPC 524 = 749 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3847 : runtimeArtifact.instructionPC 525 = 750 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3848 : runtimeArtifact.instructionPC 526 = 753 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3849 : runtimeArtifact.instructionPC 527 = 754 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3850 : runtimeArtifact.instructionPC 528 = 755 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3851 : runtimeArtifact.instructionPC 529 = 756 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3852 : runtimeArtifact.instructionPC 529 = 756 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3853 : runtimeArtifact.instructionPC 530 = 757 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3854 : runtimeArtifact.instructionPC 531 = 758 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3855 : runtimeArtifact.instructionPC 532 = 759 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3856 : runtimeArtifact.instructionPC 533 = 761 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3857 : runtimeArtifact.instructionPC 534 = 762 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3858 : runtimeArtifact.instructionPC 535 = 763 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3859 : runtimeArtifact.instructionPC 536 = 764 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3860 : runtimeArtifact.instructionPC 537 = 767 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3861 : runtimeArtifact.instructionPC 538 = 768 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3862 : runtimeArtifact.instructionPC 539 = 769 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3863 : runtimeArtifact.instructionPC 540 = 770 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3864 : runtimeArtifact.instructionPC 541 = 771 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3865 : runtimeArtifact.instructionPC 542 = 774 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3866 : runtimeArtifact.instructionPC 543 = 775 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3867 : runtimeArtifact.instructionPC 544 = 776 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3868 : runtimeArtifact.instructionPC 545 = 777 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3869 : runtimeArtifact.instructionPC 546 = 778 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3871 : runtimeArtifact.instructionPC 546 = 778 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3872 : runtimeArtifact.instructionPC 547 = 779 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3873 : runtimeArtifact.instructionPC 548 = 780 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3874 : runtimeArtifact.instructionPC 549 = 782 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3875 : runtimeArtifact.instructionPC 550 = 783 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3876 : runtimeArtifact.instructionPC 551 = 784 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3877 : runtimeArtifact.instructionPC 552 = 785 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3878 : runtimeArtifact.instructionPC 553 = 788 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3879 : runtimeArtifact.instructionPC 554 = 789 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3880 : runtimeArtifact.instructionPC 555 = 790 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3881 : runtimeArtifact.instructionPC 556 = 791 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3882 : runtimeArtifact.instructionPC 557 = 792 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3883 : runtimeArtifact.instructionPC 558 = 795 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3884 : runtimeArtifact.instructionPC 559 = 796 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3885 : runtimeArtifact.instructionPC 560 = 797 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3886 : runtimeArtifact.instructionPC 561 = 798 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3887 : runtimeArtifact.instructionPC 562 = 799 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3888 : runtimeArtifact.instructionPC 563 = 800 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3889 : runtimeArtifact.instructionPC 563 = 800 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedJump5133 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 800 = true := by
  have h : runtimeArtifact.instructionPC 563 = 800 := by
    rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
    rfl
  simpa only [h] using CycleSubmission.Global.Binding.jumpDest 563 (by rfl)
@[simp] theorem fixedPC3890 : runtimeArtifact.instructionPC 564 = 801 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3891 : runtimeArtifact.instructionPC 565 = 802 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3892 : runtimeArtifact.instructionPC 566 = 804 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3893 : runtimeArtifact.instructionPC 567 = 805 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3894 : runtimeArtifact.instructionPC 568 = 806 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3895 : runtimeArtifact.instructionPC 569 = 807 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3896 : runtimeArtifact.instructionPC 570 = 810 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3897 : runtimeArtifact.instructionPC 571 = 811 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3898 : runtimeArtifact.instructionPC 572 = 812 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3899 : runtimeArtifact.instructionPC 573 = 813 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3900 : runtimeArtifact.instructionPC 574 = 814 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3901 : runtimeArtifact.instructionPC 575 = 817 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3902 : runtimeArtifact.instructionPC 576 = 818 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3903 : runtimeArtifact.instructionPC 577 = 819 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3904 : runtimeArtifact.instructionPC 578 = 820 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3905 : runtimeArtifact.instructionPC 579 = 821 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3906 : runtimeArtifact.instructionPC 580 = 822 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3907 : runtimeArtifact.instructionPC 581 = 823 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3908 : runtimeArtifact.instructionPC 581 = 823 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3909 : runtimeArtifact.instructionPC 582 = 825 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3910 : runtimeArtifact.instructionPC 583 = 826 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3911 : runtimeArtifact.instructionPC 584 = 827 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3912 : runtimeArtifact.instructionPC 585 = 828 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3913 : runtimeArtifact.instructionPC 586 = 831 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3914 : runtimeArtifact.instructionPC 587 = 832 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3915 : runtimeArtifact.instructionPC 588 = 833 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3916 : runtimeArtifact.instructionPC 589 = 834 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3917 : runtimeArtifact.instructionPC 590 = 835 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3918 : runtimeArtifact.instructionPC 591 = 838 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3919 : runtimeArtifact.instructionPC 592 = 839 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3920 : runtimeArtifact.instructionPC 593 = 840 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3921 : runtimeArtifact.instructionPC 594 = 841 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3922 : runtimeArtifact.instructionPC 595 = 842 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3923 : runtimeArtifact.instructionPC 596 = 843 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3924 : runtimeArtifact.instructionPC 597 = 844 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3925 : runtimeArtifact.instructionPC 598 = 845 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3926 : runtimeArtifact.instructionPC 598 = 845 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3927 : runtimeArtifact.instructionPC 599 = 846 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3928 : runtimeArtifact.instructionPC 600 = 847 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3929 : runtimeArtifact.instructionPC 601 = 848 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3930 : runtimeArtifact.instructionPC 602 = 851 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3931 : runtimeArtifact.instructionPC 603 = 852 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3932 : runtimeArtifact.instructionPC 604 = 853 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3933 : runtimeArtifact.instructionPC 605 = 854 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3934 : runtimeArtifact.instructionPC 606 = 855 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3935 : runtimeArtifact.instructionPC 607 = 858 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3936 : runtimeArtifact.instructionPC 608 = 859 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3937 : runtimeArtifact.instructionPC 609 = 860 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3938 : runtimeArtifact.instructionPC 610 = 861 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3939 : runtimeArtifact.instructionPC 611 = 862 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3940 : runtimeArtifact.instructionPC 612 = 863 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3941 : runtimeArtifact.instructionPC 613 = 864 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3942 : runtimeArtifact.instructionPC 614 = 867 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3943 : runtimeArtifact.instructionPC 615 = 868 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3944 : runtimeArtifact.instructionPC 615 = 868 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3945 : runtimeArtifact.instructionPC 616 = 869 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3946 : runtimeArtifact.instructionPC 617 = 872 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3947 : runtimeArtifact.instructionPC 618 = 873 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3948 : runtimeArtifact.instructionPC 619 = 876 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3949 : runtimeArtifact.instructionPC 624 = 885 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3950 : runtimeArtifact.instructionPC 624 = 885 :=
  fixedPC3949
@[simp] theorem fixedPC3951 : runtimeArtifact.instructionPC 625 = 886 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3952 : runtimeArtifact.instructionPC 626 = 887 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3953 : runtimeArtifact.instructionPC 627 = 888 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3954 : runtimeArtifact.instructionPC 628 = 889 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3955 : runtimeArtifact.instructionPC 629 = 892 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3956 : runtimeArtifact.instructionPC 630 = 895 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3957 : runtimeArtifact.instructionPC 631 = 896 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedJump5280 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10531 = true := by
  have h : runtimeArtifact.instructionPC 7969 = 10531 := by
    rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
    rfl
  simpa only [h] using CycleSubmission.Global.Binding.jumpDest 7969 (by rfl)
@[simp] theorem fixedPC4000 : runtimeArtifact.instructionPC 7809 = 10321 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC4001 : runtimeArtifact.instructionPC 7809 = 10321 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC4002 : runtimeArtifact.instructionPC 7828 = 10344 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC4003 : runtimeArtifact.instructionPC 7969 = 10531 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC4004 : runtimeArtifact.instructionPC 7970 = 10532 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC4005 : runtimeArtifact.instructionPC 7971 = 10535 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC4006 : runtimeArtifact.instructionPC 7972 = 10536 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC4007 : runtimeArtifact.instructionPC 7973 = 10538 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC4008 : runtimeArtifact.instructionPC 7974 = 10539 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC4009 : runtimeArtifact.instructionPC 7975 = 10540 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC4010 : runtimeArtifact.instructionPC 7976 = 10541 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC4011 : runtimeArtifact.instructionPC 7977 = 10542 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC4012 : runtimeArtifact.instructionPC 7978 = 10545 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2883 : runtimeArtifact.instructionPC 7317 = 9701 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2884 : runtimeArtifact.instructionPC 7318 = 9702 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2885 : runtimeArtifact.instructionPC 7319 = 9703 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2886 : runtimeArtifact.instructionPC 7320 = 9704 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2888 : runtimeArtifact.instructionPC 7321 = 9705 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2889 : runtimeArtifact.instructionPC 7322 = 9706 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2890 : runtimeArtifact.instructionPC 7323 = 9707 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2891 : runtimeArtifact.instructionPC 7324 = 9710 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2892 : runtimeArtifact.instructionPC 7325 = 9711 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2893 : runtimeArtifact.instructionPC 7325 = 9711 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2894 : runtimeArtifact.instructionPC 7325 = 9711 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2895 : runtimeArtifact.instructionPC 7797 = 10302 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2896 : runtimeArtifact.instructionPC 7809 = 10321 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2930 : runtimeArtifact.instructionPC 7809 = 10321 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2931 : runtimeArtifact.instructionPC 7809 = 10321 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2932 : runtimeArtifact.instructionPC 7809 = 10321 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2933 : runtimeArtifact.instructionPC 7828 = 10344 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2934 : runtimeArtifact.instructionPC 7969 = 10531 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2935 : runtimeArtifact.instructionPC 7970 = 10532 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2936 : runtimeArtifact.instructionPC 7971 = 10535 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2937 : runtimeArtifact.instructionPC 7972 = 10536 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2938 : runtimeArtifact.instructionPC 7973 = 10538 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2939 : runtimeArtifact.instructionPC 7974 = 10539 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2940 : runtimeArtifact.instructionPC 7975 = 10540 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2941 : runtimeArtifact.instructionPC 7976 = 10541 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2942 : runtimeArtifact.instructionPC 7977 = 10542 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2943 : runtimeArtifact.instructionPC 7978 = 10545 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC3921 : runtimeArtifact.instructionPC 620 = 877 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC3922 : runtimeArtifact.instructionPC 620 = 877 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC3923 : runtimeArtifact.instructionPC 620 = 877 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC3924 : runtimeArtifact.instructionPC 620 = 877 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC3925 : runtimeArtifact.instructionPC 620 = 877 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC3926 : runtimeArtifact.instructionPC 621 = 878 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC3927 : runtimeArtifact.instructionPC 622 = 881 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC3928 : runtimeArtifact.instructionPC 623 = 884 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
end CycleSubmission.Global.Fast
