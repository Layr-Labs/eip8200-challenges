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
  [pushAt 485 2 2688,
   opAt 486 .MLOAD,
   pushAt 487 1 128,
   opAt 488 .EQ,
   pushAt 489 2 10435,
   opAt 490 .JUMPI]
def csFixedEntry4 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 485 2 2688,
   opAt 486 .MLOAD,
   pushAt 487 1 128,
   opAt 488 .EQ,
   pushAt 489 2 10435,
   opAt 490 .JUMPI,
   opAt 7982 .JUMPDEST]
/-- rarej: the eight-limb subtraction starts at the `s8` `JUMPDEST` (pc 4374), the target of the
square exit's carry continuation; the entry block falls into it. -/
def csFixedStep8_0 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 491 2 2336,
   opAt 492 .MLOAD,
   pushAt 493 1 224,
   opAt 494 .MLOAD,
   opAt 495 (.Dup ⟨0,by decide⟩),
   opAt 496 (.Dup ⟨2,by decide⟩),
   opAt 497 .SUB,
   pushAt 498 2 2016,
   opAt 499 .MSTORE,
   opAt 500 .GT]
def csFixedStep8_1 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 501 (.Dup ⟨0,by decide⟩),
   pushAt 502 1 192,
   opAt 503 .MLOAD,
   opAt 504 .ADD,
   opAt 505 (.Dup ⟨0,by decide⟩),
   pushAt 506 2 2304,
   opAt 507 .MLOAD,
   opAt 508 (.Dup ⟨1,by decide⟩),
   opAt 509 (.Dup ⟨1,by decide⟩),
   opAt 510 .SUB,
   pushAt 511 2 1984,
   opAt 512 .MSTORE,
   opAt 513 .LT,
   opAt 514 (.Swap ⟨1,by decide⟩),
   opAt 515 .GT,
   opAt 516 .OR]
def csFixedStep8_2 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 517 (.Dup ⟨0,by decide⟩),
   pushAt 518 1 160,
   opAt 519 .MLOAD,
   opAt 520 .ADD,
   opAt 521 (.Dup ⟨0,by decide⟩),
   pushAt 522 2 2272,
   opAt 523 .MLOAD,
   opAt 524 (.Dup ⟨1,by decide⟩),
   opAt 525 (.Dup ⟨1,by decide⟩),
   opAt 526 .SUB,
   pushAt 527 2 1952,
   opAt 528 .MSTORE,
   opAt 529 .LT,
   opAt 530 (.Swap ⟨1,by decide⟩),
   opAt 531 .GT,
   opAt 532 .OR]
def csFixedStep8_3 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 533 (.Dup ⟨0,by decide⟩),
   pushAt 534 1 128,
   opAt 535 .MLOAD,
   opAt 536 .ADD,
   opAt 537 (.Dup ⟨0,by decide⟩),
   pushAt 538 2 2240,
   opAt 539 .MLOAD,
   opAt 540 (.Dup ⟨1,by decide⟩),
   opAt 541 (.Dup ⟨1,by decide⟩),
   opAt 542 .SUB,
   pushAt 543 2 1920,
   opAt 544 .MSTORE,
   opAt 545 .LT,
   opAt 546 (.Swap ⟨1,by decide⟩),
   opAt 547 .GT,
   opAt 548 .OR]
def csFixedStep8_4 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 549 (.Dup ⟨0,by decide⟩),
   pushAt 550 1 96,
   opAt 551 .MLOAD,
   opAt 552 .ADD,
   opAt 553 (.Dup ⟨0,by decide⟩),
   pushAt 554 2 2208,
   opAt 555 .MLOAD,
   opAt 556 (.Dup ⟨1,by decide⟩),
   opAt 557 (.Dup ⟨1,by decide⟩),
   opAt 558 .SUB,
   pushAt 559 2 1888,
   opAt 560 .MSTORE,
   opAt 561 .LT,
   opAt 562 (.Swap ⟨1,by decide⟩),
   opAt 563 .GT,
   opAt 564 .OR]
def csFixedStep8_5 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 565 .JUMPDEST,
   opAt 566 (.Dup ⟨0,by decide⟩),
   pushAt 567 1 64,
   opAt 568 .MLOAD,
   opAt 569 .ADD,
   opAt 570 (.Dup ⟨0,by decide⟩),
   pushAt 571 2 2176,
   opAt 572 .MLOAD,
   opAt 573 (.Dup ⟨1,by decide⟩),
   opAt 574 (.Dup ⟨1,by decide⟩),
   opAt 575 .SUB,
   pushAt 576 2 1856,
   opAt 577 .MSTORE,
   opAt 578 .LT,
   opAt 579 (.Swap ⟨1,by decide⟩),
   opAt 580 .GT,
   opAt 581 .OR]
def csFixedStep8_6 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 582 (.Dup ⟨0,by decide⟩),
   pushAt 583 1 32,
   opAt 584 .MLOAD,
   opAt 585 .ADD,
   opAt 586 (.Dup ⟨0,by decide⟩),
   pushAt 587 2 2144,
   opAt 588 .MLOAD,
   opAt 589 (.Dup ⟨1,by decide⟩),
   opAt 590 (.Dup ⟨1,by decide⟩),
   opAt 591 .SUB,
   pushAt 592 2 1824,
   opAt 593 .MSTORE,
   opAt 594 .LT,
   opAt 595 (.Swap ⟨1,by decide⟩),
   opAt 596 .GT,
   opAt 597 .OR]
def csFixedStep8_7 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 598 (.Dup ⟨0,by decide⟩),
   pushAt 599 0 0,
   opAt 600 .MLOAD,
   opAt 601 .ADD,
   opAt 602 (.Dup ⟨0,by decide⟩),
   pushAt 603 2 2112,
   opAt 604 .MLOAD,
   opAt 605 (.Dup ⟨1,by decide⟩),
   opAt 606 (.Dup ⟨1,by decide⟩),
   opAt 607 .SUB,
   pushAt 608 2 1792,
   opAt 609 .MSTORE,
   opAt 610 .LT,
   opAt 611 (.Swap ⟨1,by decide⟩),
   opAt 612 .GT,
   opAt 613 .OR]
/-- Selection tail when `use ≠ 0` (`t ≥ m`): `JUMPI` to pc 4538, which copies the
difference block at `SUBB` (1792) to the destination and returns. -/
def csFixedTailSub : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 614 .ISZERO,
   pushAt 615 2 2080,
   opAt 616 .MLOAD,
   opAt 617 .OR,
   pushAt 618 2 890,
   opAt 619 .JUMPI,
   opAt 629 .JUMPDEST,
   pushAt 630 2 1792,
   pushAt 631 2 2688,
   opAt 632 .MLOAD,
   opAt 633 (.Swap ⟨1,by decide⟩),
   opAt 634 .MCOPY,
   opAt 635 .JUMP]
/-- Selection tail when `use = 0` (`t < m`): fall through the `JUMPI` and jump to the
shared copy block at pc 4527, which copies `t` (2112) to the destination and returns. -/
def csFixedTailKeep : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 614 .ISZERO,
   pushAt 615 2 2080,
   opAt 616 .MLOAD,
   opAt 617 .OR,
   pushAt 618 2 890,
   opAt 619 .JUMPI,
   pushAt 620 2 879,
   opAt 621 .JUMP,
   opAt 622 .JUMPDEST,
   pushAt 623 2 2112,
   pushAt 624 2 2688,
   opAt 625 .MLOAD,
   opAt 626 (.Swap ⟨1,by decide⟩),
   opAt 627 .MCOPY,
   opAt 628 .JUMP]
def csFixedStep4_0 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 7983 2 2208,
   opAt 7984 .MLOAD,
   pushAt 7985 1 96,
   opAt 7986 .MLOAD,
   opAt 7987 (.Dup ⟨0,by decide⟩),
   opAt 7988 (.Dup ⟨2,by decide⟩),
   opAt 7989 .SUB,
   pushAt 7990 2 1888,
   opAt 7991 .MSTORE,
   opAt 7992 .GT,
   pushAt 7993 2 802,
   opAt 7994 .JUMP]
def csFixedStep4_1 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 565 .JUMPDEST,
   opAt 566 (.Dup ⟨0,by decide⟩),
   pushAt 567 1 64,
   opAt 568 .MLOAD,
   opAt 569 .ADD,
   opAt 570 (.Dup ⟨0,by decide⟩),
   pushAt 571 2 2176,
   opAt 572 .MLOAD,
   opAt 573 (.Dup ⟨1,by decide⟩),
   opAt 574 (.Dup ⟨1,by decide⟩),
   opAt 575 .SUB,
   pushAt 576 2 1856,
   opAt 577 .MSTORE,
   opAt 578 .LT,
   opAt 579 (.Swap ⟨1,by decide⟩),
   opAt 580 .GT,
   opAt 581 .OR]
def csFixedStep4_2 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 582 (.Dup ⟨0,by decide⟩),
   pushAt 583 1 32,
   opAt 584 .MLOAD,
   opAt 585 .ADD,
   opAt 586 (.Dup ⟨0,by decide⟩),
   pushAt 587 2 2144,
   opAt 588 .MLOAD,
   opAt 589 (.Dup ⟨1,by decide⟩),
   opAt 590 (.Dup ⟨1,by decide⟩),
   opAt 591 .SUB,
   pushAt 592 2 1824,
   opAt 593 .MSTORE,
   opAt 594 .LT,
   opAt 595 (.Swap ⟨1,by decide⟩),
   opAt 596 .GT,
   opAt 597 .OR]
def csFixedStep4_3 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 598 (.Dup ⟨0,by decide⟩),
   pushAt 599 0 0,
   opAt 600 .MLOAD,
   opAt 601 .ADD,
   opAt 602 (.Dup ⟨0,by decide⟩),
   pushAt 603 2 2112,
   opAt 604 .MLOAD,
   opAt 605 (.Dup ⟨1,by decide⟩),
   opAt 606 (.Dup ⟨1,by decide⟩),
   opAt 607 .SUB,
   pushAt 608 2 1792,
   opAt 609 .MSTORE,
   opAt 610 .LT,
   opAt 611 (.Swap ⟨1,by decide⟩),
   opAt 612 .GT,
   opAt 613 .OR]
@[simp] theorem cycleAnchor : runtimeArtifact.instructionPC 7816 = 10216 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3777 : runtimeArtifact.instructionPC 480 = 681 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3778 : runtimeArtifact.instructionPC 620 = 875 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3779 : runtimeArtifact.instructionPC 621 = 878 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3787 : runtimeArtifact.instructionPC 622 = 879 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3788 : runtimeArtifact.instructionPC 622 = 879 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3789 : runtimeArtifact.instructionPC 622 = 879 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3790 : runtimeArtifact.instructionPC 622 = 879 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3791 : runtimeArtifact.instructionPC 622 = 879 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3792 : runtimeArtifact.instructionPC 622 = 879 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3793 : runtimeArtifact.instructionPC 623 = 880 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3794 : runtimeArtifact.instructionPC 624 = 883 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3795 : runtimeArtifact.instructionPC 625 = 886 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3796 : runtimeArtifact.instructionPC 626 = 887 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3797 : runtimeArtifact.instructionPC 627 = 888 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3798 : runtimeArtifact.instructionPC 627 = 888 := fixedPC3797
@[simp] theorem fixedPC3799 : runtimeArtifact.instructionPC 627 = 888 := fixedPC3797
@[simp] theorem fixedPC3800 : runtimeArtifact.instructionPC 628 = 889 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3801 : runtimeArtifact.instructionPC 629 = 890 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3802 : runtimeArtifact.instructionPC 630 = 891 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3803 : runtimeArtifact.instructionPC 631 = 894 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3804 : runtimeArtifact.instructionPC 632 = 897 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
/-! The rewritten conditional-subtraction dispatch occupies rows 3113..3119; its interior rows had
no pc certificates, so the block could not step. -/
@[simp] theorem fixedPC3114 : runtimeArtifact.instructionPC 481 = 682 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3115 : runtimeArtifact.instructionPC 482 = 685 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3116 : runtimeArtifact.instructionPC 483 = 686 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3117 : runtimeArtifact.instructionPC 484 = 689 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3118 : runtimeArtifact.instructionPC 485 = 692 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3119 : runtimeArtifact.instructionPC 486 = 695 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
/-- The four-limb landing of the rewritten conditional-subtraction dispatch. The old claim here named
pc 4371 through index 3273, which is now an `MCOPY` at 4392, so it was false and cost a `whnf` runaway
rather than an honest error. -/
@[simp] theorem fixedPC3009 : runtimeArtifact.instructionPC 7822 = 10225 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedJump3984 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10435 = true := by
  have h : runtimeArtifact.instructionPC 7982 = 10435 := by
    rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
    rfl
  simpa only [h] using CycleSubmission.Global.Binding.jumpDest 7982 (by rfl)
@[simp] theorem fixedPC3805 : runtimeArtifact.instructionPC 487 = 696 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3806 : runtimeArtifact.instructionPC 488 = 698 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3807 : runtimeArtifact.instructionPC 489 = 699 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3808 : runtimeArtifact.instructionPC 490 = 702 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPCs8 : runtimeArtifact.instructionPC 491 = 703 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3809 : runtimeArtifact.instructionPC 491 = 703 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3810 : runtimeArtifact.instructionPC 492 = 706 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3811 : runtimeArtifact.instructionPC 493 = 707 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3812 : runtimeArtifact.instructionPC 494 = 709 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3813 : runtimeArtifact.instructionPC 495 = 710 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3814 : runtimeArtifact.instructionPC 496 = 711 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3815 : runtimeArtifact.instructionPC 497 = 712 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3816 : runtimeArtifact.instructionPC 497 = 712 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3817 : runtimeArtifact.instructionPC 498 = 713 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3818 : runtimeArtifact.instructionPC 499 = 716 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3819 : runtimeArtifact.instructionPC 500 = 717 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3820 : runtimeArtifact.instructionPC 501 = 718 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3821 : runtimeArtifact.instructionPC 502 = 719 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3822 : runtimeArtifact.instructionPC 503 = 721 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3823 : runtimeArtifact.instructionPC 504 = 722 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3824 : runtimeArtifact.instructionPC 505 = 723 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3825 : runtimeArtifact.instructionPC 506 = 724 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3826 : runtimeArtifact.instructionPC 507 = 727 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3827 : runtimeArtifact.instructionPC 508 = 728 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3828 : runtimeArtifact.instructionPC 509 = 729 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3829 : runtimeArtifact.instructionPC 510 = 730 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3830 : runtimeArtifact.instructionPC 511 = 731 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3831 : runtimeArtifact.instructionPC 512 = 734 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3832 : runtimeArtifact.instructionPC 513 = 735 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3833 : runtimeArtifact.instructionPC 514 = 736 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3834 : runtimeArtifact.instructionPC 514 = 736 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3835 : runtimeArtifact.instructionPC 515 = 737 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3836 : runtimeArtifact.instructionPC 516 = 738 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3837 : runtimeArtifact.instructionPC 517 = 739 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3838 : runtimeArtifact.instructionPC 518 = 740 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3839 : runtimeArtifact.instructionPC 519 = 742 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3840 : runtimeArtifact.instructionPC 520 = 743 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3841 : runtimeArtifact.instructionPC 521 = 744 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3842 : runtimeArtifact.instructionPC 522 = 745 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3843 : runtimeArtifact.instructionPC 523 = 748 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3844 : runtimeArtifact.instructionPC 524 = 749 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3845 : runtimeArtifact.instructionPC 525 = 750 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3846 : runtimeArtifact.instructionPC 526 = 751 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3847 : runtimeArtifact.instructionPC 527 = 752 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3848 : runtimeArtifact.instructionPC 528 = 755 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3849 : runtimeArtifact.instructionPC 529 = 756 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3850 : runtimeArtifact.instructionPC 530 = 757 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3851 : runtimeArtifact.instructionPC 531 = 758 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3852 : runtimeArtifact.instructionPC 531 = 758 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3853 : runtimeArtifact.instructionPC 532 = 759 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3854 : runtimeArtifact.instructionPC 533 = 760 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3855 : runtimeArtifact.instructionPC 534 = 761 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3856 : runtimeArtifact.instructionPC 535 = 763 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3857 : runtimeArtifact.instructionPC 536 = 764 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3858 : runtimeArtifact.instructionPC 537 = 765 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3859 : runtimeArtifact.instructionPC 538 = 766 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3860 : runtimeArtifact.instructionPC 539 = 769 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3861 : runtimeArtifact.instructionPC 540 = 770 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3862 : runtimeArtifact.instructionPC 541 = 771 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3863 : runtimeArtifact.instructionPC 542 = 772 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3864 : runtimeArtifact.instructionPC 543 = 773 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3865 : runtimeArtifact.instructionPC 544 = 776 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3866 : runtimeArtifact.instructionPC 545 = 777 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3867 : runtimeArtifact.instructionPC 546 = 778 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3868 : runtimeArtifact.instructionPC 547 = 779 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3869 : runtimeArtifact.instructionPC 548 = 780 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3871 : runtimeArtifact.instructionPC 548 = 780 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3872 : runtimeArtifact.instructionPC 549 = 781 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3873 : runtimeArtifact.instructionPC 550 = 782 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3874 : runtimeArtifact.instructionPC 551 = 784 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3875 : runtimeArtifact.instructionPC 552 = 785 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3876 : runtimeArtifact.instructionPC 553 = 786 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3877 : runtimeArtifact.instructionPC 554 = 787 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3878 : runtimeArtifact.instructionPC 555 = 790 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3879 : runtimeArtifact.instructionPC 556 = 791 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3880 : runtimeArtifact.instructionPC 557 = 792 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3881 : runtimeArtifact.instructionPC 558 = 793 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3882 : runtimeArtifact.instructionPC 559 = 794 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3883 : runtimeArtifact.instructionPC 560 = 797 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3884 : runtimeArtifact.instructionPC 561 = 798 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3885 : runtimeArtifact.instructionPC 562 = 799 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3886 : runtimeArtifact.instructionPC 563 = 800 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3887 : runtimeArtifact.instructionPC 564 = 801 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3888 : runtimeArtifact.instructionPC 565 = 802 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3889 : runtimeArtifact.instructionPC 565 = 802 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedJump5133 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 802 = true := by
  have h : runtimeArtifact.instructionPC 565 = 802 := by
    rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
    rfl
  simpa only [h] using CycleSubmission.Global.Binding.jumpDest 565 (by rfl)
@[simp] theorem fixedPC3890 : runtimeArtifact.instructionPC 566 = 803 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3891 : runtimeArtifact.instructionPC 567 = 804 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3892 : runtimeArtifact.instructionPC 568 = 806 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3893 : runtimeArtifact.instructionPC 569 = 807 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3894 : runtimeArtifact.instructionPC 570 = 808 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3895 : runtimeArtifact.instructionPC 571 = 809 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3896 : runtimeArtifact.instructionPC 572 = 812 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3897 : runtimeArtifact.instructionPC 573 = 813 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3898 : runtimeArtifact.instructionPC 574 = 814 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3899 : runtimeArtifact.instructionPC 575 = 815 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3900 : runtimeArtifact.instructionPC 576 = 816 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3901 : runtimeArtifact.instructionPC 577 = 819 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3902 : runtimeArtifact.instructionPC 578 = 820 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3903 : runtimeArtifact.instructionPC 579 = 821 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3904 : runtimeArtifact.instructionPC 580 = 822 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3905 : runtimeArtifact.instructionPC 581 = 823 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3906 : runtimeArtifact.instructionPC 582 = 824 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3907 : runtimeArtifact.instructionPC 583 = 825 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3908 : runtimeArtifact.instructionPC 583 = 825 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3909 : runtimeArtifact.instructionPC 584 = 827 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3910 : runtimeArtifact.instructionPC 585 = 828 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3911 : runtimeArtifact.instructionPC 586 = 829 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3912 : runtimeArtifact.instructionPC 587 = 830 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3913 : runtimeArtifact.instructionPC 588 = 833 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3914 : runtimeArtifact.instructionPC 589 = 834 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3915 : runtimeArtifact.instructionPC 590 = 835 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3916 : runtimeArtifact.instructionPC 591 = 836 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3917 : runtimeArtifact.instructionPC 592 = 837 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3918 : runtimeArtifact.instructionPC 593 = 840 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3919 : runtimeArtifact.instructionPC 594 = 841 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3920 : runtimeArtifact.instructionPC 595 = 842 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3921 : runtimeArtifact.instructionPC 596 = 843 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3922 : runtimeArtifact.instructionPC 597 = 844 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3923 : runtimeArtifact.instructionPC 598 = 845 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3924 : runtimeArtifact.instructionPC 599 = 846 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3925 : runtimeArtifact.instructionPC 600 = 847 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3926 : runtimeArtifact.instructionPC 600 = 847 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3927 : runtimeArtifact.instructionPC 601 = 848 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3928 : runtimeArtifact.instructionPC 602 = 849 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3929 : runtimeArtifact.instructionPC 603 = 850 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3930 : runtimeArtifact.instructionPC 604 = 853 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3931 : runtimeArtifact.instructionPC 605 = 854 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3932 : runtimeArtifact.instructionPC 606 = 855 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3933 : runtimeArtifact.instructionPC 607 = 856 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3934 : runtimeArtifact.instructionPC 608 = 857 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3935 : runtimeArtifact.instructionPC 609 = 860 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3936 : runtimeArtifact.instructionPC 610 = 861 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3937 : runtimeArtifact.instructionPC 611 = 862 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3938 : runtimeArtifact.instructionPC 612 = 863 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3939 : runtimeArtifact.instructionPC 613 = 864 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3940 : runtimeArtifact.instructionPC 614 = 865 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3941 : runtimeArtifact.instructionPC 615 = 866 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3942 : runtimeArtifact.instructionPC 616 = 869 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3943 : runtimeArtifact.instructionPC 617 = 870 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3944 : runtimeArtifact.instructionPC 617 = 870 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3945 : runtimeArtifact.instructionPC 618 = 871 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3946 : runtimeArtifact.instructionPC 619 = 874 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3947 : runtimeArtifact.instructionPC 620 = 875 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3948 : runtimeArtifact.instructionPC 621 = 878 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3949 : runtimeArtifact.instructionPC 626 = 887 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3950 : runtimeArtifact.instructionPC 626 = 887 :=
  fixedPC3949
@[simp] theorem fixedPC3951 : runtimeArtifact.instructionPC 627 = 888 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3952 : runtimeArtifact.instructionPC 628 = 889 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3953 : runtimeArtifact.instructionPC 629 = 890 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3954 : runtimeArtifact.instructionPC 630 = 891 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3955 : runtimeArtifact.instructionPC 631 = 894 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3956 : runtimeArtifact.instructionPC 632 = 897 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC3957 : runtimeArtifact.instructionPC 633 = 898 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedJump5280 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10435 = true := by
  have h : runtimeArtifact.instructionPC 7982 = 10435 := by
    rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
    rfl
  simpa only [h] using CycleSubmission.Global.Binding.jumpDest 7982 (by rfl)
@[simp] theorem fixedPC4000 : runtimeArtifact.instructionPC 7822 = 10225 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC4001 : runtimeArtifact.instructionPC 7822 = 10225 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC4002 : runtimeArtifact.instructionPC 7841 = 10248 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC4003 : runtimeArtifact.instructionPC 7982 = 10435 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC4004 : runtimeArtifact.instructionPC 7983 = 10436 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC4005 : runtimeArtifact.instructionPC 7984 = 10439 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC4006 : runtimeArtifact.instructionPC 7985 = 10440 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC4007 : runtimeArtifact.instructionPC 7986 = 10442 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC4008 : runtimeArtifact.instructionPC 7987 = 10443 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC4009 : runtimeArtifact.instructionPC 7988 = 10444 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC4010 : runtimeArtifact.instructionPC 7989 = 10445 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC4011 : runtimeArtifact.instructionPC 7990 = 10446 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem fixedPC4012 : runtimeArtifact.instructionPC 7991 = 10449 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2883 : runtimeArtifact.instructionPC 7326 = 9658 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2884 : runtimeArtifact.instructionPC 7327 = 9659 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2885 : runtimeArtifact.instructionPC 7328 = 9660 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2886 : runtimeArtifact.instructionPC 7329 = 9661 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2888 : runtimeArtifact.instructionPC 7330 = 9662 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2889 : runtimeArtifact.instructionPC 7331 = 9663 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2890 : runtimeArtifact.instructionPC 7332 = 9664 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2891 : runtimeArtifact.instructionPC 7333 = 9667 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2892 : runtimeArtifact.instructionPC 7334 = 9668 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2893 : runtimeArtifact.instructionPC 7334 = 9668 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2894 : runtimeArtifact.instructionPC 7334 = 9668 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2895 : runtimeArtifact.instructionPC 7810 = 10206 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2896 : runtimeArtifact.instructionPC 7822 = 10225 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2930 : runtimeArtifact.instructionPC 7822 = 10225 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2931 : runtimeArtifact.instructionPC 7822 = 10225 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2932 : runtimeArtifact.instructionPC 7822 = 10225 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2933 : runtimeArtifact.instructionPC 7841 = 10248 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2934 : runtimeArtifact.instructionPC 7982 = 10435 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2935 : runtimeArtifact.instructionPC 7983 = 10436 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2936 : runtimeArtifact.instructionPC 7984 = 10439 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2937 : runtimeArtifact.instructionPC 7985 = 10440 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2938 : runtimeArtifact.instructionPC 7986 = 10442 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2939 : runtimeArtifact.instructionPC 7987 = 10443 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2940 : runtimeArtifact.instructionPC 7988 = 10444 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2941 : runtimeArtifact.instructionPC 7989 = 10445 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2942 : runtimeArtifact.instructionPC 7990 = 10446 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC2943 : runtimeArtifact.instructionPC 7991 = 10449 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC3921 : runtimeArtifact.instructionPC 622 = 879 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC3922 : runtimeArtifact.instructionPC 622 = 879 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC3923 : runtimeArtifact.instructionPC 622 = 879 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC3924 : runtimeArtifact.instructionPC 622 = 879 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC3925 : runtimeArtifact.instructionPC 622 = 879 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC3926 : runtimeArtifact.instructionPC 623 = 880 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC3927 : runtimeArtifact.instructionPC 624 = 883 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
@[simp] theorem earlyExtraPC3928 : runtimeArtifact.instructionPC 625 = 886 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]
  rfl
end CycleSubmission.Global.Fast
