import Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
namespace Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs

private theorem instructionPC_add
    (p : Challenge.EvmProof.ProgramArtifact) (base count : Nat) :
    p.instructionPC (base + count) = p.instructionPC base +
      (YulEvmCompiler.assembleBytes ((p.instructions.drop base).take count)).length := by
  simp only [Challenge.EvmProof.ProgramArtifact.instructionPC, List.take_add,
    YulEvmCompiler.assembleBytes_append, List.length_append]


@[simp] theorem pc2653 : Artifact.submissionArtifact.instructionPC 2655 = 3496 := by rfl
@[simp] theorem pc2654 : Artifact.submissionArtifact.instructionPC 2656 = 3497 := by
  calc
    Artifact.submissionArtifact.instructionPC 2656 =
        Artifact.submissionArtifact.instructionPC 2655 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2655).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2655 1
    _ = 3497 := by
      rw [pc2653]
      rfl
@[simp] theorem pc2655 : Artifact.submissionArtifact.instructionPC 2657 = 3498 := by
  calc
    Artifact.submissionArtifact.instructionPC 2657 =
        Artifact.submissionArtifact.instructionPC 2656 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2656).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2656 1
    _ = 3498 := by
      rw [pc2654]
      rfl
@[simp] theorem pc2656 : Artifact.submissionArtifact.instructionPC 2658 = 3499 := by
  calc
    Artifact.submissionArtifact.instructionPC 2658 =
        Artifact.submissionArtifact.instructionPC 2657 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2657).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2657 1
    _ = 3499 := by
      rw [pc2655]
      rfl
@[simp] theorem pc2657 : Artifact.submissionArtifact.instructionPC 2659 = 3500 := by
  calc
    Artifact.submissionArtifact.instructionPC 2659 =
        Artifact.submissionArtifact.instructionPC 2658 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2658).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2658 1
    _ = 3500 := by
      rw [pc2656]
      rfl
@[simp] theorem pc2658 : Artifact.submissionArtifact.instructionPC 2660 = 3501 := by
  calc
    Artifact.submissionArtifact.instructionPC 2660 =
        Artifact.submissionArtifact.instructionPC 2659 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2659).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2659 1
    _ = 3501 := by
      rw [pc2657]
      rfl
@[simp] theorem pc2659 : Artifact.submissionArtifact.instructionPC 2661 = 3502 := by
  calc
    Artifact.submissionArtifact.instructionPC 2661 =
        Artifact.submissionArtifact.instructionPC 2660 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2660).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2660 1
    _ = 3502 := by
      rw [pc2658]
      rfl
@[simp] theorem pc2660 : Artifact.submissionArtifact.instructionPC 2662 = 3504 := by
  calc
    Artifact.submissionArtifact.instructionPC 2662 =
        Artifact.submissionArtifact.instructionPC 2661 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2661).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2661 1
    _ = 3504 := by
      rw [pc2659]
      rfl
@[simp] theorem pc2661 : Artifact.submissionArtifact.instructionPC 2663 = 3505 := by
  calc
    Artifact.submissionArtifact.instructionPC 2663 =
        Artifact.submissionArtifact.instructionPC 2662 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2662).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2662 1
    _ = 3505 := by
      rw [pc2660]
      rfl
@[simp] theorem pc2662 : Artifact.submissionArtifact.instructionPC 2664 = 3506 := by
  calc
    Artifact.submissionArtifact.instructionPC 2664 =
        Artifact.submissionArtifact.instructionPC 2663 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2663).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2663 1
    _ = 3506 := by
      rw [pc2661]
      rfl
@[simp] theorem pc2663 : Artifact.submissionArtifact.instructionPC 2665 = 3507 := by
  calc
    Artifact.submissionArtifact.instructionPC 2665 =
        Artifact.submissionArtifact.instructionPC 2664 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2664).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2664 1
    _ = 3507 := by
      rw [pc2662]
      rfl
@[simp] theorem pc2664 : Artifact.submissionArtifact.instructionPC 2666 = 3510 := by
  calc
    Artifact.submissionArtifact.instructionPC 2666 =
        Artifact.submissionArtifact.instructionPC 2665 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2665).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2665 1
    _ = 3510 := by
      rw [pc2663]
      rfl
@[simp] theorem pc2665 : Artifact.submissionArtifact.instructionPC 2667 = 3511 := by
  calc
    Artifact.submissionArtifact.instructionPC 2667 =
        Artifact.submissionArtifact.instructionPC 2666 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2666).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2666 1
    _ = 3511 := by
      rw [pc2664]
      rfl
@[simp] theorem pc2666 : Artifact.submissionArtifact.instructionPC 2668 = 3512 := by
  calc
    Artifact.submissionArtifact.instructionPC 2668 =
        Artifact.submissionArtifact.instructionPC 2667 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2667).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2667 1
    _ = 3512 := by
      rw [pc2665]
      rfl
@[simp] theorem pc2667 : Artifact.submissionArtifact.instructionPC 2669 = 3514 := by
  calc
    Artifact.submissionArtifact.instructionPC 2669 =
        Artifact.submissionArtifact.instructionPC 2668 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2668).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2668 1
    _ = 3514 := by
      rw [pc2666]
      rfl
@[simp] theorem pc2668 : Artifact.submissionArtifact.instructionPC 2670 = 3517 := by
  calc
    Artifact.submissionArtifact.instructionPC 2670 =
        Artifact.submissionArtifact.instructionPC 2669 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2669).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2669 1
    _ = 3517 := by
      rw [pc2667]
      rfl
@[simp] theorem pc2669 : Artifact.submissionArtifact.instructionPC 2671 = 3518 := by
  calc
    Artifact.submissionArtifact.instructionPC 2671 =
        Artifact.submissionArtifact.instructionPC 2670 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2670).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2670 1
    _ = 3518 := by
      rw [pc2668]
      rfl
@[simp] theorem pc2670 : Artifact.submissionArtifact.instructionPC 2672 = 3519 := by
  calc
    Artifact.submissionArtifact.instructionPC 2672 =
        Artifact.submissionArtifact.instructionPC 2671 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2671).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2671 1
    _ = 3519 := by
      rw [pc2669]
      rfl
@[simp] theorem pc2671 : Artifact.submissionArtifact.instructionPC 2673 = 3521 := by
  calc
    Artifact.submissionArtifact.instructionPC 2673 =
        Artifact.submissionArtifact.instructionPC 2672 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2672).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2672 1
    _ = 3521 := by
      rw [pc2670]
      rfl
@[simp] theorem pc2672 : Artifact.submissionArtifact.instructionPC 2674 = 3524 := by
  calc
    Artifact.submissionArtifact.instructionPC 2674 =
        Artifact.submissionArtifact.instructionPC 2673 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2673).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2673 1
    _ = 3524 := by
      rw [pc2671]
      rfl
@[simp] theorem pc2673 : Artifact.submissionArtifact.instructionPC 2675 = 3525 := by
  calc
    Artifact.submissionArtifact.instructionPC 2675 =
        Artifact.submissionArtifact.instructionPC 2674 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2674).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2674 1
    _ = 3525 := by
      rw [pc2672]
      rfl
@[simp] theorem pc2674 : Artifact.submissionArtifact.instructionPC 2676 = 3526 := by
  calc
    Artifact.submissionArtifact.instructionPC 2676 =
        Artifact.submissionArtifact.instructionPC 2675 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2675).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2675 1
    _ = 3526 := by
      rw [pc2673]
      rfl
@[simp] theorem pc2675 : Artifact.submissionArtifact.instructionPC 2677 = 3529 := by
  calc
    Artifact.submissionArtifact.instructionPC 2677 =
        Artifact.submissionArtifact.instructionPC 2676 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2676).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2676 1
    _ = 3529 := by
      rw [pc2674]
      rfl
@[simp] theorem pc2676 : Artifact.submissionArtifact.instructionPC 2678 = 3530 := by
  calc
    Artifact.submissionArtifact.instructionPC 2678 =
        Artifact.submissionArtifact.instructionPC 2677 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2677).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2677 1
    _ = 3530 := by
      rw [pc2675]
      rfl
@[simp] theorem pc2677 : Artifact.submissionArtifact.instructionPC 2679 = 3533 := by
  calc
    Artifact.submissionArtifact.instructionPC 2679 =
        Artifact.submissionArtifact.instructionPC 2678 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2678).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2678 1
    _ = 3533 := by
      rw [pc2676]
      rfl
@[simp] theorem pc2678 : Artifact.submissionArtifact.instructionPC 2680 = 3536 := by
  calc
    Artifact.submissionArtifact.instructionPC 2680 =
        Artifact.submissionArtifact.instructionPC 2679 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2679).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2679 1
    _ = 3536 := by
      rw [pc2677]
      rfl
@[simp] theorem pc2679 : Artifact.submissionArtifact.instructionPC 2681 = 3539 := by
  calc
    Artifact.submissionArtifact.instructionPC 2681 =
        Artifact.submissionArtifact.instructionPC 2680 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2680).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2680 1
    _ = 3539 := by
      rw [pc2678]
      rfl
@[simp] theorem pc2680 : Artifact.submissionArtifact.instructionPC 2682 = 3540 := by
  calc
    Artifact.submissionArtifact.instructionPC 2682 =
        Artifact.submissionArtifact.instructionPC 2681 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2681).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2681 1
    _ = 3540 := by
      rw [pc2679]
      rfl
@[simp] theorem pc2681 : Artifact.submissionArtifact.instructionPC 2683 = 3541 := by
  calc
    Artifact.submissionArtifact.instructionPC 2683 =
        Artifact.submissionArtifact.instructionPC 2682 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2682).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2682 1
    _ = 3541 := by
      rw [pc2680]
      rfl
@[simp] theorem pc2682 : Artifact.submissionArtifact.instructionPC 2684 = 3544 := by
  calc
    Artifact.submissionArtifact.instructionPC 2684 =
        Artifact.submissionArtifact.instructionPC 2683 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2683).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2683 1
    _ = 3544 := by
      rw [pc2681]
      rfl
@[simp] theorem pc2683 : Artifact.submissionArtifact.instructionPC 2685 = 3545 := by
  calc
    Artifact.submissionArtifact.instructionPC 2685 =
        Artifact.submissionArtifact.instructionPC 2684 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2684).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2684 1
    _ = 3545 := by
      rw [pc2682]
      rfl
@[simp] theorem pc2684 : Artifact.submissionArtifact.instructionPC 2686 = 3546 := by
  calc
    Artifact.submissionArtifact.instructionPC 2686 =
        Artifact.submissionArtifact.instructionPC 2685 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2685).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2685 1
    _ = 3546 := by
      rw [pc2683]
      rfl
@[simp] theorem pc2685 : Artifact.submissionArtifact.instructionPC 2687 = 3548 := by
  calc
    Artifact.submissionArtifact.instructionPC 2687 =
        Artifact.submissionArtifact.instructionPC 2686 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2686).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2686 1
    _ = 3548 := by
      rw [pc2684]
      rfl
@[simp] theorem pc2686 : Artifact.submissionArtifact.instructionPC 2688 = 3551 := by
  calc
    Artifact.submissionArtifact.instructionPC 2688 =
        Artifact.submissionArtifact.instructionPC 2687 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2687).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2687 1
    _ = 3551 := by
      rw [pc2685]
      rfl
@[simp] theorem pc2687 : Artifact.submissionArtifact.instructionPC 2689 = 3552 := by
  calc
    Artifact.submissionArtifact.instructionPC 2689 =
        Artifact.submissionArtifact.instructionPC 2688 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2688).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2688 1
    _ = 3552 := by
      rw [pc2686]
      rfl
@[simp] theorem pc2688 : Artifact.submissionArtifact.instructionPC 2690 = 3553 := by
  calc
    Artifact.submissionArtifact.instructionPC 2690 =
        Artifact.submissionArtifact.instructionPC 2689 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2689).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2689 1
    _ = 3553 := by
      rw [pc2687]
      rfl
@[simp] theorem pc2689 : Artifact.submissionArtifact.instructionPC 2691 = 3554 := by
  calc
    Artifact.submissionArtifact.instructionPC 2691 =
        Artifact.submissionArtifact.instructionPC 2690 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2690).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2690 1
    _ = 3554 := by
      rw [pc2688]
      rfl
@[simp] theorem pc2690 : Artifact.submissionArtifact.instructionPC 2692 = 3555 := by
  calc
    Artifact.submissionArtifact.instructionPC 2692 =
        Artifact.submissionArtifact.instructionPC 2691 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2691).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2691 1
    _ = 3555 := by
      rw [pc2689]
      rfl
@[simp] theorem pc2691 : Artifact.submissionArtifact.instructionPC 2693 = 3556 := by
  calc
    Artifact.submissionArtifact.instructionPC 2693 =
        Artifact.submissionArtifact.instructionPC 2692 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2692).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2692 1
    _ = 3556 := by
      rw [pc2690]
      rfl
@[simp] theorem pc2692 : Artifact.submissionArtifact.instructionPC 2694 = 3557 := by
  calc
    Artifact.submissionArtifact.instructionPC 2694 =
        Artifact.submissionArtifact.instructionPC 2693 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2693).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2693 1
    _ = 3557 := by
      rw [pc2691]
      rfl
@[simp] theorem pc2693 : Artifact.submissionArtifact.instructionPC 2695 = 3558 := by
  calc
    Artifact.submissionArtifact.instructionPC 2695 =
        Artifact.submissionArtifact.instructionPC 2694 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2694).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2694 1
    _ = 3558 := by
      rw [pc2692]
      rfl
@[simp] theorem pc2694 : Artifact.submissionArtifact.instructionPC 2696 = 3559 := by
  calc
    Artifact.submissionArtifact.instructionPC 2696 =
        Artifact.submissionArtifact.instructionPC 2695 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2695).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2695 1
    _ = 3559 := by
      rw [pc2693]
      rfl
@[simp] theorem pc2695 : Artifact.submissionArtifact.instructionPC 2697 = 3560 := by
  calc
    Artifact.submissionArtifact.instructionPC 2697 =
        Artifact.submissionArtifact.instructionPC 2696 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2696).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2696 1
    _ = 3560 := by
      rw [pc2694]
      rfl
@[simp] theorem pc2696 : Artifact.submissionArtifact.instructionPC 2698 = 3561 := by
  calc
    Artifact.submissionArtifact.instructionPC 2698 =
        Artifact.submissionArtifact.instructionPC 2697 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2697).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2697 1
    _ = 3561 := by
      rw [pc2695]
      rfl
@[simp] theorem pc2697 : Artifact.submissionArtifact.instructionPC 2699 = 3562 := by
  calc
    Artifact.submissionArtifact.instructionPC 2699 =
        Artifact.submissionArtifact.instructionPC 2698 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2698).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2698 1
    _ = 3562 := by
      rw [pc2696]
      rfl
@[simp] theorem pc2698 : Artifact.submissionArtifact.instructionPC 2700 = 3563 := by
  calc
    Artifact.submissionArtifact.instructionPC 2700 =
        Artifact.submissionArtifact.instructionPC 2699 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2699).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2699 1
    _ = 3563 := by
      rw [pc2697]
      rfl
@[simp] theorem pc2699 : Artifact.submissionArtifact.instructionPC 2701 = 3564 := by
  calc
    Artifact.submissionArtifact.instructionPC 2701 =
        Artifact.submissionArtifact.instructionPC 2700 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2700).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2700 1
    _ = 3564 := by
      rw [pc2698]
      rfl
@[simp] theorem pc2700 : Artifact.submissionArtifact.instructionPC 2702 = 3567 := by
  calc
    Artifact.submissionArtifact.instructionPC 2702 =
        Artifact.submissionArtifact.instructionPC 2701 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2701).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2701 1
    _ = 3567 := by
      rw [pc2699]
      rfl
@[simp] theorem pc2701 : Artifact.submissionArtifact.instructionPC 2703 = 3568 := by
  calc
    Artifact.submissionArtifact.instructionPC 2703 =
        Artifact.submissionArtifact.instructionPC 2702 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2702).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2702 1
    _ = 3568 := by
      rw [pc2700]
      rfl
@[simp] theorem pc2702 : Artifact.submissionArtifact.instructionPC 2704 = 3569 := by
  calc
    Artifact.submissionArtifact.instructionPC 2704 =
        Artifact.submissionArtifact.instructionPC 2703 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2703).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2703 1
    _ = 3569 := by
      rw [pc2701]
      rfl
@[simp] theorem pc2703 : Artifact.submissionArtifact.instructionPC 2705 = 3570 := by
  calc
    Artifact.submissionArtifact.instructionPC 2705 =
        Artifact.submissionArtifact.instructionPC 2704 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2704).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2704 1
    _ = 3570 := by
      rw [pc2702]
      rfl
@[simp] theorem pc2704 : Artifact.submissionArtifact.instructionPC 2706 = 3571 := by
  calc
    Artifact.submissionArtifact.instructionPC 2706 =
        Artifact.submissionArtifact.instructionPC 2705 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2705).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2705 1
    _ = 3571 := by
      rw [pc2703]
      rfl
@[simp] theorem pc2705 : Artifact.submissionArtifact.instructionPC 2707 = 3574 := by
  calc
    Artifact.submissionArtifact.instructionPC 2707 =
        Artifact.submissionArtifact.instructionPC 2706 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2706).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2706 1
    _ = 3574 := by
      rw [pc2704]
      rfl
@[simp] theorem pc2706 : Artifact.submissionArtifact.instructionPC 2708 = 3575 := by
  calc
    Artifact.submissionArtifact.instructionPC 2708 =
        Artifact.submissionArtifact.instructionPC 2707 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2707).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2707 1
    _ = 3575 := by
      rw [pc2705]
      rfl
@[simp] theorem pc2707 : Artifact.submissionArtifact.instructionPC 2709 = 3577 := by
  calc
    Artifact.submissionArtifact.instructionPC 2709 =
        Artifact.submissionArtifact.instructionPC 2708 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2708).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2708 1
    _ = 3577 := by
      rw [pc2706]
      rfl
@[simp] theorem pc2708 : Artifact.submissionArtifact.instructionPC 2710 = 3578 := by
  calc
    Artifact.submissionArtifact.instructionPC 2710 =
        Artifact.submissionArtifact.instructionPC 2709 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2709).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2709 1
    _ = 3578 := by
      rw [pc2707]
      rfl
@[simp] theorem pc2709 : Artifact.submissionArtifact.instructionPC 2711 = 3579 := by
  calc
    Artifact.submissionArtifact.instructionPC 2711 =
        Artifact.submissionArtifact.instructionPC 2710 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2710).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2710 1
    _ = 3579 := by
      rw [pc2708]
      rfl
@[simp] theorem pc2710 : Artifact.submissionArtifact.instructionPC 2712 = 3582 := by
  calc
    Artifact.submissionArtifact.instructionPC 2712 =
        Artifact.submissionArtifact.instructionPC 2711 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2711).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2711 1
    _ = 3582 := by
      rw [pc2709]
      rfl
@[simp] theorem pc2711 : Artifact.submissionArtifact.instructionPC 2713 = 3583 := by
  calc
    Artifact.submissionArtifact.instructionPC 2713 =
        Artifact.submissionArtifact.instructionPC 2712 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2712).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2712 1
    _ = 3583 := by
      rw [pc2710]
      rfl
@[simp] theorem pc2712 : Artifact.submissionArtifact.instructionPC 2714 = 3584 := by
  calc
    Artifact.submissionArtifact.instructionPC 2714 =
        Artifact.submissionArtifact.instructionPC 2713 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2713).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2713 1
    _ = 3584 := by
      rw [pc2711]
      rfl
@[simp] theorem pc2713 : Artifact.submissionArtifact.instructionPC 2715 = 3585 := by
  calc
    Artifact.submissionArtifact.instructionPC 2715 =
        Artifact.submissionArtifact.instructionPC 2714 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2714).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2714 1
    _ = 3585 := by
      rw [pc2712]
      rfl
@[simp] theorem pc2714 : Artifact.submissionArtifact.instructionPC 2716 = 3586 := by
  calc
    Artifact.submissionArtifact.instructionPC 2716 =
        Artifact.submissionArtifact.instructionPC 2715 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2715).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2715 1
    _ = 3586 := by
      rw [pc2713]
      rfl
@[simp] theorem pc2715 : Artifact.submissionArtifact.instructionPC 2717 = 3587 := by
  calc
    Artifact.submissionArtifact.instructionPC 2717 =
        Artifact.submissionArtifact.instructionPC 2716 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2716).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2716 1
    _ = 3587 := by
      rw [pc2714]
      rfl
@[simp] theorem pc2716 : Artifact.submissionArtifact.instructionPC 2718 = 3588 := by
  calc
    Artifact.submissionArtifact.instructionPC 2718 =
        Artifact.submissionArtifact.instructionPC 2717 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2717).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2717 1
    _ = 3588 := by
      rw [pc2715]
      rfl
@[simp] theorem pc2717 : Artifact.submissionArtifact.instructionPC 2719 = 3589 := by
  calc
    Artifact.submissionArtifact.instructionPC 2719 =
        Artifact.submissionArtifact.instructionPC 2718 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2718).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2718 1
    _ = 3589 := by
      rw [pc2716]
      rfl
@[simp] theorem pc2718 : Artifact.submissionArtifact.instructionPC 2720 = 3590 := by
  calc
    Artifact.submissionArtifact.instructionPC 2720 =
        Artifact.submissionArtifact.instructionPC 2719 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2719).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2719 1
    _ = 3590 := by
      rw [pc2717]
      rfl
@[simp] theorem pc2719 : Artifact.submissionArtifact.instructionPC 2721 = 3591 := by
  calc
    Artifact.submissionArtifact.instructionPC 2721 =
        Artifact.submissionArtifact.instructionPC 2720 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2720).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2720 1
    _ = 3591 := by
      rw [pc2718]
      rfl
@[simp] theorem pc2720 : Artifact.submissionArtifact.instructionPC 2722 = 3592 := by
  calc
    Artifact.submissionArtifact.instructionPC 2722 =
        Artifact.submissionArtifact.instructionPC 2721 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2721).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2721 1
    _ = 3592 := by
      rw [pc2719]
      rfl
@[simp] theorem pc2721 : Artifact.submissionArtifact.instructionPC 2723 = 3593 := by
  calc
    Artifact.submissionArtifact.instructionPC 2723 =
        Artifact.submissionArtifact.instructionPC 2722 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2722).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2722 1
    _ = 3593 := by
      rw [pc2720]
      rfl
@[simp] theorem pc2722 : Artifact.submissionArtifact.instructionPC 2724 = 3594 := by
  calc
    Artifact.submissionArtifact.instructionPC 2724 =
        Artifact.submissionArtifact.instructionPC 2723 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2723).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2723 1
    _ = 3594 := by
      rw [pc2721]
      rfl
@[simp] theorem pc2723 : Artifact.submissionArtifact.instructionPC 2725 = 3597 := by
  calc
    Artifact.submissionArtifact.instructionPC 2725 =
        Artifact.submissionArtifact.instructionPC 2724 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2724).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2724 1
    _ = 3597 := by
      rw [pc2722]
      rfl
@[simp] theorem pc2724 : Artifact.submissionArtifact.instructionPC 2726 = 3598 := by
  calc
    Artifact.submissionArtifact.instructionPC 2726 =
        Artifact.submissionArtifact.instructionPC 2725 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2725).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2725 1
    _ = 3598 := by
      rw [pc2723]
      rfl
@[simp] theorem pc2725 : Artifact.submissionArtifact.instructionPC 2727 = 3599 := by
  calc
    Artifact.submissionArtifact.instructionPC 2727 =
        Artifact.submissionArtifact.instructionPC 2726 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2726).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2726 1
    _ = 3599 := by
      rw [pc2724]
      rfl
@[simp] theorem pc2726 : Artifact.submissionArtifact.instructionPC 2728 = 3600 := by
  calc
    Artifact.submissionArtifact.instructionPC 2728 =
        Artifact.submissionArtifact.instructionPC 2727 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2727).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2727 1
    _ = 3600 := by
      rw [pc2725]
      rfl
@[simp] theorem pc2727 : Artifact.submissionArtifact.instructionPC 2729 = 3601 := by
  calc
    Artifact.submissionArtifact.instructionPC 2729 =
        Artifact.submissionArtifact.instructionPC 2728 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2728).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2728 1
    _ = 3601 := by
      rw [pc2726]
      rfl
@[simp] theorem pc2728 : Artifact.submissionArtifact.instructionPC 2730 = 3602 := by
  calc
    Artifact.submissionArtifact.instructionPC 2730 =
        Artifact.submissionArtifact.instructionPC 2729 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2729).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2729 1
    _ = 3602 := by
      rw [pc2727]
      rfl
@[simp] theorem pc2729 : Artifact.submissionArtifact.instructionPC 2731 = 3605 := by
  calc
    Artifact.submissionArtifact.instructionPC 2731 =
        Artifact.submissionArtifact.instructionPC 2730 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2730).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2730 1
    _ = 3605 := by
      rw [pc2728]
      rfl
@[simp] theorem pc2730 : Artifact.submissionArtifact.instructionPC 2732 = 3606 := by
  calc
    Artifact.submissionArtifact.instructionPC 2732 =
        Artifact.submissionArtifact.instructionPC 2731 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2731).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2731 1
    _ = 3606 := by
      rw [pc2729]
      rfl
@[simp] theorem pc2731 : Artifact.submissionArtifact.instructionPC 2733 = 3607 := by
  calc
    Artifact.submissionArtifact.instructionPC 2733 =
        Artifact.submissionArtifact.instructionPC 2732 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2732).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2732 1
    _ = 3607 := by
      rw [pc2730]
      rfl
@[simp] theorem pc2732 : Artifact.submissionArtifact.instructionPC 2734 = 3608 := by
  calc
    Artifact.submissionArtifact.instructionPC 2734 =
        Artifact.submissionArtifact.instructionPC 2733 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2733).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2733 1
    _ = 3608 := by
      rw [pc2731]
      rfl
@[simp] theorem pc2733 : Artifact.submissionArtifact.instructionPC 2735 = 3609 := by
  calc
    Artifact.submissionArtifact.instructionPC 2735 =
        Artifact.submissionArtifact.instructionPC 2734 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2734).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2734 1
    _ = 3609 := by
      rw [pc2732]
      rfl
@[simp] theorem pc2734 : Artifact.submissionArtifact.instructionPC 2736 = 3610 := by
  calc
    Artifact.submissionArtifact.instructionPC 2736 =
        Artifact.submissionArtifact.instructionPC 2735 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2735).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2735 1
    _ = 3610 := by
      rw [pc2733]
      rfl
@[simp] theorem pc2735 : Artifact.submissionArtifact.instructionPC 2737 = 3611 := by
  calc
    Artifact.submissionArtifact.instructionPC 2737 =
        Artifact.submissionArtifact.instructionPC 2736 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2736).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2736 1
    _ = 3611 := by
      rw [pc2734]
      rfl
@[simp] theorem pc2736 : Artifact.submissionArtifact.instructionPC 2738 = 3612 := by
  calc
    Artifact.submissionArtifact.instructionPC 2738 =
        Artifact.submissionArtifact.instructionPC 2737 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2737).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2737 1
    _ = 3612 := by
      rw [pc2735]
      rfl
@[simp] theorem pc2737 : Artifact.submissionArtifact.instructionPC 2739 = 3614 := by
  calc
    Artifact.submissionArtifact.instructionPC 2739 =
        Artifact.submissionArtifact.instructionPC 2738 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2738).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2738 1
    _ = 3614 := by
      rw [pc2736]
      rfl
@[simp] theorem pc2738 : Artifact.submissionArtifact.instructionPC 2740 = 3615 := by
  calc
    Artifact.submissionArtifact.instructionPC 2740 =
        Artifact.submissionArtifact.instructionPC 2739 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2739).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2739 1
    _ = 3615 := by
      rw [pc2737]
      rfl
@[simp] theorem pc2739 : Artifact.submissionArtifact.instructionPC 2741 = 3618 := by
  calc
    Artifact.submissionArtifact.instructionPC 2741 =
        Artifact.submissionArtifact.instructionPC 2740 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2740).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2740 1
    _ = 3618 := by
      rw [pc2738]
      rfl
@[simp] theorem pc2740 : Artifact.submissionArtifact.instructionPC 2742 = 3619 := by
  calc
    Artifact.submissionArtifact.instructionPC 2742 =
        Artifact.submissionArtifact.instructionPC 2741 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2741).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2741 1
    _ = 3619 := by
      rw [pc2739]
      rfl
@[simp] theorem pc2741 : Artifact.submissionArtifact.instructionPC 2743 = 3620 := by
  calc
    Artifact.submissionArtifact.instructionPC 2743 =
        Artifact.submissionArtifact.instructionPC 2742 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2742).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2742 1
    _ = 3620 := by
      rw [pc2740]
      rfl
@[simp] theorem pc2742 : Artifact.submissionArtifact.instructionPC 2744 = 3621 := by
  calc
    Artifact.submissionArtifact.instructionPC 2744 =
        Artifact.submissionArtifact.instructionPC 2743 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2743).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2743 1
    _ = 3621 := by
      rw [pc2741]
      rfl
@[simp] theorem pc2743 : Artifact.submissionArtifact.instructionPC 2745 = 3622 := by
  calc
    Artifact.submissionArtifact.instructionPC 2745 =
        Artifact.submissionArtifact.instructionPC 2744 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2744).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2744 1
    _ = 3622 := by
      rw [pc2742]
      rfl
@[simp] theorem pc2744 : Artifact.submissionArtifact.instructionPC 2746 = 3623 := by
  calc
    Artifact.submissionArtifact.instructionPC 2746 =
        Artifact.submissionArtifact.instructionPC 2745 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2745).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2745 1
    _ = 3623 := by
      rw [pc2743]
      rfl
@[simp] theorem pc2745 : Artifact.submissionArtifact.instructionPC 2747 = 3624 := by
  calc
    Artifact.submissionArtifact.instructionPC 2747 =
        Artifact.submissionArtifact.instructionPC 2746 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2746).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2746 1
    _ = 3624 := by
      rw [pc2744]
      rfl
@[simp] theorem pc2746 : Artifact.submissionArtifact.instructionPC 2748 = 3625 := by
  calc
    Artifact.submissionArtifact.instructionPC 2748 =
        Artifact.submissionArtifact.instructionPC 2747 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2747).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2747 1
    _ = 3625 := by
      rw [pc2745]
      rfl
@[simp] theorem pc2747 : Artifact.submissionArtifact.instructionPC 2749 = 3628 := by
  calc
    Artifact.submissionArtifact.instructionPC 2749 =
        Artifact.submissionArtifact.instructionPC 2748 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2748).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2748 1
    _ = 3628 := by
      rw [pc2746]
      rfl
@[simp] theorem pc2748 : Artifact.submissionArtifact.instructionPC 2750 = 3629 := by
  calc
    Artifact.submissionArtifact.instructionPC 2750 =
        Artifact.submissionArtifact.instructionPC 2749 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2749).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2749 1
    _ = 3629 := by
      rw [pc2747]
      rfl
@[simp] theorem pc2749 : Artifact.submissionArtifact.instructionPC 2751 = 3630 := by
  calc
    Artifact.submissionArtifact.instructionPC 2751 =
        Artifact.submissionArtifact.instructionPC 2750 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2750).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2750 1
    _ = 3630 := by
      rw [pc2748]
      rfl
@[simp] theorem pc2750 : Artifact.submissionArtifact.instructionPC 2752 = 3632 := by
  calc
    Artifact.submissionArtifact.instructionPC 2752 =
        Artifact.submissionArtifact.instructionPC 2751 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2751).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2751 1
    _ = 3632 := by
      rw [pc2749]
      rfl
@[simp] theorem pc2751 : Artifact.submissionArtifact.instructionPC 2753 = 3633 := by
  calc
    Artifact.submissionArtifact.instructionPC 2753 =
        Artifact.submissionArtifact.instructionPC 2752 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2752).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2752 1
    _ = 3633 := by
      rw [pc2750]
      rfl
@[simp] theorem pc2752 : Artifact.submissionArtifact.instructionPC 2754 = 3634 := by
  calc
    Artifact.submissionArtifact.instructionPC 2754 =
        Artifact.submissionArtifact.instructionPC 2753 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2753).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2753 1
    _ = 3634 := by
      rw [pc2751]
      rfl
@[simp] theorem pc2753 : Artifact.submissionArtifact.instructionPC 2755 = 3635 := by
  calc
    Artifact.submissionArtifact.instructionPC 2755 =
        Artifact.submissionArtifact.instructionPC 2754 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2754).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2754 1
    _ = 3635 := by
      rw [pc2752]
      rfl
@[simp] theorem pc2754 : Artifact.submissionArtifact.instructionPC 2756 = 3636 := by
  calc
    Artifact.submissionArtifact.instructionPC 2756 =
        Artifact.submissionArtifact.instructionPC 2755 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2755).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2755 1
    _ = 3636 := by
      rw [pc2753]
      rfl
@[simp] theorem pc2755 : Artifact.submissionArtifact.instructionPC 2757 = 3638 := by
  calc
    Artifact.submissionArtifact.instructionPC 2757 =
        Artifact.submissionArtifact.instructionPC 2756 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2756).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2756 1
    _ = 3638 := by
      rw [pc2754]
      rfl
@[simp] theorem pc2756 : Artifact.submissionArtifact.instructionPC 2758 = 3639 := by
  calc
    Artifact.submissionArtifact.instructionPC 2758 =
        Artifact.submissionArtifact.instructionPC 2757 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2757).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2757 1
    _ = 3639 := by
      rw [pc2755]
      rfl
@[simp] theorem pc2757 : Artifact.submissionArtifact.instructionPC 2759 = 3640 := by
  calc
    Artifact.submissionArtifact.instructionPC 2759 =
        Artifact.submissionArtifact.instructionPC 2758 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2758).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2758 1
    _ = 3640 := by
      rw [pc2756]
      rfl
@[simp] theorem pc2758 : Artifact.submissionArtifact.instructionPC 2760 = 3641 := by
  calc
    Artifact.submissionArtifact.instructionPC 2760 =
        Artifact.submissionArtifact.instructionPC 2759 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2759).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2759 1
    _ = 3641 := by
      rw [pc2757]
      rfl
@[simp] theorem pc2759 : Artifact.submissionArtifact.instructionPC 2761 = 3642 := by
  calc
    Artifact.submissionArtifact.instructionPC 2761 =
        Artifact.submissionArtifact.instructionPC 2760 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2760).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2760 1
    _ = 3642 := by
      rw [pc2758]
      rfl
@[simp] theorem pc2760 : Artifact.submissionArtifact.instructionPC 2762 = 3643 := by
  calc
    Artifact.submissionArtifact.instructionPC 2762 =
        Artifact.submissionArtifact.instructionPC 2761 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2761).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2761 1
    _ = 3643 := by
      rw [pc2759]
      rfl
@[simp] theorem pc2761 : Artifact.submissionArtifact.instructionPC 2763 = 3645 := by
  calc
    Artifact.submissionArtifact.instructionPC 2763 =
        Artifact.submissionArtifact.instructionPC 2762 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2762).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2762 1
    _ = 3645 := by
      rw [pc2760]
      rfl
@[simp] theorem pc2762 : Artifact.submissionArtifact.instructionPC 2764 = 3646 := by
  calc
    Artifact.submissionArtifact.instructionPC 2764 =
        Artifact.submissionArtifact.instructionPC 2763 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2763).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2763 1
    _ = 3646 := by
      rw [pc2761]
      rfl
@[simp] theorem pc2763 : Artifact.submissionArtifact.instructionPC 2765 = 3647 := by
  calc
    Artifact.submissionArtifact.instructionPC 2765 =
        Artifact.submissionArtifact.instructionPC 2764 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2764).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2764 1
    _ = 3647 := by
      rw [pc2762]
      rfl
@[simp] theorem pc2764 : Artifact.submissionArtifact.instructionPC 2766 = 3648 := by
  calc
    Artifact.submissionArtifact.instructionPC 2766 =
        Artifact.submissionArtifact.instructionPC 2765 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2765).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2765 1
    _ = 3648 := by
      rw [pc2763]
      rfl
@[simp] theorem pc2765 : Artifact.submissionArtifact.instructionPC 2767 = 3649 := by
  calc
    Artifact.submissionArtifact.instructionPC 2767 =
        Artifact.submissionArtifact.instructionPC 2766 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2766).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2766 1
    _ = 3649 := by
      rw [pc2764]
      rfl
@[simp] theorem pc2766 : Artifact.submissionArtifact.instructionPC 2768 = 3650 := by
  calc
    Artifact.submissionArtifact.instructionPC 2768 =
        Artifact.submissionArtifact.instructionPC 2767 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2767).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2767 1
    _ = 3650 := by
      rw [pc2765]
      rfl
@[simp] theorem pc2767 : Artifact.submissionArtifact.instructionPC 2769 = 3652 := by
  calc
    Artifact.submissionArtifact.instructionPC 2769 =
        Artifact.submissionArtifact.instructionPC 2768 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2768).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2768 1
    _ = 3652 := by
      rw [pc2766]
      rfl
@[simp] theorem pc2768 : Artifact.submissionArtifact.instructionPC 2770 = 3653 := by
  calc
    Artifact.submissionArtifact.instructionPC 2770 =
        Artifact.submissionArtifact.instructionPC 2769 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2769).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2769 1
    _ = 3653 := by
      rw [pc2767]
      rfl
@[simp] theorem pc2769 : Artifact.submissionArtifact.instructionPC 2771 = 3654 := by
  calc
    Artifact.submissionArtifact.instructionPC 2771 =
        Artifact.submissionArtifact.instructionPC 2770 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2770).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2770 1
    _ = 3654 := by
      rw [pc2768]
      rfl
@[simp] theorem pc2770 : Artifact.submissionArtifact.instructionPC 2772 = 3655 := by
  calc
    Artifact.submissionArtifact.instructionPC 2772 =
        Artifact.submissionArtifact.instructionPC 2771 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2771).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2771 1
    _ = 3655 := by
      rw [pc2769]
      rfl
@[simp] theorem pc2771 : Artifact.submissionArtifact.instructionPC 2773 = 3656 := by
  calc
    Artifact.submissionArtifact.instructionPC 2773 =
        Artifact.submissionArtifact.instructionPC 2772 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2772).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2772 1
    _ = 3656 := by
      rw [pc2770]
      rfl
@[simp] theorem pc2772 : Artifact.submissionArtifact.instructionPC 2774 = 3657 := by
  calc
    Artifact.submissionArtifact.instructionPC 2774 =
        Artifact.submissionArtifact.instructionPC 2773 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2773).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2773 1
    _ = 3657 := by
      rw [pc2771]
      rfl
@[simp] theorem pc2773 : Artifact.submissionArtifact.instructionPC 2775 = 3659 := by
  calc
    Artifact.submissionArtifact.instructionPC 2775 =
        Artifact.submissionArtifact.instructionPC 2774 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2774).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2774 1
    _ = 3659 := by
      rw [pc2772]
      rfl
@[simp] theorem pc2774 : Artifact.submissionArtifact.instructionPC 2776 = 3660 := by
  calc
    Artifact.submissionArtifact.instructionPC 2776 =
        Artifact.submissionArtifact.instructionPC 2775 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2775).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2775 1
    _ = 3660 := by
      rw [pc2773]
      rfl
@[simp] theorem pc2775 : Artifact.submissionArtifact.instructionPC 2777 = 3661 := by
  calc
    Artifact.submissionArtifact.instructionPC 2777 =
        Artifact.submissionArtifact.instructionPC 2776 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2776).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2776 1
    _ = 3661 := by
      rw [pc2774]
      rfl
@[simp] theorem pc2776 : Artifact.submissionArtifact.instructionPC 2778 = 3662 := by
  calc
    Artifact.submissionArtifact.instructionPC 2778 =
        Artifact.submissionArtifact.instructionPC 2777 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2777).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2777 1
    _ = 3662 := by
      rw [pc2775]
      rfl
@[simp] theorem pc2777 : Artifact.submissionArtifact.instructionPC 2779 = 3663 := by
  calc
    Artifact.submissionArtifact.instructionPC 2779 =
        Artifact.submissionArtifact.instructionPC 2778 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2778).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2778 1
    _ = 3663 := by
      rw [pc2776]
      rfl
@[simp] theorem pc2778 : Artifact.submissionArtifact.instructionPC 2780 = 3664 := by
  calc
    Artifact.submissionArtifact.instructionPC 2780 =
        Artifact.submissionArtifact.instructionPC 2779 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2779).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2779 1
    _ = 3664 := by
      rw [pc2777]
      rfl
@[simp] theorem pc2779 : Artifact.submissionArtifact.instructionPC 2781 = 3666 := by
  calc
    Artifact.submissionArtifact.instructionPC 2781 =
        Artifact.submissionArtifact.instructionPC 2780 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2780).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2780 1
    _ = 3666 := by
      rw [pc2778]
      rfl
@[simp] theorem pc2780 : Artifact.submissionArtifact.instructionPC 2782 = 3667 := by
  calc
    Artifact.submissionArtifact.instructionPC 2782 =
        Artifact.submissionArtifact.instructionPC 2781 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2781).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2781 1
    _ = 3667 := by
      rw [pc2779]
      rfl
@[simp] theorem pc2781 : Artifact.submissionArtifact.instructionPC 2783 = 3668 := by
  calc
    Artifact.submissionArtifact.instructionPC 2783 =
        Artifact.submissionArtifact.instructionPC 2782 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2782).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2782 1
    _ = 3668 := by
      rw [pc2780]
      rfl
@[simp] theorem pc2782 : Artifact.submissionArtifact.instructionPC 2784 = 3669 := by
  calc
    Artifact.submissionArtifact.instructionPC 2784 =
        Artifact.submissionArtifact.instructionPC 2783 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2783).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2783 1
    _ = 3669 := by
      rw [pc2781]
      rfl
@[simp] theorem pc2783 : Artifact.submissionArtifact.instructionPC 2785 = 3670 := by
  calc
    Artifact.submissionArtifact.instructionPC 2785 =
        Artifact.submissionArtifact.instructionPC 2784 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2784).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2784 1
    _ = 3670 := by
      rw [pc2782]
      rfl
@[simp] theorem pc2784 : Artifact.submissionArtifact.instructionPC 2786 = 3671 := by
  calc
    Artifact.submissionArtifact.instructionPC 2786 =
        Artifact.submissionArtifact.instructionPC 2785 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2785).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2785 1
    _ = 3671 := by
      rw [pc2783]
      rfl
@[simp] theorem pc2785 : Artifact.submissionArtifact.instructionPC 2787 = 3673 := by
  calc
    Artifact.submissionArtifact.instructionPC 2787 =
        Artifact.submissionArtifact.instructionPC 2786 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2786).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2786 1
    _ = 3673 := by
      rw [pc2784]
      rfl
@[simp] theorem pc2786 : Artifact.submissionArtifact.instructionPC 2788 = 3674 := by
  calc
    Artifact.submissionArtifact.instructionPC 2788 =
        Artifact.submissionArtifact.instructionPC 2787 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2787).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2787 1
    _ = 3674 := by
      rw [pc2785]
      rfl
@[simp] theorem pc2787 : Artifact.submissionArtifact.instructionPC 2789 = 3675 := by
  calc
    Artifact.submissionArtifact.instructionPC 2789 =
        Artifact.submissionArtifact.instructionPC 2788 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2788).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2788 1
    _ = 3675 := by
      rw [pc2786]
      rfl
@[simp] theorem pc2788 : Artifact.submissionArtifact.instructionPC 2790 = 3676 := by
  calc
    Artifact.submissionArtifact.instructionPC 2790 =
        Artifact.submissionArtifact.instructionPC 2789 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2789).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2789 1
    _ = 3676 := by
      rw [pc2787]
      rfl
@[simp] theorem pc2789 : Artifact.submissionArtifact.instructionPC 2791 = 3677 := by
  calc
    Artifact.submissionArtifact.instructionPC 2791 =
        Artifact.submissionArtifact.instructionPC 2790 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2790).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2790 1
    _ = 3677 := by
      rw [pc2788]
      rfl
@[simp] theorem pc2790 : Artifact.submissionArtifact.instructionPC 2792 = 3678 := by
  calc
    Artifact.submissionArtifact.instructionPC 2792 =
        Artifact.submissionArtifact.instructionPC 2791 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2791).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2791 1
    _ = 3678 := by
      rw [pc2789]
      rfl
@[simp] theorem pc2791 : Artifact.submissionArtifact.instructionPC 2793 = 3680 := by
  calc
    Artifact.submissionArtifact.instructionPC 2793 =
        Artifact.submissionArtifact.instructionPC 2792 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2792).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2792 1
    _ = 3680 := by
      rw [pc2790]
      rfl
@[simp] theorem pc2792 : Artifact.submissionArtifact.instructionPC 2794 = 3681 := by
  calc
    Artifact.submissionArtifact.instructionPC 2794 =
        Artifact.submissionArtifact.instructionPC 2793 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2793).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2793 1
    _ = 3681 := by
      rw [pc2791]
      rfl
@[simp] theorem pc2793 : Artifact.submissionArtifact.instructionPC 2795 = 3682 := by
  calc
    Artifact.submissionArtifact.instructionPC 2795 =
        Artifact.submissionArtifact.instructionPC 2794 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2794).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2794 1
    _ = 3682 := by
      rw [pc2792]
      rfl
@[simp] theorem pc2794 : Artifact.submissionArtifact.instructionPC 2796 = 3685 := by
  calc
    Artifact.submissionArtifact.instructionPC 2796 =
        Artifact.submissionArtifact.instructionPC 2795 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2795).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2795 1
    _ = 3685 := by
      rw [pc2793]
      rfl
@[simp] theorem pc2795 : Artifact.submissionArtifact.instructionPC 2797 = 3686 := by
  calc
    Artifact.submissionArtifact.instructionPC 2797 =
        Artifact.submissionArtifact.instructionPC 2796 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2796).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2796 1
    _ = 3686 := by
      rw [pc2794]
      rfl
@[simp] theorem pc2796 : Artifact.submissionArtifact.instructionPC 2798 = 3687 := by
  calc
    Artifact.submissionArtifact.instructionPC 2798 =
        Artifact.submissionArtifact.instructionPC 2797 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2797).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2797 1
    _ = 3687 := by
      rw [pc2795]
      rfl
@[simp] theorem pc2797 : Artifact.submissionArtifact.instructionPC 2799 = 3688 := by
  calc
    Artifact.submissionArtifact.instructionPC 2799 =
        Artifact.submissionArtifact.instructionPC 2798 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2798).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2798 1
    _ = 3688 := by
      rw [pc2796]
      rfl
@[simp] theorem pc2798 : Artifact.submissionArtifact.instructionPC 2800 = 3689 := by
  calc
    Artifact.submissionArtifact.instructionPC 2800 =
        Artifact.submissionArtifact.instructionPC 2799 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2799).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2799 1
    _ = 3689 := by
      rw [pc2797]
      rfl
@[simp] theorem pc2799 : Artifact.submissionArtifact.instructionPC 2801 = 3690 := by
  calc
    Artifact.submissionArtifact.instructionPC 2801 =
        Artifact.submissionArtifact.instructionPC 2800 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2800).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2800 1
    _ = 3690 := by
      rw [pc2798]
      rfl
@[simp] theorem pc2800 : Artifact.submissionArtifact.instructionPC 2802 = 3691 := by
  calc
    Artifact.submissionArtifact.instructionPC 2802 =
        Artifact.submissionArtifact.instructionPC 2801 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2801).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2801 1
    _ = 3691 := by
      rw [pc2799]
      rfl
@[simp] theorem pc2801 : Artifact.submissionArtifact.instructionPC 2803 = 3692 := by
  calc
    Artifact.submissionArtifact.instructionPC 2803 =
        Artifact.submissionArtifact.instructionPC 2802 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2802).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2802 1
    _ = 3692 := by
      rw [pc2800]
      rfl
@[simp] theorem pc2802 : Artifact.submissionArtifact.instructionPC 2804 = 3693 := by
  calc
    Artifact.submissionArtifact.instructionPC 2804 =
        Artifact.submissionArtifact.instructionPC 2803 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2803).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2803 1
    _ = 3693 := by
      rw [pc2801]
      rfl
@[simp] theorem pc2803 : Artifact.submissionArtifact.instructionPC 2805 = 3696 := by
  calc
    Artifact.submissionArtifact.instructionPC 2805 =
        Artifact.submissionArtifact.instructionPC 2804 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2804).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2804 1
    _ = 3696 := by
      rw [pc2802]
      rfl
@[simp] theorem pc2804 : Artifact.submissionArtifact.instructionPC 2806 = 3697 := by
  calc
    Artifact.submissionArtifact.instructionPC 2806 =
        Artifact.submissionArtifact.instructionPC 2805 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2805).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2805 1
    _ = 3697 := by
      rw [pc2803]
      rfl
@[simp] theorem pc2805 : Artifact.submissionArtifact.instructionPC 2807 = 3698 := by
  calc
    Artifact.submissionArtifact.instructionPC 2807 =
        Artifact.submissionArtifact.instructionPC 2806 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2806).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2806 1
    _ = 3698 := by
      rw [pc2804]
      rfl
@[simp] theorem pc2806 : Artifact.submissionArtifact.instructionPC 2808 = 3701 := by
  calc
    Artifact.submissionArtifact.instructionPC 2808 =
        Artifact.submissionArtifact.instructionPC 2807 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2807).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2807 1
    _ = 3701 := by
      rw [pc2805]
      rfl
@[simp] theorem pc2807 : Artifact.submissionArtifact.instructionPC 2809 = 3704 := by
  calc
    Artifact.submissionArtifact.instructionPC 2809 =
        Artifact.submissionArtifact.instructionPC 2808 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2808).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2808 1
    _ = 3704 := by
      rw [pc2806]
      rfl
@[simp] theorem pc2808 : Artifact.submissionArtifact.instructionPC 2810 = 3705 := by
  calc
    Artifact.submissionArtifact.instructionPC 2810 =
        Artifact.submissionArtifact.instructionPC 2809 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2809).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2809 1
    _ = 3705 := by
      rw [pc2807]
      rfl
@[simp] theorem pc2809 : Artifact.submissionArtifact.instructionPC 2811 = 3706 := by
  calc
    Artifact.submissionArtifact.instructionPC 2811 =
        Artifact.submissionArtifact.instructionPC 2810 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2810).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2810 1
    _ = 3706 := by
      rw [pc2808]
      rfl
@[simp] theorem pc2810 : Artifact.submissionArtifact.instructionPC 2812 = 3709 := by
  calc
    Artifact.submissionArtifact.instructionPC 2812 =
        Artifact.submissionArtifact.instructionPC 2811 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2811).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2811 1
    _ = 3709 := by
      rw [pc2809]
      rfl
@[simp] theorem pc2811 : Artifact.submissionArtifact.instructionPC 2813 = 3710 := by
  calc
    Artifact.submissionArtifact.instructionPC 2813 =
        Artifact.submissionArtifact.instructionPC 2812 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2812).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2812 1
    _ = 3710 := by
      rw [pc2810]
      rfl
@[simp] theorem pc2812 : Artifact.submissionArtifact.instructionPC 2814 = 3711 := by
  calc
    Artifact.submissionArtifact.instructionPC 2814 =
        Artifact.submissionArtifact.instructionPC 2813 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2813).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2813 1
    _ = 3711 := by
      rw [pc2811]
      rfl
@[simp] theorem pc2813 : Artifact.submissionArtifact.instructionPC 2815 = 3714 := by
  calc
    Artifact.submissionArtifact.instructionPC 2815 =
        Artifact.submissionArtifact.instructionPC 2814 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2814).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2814 1
    _ = 3714 := by
      rw [pc2812]
      rfl
@[simp] theorem pc2814 : Artifact.submissionArtifact.instructionPC 2816 = 3715 := by
  calc
    Artifact.submissionArtifact.instructionPC 2816 =
        Artifact.submissionArtifact.instructionPC 2815 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2815).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2815 1
    _ = 3715 := by
      rw [pc2813]
      rfl
@[simp] theorem pc2815 : Artifact.submissionArtifact.instructionPC 2817 = 3718 := by
  calc
    Artifact.submissionArtifact.instructionPC 2817 =
        Artifact.submissionArtifact.instructionPC 2816 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2816).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2816 1
    _ = 3718 := by
      rw [pc2814]
      rfl
@[simp] theorem pc2816 : Artifact.submissionArtifact.instructionPC 2818 = 3719 := by
  calc
    Artifact.submissionArtifact.instructionPC 2818 =
        Artifact.submissionArtifact.instructionPC 2817 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2817).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2817 1
    _ = 3719 := by
      rw [pc2815]
      rfl
@[simp] theorem pc2817 : Artifact.submissionArtifact.instructionPC 2819 = 3720 := by
  calc
    Artifact.submissionArtifact.instructionPC 2819 =
        Artifact.submissionArtifact.instructionPC 2818 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2818).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2818 1
    _ = 3720 := by
      rw [pc2816]
      rfl
@[simp] theorem pc2818 : Artifact.submissionArtifact.instructionPC 2820 = 3721 := by
  calc
    Artifact.submissionArtifact.instructionPC 2820 =
        Artifact.submissionArtifact.instructionPC 2819 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2819).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2819 1
    _ = 3721 := by
      rw [pc2817]
      rfl
@[simp] theorem pc2819 : Artifact.submissionArtifact.instructionPC 2821 = 3722 := by
  calc
    Artifact.submissionArtifact.instructionPC 2821 =
        Artifact.submissionArtifact.instructionPC 2820 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2820).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2820 1
    _ = 3722 := by
      rw [pc2818]
      rfl
@[simp] theorem pc2820 : Artifact.submissionArtifact.instructionPC 2822 = 3723 := by
  calc
    Artifact.submissionArtifact.instructionPC 2822 =
        Artifact.submissionArtifact.instructionPC 2821 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2821).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2821 1
    _ = 3723 := by
      rw [pc2819]
      rfl
@[simp] theorem pc2821 : Artifact.submissionArtifact.instructionPC 2823 = 3724 := by
  calc
    Artifact.submissionArtifact.instructionPC 2823 =
        Artifact.submissionArtifact.instructionPC 2822 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2822).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2822 1
    _ = 3724 := by
      rw [pc2820]
      rfl
@[simp] theorem pc2822 : Artifact.submissionArtifact.instructionPC 2824 = 3727 := by
  calc
    Artifact.submissionArtifact.instructionPC 2824 =
        Artifact.submissionArtifact.instructionPC 2823 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2823).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2823 1
    _ = 3727 := by
      rw [pc2821]
      rfl
@[simp] theorem pc2823 : Artifact.submissionArtifact.instructionPC 2825 = 3728 := by
  calc
    Artifact.submissionArtifact.instructionPC 2825 =
        Artifact.submissionArtifact.instructionPC 2824 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2824).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2824 1
    _ = 3728 := by
      rw [pc2822]
      rfl
@[simp] theorem pc2824 : Artifact.submissionArtifact.instructionPC 2826 = 3729 := by
  calc
    Artifact.submissionArtifact.instructionPC 2826 =
        Artifact.submissionArtifact.instructionPC 2825 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2825).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2825 1
    _ = 3729 := by
      rw [pc2823]
      rfl
@[simp] theorem pc2825 : Artifact.submissionArtifact.instructionPC 2827 = 3732 := by
  calc
    Artifact.submissionArtifact.instructionPC 2827 =
        Artifact.submissionArtifact.instructionPC 2826 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2826).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2826 1
    _ = 3732 := by
      rw [pc2824]
      rfl
@[simp] theorem pc2826 : Artifact.submissionArtifact.instructionPC 2828 = 3733 := by
  calc
    Artifact.submissionArtifact.instructionPC 2828 =
        Artifact.submissionArtifact.instructionPC 2827 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2827).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2827 1
    _ = 3733 := by
      rw [pc2825]
      rfl
@[simp] theorem pc2827 : Artifact.submissionArtifact.instructionPC 2829 = 3736 := by
  calc
    Artifact.submissionArtifact.instructionPC 2829 =
        Artifact.submissionArtifact.instructionPC 2828 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2828).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2828 1
    _ = 3736 := by
      rw [pc2826]
      rfl
@[simp] theorem pc2828 : Artifact.submissionArtifact.instructionPC 2830 = 3737 := by
  calc
    Artifact.submissionArtifact.instructionPC 2830 =
        Artifact.submissionArtifact.instructionPC 2829 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2829).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2829 1
    _ = 3737 := by
      rw [pc2827]
      rfl
@[simp] theorem pc2829 : Artifact.submissionArtifact.instructionPC 2831 = 3738 := by
  calc
    Artifact.submissionArtifact.instructionPC 2831 =
        Artifact.submissionArtifact.instructionPC 2830 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2830).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2830 1
    _ = 3738 := by
      rw [pc2828]
      rfl
@[simp] theorem pc2830 : Artifact.submissionArtifact.instructionPC 2832 = 3739 := by
  calc
    Artifact.submissionArtifact.instructionPC 2832 =
        Artifact.submissionArtifact.instructionPC 2831 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2831).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2831 1
    _ = 3739 := by
      rw [pc2829]
      rfl
@[simp] theorem pc2831 : Artifact.submissionArtifact.instructionPC 2833 = 3740 := by
  calc
    Artifact.submissionArtifact.instructionPC 2833 =
        Artifact.submissionArtifact.instructionPC 2832 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2832).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2832 1
    _ = 3740 := by
      rw [pc2830]
      rfl
@[simp] theorem pc2832 : Artifact.submissionArtifact.instructionPC 2834 = 3743 := by
  calc
    Artifact.submissionArtifact.instructionPC 2834 =
        Artifact.submissionArtifact.instructionPC 2833 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2833).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2833 1
    _ = 3743 := by
      rw [pc2831]
      rfl
@[simp] theorem pc2833 : Artifact.submissionArtifact.instructionPC 2835 = 3744 := by
  calc
    Artifact.submissionArtifact.instructionPC 2835 =
        Artifact.submissionArtifact.instructionPC 2834 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2834).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2834 1
    _ = 3744 := by
      rw [pc2832]
      rfl
@[simp] theorem pc2834 : Artifact.submissionArtifact.instructionPC 2836 = 3745 := by
  calc
    Artifact.submissionArtifact.instructionPC 2836 =
        Artifact.submissionArtifact.instructionPC 2835 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2835).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2835 1
    _ = 3745 := by
      rw [pc2833]
      rfl
@[simp] theorem pc2835 : Artifact.submissionArtifact.instructionPC 2837 = 3748 := by
  calc
    Artifact.submissionArtifact.instructionPC 2837 =
        Artifact.submissionArtifact.instructionPC 2836 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2836).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2836 1
    _ = 3748 := by
      rw [pc2834]
      rfl
@[simp] theorem pc2836 : Artifact.submissionArtifact.instructionPC 2838 = 3749 := by
  calc
    Artifact.submissionArtifact.instructionPC 2838 =
        Artifact.submissionArtifact.instructionPC 2837 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2837).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2837 1
    _ = 3749 := by
      rw [pc2835]
      rfl
@[simp] theorem pc2837 : Artifact.submissionArtifact.instructionPC 2839 = 3750 := by
  calc
    Artifact.submissionArtifact.instructionPC 2839 =
        Artifact.submissionArtifact.instructionPC 2838 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2838).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2838 1
    _ = 3750 := by
      rw [pc2836]
      rfl
@[simp] theorem pc2838 : Artifact.submissionArtifact.instructionPC 2840 = 3751 := by
  calc
    Artifact.submissionArtifact.instructionPC 2840 =
        Artifact.submissionArtifact.instructionPC 2839 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2839).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2839 1
    _ = 3751 := by
      rw [pc2837]
      rfl
@[simp] theorem pc2839 : Artifact.submissionArtifact.instructionPC 2841 = 3752 := by
  calc
    Artifact.submissionArtifact.instructionPC 2841 =
        Artifact.submissionArtifact.instructionPC 2840 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2840).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2840 1
    _ = 3752 := by
      rw [pc2838]
      rfl
@[simp] theorem pc2840 : Artifact.submissionArtifact.instructionPC 2842 = 3753 := by
  calc
    Artifact.submissionArtifact.instructionPC 2842 =
        Artifact.submissionArtifact.instructionPC 2841 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2841).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2841 1
    _ = 3753 := by
      rw [pc2839]
      rfl
@[simp] theorem pc2841 : Artifact.submissionArtifact.instructionPC 2843 = 3754 := by
  calc
    Artifact.submissionArtifact.instructionPC 2843 =
        Artifact.submissionArtifact.instructionPC 2842 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2842).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2842 1
    _ = 3754 := by
      rw [pc2840]
      rfl
@[simp] theorem pc2842 : Artifact.submissionArtifact.instructionPC 2844 = 3755 := by
  calc
    Artifact.submissionArtifact.instructionPC 2844 =
        Artifact.submissionArtifact.instructionPC 2843 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2843).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2843 1
    _ = 3755 := by
      rw [pc2841]
      rfl
@[simp] theorem pc2843 : Artifact.submissionArtifact.instructionPC 2845 = 3758 := by
  calc
    Artifact.submissionArtifact.instructionPC 2845 =
        Artifact.submissionArtifact.instructionPC 2844 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2844).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2844 1
    _ = 3758 := by
      rw [pc2842]
      rfl
@[simp] theorem pc2844 : Artifact.submissionArtifact.instructionPC 2846 = 3759 := by
  calc
    Artifact.submissionArtifact.instructionPC 2846 =
        Artifact.submissionArtifact.instructionPC 2845 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2845).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2845 1
    _ = 3759 := by
      rw [pc2843]
      rfl
@[simp] theorem pc2845 : Artifact.submissionArtifact.instructionPC 2847 = 3760 := by
  calc
    Artifact.submissionArtifact.instructionPC 2847 =
        Artifact.submissionArtifact.instructionPC 2846 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2846).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2846 1
    _ = 3760 := by
      rw [pc2844]
      rfl
@[simp] theorem pc2846 : Artifact.submissionArtifact.instructionPC 2848 = 3761 := by
  calc
    Artifact.submissionArtifact.instructionPC 2848 =
        Artifact.submissionArtifact.instructionPC 2847 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2847).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2847 1
    _ = 3761 := by
      rw [pc2845]
      rfl
@[simp] theorem pc2847 : Artifact.submissionArtifact.instructionPC 2849 = 3762 := by
  calc
    Artifact.submissionArtifact.instructionPC 2849 =
        Artifact.submissionArtifact.instructionPC 2848 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2848).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2848 1
    _ = 3762 := by
      rw [pc2846]
      rfl
@[simp] theorem pc2848 : Artifact.submissionArtifact.instructionPC 2850 = 3763 := by
  calc
    Artifact.submissionArtifact.instructionPC 2850 =
        Artifact.submissionArtifact.instructionPC 2849 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2849).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2849 1
    _ = 3763 := by
      rw [pc2847]
      rfl
@[simp] theorem pc2849 : Artifact.submissionArtifact.instructionPC 2851 = 3764 := by
  calc
    Artifact.submissionArtifact.instructionPC 2851 =
        Artifact.submissionArtifact.instructionPC 2850 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2850).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2850 1
    _ = 3764 := by
      rw [pc2848]
      rfl
@[simp] theorem pc2850 : Artifact.submissionArtifact.instructionPC 2852 = 3767 := by
  calc
    Artifact.submissionArtifact.instructionPC 2852 =
        Artifact.submissionArtifact.instructionPC 2851 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2851).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2851 1
    _ = 3767 := by
      rw [pc2849]
      rfl
@[simp] theorem pc2851 : Artifact.submissionArtifact.instructionPC 2853 = 3768 := by
  calc
    Artifact.submissionArtifact.instructionPC 2853 =
        Artifact.submissionArtifact.instructionPC 2852 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2852).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2852 1
    _ = 3768 := by
      rw [pc2850]
      rfl
@[simp] theorem pc2852 : Artifact.submissionArtifact.instructionPC 2854 = 3769 := by
  calc
    Artifact.submissionArtifact.instructionPC 2854 =
        Artifact.submissionArtifact.instructionPC 2853 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2853).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2853 1
    _ = 3769 := by
      rw [pc2851]
      rfl
@[simp] theorem pc2853 : Artifact.submissionArtifact.instructionPC 2855 = 3771 := by
  calc
    Artifact.submissionArtifact.instructionPC 2855 =
        Artifact.submissionArtifact.instructionPC 2854 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2854).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2854 1
    _ = 3771 := by
      rw [pc2852]
      rfl
@[simp] theorem pc2854 : Artifact.submissionArtifact.instructionPC 2856 = 3772 := by
  calc
    Artifact.submissionArtifact.instructionPC 2856 =
        Artifact.submissionArtifact.instructionPC 2855 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2855).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2855 1
    _ = 3772 := by
      rw [pc2853]
      rfl
@[simp] theorem pc2855 : Artifact.submissionArtifact.instructionPC 2857 = 3774 := by
  calc
    Artifact.submissionArtifact.instructionPC 2857 =
        Artifact.submissionArtifact.instructionPC 2856 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2856).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2856 1
    _ = 3774 := by
      rw [pc2854]
      rfl
@[simp] theorem pc2856 : Artifact.submissionArtifact.instructionPC 2858 = 3775 := by
  calc
    Artifact.submissionArtifact.instructionPC 2858 =
        Artifact.submissionArtifact.instructionPC 2857 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2857).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2857 1
    _ = 3775 := by
      rw [pc2855]
      rfl
@[simp] theorem pc2857 : Artifact.submissionArtifact.instructionPC 2859 = 3776 := by
  calc
    Artifact.submissionArtifact.instructionPC 2859 =
        Artifact.submissionArtifact.instructionPC 2858 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2858).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2858 1
    _ = 3776 := by
      rw [pc2856]
      rfl
@[simp] theorem pc2858 : Artifact.submissionArtifact.instructionPC 2860 = 3778 := by
  calc
    Artifact.submissionArtifact.instructionPC 2860 =
        Artifact.submissionArtifact.instructionPC 2859 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2859).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2859 1
    _ = 3778 := by
      rw [pc2857]
      rfl
@[simp] theorem pc2859 : Artifact.submissionArtifact.instructionPC 2861 = 3779 := by
  calc
    Artifact.submissionArtifact.instructionPC 2861 =
        Artifact.submissionArtifact.instructionPC 2860 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2860).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2860 1
    _ = 3779 := by
      rw [pc2858]
      rfl
@[simp] theorem pc2860 : Artifact.submissionArtifact.instructionPC 2862 = 3780 := by
  calc
    Artifact.submissionArtifact.instructionPC 2862 =
        Artifact.submissionArtifact.instructionPC 2861 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2861).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2861 1
    _ = 3780 := by
      rw [pc2859]
      rfl
@[simp] theorem correctionSwapPC : Artifact.submissionArtifact.instructionPC 2863 = 3781 := by
  calc
    Artifact.submissionArtifact.instructionPC 2863 =
        Artifact.submissionArtifact.instructionPC 2862 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2862).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2862 1
    _ = 3781 := by
      rw [pc2860]
      rfl
@[simp] theorem correctionSubPC : Artifact.submissionArtifact.instructionPC 2864 = 3782 := by
  calc
    Artifact.submissionArtifact.instructionPC 2864 =
        Artifact.submissionArtifact.instructionPC 2863 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2863).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2863 1
    _ = 3782 := by
      rw [correctionSwapPC]
      rfl
@[simp] theorem pc2861 : Artifact.submissionArtifact.instructionPC 2865 = 3783 := by
  calc
    Artifact.submissionArtifact.instructionPC 2865 =
        Artifact.submissionArtifact.instructionPC 2864 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2864).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2864 1
    _ = 3783 := by
      rw [correctionSubPC]
      rfl
@[simp] theorem pc2862 : Artifact.submissionArtifact.instructionPC 2866 = 3784 := by
  calc
    Artifact.submissionArtifact.instructionPC 2866 =
        Artifact.submissionArtifact.instructionPC 2865 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2865).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2865 1
    _ = 3784 := by
      rw [pc2861]
      rfl
@[simp] theorem pc2863 : Artifact.submissionArtifact.instructionPC 2867 = 3787 := by
  calc
    Artifact.submissionArtifact.instructionPC 2867 =
        Artifact.submissionArtifact.instructionPC 2866 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2866).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2866 1
    _ = 3787 := by
      rw [pc2862]
      rfl
@[simp] theorem pc2864 : Artifact.submissionArtifact.instructionPC 2868 = 3788 := by
  calc
    Artifact.submissionArtifact.instructionPC 2868 =
        Artifact.submissionArtifact.instructionPC 2867 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2867).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2867 1
    _ = 3788 := by
      rw [pc2863]
      rfl
@[simp] theorem pc2865 : Artifact.submissionArtifact.instructionPC 2869 = 3789 := by
  calc
    Artifact.submissionArtifact.instructionPC 2869 =
        Artifact.submissionArtifact.instructionPC 2868 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2868).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2868 1
    _ = 3789 := by
      rw [pc2864]
      rfl
@[simp] theorem pc2866 : Artifact.submissionArtifact.instructionPC 2870 = 3790 := by
  calc
    Artifact.submissionArtifact.instructionPC 2870 =
        Artifact.submissionArtifact.instructionPC 2869 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2869).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2869 1
    _ = 3790 := by
      rw [pc2865]
      rfl
@[simp] theorem pc2867 : Artifact.submissionArtifact.instructionPC 2871 = 3791 := by
  calc
    Artifact.submissionArtifact.instructionPC 2871 =
        Artifact.submissionArtifact.instructionPC 2870 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2870).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2870 1
    _ = 3791 := by
      rw [pc2866]
      rfl
@[simp] theorem pc2868 : Artifact.submissionArtifact.instructionPC 2872 = 3792 := by
  calc
    Artifact.submissionArtifact.instructionPC 2872 =
        Artifact.submissionArtifact.instructionPC 2871 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2871).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2871 1
    _ = 3792 := by
      rw [pc2867]
      rfl
@[simp] theorem pc2869 : Artifact.submissionArtifact.instructionPC 2873 = 3793 := by
  calc
    Artifact.submissionArtifact.instructionPC 2873 =
        Artifact.submissionArtifact.instructionPC 2872 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2872).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2872 1
    _ = 3793 := by
      rw [pc2868]
      rfl
@[simp] theorem pc2870 : Artifact.submissionArtifact.instructionPC 2874 = 3794 := by
  calc
    Artifact.submissionArtifact.instructionPC 2874 =
        Artifact.submissionArtifact.instructionPC 2873 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2873).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2873 1
    _ = 3794 := by
      rw [pc2869]
      rfl
@[simp] theorem pc2871 : Artifact.submissionArtifact.instructionPC 2875 = 3796 := by
  calc
    Artifact.submissionArtifact.instructionPC 2875 =
        Artifact.submissionArtifact.instructionPC 2874 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2874).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2874 1
    _ = 3796 := by
      rw [pc2870]
      rfl
@[simp] theorem pc2872 : Artifact.submissionArtifact.instructionPC 2876 = 3797 := by
  calc
    Artifact.submissionArtifact.instructionPC 2876 =
        Artifact.submissionArtifact.instructionPC 2875 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2875).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2875 1
    _ = 3797 := by
      rw [pc2871]
      rfl
@[simp] theorem pc2873 : Artifact.submissionArtifact.instructionPC 2877 = 3800 := by
  calc
    Artifact.submissionArtifact.instructionPC 2877 =
        Artifact.submissionArtifact.instructionPC 2876 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2876).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2876 1
    _ = 3800 := by
      rw [pc2872]
      rfl
@[simp] theorem pc2874 : Artifact.submissionArtifact.instructionPC 2878 = 3801 := by
  calc
    Artifact.submissionArtifact.instructionPC 2878 =
        Artifact.submissionArtifact.instructionPC 2877 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2877).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2877 1
    _ = 3801 := by
      rw [pc2873]
      rfl
@[simp] theorem pc2875 : Artifact.submissionArtifact.instructionPC 2879 = 3804 := by
  calc
    Artifact.submissionArtifact.instructionPC 2879 =
        Artifact.submissionArtifact.instructionPC 2878 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2878).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2878 1
    _ = 3804 := by
      rw [pc2874]
      rfl
@[simp] theorem pc2876 : Artifact.submissionArtifact.instructionPC 2880 = 3805 := by
  calc
    Artifact.submissionArtifact.instructionPC 2880 =
        Artifact.submissionArtifact.instructionPC 2879 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2879).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2879 1
    _ = 3805 := by
      rw [pc2875]
      rfl
@[simp] theorem pc2877 : Artifact.submissionArtifact.instructionPC 2881 = 3808 := by
  calc
    Artifact.submissionArtifact.instructionPC 2881 =
        Artifact.submissionArtifact.instructionPC 2880 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2880).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2880 1
    _ = 3808 := by
      rw [pc2876]
      rfl
@[simp] theorem pc2878 : Artifact.submissionArtifact.instructionPC 2882 = 3809 := by
  calc
    Artifact.submissionArtifact.instructionPC 2882 =
        Artifact.submissionArtifact.instructionPC 2881 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2881).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2881 1
    _ = 3809 := by
      rw [pc2877]
      rfl
@[simp] theorem pc2879 : Artifact.submissionArtifact.instructionPC 2883 = 3810 := by
  calc
    Artifact.submissionArtifact.instructionPC 2883 =
        Artifact.submissionArtifact.instructionPC 2882 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2882).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2882 1
    _ = 3810 := by
      rw [pc2878]
      rfl
@[simp] theorem pc2880 : Artifact.submissionArtifact.instructionPC 2884 = 3811 := by
  calc
    Artifact.submissionArtifact.instructionPC 2884 =
        Artifact.submissionArtifact.instructionPC 2883 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2883).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2883 1
    _ = 3811 := by
      rw [pc2879]
      rfl
@[simp] theorem pc2881 : Artifact.submissionArtifact.instructionPC 2885 = 3812 := by
  calc
    Artifact.submissionArtifact.instructionPC 2885 =
        Artifact.submissionArtifact.instructionPC 2884 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2884).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2884 1
    _ = 3812 := by
      rw [pc2880]
      rfl
@[simp] theorem pc2882 : Artifact.submissionArtifact.instructionPC 2886 = 3813 := by
  calc
    Artifact.submissionArtifact.instructionPC 2886 =
        Artifact.submissionArtifact.instructionPC 2885 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2885).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2885 1
    _ = 3813 := by
      rw [pc2881]
      rfl
@[simp] theorem pc2883 : Artifact.submissionArtifact.instructionPC 2887 = 3814 := by
  calc
    Artifact.submissionArtifact.instructionPC 2887 =
        Artifact.submissionArtifact.instructionPC 2886 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2886).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2886 1
    _ = 3814 := by
      rw [pc2882]
      rfl
@[simp] theorem pc2884 : Artifact.submissionArtifact.instructionPC 2888 = 3815 := by
  calc
    Artifact.submissionArtifact.instructionPC 2888 =
        Artifact.submissionArtifact.instructionPC 2887 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2887).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2887 1
    _ = 3815 := by
      rw [pc2883]
      rfl
@[simp] theorem pc2885 : Artifact.submissionArtifact.instructionPC 2889 = 3816 := by
  calc
    Artifact.submissionArtifact.instructionPC 2889 =
        Artifact.submissionArtifact.instructionPC 2888 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2888).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2888 1
    _ = 3816 := by
      rw [pc2884]
      rfl
@[simp] theorem pc2886 : Artifact.submissionArtifact.instructionPC 2890 = 3817 := by
  calc
    Artifact.submissionArtifact.instructionPC 2890 =
        Artifact.submissionArtifact.instructionPC 2889 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2889).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2889 1
    _ = 3817 := by
      rw [pc2885]
      rfl
@[simp] theorem pc2887 : Artifact.submissionArtifact.instructionPC 2891 = 3818 := by
  calc
    Artifact.submissionArtifact.instructionPC 2891 =
        Artifact.submissionArtifact.instructionPC 2890 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2890).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2890 1
    _ = 3818 := by
      rw [pc2886]
      rfl
@[simp] theorem pc2888 : Artifact.submissionArtifact.instructionPC 2892 = 3819 := by
  calc
    Artifact.submissionArtifact.instructionPC 2892 =
        Artifact.submissionArtifact.instructionPC 2891 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2891).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2891 1
    _ = 3819 := by
      rw [pc2887]
      rfl
@[simp] theorem pc2889 : Artifact.submissionArtifact.instructionPC 2893 = 3820 := by
  calc
    Artifact.submissionArtifact.instructionPC 2893 =
        Artifact.submissionArtifact.instructionPC 2892 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2892).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2892 1
    _ = 3820 := by
      rw [pc2888]
      rfl
@[simp] theorem pc2890 : Artifact.submissionArtifact.instructionPC 2894 = 3821 := by
  calc
    Artifact.submissionArtifact.instructionPC 2894 =
        Artifact.submissionArtifact.instructionPC 2893 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2893).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2893 1
    _ = 3821 := by
      rw [pc2889]
      rfl
@[simp] theorem pc2891 : Artifact.submissionArtifact.instructionPC 2895 = 3822 := by
  calc
    Artifact.submissionArtifact.instructionPC 2895 =
        Artifact.submissionArtifact.instructionPC 2894 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2894).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2894 1
    _ = 3822 := by
      rw [pc2890]
      rfl
@[simp] theorem pc2892 : Artifact.submissionArtifact.instructionPC 2896 = 3823 := by
  calc
    Artifact.submissionArtifact.instructionPC 2896 =
        Artifact.submissionArtifact.instructionPC 2895 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2895).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2895 1
    _ = 3823 := by
      rw [pc2891]
      rfl
@[simp] theorem pc2893 : Artifact.submissionArtifact.instructionPC 2897 = 3824 := by
  calc
    Artifact.submissionArtifact.instructionPC 2897 =
        Artifact.submissionArtifact.instructionPC 2896 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2896).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2896 1
    _ = 3824 := by
      rw [pc2892]
      rfl
@[simp] theorem pc2894 : Artifact.submissionArtifact.instructionPC 2898 = 3825 := by
  calc
    Artifact.submissionArtifact.instructionPC 2898 =
        Artifact.submissionArtifact.instructionPC 2897 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2897).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2897 1
    _ = 3825 := by
      rw [pc2893]
      rfl
@[simp] theorem pc2895 : Artifact.submissionArtifact.instructionPC 2899 = 3826 := by
  calc
    Artifact.submissionArtifact.instructionPC 2899 =
        Artifact.submissionArtifact.instructionPC 2898 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2898).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2898 1
    _ = 3826 := by
      rw [pc2894]
      rfl
@[simp] theorem pc2896 : Artifact.submissionArtifact.instructionPC 2900 = 3827 := by
  calc
    Artifact.submissionArtifact.instructionPC 2900 =
        Artifact.submissionArtifact.instructionPC 2899 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2899).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2899 1
    _ = 3827 := by
      rw [pc2895]
      rfl
@[simp] theorem pc2897 : Artifact.submissionArtifact.instructionPC 2901 = 3828 := by
  calc
    Artifact.submissionArtifact.instructionPC 2901 =
        Artifact.submissionArtifact.instructionPC 2900 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2900).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2900 1
    _ = 3828 := by
      rw [pc2896]
      rfl
@[simp] theorem pc2898 : Artifact.submissionArtifact.instructionPC 2902 = 3829 := by
  calc
    Artifact.submissionArtifact.instructionPC 2902 =
        Artifact.submissionArtifact.instructionPC 2901 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2901).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2901 1
    _ = 3829 := by
      rw [pc2897]
      rfl
@[simp] theorem pc2899 : Artifact.submissionArtifact.instructionPC 2903 = 3830 := by
  calc
    Artifact.submissionArtifact.instructionPC 2903 =
        Artifact.submissionArtifact.instructionPC 2902 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2902).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2902 1
    _ = 3830 := by
      rw [pc2898]
      rfl
@[simp] theorem pc2900 : Artifact.submissionArtifact.instructionPC 2904 = 3831 := by
  calc
    Artifact.submissionArtifact.instructionPC 2904 =
        Artifact.submissionArtifact.instructionPC 2903 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2903).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2903 1
    _ = 3831 := by
      rw [pc2899]
      rfl
@[simp] theorem pc2901 : Artifact.submissionArtifact.instructionPC 2905 = 3832 := by
  calc
    Artifact.submissionArtifact.instructionPC 2905 =
        Artifact.submissionArtifact.instructionPC 2904 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2904).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2904 1
    _ = 3832 := by
      rw [pc2900]
      rfl
@[simp] theorem pc2902 : Artifact.submissionArtifact.instructionPC 2906 = 3833 := by
  calc
    Artifact.submissionArtifact.instructionPC 2906 =
        Artifact.submissionArtifact.instructionPC 2905 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2905).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2905 1
    _ = 3833 := by
      rw [pc2901]
      rfl
@[simp] theorem pc2903 : Artifact.submissionArtifact.instructionPC 2907 = 3834 := by
  calc
    Artifact.submissionArtifact.instructionPC 2907 =
        Artifact.submissionArtifact.instructionPC 2906 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2906).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2906 1
    _ = 3834 := by
      rw [pc2902]
      rfl
@[simp] theorem pc2904 : Artifact.submissionArtifact.instructionPC 2908 = 3835 := by
  calc
    Artifact.submissionArtifact.instructionPC 2908 =
        Artifact.submissionArtifact.instructionPC 2907 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2907).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2907 1
    _ = 3835 := by
      rw [pc2903]
      rfl
@[simp] theorem pc2905 : Artifact.submissionArtifact.instructionPC 2909 = 3836 := by
  calc
    Artifact.submissionArtifact.instructionPC 2909 =
        Artifact.submissionArtifact.instructionPC 2908 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2908).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2908 1
    _ = 3836 := by
      rw [pc2904]
      rfl
@[simp] theorem pc2906 : Artifact.submissionArtifact.instructionPC 2910 = 3837 := by
  calc
    Artifact.submissionArtifact.instructionPC 2910 =
        Artifact.submissionArtifact.instructionPC 2909 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2909).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2909 1
    _ = 3837 := by
      rw [pc2905]
      rfl
@[simp] theorem pc2907 : Artifact.submissionArtifact.instructionPC 2911 = 3838 := by
  calc
    Artifact.submissionArtifact.instructionPC 2911 =
        Artifact.submissionArtifact.instructionPC 2910 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2910).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2910 1
    _ = 3838 := by
      rw [pc2906]
      rfl
@[simp] theorem pc2908 : Artifact.submissionArtifact.instructionPC 2912 = 3839 := by
  calc
    Artifact.submissionArtifact.instructionPC 2912 =
        Artifact.submissionArtifact.instructionPC 2911 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2911).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2911 1
    _ = 3839 := by
      rw [pc2907]
      rfl
@[simp] theorem pc2909 : Artifact.submissionArtifact.instructionPC 2913 = 3840 := by
  calc
    Artifact.submissionArtifact.instructionPC 2913 =
        Artifact.submissionArtifact.instructionPC 2912 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2912).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2912 1
    _ = 3840 := by
      rw [pc2908]
      rfl
@[simp] theorem pc2910 : Artifact.submissionArtifact.instructionPC 2914 = 3841 := by
  calc
    Artifact.submissionArtifact.instructionPC 2914 =
        Artifact.submissionArtifact.instructionPC 2913 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2913).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2913 1
    _ = 3841 := by
      rw [pc2909]
      rfl
@[simp] theorem pc2911 : Artifact.submissionArtifact.instructionPC 2915 = 3842 := by
  calc
    Artifact.submissionArtifact.instructionPC 2915 =
        Artifact.submissionArtifact.instructionPC 2914 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2914).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2914 1
    _ = 3842 := by
      rw [pc2910]
      rfl
@[simp] theorem pc2912 : Artifact.submissionArtifact.instructionPC 2916 = 3843 := by
  calc
    Artifact.submissionArtifact.instructionPC 2916 =
        Artifact.submissionArtifact.instructionPC 2915 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2915).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2915 1
    _ = 3843 := by
      rw [pc2911]
      rfl
@[simp] theorem pc2913 : Artifact.submissionArtifact.instructionPC 2917 = 3844 := by
  calc
    Artifact.submissionArtifact.instructionPC 2917 =
        Artifact.submissionArtifact.instructionPC 2916 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2916).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2916 1
    _ = 3844 := by
      rw [pc2912]
      rfl
@[simp] theorem pc2914 : Artifact.submissionArtifact.instructionPC 2918 = 3845 := by
  calc
    Artifact.submissionArtifact.instructionPC 2918 =
        Artifact.submissionArtifact.instructionPC 2917 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2917).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2917 1
    _ = 3845 := by
      rw [pc2913]
      rfl
@[simp] theorem pc2915 : Artifact.submissionArtifact.instructionPC 2919 = 3846 := by
  calc
    Artifact.submissionArtifact.instructionPC 2919 =
        Artifact.submissionArtifact.instructionPC 2918 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2918).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2918 1
    _ = 3846 := by
      rw [pc2914]
      rfl
@[simp] theorem pc2916 : Artifact.submissionArtifact.instructionPC 2920 = 3847 := by
  calc
    Artifact.submissionArtifact.instructionPC 2920 =
        Artifact.submissionArtifact.instructionPC 2919 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2919).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2919 1
    _ = 3847 := by
      rw [pc2915]
      rfl
@[simp] theorem pc2917 : Artifact.submissionArtifact.instructionPC 2921 = 3848 := by
  calc
    Artifact.submissionArtifact.instructionPC 2921 =
        Artifact.submissionArtifact.instructionPC 2920 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2920).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2920 1
    _ = 3848 := by
      rw [pc2916]
      rfl
@[simp] theorem pc2918 : Artifact.submissionArtifact.instructionPC 2922 = 3851 := by
  calc
    Artifact.submissionArtifact.instructionPC 2922 =
        Artifact.submissionArtifact.instructionPC 2921 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2921).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2921 1
    _ = 3851 := by
      rw [pc2917]
      rfl
@[simp] theorem pc2919 : Artifact.submissionArtifact.instructionPC 2923 = 3852 := by
  calc
    Artifact.submissionArtifact.instructionPC 2923 =
        Artifact.submissionArtifact.instructionPC 2922 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2922).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2922 1
    _ = 3852 := by
      rw [pc2918]
      rfl
@[simp] theorem pc2920 : Artifact.submissionArtifact.instructionPC 2924 = 3853 := by
  calc
    Artifact.submissionArtifact.instructionPC 2924 =
        Artifact.submissionArtifact.instructionPC 2923 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2923).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2923 1
    _ = 3853 := by
      rw [pc2919]
      rfl
@[simp] theorem pc2921 : Artifact.submissionArtifact.instructionPC 2925 = 3856 := by
  calc
    Artifact.submissionArtifact.instructionPC 2925 =
        Artifact.submissionArtifact.instructionPC 2924 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2924).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2924 1
    _ = 3856 := by
      rw [pc2920]
      rfl
@[simp] theorem pcMidPop : Artifact.submissionArtifact.instructionPC 2926 = 3857 := by
  calc
    Artifact.submissionArtifact.instructionPC 2926 =
        Artifact.submissionArtifact.instructionPC 2925 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2925).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2925 1
    _ = 3857 := by
      rw [pc2921]
      rfl
@[simp] theorem pc2922 : Artifact.submissionArtifact.instructionPC 2927 = 3858 := by
  calc
    Artifact.submissionArtifact.instructionPC 2927 =
        Artifact.submissionArtifact.instructionPC 2926 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2926).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2926 1
    _ = 3858 := by
      rw [pcMidPop]
      rfl
@[simp] theorem pc2923 : Artifact.submissionArtifact.instructionPC 2928 = 3859 := by
  calc
    Artifact.submissionArtifact.instructionPC 2928 =
        Artifact.submissionArtifact.instructionPC 2927 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2927).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2927 1
    _ = 3859 := by
      rw [pc2922]
      rfl
@[simp] theorem pc2924 : Artifact.submissionArtifact.instructionPC 2929 = 3860 := by
  calc
    Artifact.submissionArtifact.instructionPC 2929 =
        Artifact.submissionArtifact.instructionPC 2928 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2928).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2928 1
    _ = 3860 := by
      rw [pc2923]
      rfl
@[simp] theorem pc2925 : Artifact.submissionArtifact.instructionPC 2930 = 3863 := by
  calc
    Artifact.submissionArtifact.instructionPC 2930 =
        Artifact.submissionArtifact.instructionPC 2929 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2929).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2929 1
    _ = 3863 := by
      rw [pc2924]
      rfl
@[simp] theorem pc2926 : Artifact.submissionArtifact.instructionPC 2931 = 3864 := by
  calc
    Artifact.submissionArtifact.instructionPC 2931 =
        Artifact.submissionArtifact.instructionPC 2930 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2930).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2930 1
    _ = 3864 := by
      rw [pc2925]
      rfl
@[simp] theorem pc2927 : Artifact.submissionArtifact.instructionPC 2932 = 3865 := by
  calc
    Artifact.submissionArtifact.instructionPC 2932 =
        Artifact.submissionArtifact.instructionPC 2931 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2931).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2931 1
    _ = 3865 := by
      rw [pc2926]
      rfl
@[simp] theorem pc2928 : Artifact.submissionArtifact.instructionPC 2933 = 3866 := by
  calc
    Artifact.submissionArtifact.instructionPC 2933 =
        Artifact.submissionArtifact.instructionPC 2932 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2932).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2932 1
    _ = 3866 := by
      rw [pc2927]
      rfl
@[simp] theorem pc2929 : Artifact.submissionArtifact.instructionPC 2934 = 3867 := by
  calc
    Artifact.submissionArtifact.instructionPC 2934 =
        Artifact.submissionArtifact.instructionPC 2933 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2933).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2933 1
    _ = 3867 := by
      rw [pc2928]
      rfl
@[simp] theorem pc2930 : Artifact.submissionArtifact.instructionPC 2935 = 3868 := by
  calc
    Artifact.submissionArtifact.instructionPC 2935 =
        Artifact.submissionArtifact.instructionPC 2934 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2934).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2934 1
    _ = 3868 := by
      rw [pc2929]
      rfl
@[simp] theorem pc2931 : Artifact.submissionArtifact.instructionPC 2936 = 3869 := by
  calc
    Artifact.submissionArtifact.instructionPC 2936 =
        Artifact.submissionArtifact.instructionPC 2935 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2935).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2935 1
    _ = 3869 := by
      rw [pc2930]
      rfl
@[simp] theorem pc2932 : Artifact.submissionArtifact.instructionPC 2937 = 3870 := by
  calc
    Artifact.submissionArtifact.instructionPC 2937 =
        Artifact.submissionArtifact.instructionPC 2936 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2936).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2936 1
    _ = 3870 := by
      rw [pc2931]
      rfl
@[simp] theorem pc2933 : Artifact.submissionArtifact.instructionPC 2938 = 3871 := by
  calc
    Artifact.submissionArtifact.instructionPC 2938 =
        Artifact.submissionArtifact.instructionPC 2937 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2937).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2937 1
    _ = 3871 := by
      rw [pc2932]
      rfl
@[simp] theorem pc2934 : Artifact.submissionArtifact.instructionPC 2939 = 3872 := by
  calc
    Artifact.submissionArtifact.instructionPC 2939 =
        Artifact.submissionArtifact.instructionPC 2938 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2938).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2938 1
    _ = 3872 := by
      rw [pc2933]
      rfl
@[simp] theorem pc2935 : Artifact.submissionArtifact.instructionPC 2940 = 3873 := by
  calc
    Artifact.submissionArtifact.instructionPC 2940 =
        Artifact.submissionArtifact.instructionPC 2939 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2939).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2939 1
    _ = 3873 := by
      rw [pc2934]
      rfl
@[simp] theorem pc2936 : Artifact.submissionArtifact.instructionPC 2941 = 3874 := by
  calc
    Artifact.submissionArtifact.instructionPC 2941 =
        Artifact.submissionArtifact.instructionPC 2940 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2940).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2940 1
    _ = 3874 := by
      rw [pc2935]
      rfl
@[simp] theorem pc2937 : Artifact.submissionArtifact.instructionPC 2942 = 3875 := by
  calc
    Artifact.submissionArtifact.instructionPC 2942 =
        Artifact.submissionArtifact.instructionPC 2941 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2941).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2941 1
    _ = 3875 := by
      rw [pc2936]
      rfl
@[simp] theorem pc2938 : Artifact.submissionArtifact.instructionPC 2943 = 3876 := by
  calc
    Artifact.submissionArtifact.instructionPC 2943 =
        Artifact.submissionArtifact.instructionPC 2942 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2942).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2942 1
    _ = 3876 := by
      rw [pc2937]
      rfl
@[simp] theorem pc2939 : Artifact.submissionArtifact.instructionPC 2944 = 3877 := by
  calc
    Artifact.submissionArtifact.instructionPC 2944 =
        Artifact.submissionArtifact.instructionPC 2943 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2943).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2943 1
    _ = 3877 := by
      rw [pc2938]
      rfl
@[simp] theorem pc2940 : Artifact.submissionArtifact.instructionPC 2945 = 3878 := by
  calc
    Artifact.submissionArtifact.instructionPC 2945 =
        Artifact.submissionArtifact.instructionPC 2944 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2944).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2944 1
    _ = 3878 := by
      rw [pc2939]
      rfl
@[simp] theorem pc2941 : Artifact.submissionArtifact.instructionPC 2946 = 3879 := by
  calc
    Artifact.submissionArtifact.instructionPC 2946 =
        Artifact.submissionArtifact.instructionPC 2945 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2945).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2945 1
    _ = 3879 := by
      rw [pc2940]
      rfl
@[simp] theorem pc2942 : Artifact.submissionArtifact.instructionPC 2947 = 3882 := by
  calc
    Artifact.submissionArtifact.instructionPC 2947 =
        Artifact.submissionArtifact.instructionPC 2946 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2946).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2946 1
    _ = 3882 := by
      rw [pc2941]
      rfl
@[simp] theorem pc2943 : Artifact.submissionArtifact.instructionPC 2948 = 3883 := by
  calc
    Artifact.submissionArtifact.instructionPC 2948 =
        Artifact.submissionArtifact.instructionPC 2947 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2947).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2947 1
    _ = 3883 := by
      rw [pc2942]
      rfl
@[simp] theorem pc2944 : Artifact.submissionArtifact.instructionPC 2949 = 3884 := by
  calc
    Artifact.submissionArtifact.instructionPC 2949 =
        Artifact.submissionArtifact.instructionPC 2948 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2948).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2948 1
    _ = 3884 := by
      rw [pc2943]
      rfl
@[simp] theorem pc2945 : Artifact.submissionArtifact.instructionPC 2950 = 3885 := by
  calc
    Artifact.submissionArtifact.instructionPC 2950 =
        Artifact.submissionArtifact.instructionPC 2949 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2949).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2949 1
    _ = 3885 := by
      rw [pc2944]
      rfl
@[simp] theorem pc2946 : Artifact.submissionArtifact.instructionPC 2951 = 3886 := by
  calc
    Artifact.submissionArtifact.instructionPC 2951 =
        Artifact.submissionArtifact.instructionPC 2950 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2950).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2950 1
    _ = 3886 := by
      rw [pc2945]
      rfl
@[simp] theorem pc2947 : Artifact.submissionArtifact.instructionPC 2952 = 3887 := by
  calc
    Artifact.submissionArtifact.instructionPC 2952 =
        Artifact.submissionArtifact.instructionPC 2951 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2951).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2951 1
    _ = 3887 := by
      rw [pc2946]
      rfl
@[simp] theorem pc2948 : Artifact.submissionArtifact.instructionPC 2953 = 3888 := by
  calc
    Artifact.submissionArtifact.instructionPC 2953 =
        Artifact.submissionArtifact.instructionPC 2952 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2952).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2952 1
    _ = 3888 := by
      rw [pc2947]
      rfl
@[simp] theorem pc2949 : Artifact.submissionArtifact.instructionPC 2954 = 3891 := by
  calc
    Artifact.submissionArtifact.instructionPC 2954 =
        Artifact.submissionArtifact.instructionPC 2953 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2953).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2953 1
    _ = 3891 := by
      rw [pc2948]
      rfl
@[simp] theorem pc2950 : Artifact.submissionArtifact.instructionPC 2955 = 3892 := by
  calc
    Artifact.submissionArtifact.instructionPC 2955 =
        Artifact.submissionArtifact.instructionPC 2954 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2954).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2954 1
    _ = 3892 := by
      rw [pc2949]
      rfl
@[simp] theorem pc2951 : Artifact.submissionArtifact.instructionPC 2956 = 3893 := by
  calc
    Artifact.submissionArtifact.instructionPC 2956 =
        Artifact.submissionArtifact.instructionPC 2955 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2955).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2955 1
    _ = 3893 := by
      rw [pc2950]
      rfl
@[simp] theorem pc2952 : Artifact.submissionArtifact.instructionPC 2957 = 3894 := by
  calc
    Artifact.submissionArtifact.instructionPC 2957 =
        Artifact.submissionArtifact.instructionPC 2956 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2956).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2956 1
    _ = 3894 := by
      rw [pc2951]
      rfl
@[simp] theorem pc2953 : Artifact.submissionArtifact.instructionPC 2958 = 3897 := by
  calc
    Artifact.submissionArtifact.instructionPC 2958 =
        Artifact.submissionArtifact.instructionPC 2957 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2957).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2957 1
    _ = 3897 := by
      rw [pc2952]
      rfl
@[simp] theorem pc2954 : Artifact.submissionArtifact.instructionPC 2959 = 3898 := by
  calc
    Artifact.submissionArtifact.instructionPC 2959 =
        Artifact.submissionArtifact.instructionPC 2958 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2958).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2958 1
    _ = 3898 := by
      rw [pc2953]
      rfl
@[simp] theorem pc2955 : Artifact.submissionArtifact.instructionPC 2960 = 3899 := by
  calc
    Artifact.submissionArtifact.instructionPC 2960 =
        Artifact.submissionArtifact.instructionPC 2959 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2959).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2959 1
    _ = 3899 := by
      rw [pc2954]
      rfl
@[simp] theorem pc2956 : Artifact.submissionArtifact.instructionPC 2961 = 3900 := by
  calc
    Artifact.submissionArtifact.instructionPC 2961 =
        Artifact.submissionArtifact.instructionPC 2960 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2960).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2960 1
    _ = 3900 := by
      rw [pc2955]
      rfl
@[simp] theorem pc2957 : Artifact.submissionArtifact.instructionPC 2962 = 3901 := by
  calc
    Artifact.submissionArtifact.instructionPC 2962 =
        Artifact.submissionArtifact.instructionPC 2961 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2961).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2961 1
    _ = 3901 := by
      rw [pc2956]
      rfl
@[simp] theorem pc2958 : Artifact.submissionArtifact.instructionPC 2963 = 3902 := by
  calc
    Artifact.submissionArtifact.instructionPC 2963 =
        Artifact.submissionArtifact.instructionPC 2962 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2962).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2962 1
    _ = 3902 := by
      rw [pc2957]
      rfl
@[simp] theorem pc2959 : Artifact.submissionArtifact.instructionPC 2964 = 3905 := by
  calc
    Artifact.submissionArtifact.instructionPC 2964 =
        Artifact.submissionArtifact.instructionPC 2963 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2963).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2963 1
    _ = 3905 := by
      rw [pc2958]
      rfl
@[simp] theorem pc2960 : Artifact.submissionArtifact.instructionPC 2965 = 3906 := by
  calc
    Artifact.submissionArtifact.instructionPC 2965 =
        Artifact.submissionArtifact.instructionPC 2964 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2964).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2964 1
    _ = 3906 := by
      rw [pc2959]
      rfl
@[simp] theorem pc2961 : Artifact.submissionArtifact.instructionPC 2966 = 3907 := by
  calc
    Artifact.submissionArtifact.instructionPC 2966 =
        Artifact.submissionArtifact.instructionPC 2965 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2965).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2965 1
    _ = 3907 := by
      rw [pc2960]
      rfl
@[simp] theorem pc2962 : Artifact.submissionArtifact.instructionPC 2967 = 3908 := by
  calc
    Artifact.submissionArtifact.instructionPC 2967 =
        Artifact.submissionArtifact.instructionPC 2966 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2966).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2966 1
    _ = 3908 := by
      rw [pc2961]
      rfl
@[simp] theorem pc2963 : Artifact.submissionArtifact.instructionPC 2968 = 3909 := by
  calc
    Artifact.submissionArtifact.instructionPC 2968 =
        Artifact.submissionArtifact.instructionPC 2967 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2967).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2967 1
    _ = 3909 := by
      rw [pc2962]
      rfl
@[simp] theorem pc2964 : Artifact.submissionArtifact.instructionPC 2969 = 3910 := by
  calc
    Artifact.submissionArtifact.instructionPC 2969 =
        Artifact.submissionArtifact.instructionPC 2968 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2968).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2968 1
    _ = 3910 := by
      rw [pc2963]
      rfl
@[simp] theorem pc2965 : Artifact.submissionArtifact.instructionPC 2970 = 3911 := by
  calc
    Artifact.submissionArtifact.instructionPC 2970 =
        Artifact.submissionArtifact.instructionPC 2969 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2969).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2969 1
    _ = 3911 := by
      rw [pc2964]
      rfl
@[simp] theorem pc2966 : Artifact.submissionArtifact.instructionPC 2971 = 3912 := by
  calc
    Artifact.submissionArtifact.instructionPC 2971 =
        Artifact.submissionArtifact.instructionPC 2970 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2970).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2970 1
    _ = 3912 := by
      rw [pc2965]
      rfl
@[simp] theorem pc2967 : Artifact.submissionArtifact.instructionPC 2972 = 3913 := by
  calc
    Artifact.submissionArtifact.instructionPC 2972 =
        Artifact.submissionArtifact.instructionPC 2971 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2971).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2971 1
    _ = 3913 := by
      rw [pc2966]
      rfl
@[simp] theorem pc2968 : Artifact.submissionArtifact.instructionPC 2973 = 3914 := by
  calc
    Artifact.submissionArtifact.instructionPC 2973 =
        Artifact.submissionArtifact.instructionPC 2972 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2972).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2972 1
    _ = 3914 := by
      rw [pc2967]
      rfl
@[simp] theorem pc2969 : Artifact.submissionArtifact.instructionPC 2974 = 3915 := by
  calc
    Artifact.submissionArtifact.instructionPC 2974 =
        Artifact.submissionArtifact.instructionPC 2973 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2973).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2973 1
    _ = 3915 := by
      rw [pc2968]
      rfl
@[simp] theorem pc2970 : Artifact.submissionArtifact.instructionPC 2975 = 3916 := by
  calc
    Artifact.submissionArtifact.instructionPC 2975 =
        Artifact.submissionArtifact.instructionPC 2974 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2974).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2974 1
    _ = 3916 := by
      rw [pc2969]
      rfl
@[simp] theorem pc2971 : Artifact.submissionArtifact.instructionPC 2976 = 3917 := by
  calc
    Artifact.submissionArtifact.instructionPC 2976 =
        Artifact.submissionArtifact.instructionPC 2975 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2975).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2975 1
    _ = 3917 := by
      rw [pc2970]
      rfl
@[simp] theorem pc2972 : Artifact.submissionArtifact.instructionPC 2977 = 3918 := by
  calc
    Artifact.submissionArtifact.instructionPC 2977 =
        Artifact.submissionArtifact.instructionPC 2976 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2976).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2976 1
    _ = 3918 := by
      rw [pc2971]
      rfl
@[simp] theorem pc2973 : Artifact.submissionArtifact.instructionPC 2978 = 3919 := by
  calc
    Artifact.submissionArtifact.instructionPC 2978 =
        Artifact.submissionArtifact.instructionPC 2977 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2977).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2977 1
    _ = 3919 := by
      rw [pc2972]
      rfl
@[simp] theorem pc2974 : Artifact.submissionArtifact.instructionPC 2979 = 3920 := by
  calc
    Artifact.submissionArtifact.instructionPC 2979 =
        Artifact.submissionArtifact.instructionPC 2978 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2978).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2978 1
    _ = 3920 := by
      rw [pc2973]
      rfl
@[simp] theorem pc2975 : Artifact.submissionArtifact.instructionPC 2980 = 3921 := by
  calc
    Artifact.submissionArtifact.instructionPC 2980 =
        Artifact.submissionArtifact.instructionPC 2979 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2979).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2979 1
    _ = 3921 := by
      rw [pc2974]
      rfl
@[simp] theorem pc2976 : Artifact.submissionArtifact.instructionPC 2981 = 3922 := by
  calc
    Artifact.submissionArtifact.instructionPC 2981 =
        Artifact.submissionArtifact.instructionPC 2980 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2980).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2980 1
    _ = 3922 := by
      rw [pc2975]
      rfl
@[simp] theorem pc2977 : Artifact.submissionArtifact.instructionPC 2982 = 3923 := by
  calc
    Artifact.submissionArtifact.instructionPC 2982 =
        Artifact.submissionArtifact.instructionPC 2981 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2981).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2981 1
    _ = 3923 := by
      rw [pc2976]
      rfl
@[simp] theorem pc2978 : Artifact.submissionArtifact.instructionPC 2983 = 3924 := by
  calc
    Artifact.submissionArtifact.instructionPC 2983 =
        Artifact.submissionArtifact.instructionPC 2982 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2982).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2982 1
    _ = 3924 := by
      rw [pc2977]
      rfl
@[simp] theorem pc2979 : Artifact.submissionArtifact.instructionPC 2984 = 3925 := by
  calc
    Artifact.submissionArtifact.instructionPC 2984 =
        Artifact.submissionArtifact.instructionPC 2983 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2983).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2983 1
    _ = 3925 := by
      rw [pc2978]
      rfl
@[simp] theorem pc2980 : Artifact.submissionArtifact.instructionPC 2985 = 3926 := by
  calc
    Artifact.submissionArtifact.instructionPC 2985 =
        Artifact.submissionArtifact.instructionPC 2984 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2984).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2984 1
    _ = 3926 := by
      rw [pc2979]
      rfl
@[simp] theorem pc2981 : Artifact.submissionArtifact.instructionPC 2986 = 3927 := by
  calc
    Artifact.submissionArtifact.instructionPC 2986 =
        Artifact.submissionArtifact.instructionPC 2985 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2985).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2985 1
    _ = 3927 := by
      rw [pc2980]
      rfl
@[simp] theorem pc2982 : Artifact.submissionArtifact.instructionPC 2987 = 3928 := by
  calc
    Artifact.submissionArtifact.instructionPC 2987 =
        Artifact.submissionArtifact.instructionPC 2986 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2986).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2986 1
    _ = 3928 := by
      rw [pc2981]
      rfl
@[simp] theorem pc2983 : Artifact.submissionArtifact.instructionPC 2988 = 3930 := by
  calc
    Artifact.submissionArtifact.instructionPC 2988 =
        Artifact.submissionArtifact.instructionPC 2987 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2987).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2987 1
    _ = 3930 := by
      rw [pc2982]
      rfl
@[simp] theorem pc2984 : Artifact.submissionArtifact.instructionPC 2989 = 3931 := by
  calc
    Artifact.submissionArtifact.instructionPC 2989 =
        Artifact.submissionArtifact.instructionPC 2988 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2988).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2988 1
    _ = 3931 := by
      rw [pc2983]
      rfl
@[simp] theorem pc2985 : Artifact.submissionArtifact.instructionPC 2990 = 3932 := by
  calc
    Artifact.submissionArtifact.instructionPC 2990 =
        Artifact.submissionArtifact.instructionPC 2989 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2989).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2989 1
    _ = 3932 := by
      rw [pc2984]
      rfl
@[simp] theorem pc2986 : Artifact.submissionArtifact.instructionPC 2991 = 3935 := by
  calc
    Artifact.submissionArtifact.instructionPC 2991 =
        Artifact.submissionArtifact.instructionPC 2990 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2990).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2990 1
    _ = 3935 := by
      rw [pc2985]
      rfl
@[simp] theorem pc2987 : Artifact.submissionArtifact.instructionPC 2992 = 3936 := by
  calc
    Artifact.submissionArtifact.instructionPC 2992 =
        Artifact.submissionArtifact.instructionPC 2991 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2991).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2991 1
    _ = 3936 := by
      rw [pc2986]
      rfl
@[simp] theorem pc2988 : Artifact.submissionArtifact.instructionPC 2993 = 3937 := by
  calc
    Artifact.submissionArtifact.instructionPC 2993 =
        Artifact.submissionArtifact.instructionPC 2992 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2992).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2992 1
    _ = 3937 := by
      rw [pc2987]
      rfl
@[simp] theorem pc2989 : Artifact.submissionArtifact.instructionPC 2994 = 3940 := by
  calc
    Artifact.submissionArtifact.instructionPC 2994 =
        Artifact.submissionArtifact.instructionPC 2993 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2993).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2993 1
    _ = 3940 := by
      rw [pc2988]
      rfl
@[simp] theorem pc2990 : Artifact.submissionArtifact.instructionPC 2995 = 3941 := by
  calc
    Artifact.submissionArtifact.instructionPC 2995 =
        Artifact.submissionArtifact.instructionPC 2994 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2994).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2994 1
    _ = 3941 := by
      rw [pc2989]
      rfl
@[simp] theorem pc2991 : Artifact.submissionArtifact.instructionPC 2996 = 3942 := by
  calc
    Artifact.submissionArtifact.instructionPC 2996 =
        Artifact.submissionArtifact.instructionPC 2995 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2995).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2995 1
    _ = 3942 := by
      rw [pc2990]
      rfl
@[simp] theorem pc2992 : Artifact.submissionArtifact.instructionPC 2997 = 3945 := by
  calc
    Artifact.submissionArtifact.instructionPC 2997 =
        Artifact.submissionArtifact.instructionPC 2996 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2996).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2996 1
    _ = 3945 := by
      rw [pc2991]
      rfl
@[simp] theorem pc2993 : Artifact.submissionArtifact.instructionPC 2998 = 3946 := by
  calc
    Artifact.submissionArtifact.instructionPC 2998 =
        Artifact.submissionArtifact.instructionPC 2997 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2997).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2997 1
    _ = 3946 := by
      rw [pc2992]
      rfl
@[simp] theorem pc2994 : Artifact.submissionArtifact.instructionPC 2999 = 3947 := by
  calc
    Artifact.submissionArtifact.instructionPC 2999 =
        Artifact.submissionArtifact.instructionPC 2998 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2998).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2998 1
    _ = 3947 := by
      rw [pc2993]
      rfl
@[simp] theorem pc2995 : Artifact.submissionArtifact.instructionPC 3000 = 3948 := by
  calc
    Artifact.submissionArtifact.instructionPC 3000 =
        Artifact.submissionArtifact.instructionPC 2999 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2999).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 2999 1
    _ = 3948 := by
      rw [pc2994]
      rfl
@[simp] theorem pc2996 : Artifact.submissionArtifact.instructionPC 3001 = 3949 := by
  calc
    Artifact.submissionArtifact.instructionPC 3001 =
        Artifact.submissionArtifact.instructionPC 3000 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 3000).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 3000 1
    _ = 3949 := by
      rw [pc2995]
      rfl
@[simp] theorem pc2997 : Artifact.submissionArtifact.instructionPC 3002 = 3952 := by
  calc
    Artifact.submissionArtifact.instructionPC 3002 =
        Artifact.submissionArtifact.instructionPC 3001 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 3001).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 3001 1
    _ = 3952 := by
      rw [pc2996]
      rfl
@[simp] theorem pc2998 : Artifact.submissionArtifact.instructionPC 3003 = 3953 := by
  calc
    Artifact.submissionArtifact.instructionPC 3003 =
        Artifact.submissionArtifact.instructionPC 3002 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 3002).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 3002 1
    _ = 3953 := by
      rw [pc2997]
      rfl
@[simp] theorem pc2999 : Artifact.submissionArtifact.instructionPC 3004 = 3954 := by
  calc
    Artifact.submissionArtifact.instructionPC 3004 =
        Artifact.submissionArtifact.instructionPC 3003 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 3003).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 3003 1
    _ = 3954 := by
      rw [pc2998]
      rfl
@[simp] theorem pc3000 : Artifact.submissionArtifact.instructionPC 3005 = 3955 := by
  calc
    Artifact.submissionArtifact.instructionPC 3005 =
        Artifact.submissionArtifact.instructionPC 3004 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 3004).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 3004 1
    _ = 3955 := by
      rw [pc2999]
      rfl
@[simp] theorem pc3001 : Artifact.submissionArtifact.instructionPC 3006 = 3958 := by
  calc
    Artifact.submissionArtifact.instructionPC 3006 =
        Artifact.submissionArtifact.instructionPC 3005 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 3005).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 3005 1
    _ = 3958 := by
      rw [pc3000]
      rfl
@[simp] theorem pc3002 : Artifact.submissionArtifact.instructionPC 3007 = 3959 := by
  calc
    Artifact.submissionArtifact.instructionPC 3007 =
        Artifact.submissionArtifact.instructionPC 3006 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 3006).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 3006 1
    _ = 3959 := by
      rw [pc3001]
      rfl
@[simp] theorem pc3003 : Artifact.submissionArtifact.instructionPC 3008 = 3960 := by
  calc
    Artifact.submissionArtifact.instructionPC 3008 =
        Artifact.submissionArtifact.instructionPC 3007 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 3007).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 3007 1
    _ = 3960 := by
      rw [pc3002]
      rfl
@[simp] theorem pc3004 : Artifact.submissionArtifact.instructionPC 3009 = 3963 := by
  calc
    Artifact.submissionArtifact.instructionPC 3009 =
        Artifact.submissionArtifact.instructionPC 3008 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 3008).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 3008 1
    _ = 3963 := by
      rw [pc3003]
      rfl
@[simp] theorem pc3005 : Artifact.submissionArtifact.instructionPC 3010 = 3964 := by
  calc
    Artifact.submissionArtifact.instructionPC 3010 =
        Artifact.submissionArtifact.instructionPC 3009 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 3009).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 3009 1
    _ = 3964 := by
      rw [pc3004]
      rfl
@[simp] theorem pc3006 : Artifact.submissionArtifact.instructionPC 3011 = 3965 := by
  calc
    Artifact.submissionArtifact.instructionPC 3011 =
        Artifact.submissionArtifact.instructionPC 3010 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 3010).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 3010 1
    _ = 3965 := by
      rw [pc3005]
      rfl
@[simp] theorem pc3007 : Artifact.submissionArtifact.instructionPC 3012 = 3968 := by
  calc
    Artifact.submissionArtifact.instructionPC 3012 =
        Artifact.submissionArtifact.instructionPC 3011 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 3011).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 3011 1
    _ = 3968 := by
      rw [pc3006]
      rfl
@[simp] theorem pc3008 : Artifact.submissionArtifact.instructionPC 3013 = 3969 := by
  calc
    Artifact.submissionArtifact.instructionPC 3013 =
        Artifact.submissionArtifact.instructionPC 3012 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 3012).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 3012 1
    _ = 3969 := by
      rw [pc3007]
      rfl
@[simp] theorem pc3009 : Artifact.submissionArtifact.instructionPC 3014 = 3970 := by
  calc
    Artifact.submissionArtifact.instructionPC 3014 =
        Artifact.submissionArtifact.instructionPC 3013 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 3013).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 3013 1
    _ = 3970 := by
      rw [pc3008]
      rfl
@[simp] theorem pc3010 : Artifact.submissionArtifact.instructionPC 3015 = 3973 := by
  calc
    Artifact.submissionArtifact.instructionPC 3015 =
        Artifact.submissionArtifact.instructionPC 3014 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 3014).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 3014 1
    _ = 3973 := by
      rw [pc3009]
      rfl
@[simp] theorem pc3011 : Artifact.submissionArtifact.instructionPC 3016 = 3974 := by
  calc
    Artifact.submissionArtifact.instructionPC 3016 =
        Artifact.submissionArtifact.instructionPC 3015 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 3015).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 3015 1
    _ = 3974 := by
      rw [pc3010]
      rfl
@[simp] theorem pc3012 : Artifact.submissionArtifact.instructionPC 3017 = 3975 := by
  calc
    Artifact.submissionArtifact.instructionPC 3017 =
        Artifact.submissionArtifact.instructionPC 3016 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 3016).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 3016 1
    _ = 3975 := by
      rw [pc3011]
      rfl
@[simp] theorem pc3013 : Artifact.submissionArtifact.instructionPC 3018 = 3976 := by
  calc
    Artifact.submissionArtifact.instructionPC 3018 =
        Artifact.submissionArtifact.instructionPC 3017 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 3017).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 3017 1
    _ = 3976 := by
      rw [pc3012]
      rfl
@[simp] theorem pc3014 : Artifact.submissionArtifact.instructionPC 3019 = 3977 := by
  calc
    Artifact.submissionArtifact.instructionPC 3019 =
        Artifact.submissionArtifact.instructionPC 3018 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 3018).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 3018 1
    _ = 3977 := by
      rw [pc3013]
      rfl
@[simp] theorem pc3015 : Artifact.submissionArtifact.instructionPC 3020 = 3980 := by
  calc
    Artifact.submissionArtifact.instructionPC 3020 =
        Artifact.submissionArtifact.instructionPC 3019 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 3019).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 3019 1
    _ = 3980 := by
      rw [pc3014]
      rfl
@[simp] theorem pc3016 : Artifact.submissionArtifact.instructionPC 3021 = 3981 := by
  calc
    Artifact.submissionArtifact.instructionPC 3021 =
        Artifact.submissionArtifact.instructionPC 3020 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 3020).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 3020 1
    _ = 3981 := by
      rw [pc3015]
      rfl
@[simp] theorem pc3017 : Artifact.submissionArtifact.instructionPC 3022 = 3982 := by
  calc
    Artifact.submissionArtifact.instructionPC 3022 =
        Artifact.submissionArtifact.instructionPC 3021 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 3021).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 3021 1
    _ = 3982 := by
      rw [pc3016]
      rfl
@[simp] theorem pc3018 : Artifact.submissionArtifact.instructionPC 3023 = 3983 := by
  calc
    Artifact.submissionArtifact.instructionPC 3023 =
        Artifact.submissionArtifact.instructionPC 3022 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 3022).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 3022 1
    _ = 3983 := by
      rw [pc3017]
      rfl
@[simp] theorem pc3019 : Artifact.submissionArtifact.instructionPC 3024 = 3984 := by
  calc
    Artifact.submissionArtifact.instructionPC 3024 =
        Artifact.submissionArtifact.instructionPC 3023 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 3023).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 3023 1
    _ = 3984 := by
      rw [pc3018]
      rfl
@[simp] theorem pc3020 : Artifact.submissionArtifact.instructionPC 3025 = 3985 := by
  calc
    Artifact.submissionArtifact.instructionPC 3025 =
        Artifact.submissionArtifact.instructionPC 3024 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 3024).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 3024 1
    _ = 3985 := by
      rw [pc3019]
      rfl
@[simp] theorem pc3021 : Artifact.submissionArtifact.instructionPC 3026 = 3986 := by
  calc
    Artifact.submissionArtifact.instructionPC 3026 =
        Artifact.submissionArtifact.instructionPC 3025 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 3025).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 3025 1
    _ = 3986 := by
      rw [pc3020]
      rfl
@[simp] theorem pc3022 : Artifact.submissionArtifact.instructionPC 3027 = 3987 := by
  calc
    Artifact.submissionArtifact.instructionPC 3027 =
        Artifact.submissionArtifact.instructionPC 3026 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 3026).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 3026 1
    _ = 3987 := by
      rw [pc3021]
      rfl
@[simp] theorem pc3023 : Artifact.submissionArtifact.instructionPC 3028 = 3988 := by
  calc
    Artifact.submissionArtifact.instructionPC 3028 =
        Artifact.submissionArtifact.instructionPC 3027 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 3027).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 3027 1
    _ = 3988 := by
      rw [pc3022]
      rfl
@[simp] theorem pc3024 : Artifact.submissionArtifact.instructionPC 3029 = 3989 := by
  calc
    Artifact.submissionArtifact.instructionPC 3029 =
        Artifact.submissionArtifact.instructionPC 3028 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 3028).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 3028 1
    _ = 3989 := by
      rw [pc3023]
      rfl
@[simp] theorem pc3025 : Artifact.submissionArtifact.instructionPC 3030 = 3990 := by
  calc
    Artifact.submissionArtifact.instructionPC 3030 =
        Artifact.submissionArtifact.instructionPC 3029 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 3029).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 3029 1
    _ = 3990 := by
      rw [pc3024]
      rfl
@[simp] theorem pc3026 : Artifact.submissionArtifact.instructionPC 3031 = 3991 := by
  calc
    Artifact.submissionArtifact.instructionPC 3031 =
        Artifact.submissionArtifact.instructionPC 3030 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 3030).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 3030 1
    _ = 3991 := by
      rw [pc3025]
      rfl
@[simp] theorem pc3027 : Artifact.submissionArtifact.instructionPC 3032 = 3992 := by
  calc
    Artifact.submissionArtifact.instructionPC 3032 =
        Artifact.submissionArtifact.instructionPC 3031 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 3031).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 3031 1
    _ = 3992 := by
      rw [pc3026]
      rfl
@[simp] theorem pc3028 : Artifact.submissionArtifact.instructionPC 3033 = 3993 := by
  calc
    Artifact.submissionArtifact.instructionPC 3033 =
        Artifact.submissionArtifact.instructionPC 3032 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 3032).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 3032 1
    _ = 3993 := by
      rw [pc3027]
      rfl
@[simp] theorem pc3029 : Artifact.submissionArtifact.instructionPC 3034 = 3994 := by
  calc
    Artifact.submissionArtifact.instructionPC 3034 =
        Artifact.submissionArtifact.instructionPC 3033 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 3033).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 3033 1
    _ = 3994 := by
      rw [pc3028]
      rfl
@[simp] theorem pc3030 : Artifact.submissionArtifact.instructionPC 3035 = 3995 := by
  calc
    Artifact.submissionArtifact.instructionPC 3035 =
        Artifact.submissionArtifact.instructionPC 3034 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 3034).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 3034 1
    _ = 3995 := by
      rw [pc3029]
      rfl
@[simp] theorem pc3031 : Artifact.submissionArtifact.instructionPC 3036 = 3996 := by
  calc
    Artifact.submissionArtifact.instructionPC 3036 =
        Artifact.submissionArtifact.instructionPC 3035 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 3035).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 3035 1
    _ = 3996 := by
      rw [pc3030]
      rfl
@[simp] theorem pc3032 : Artifact.submissionArtifact.instructionPC 3037 = 3997 := by
  calc
    Artifact.submissionArtifact.instructionPC 3037 =
        Artifact.submissionArtifact.instructionPC 3036 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 3036).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 3036 1
    _ = 3997 := by
      rw [pc3031]
      rfl
@[simp] theorem pc3033 : Artifact.submissionArtifact.instructionPC 3038 = 3998 := by
  calc
    Artifact.submissionArtifact.instructionPC 3038 =
        Artifact.submissionArtifact.instructionPC 3037 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 3037).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 3037 1
    _ = 3998 := by
      rw [pc3032]
      rfl
@[simp] theorem pc3034 : Artifact.submissionArtifact.instructionPC 3039 = 3999 := by
  calc
    Artifact.submissionArtifact.instructionPC 3039 =
        Artifact.submissionArtifact.instructionPC 3038 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 3038).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 3038 1
    _ = 3999 := by
      rw [pc3033]
      rfl
@[simp] theorem pc3035 : Artifact.submissionArtifact.instructionPC 3040 = 4000 := by
  calc
    Artifact.submissionArtifact.instructionPC 3040 =
        Artifact.submissionArtifact.instructionPC 3039 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 3039).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 3039 1
    _ = 4000 := by
      rw [pc3034]
      rfl
@[simp] theorem pc3036 : Artifact.submissionArtifact.instructionPC 3041 = 4002 := by
  calc
    Artifact.submissionArtifact.instructionPC 3041 =
        Artifact.submissionArtifact.instructionPC 3040 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 3040).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 3040 1
    _ = 4002 := by
      rw [pc3035]
      rfl
@[simp] theorem pc3037 : Artifact.submissionArtifact.instructionPC 3042 = 4003 := by
  calc
    Artifact.submissionArtifact.instructionPC 3042 =
        Artifact.submissionArtifact.instructionPC 3041 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 3041).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 3041 1
    _ = 4003 := by
      rw [pc3036]
      rfl
@[simp] theorem pc3038 : Artifact.submissionArtifact.instructionPC 3043 = 4004 := by
  calc
    Artifact.submissionArtifact.instructionPC 3043 =
        Artifact.submissionArtifact.instructionPC 3042 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 3042).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 3042 1
    _ = 4004 := by
      rw [pc3037]
      rfl
@[simp] theorem pc3039 : Artifact.submissionArtifact.instructionPC 3044 = 4007 := by
  calc
    Artifact.submissionArtifact.instructionPC 3044 =
        Artifact.submissionArtifact.instructionPC 3043 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 3043).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 3043 1
    _ = 4007 := by
      rw [pc3038]
      rfl
@[simp] theorem pc3040 : Artifact.submissionArtifact.instructionPC 3045 = 4008 := by
  calc
    Artifact.submissionArtifact.instructionPC 3045 =
        Artifact.submissionArtifact.instructionPC 3044 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 3044).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 3044 1
    _ = 4008 := by
      rw [pc3039]
      rfl
@[simp] theorem pc3041 : Artifact.submissionArtifact.instructionPC 3046 = 4009 := by
  calc
    Artifact.submissionArtifact.instructionPC 3046 =
        Artifact.submissionArtifact.instructionPC 3045 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 3045).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 3045 1
    _ = 4009 := by
      rw [pc3040]
      rfl
@[simp] theorem pc3042 : Artifact.submissionArtifact.instructionPC 3047 = 4012 := by
  calc
    Artifact.submissionArtifact.instructionPC 3047 =
        Artifact.submissionArtifact.instructionPC 3046 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 3046).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 3046 1
    _ = 4012 := by
      rw [pc3041]
      rfl
@[simp] theorem pc3043 : Artifact.submissionArtifact.instructionPC 3048 = 4013 := by
  calc
    Artifact.submissionArtifact.instructionPC 3048 =
        Artifact.submissionArtifact.instructionPC 3047 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 3047).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 3047 1
    _ = 4013 := by
      rw [pc3042]
      rfl
@[simp] theorem pc3044 : Artifact.submissionArtifact.instructionPC 3049 = 4014 := by
  calc
    Artifact.submissionArtifact.instructionPC 3049 =
        Artifact.submissionArtifact.instructionPC 3048 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 3048).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 3048 1
    _ = 4014 := by
      rw [pc3043]
      rfl
@[simp] theorem pc3045 : Artifact.submissionArtifact.instructionPC 3050 = 4017 := by
  calc
    Artifact.submissionArtifact.instructionPC 3050 =
        Artifact.submissionArtifact.instructionPC 3049 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 3049).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 3049 1
    _ = 4017 := by
      rw [pc3044]
      rfl
@[simp] theorem pc3046 : Artifact.submissionArtifact.instructionPC 3051 = 4018 := by
  calc
    Artifact.submissionArtifact.instructionPC 3051 =
        Artifact.submissionArtifact.instructionPC 3050 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 3050).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 3050 1
    _ = 4018 := by
      rw [pc3045]
      rfl
@[simp] theorem pc3047 : Artifact.submissionArtifact.instructionPC 3052 = 4019 := by
  calc
    Artifact.submissionArtifact.instructionPC 3052 =
        Artifact.submissionArtifact.instructionPC 3051 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 3051).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 3051 1
    _ = 4019 := by
      rw [pc3046]
      rfl
@[simp] theorem pc3048 : Artifact.submissionArtifact.instructionPC 3053 = 4022 := by
  calc
    Artifact.submissionArtifact.instructionPC 3053 =
        Artifact.submissionArtifact.instructionPC 3052 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 3052).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 3052 1
    _ = 4022 := by
      rw [pc3047]
      rfl
@[simp] theorem pc3049 : Artifact.submissionArtifact.instructionPC 3054 = 4023 := by
  calc
    Artifact.submissionArtifact.instructionPC 3054 =
        Artifact.submissionArtifact.instructionPC 3053 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 3053).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 3053 1
    _ = 4023 := by
      rw [pc3048]
      rfl
@[simp] theorem pc3050 : Artifact.submissionArtifact.instructionPC 3055 = 4026 := by
  calc
    Artifact.submissionArtifact.instructionPC 3055 =
        Artifact.submissionArtifact.instructionPC 3054 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 3054).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 3054 1
    _ = 4026 := by
      rw [pc3049]
      rfl
@[simp] theorem pc3051 : Artifact.submissionArtifact.instructionPC 3056 = 4027 := by
  calc
    Artifact.submissionArtifact.instructionPC 3056 =
        Artifact.submissionArtifact.instructionPC 3055 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 3055).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 3055 1
    _ = 4027 := by
      rw [pc3050]
      rfl
@[simp] theorem pc3052 : Artifact.submissionArtifact.instructionPC 3057 = 4028 := by
  calc
    Artifact.submissionArtifact.instructionPC 3057 =
        Artifact.submissionArtifact.instructionPC 3056 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 3056).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 3056 1
    _ = 4028 := by
      rw [pc3051]
      rfl
@[simp] theorem pc3053 : Artifact.submissionArtifact.instructionPC 3058 = 4031 := by
  calc
    Artifact.submissionArtifact.instructionPC 3058 =
        Artifact.submissionArtifact.instructionPC 3057 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 3057).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 3057 1
    _ = 4031 := by
      rw [pc3052]
      rfl
@[simp] theorem pc3054 : Artifact.submissionArtifact.instructionPC 3059 = 4034 := by
  calc
    Artifact.submissionArtifact.instructionPC 3059 =
        Artifact.submissionArtifact.instructionPC 3058 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 3058).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 3058 1
    _ = 4034 := by
      rw [pc3053]
      rfl
@[simp] theorem pc3055 : Artifact.submissionArtifact.instructionPC 3060 = 4037 := by
  calc
    Artifact.submissionArtifact.instructionPC 3060 =
        Artifact.submissionArtifact.instructionPC 3059 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 3059).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 3059 1
    _ = 4037 := by
      rw [pc3054]
      rfl
@[simp] theorem pc3056 : Artifact.submissionArtifact.instructionPC 3061 = 4038 := by
  calc
    Artifact.submissionArtifact.instructionPC 3061 =
        Artifact.submissionArtifact.instructionPC 3060 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 3060).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 3060 1
    _ = 4038 := by
      rw [pc3055]
      rfl
@[simp] theorem pc3057 : Artifact.submissionArtifact.instructionPC 3062 = 4039 := by
  calc
    Artifact.submissionArtifact.instructionPC 3062 =
        Artifact.submissionArtifact.instructionPC 3061 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 3061).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 3061 1
    _ = 4039 := by
      rw [pc3056]
      rfl
@[simp] theorem pc3058 : Artifact.submissionArtifact.instructionPC 3063 = 4041 := by
  calc
    Artifact.submissionArtifact.instructionPC 3063 =
        Artifact.submissionArtifact.instructionPC 3062 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 3062).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 3062 1
    _ = 4041 := by
      rw [pc3057]
      rfl
@[simp] theorem pc3059 : Artifact.submissionArtifact.instructionPC 3064 = 4042 := by
  calc
    Artifact.submissionArtifact.instructionPC 3064 =
        Artifact.submissionArtifact.instructionPC 3063 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 3063).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 3063 1
    _ = 4042 := by
      rw [pc3058]
      rfl
@[simp] theorem pc3060 : Artifact.submissionArtifact.instructionPC 3065 = 4043 := by
  calc
    Artifact.submissionArtifact.instructionPC 3065 =
        Artifact.submissionArtifact.instructionPC 3064 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 3064).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 3064 1
    _ = 4043 := by
      rw [pc3059]
      rfl
@[simp] theorem pc3061 : Artifact.submissionArtifact.instructionPC 3066 = 4046 := by
  calc
    Artifact.submissionArtifact.instructionPC 3066 =
        Artifact.submissionArtifact.instructionPC 3065 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 3065).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 3065 1
    _ = 4046 := by
      rw [pc3060]
      rfl
@[simp] theorem pc3062 : Artifact.submissionArtifact.instructionPC 3067 = 4047 := by
  calc
    Artifact.submissionArtifact.instructionPC 3067 =
        Artifact.submissionArtifact.instructionPC 3066 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 3066).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 3066 1
    _ = 4047 := by
      rw [pc3061]
      rfl
@[simp] theorem pc3063 : Artifact.submissionArtifact.instructionPC 3068 = 4048 := by
  calc
    Artifact.submissionArtifact.instructionPC 3068 =
        Artifact.submissionArtifact.instructionPC 3067 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 3067).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 3067 1
    _ = 4048 := by
      rw [pc3062]
      rfl
@[simp] theorem pc3064 : Artifact.submissionArtifact.instructionPC 3069 = 4049 := by
  calc
    Artifact.submissionArtifact.instructionPC 3069 =
        Artifact.submissionArtifact.instructionPC 3068 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 3068).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 3068 1
    _ = 4049 := by
      rw [pc3063]
      rfl
@[simp] theorem pc3065 : Artifact.submissionArtifact.instructionPC 3070 = 4052 := by
  calc
    Artifact.submissionArtifact.instructionPC 3070 =
        Artifact.submissionArtifact.instructionPC 3069 +
          (YulEvmCompiler.assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 3069).take 1)).length :=
      instructionPC_add Artifact.submissionArtifact 3069 1
    _ = 4052 := by
      rw [pc3064]
      rfl

end Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs
