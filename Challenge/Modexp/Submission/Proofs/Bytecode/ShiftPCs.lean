import Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
/-!
# Program counters for the appended shift-reduce blocks

Instruction indices 2862 .. 3523, one lemma each.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs

open EvmSemantics
open EvmSemantics.EVM YulEvmCompiler


private theorem instructionPC_succ (p : Challenge.EvmProof.ProgramArtifact) (index : Nat) (instr : Instr)
    (hget : p.instructions[index]? = some instr) :
    p.instructionPC (index + 1) = p.instructionPC index + instr.bytes.length := by
  simp only [Challenge.EvmProof.ProgramArtifact.instructionPC,
    List.take_add_one, hget, Option.toList_some, assembleBytes_append,
    assembleBytes_cons, assembleBytes_nil, List.append_nil, List.length_append]

@[simp] theorem pc2862 : Artifact.submissionArtifact.instructionPC 2582 = 3437 := by rfl

@[simp] theorem pc2863 : Artifact.submissionArtifact.instructionPC 2583 = 3438 := by
  calc
    Artifact.submissionArtifact.instructionPC 2583 = Artifact.submissionArtifact.instructionPC 2582 + (Instr.op .JUMPDEST).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2582 (Instr.op .JUMPDEST) (by rfl)
    _ = 3438 := by rw [pc2862]; rfl

@[simp] theorem pc2864 : Artifact.submissionArtifact.instructionPC 2584 = 3439 := by
  calc
    Artifact.submissionArtifact.instructionPC 2584 = Artifact.submissionArtifact.instructionPC 2583 + (Instr.op (.Dup { idx := 0 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2583 (Instr.op (.Dup { idx := 0 })) (by rfl)
    _ = 3439 := by rw [pc2863]; rfl

@[simp] theorem pc2865 : Artifact.submissionArtifact.instructionPC 2585 = 3440 := by
  calc
    Artifact.submissionArtifact.instructionPC 2585 = Artifact.submissionArtifact.instructionPC 2584 + (Instr.op (.Dup { idx := 3 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2584 (Instr.op (.Dup { idx := 3 })) (by rfl)
    _ = 3440 := by rw [pc2864]; rfl

@[simp] theorem pc2866 : Artifact.submissionArtifact.instructionPC 2586 = 3441 := by
  calc
    Artifact.submissionArtifact.instructionPC 2586 = Artifact.submissionArtifact.instructionPC 2585 + (Instr.op .EQ).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2585 (Instr.op .EQ) (by rfl)
    _ = 3441 := by rw [pc2865]; rfl

@[simp] theorem pc2867 : Artifact.submissionArtifact.instructionPC 2587 = 3442 := by
  calc
    Artifact.submissionArtifact.instructionPC 2587 = Artifact.submissionArtifact.instructionPC 2586 + (Instr.push 0 0).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2586 (Instr.push 0 0) (by rfl)
    _ = 3442 := by rw [pc2866]; rfl

@[simp] theorem pc2868 : Artifact.submissionArtifact.instructionPC 2588 = 3443 := by
  calc
    Artifact.submissionArtifact.instructionPC 2588 = Artifact.submissionArtifact.instructionPC 2587 + (Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2587 (Instr.op .MLOAD) (by rfl)
    _ = 3443 := by rw [pc2867]; rfl

@[simp] theorem pc2869 : Artifact.submissionArtifact.instructionPC 2589 = 3445 := by
  calc
    Artifact.submissionArtifact.instructionPC 2589 = Artifact.submissionArtifact.instructionPC 2588 + (Instr.push 1 255).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2588 (Instr.push 1 255) (by rfl)
    _ = 3445 := by rw [pc2868]; rfl

@[simp] theorem pc2870 : Artifact.submissionArtifact.instructionPC 2590 = 3446 := by
  calc
    Artifact.submissionArtifact.instructionPC 2590 = Artifact.submissionArtifact.instructionPC 2589 + (Instr.op .SHR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2589 (Instr.op .SHR) (by rfl)
    _ = 3446 := by rw [pc2869]; rfl

@[simp] theorem pc2871 : Artifact.submissionArtifact.instructionPC 2591 = 3447 := by
  calc
    Artifact.submissionArtifact.instructionPC 2591 = Artifact.submissionArtifact.instructionPC 2590 + (Instr.op .AND).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2590 (Instr.op .AND) (by rfl)
    _ = 3447 := by rw [pc2870]; rfl

@[simp] theorem pc2872 : Artifact.submissionArtifact.instructionPC 2592 = 3448 := by
  calc
    Artifact.submissionArtifact.instructionPC 2592 = Artifact.submissionArtifact.instructionPC 2591 + (Instr.op .ISZERO).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2591 (Instr.op .ISZERO) (by rfl)
    _ = 3448 := by rw [pc2871]; rfl

@[simp] theorem pc2873 : Artifact.submissionArtifact.instructionPC 2593 = 3451 := by
  calc
    Artifact.submissionArtifact.instructionPC 2593 = Artifact.submissionArtifact.instructionPC 2592 + (Instr.push 2 3481).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2592 (Instr.push 2 3481) (by rfl)
    _ = 3451 := by rw [pc2872]; rfl

@[simp] theorem pc2874 : Artifact.submissionArtifact.instructionPC 2594 = 3452 := by
  calc
    Artifact.submissionArtifact.instructionPC 2594 = Artifact.submissionArtifact.instructionPC 2593 + (Instr.op .JUMPI).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2593 (Instr.op .JUMPI) (by rfl)
    _ = 3452 := by rw [pc2873]; rfl

@[simp] theorem pc2875 : Artifact.submissionArtifact.instructionPC 2595 = 3453 := by
  calc
    Artifact.submissionArtifact.instructionPC 2595 = Artifact.submissionArtifact.instructionPC 2594 + (Instr.op (.Dup { idx := 0 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2594 (Instr.op (.Dup { idx := 0 })) (by rfl)
    _ = 3453 := by rw [pc2874]; rfl

@[simp] theorem pc2876 : Artifact.submissionArtifact.instructionPC 2596 = 3455 := by
  calc
    Artifact.submissionArtifact.instructionPC 2596 = Artifact.submissionArtifact.instructionPC 2595 + (Instr.push 1 96).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2595 (Instr.push 1 96) (by rfl)
    _ = 3455 := by rw [pc2875]; rfl

@[simp] theorem pc2877 : Artifact.submissionArtifact.instructionPC 2597 = 3458 := by
  calc
    Artifact.submissionArtifact.instructionPC 2597 = Artifact.submissionArtifact.instructionPC 2596 + (Instr.push 2 256).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2596 (Instr.push 2 256) (by rfl)
    _ = 3458 := by rw [pc2876]; rfl

@[simp] theorem pc2878 : Artifact.submissionArtifact.instructionPC 2598 = 3459 := by
  calc
    Artifact.submissionArtifact.instructionPC 2598 = Artifact.submissionArtifact.instructionPC 2597 + (Instr.op .CALLDATACOPY).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2597 (Instr.op .CALLDATACOPY) (by rfl)
    _ = 3459 := by rw [pc2877]; rfl

@[simp] theorem pc2879 : Artifact.submissionArtifact.instructionPC 2599 = 3460 := by
  calc
    Artifact.submissionArtifact.instructionPC 2599 = Artifact.submissionArtifact.instructionPC 2598 + (Instr.op (.Dup { idx := 0 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2598 (Instr.op (.Dup { idx := 0 })) (by rfl)
    _ = 3460 := by rw [pc2878]; rfl

@[simp] theorem pc2880 : Artifact.submissionArtifact.instructionPC 2600 = 3462 := by
  calc
    Artifact.submissionArtifact.instructionPC 2600 = Artifact.submissionArtifact.instructionPC 2599 + (Instr.push 1 96).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2599 (Instr.push 1 96) (by rfl)
    _ = 3462 := by rw [pc2879]; rfl

@[simp] theorem pc2881 : Artifact.submissionArtifact.instructionPC 2601 = 3465 := by
  calc
    Artifact.submissionArtifact.instructionPC 2601 = Artifact.submissionArtifact.instructionPC 2600 + (Instr.push 2 4160).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2600 (Instr.push 2 4160) (by rfl)
    _ = 3465 := by rw [pc2880]; rfl

@[simp] theorem pc2882 : Artifact.submissionArtifact.instructionPC 2602 = 3466 := by
  calc
    Artifact.submissionArtifact.instructionPC 2602 = Artifact.submissionArtifact.instructionPC 2601 + (Instr.op .CALLDATACOPY).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2601 (Instr.op .CALLDATACOPY) (by rfl)
    _ = 3466 := by rw [pc2881]; rfl

@[simp] theorem pc2883 : Artifact.submissionArtifact.instructionPC 2603 = 3467 := by
  calc
    Artifact.submissionArtifact.instructionPC 2603 = Artifact.submissionArtifact.instructionPC 2602 + (Instr.push 0 0).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2602 (Instr.push 0 0) (by rfl)
    _ = 3467 := by rw [pc2882]; rfl

@[simp] theorem pc2884 : Artifact.submissionArtifact.instructionPC 2604 = 3470 := by
  calc
    Artifact.submissionArtifact.instructionPC 2604 = Artifact.submissionArtifact.instructionPC 2603 + (Instr.push 2 4128).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2603 (Instr.push 2 4128) (by rfl)
    _ = 3470 := by rw [pc2883]; rfl

@[simp] theorem pc2885 : Artifact.submissionArtifact.instructionPC 2605 = 3471 := by
  calc
    Artifact.submissionArtifact.instructionPC 2605 = Artifact.submissionArtifact.instructionPC 2604 + (Instr.op .MSTORE).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2604 (Instr.op .MSTORE) (by rfl)
    _ = 3471 := by rw [pc2884]; rfl

@[simp] theorem pc2886 : Artifact.submissionArtifact.instructionPC 2606 = 3474 := by
  calc
    Artifact.submissionArtifact.instructionPC 2606 = Artifact.submissionArtifact.instructionPC 2605 + (Instr.push 2 3498).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2605 (Instr.push 2 3498) (by rfl)
    _ = 3474 := by rw [pc2885]; rfl

@[simp] theorem pc2887 : Artifact.submissionArtifact.instructionPC 2607 = 3477 := by
  calc
    Artifact.submissionArtifact.instructionPC 2607 = Artifact.submissionArtifact.instructionPC 2606 + (Instr.push 2 512).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2606 (Instr.push 2 512) (by rfl)
    _ = 3477 := by rw [pc2886]; rfl

@[simp] theorem pc2888 : Artifact.submissionArtifact.instructionPC 2608 = 3480 := by
  calc
    Artifact.submissionArtifact.instructionPC 2608 = Artifact.submissionArtifact.instructionPC 2607 + (Instr.push 2 4824).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2607 (Instr.push 2 4824) (by rfl)
    _ = 3480 := by rw [pc2887]; rfl

@[simp] theorem pc2889 : Artifact.submissionArtifact.instructionPC 2609 = 3481 := by
  calc
    Artifact.submissionArtifact.instructionPC 2609 = Artifact.submissionArtifact.instructionPC 2608 + (Instr.op .JUMP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2608 (Instr.op .JUMP) (by rfl)
    _ = 3481 := by rw [pc2888]; rfl

@[simp] theorem pc2889a : Artifact.submissionArtifact.instructionPC 2610 = 3482 := by
  calc
    Artifact.submissionArtifact.instructionPC 2610 = Artifact.submissionArtifact.instructionPC 2609 + (Instr.op .JUMPDEST).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2609 (Instr.op .JUMPDEST) (by rfl)
    _ = 3482 := by rw [pc2889]; rfl

@[simp] theorem pc2889b : Artifact.submissionArtifact.instructionPC 2611 = 3484 := by
  calc
    Artifact.submissionArtifact.instructionPC 2611 = Artifact.submissionArtifact.instructionPC 2610 + (Instr.push 1 1).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2610 (Instr.push 1 1) (by rfl)
    _ = 3484 := by rw [pc2889a]; rfl

@[simp] theorem pc2889c : Artifact.submissionArtifact.instructionPC 2612 = 3487 := by
  calc
    Artifact.submissionArtifact.instructionPC 2612 = Artifact.submissionArtifact.instructionPC 2611 + (Instr.push 2 1024).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2611 (Instr.push 2 1024) (by rfl)
    _ = 3487 := by rw [pc2889b]; rfl

@[simp] theorem pc2889d : Artifact.submissionArtifact.instructionPC 2613 = 3488 := by
  calc
    Artifact.submissionArtifact.instructionPC 2613 = Artifact.submissionArtifact.instructionPC 2612 + (Instr.op .MSTORE).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2612 (Instr.op .MSTORE) (by rfl)
    _ = 3488 := by rw [pc2889c]; rfl

@[simp] theorem pc2889e : Artifact.submissionArtifact.instructionPC 2614 = 3491 := by
  calc
    Artifact.submissionArtifact.instructionPC 2614 = Artifact.submissionArtifact.instructionPC 2613 + (Instr.push 2 1435).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2613 (Instr.push 2 1435) (by rfl)
    _ = 3491 := by rw [pc2889d]; rfl

@[simp] theorem pc2890 : Artifact.submissionArtifact.instructionPC 2615 = 3494 := by
  calc
    Artifact.submissionArtifact.instructionPC 2615 = Artifact.submissionArtifact.instructionPC 2614 + (Instr.push 2 1024).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2614 (Instr.push 2 1024) (by rfl)
    _ = 3494 := by rw [pc2889e]; rfl

@[simp] theorem pc2891 : Artifact.submissionArtifact.instructionPC 2616 = 3497 := by
  calc
    Artifact.submissionArtifact.instructionPC 2616 = Artifact.submissionArtifact.instructionPC 2615 + (Instr.push 2 2216).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2615 (Instr.push 2 2216) (by rfl)
    _ = 3497 := by rw [pc2890]; rfl

@[simp] theorem pc2892 : Artifact.submissionArtifact.instructionPC 2617 = 3498 := by
  calc
    Artifact.submissionArtifact.instructionPC 2617 = Artifact.submissionArtifact.instructionPC 2616 + (Instr.op .JUMP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2616 (Instr.op .JUMP) (by rfl)
    _ = 3498 := by rw [pc2891]; rfl

@[simp] theorem pc2893 : Artifact.submissionArtifact.instructionPC 2618 = 3499 := by
  calc
    Artifact.submissionArtifact.instructionPC 2618 = Artifact.submissionArtifact.instructionPC 2617 + (Instr.op .JUMPDEST).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2617 (Instr.op .JUMPDEST) (by rfl)
    _ = 3499 := by rw [pc2892]; rfl

@[simp] theorem pc2894 : Artifact.submissionArtifact.instructionPC 2619 = 3501 := by
  calc
    Artifact.submissionArtifact.instructionPC 2619 = Artifact.submissionArtifact.instructionPC 2618 + (Instr.push 1 1).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2618 (Instr.push 1 1) (by rfl)
    _ = 3501 := by rw [pc2893]; rfl

@[simp] theorem pc2895 : Artifact.submissionArtifact.instructionPC 2620 = 3504 := by
  calc
    Artifact.submissionArtifact.instructionPC 2620 = Artifact.submissionArtifact.instructionPC 2619 + (Instr.push 2 5312).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2619 (Instr.push 2 5312) (by rfl)
    _ = 3504 := by rw [pc2894]; rfl

@[simp] theorem pc2896 : Artifact.submissionArtifact.instructionPC 2621 = 3505 := by
  calc
    Artifact.submissionArtifact.instructionPC 2621 = Artifact.submissionArtifact.instructionPC 2620 + (Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2620 (Instr.op .MLOAD) (by rfl)
    _ = 3505 := by rw [pc2895]; rfl

@[simp] theorem pc2897 : Artifact.submissionArtifact.instructionPC 2622 = 3506 := by
  calc
    Artifact.submissionArtifact.instructionPC 2622 = Artifact.submissionArtifact.instructionPC 2621 + (Instr.op .JUMPDEST).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2621 (Instr.op .JUMPDEST) (by rfl)
    _ = 3506 := by rw [pc2896]; rfl

@[simp] theorem pc2898 : Artifact.submissionArtifact.instructionPC 2623 = 3507 := by
  calc
    Artifact.submissionArtifact.instructionPC 2623 = Artifact.submissionArtifact.instructionPC 2622 + (Instr.op (.Dup { idx := 0 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2622 (Instr.op (.Dup { idx := 0 })) (by rfl)
    _ = 3507 := by rw [pc2897]; rfl

@[simp] theorem pc2899 : Artifact.submissionArtifact.instructionPC 2624 = 3508 := by
  calc
    Artifact.submissionArtifact.instructionPC 2624 = Artifact.submissionArtifact.instructionPC 2623 + (Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2623 (Instr.op .MLOAD) (by rfl)
    _ = 3508 := by rw [pc2898]; rfl

@[simp] theorem pc2900 : Artifact.submissionArtifact.instructionPC 2625 = 3509 := by
  calc
    Artifact.submissionArtifact.instructionPC 2625 = Artifact.submissionArtifact.instructionPC 2624 + (Instr.op .NOT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2624 (Instr.op .NOT) (by rfl)
    _ = 3509 := by rw [pc2899]; rfl

@[simp] theorem pc2901 : Artifact.submissionArtifact.instructionPC 2626 = 3510 := by
  calc
    Artifact.submissionArtifact.instructionPC 2626 = Artifact.submissionArtifact.instructionPC 2625 + (Instr.op (.Dup { idx := 2 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2625 (Instr.op (.Dup { idx := 2 })) (by rfl)
    _ = 3510 := by rw [pc2900]; rfl

@[simp] theorem pc2902 : Artifact.submissionArtifact.instructionPC 2627 = 3511 := by
  calc
    Artifact.submissionArtifact.instructionPC 2627 = Artifact.submissionArtifact.instructionPC 2626 + (Instr.op .ADD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2626 (Instr.op .ADD) (by rfl)
    _ = 3511 := by rw [pc2901]; rfl

@[simp] theorem pc2903 : Artifact.submissionArtifact.instructionPC 2628 = 3512 := by
  calc
    Artifact.submissionArtifact.instructionPC 2628 = Artifact.submissionArtifact.instructionPC 2627 + (Instr.op (.Dup { idx := 2 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2627 (Instr.op (.Dup { idx := 2 })) (by rfl)
    _ = 3512 := by rw [pc2902]; rfl

@[simp] theorem pc2904 : Artifact.submissionArtifact.instructionPC 2629 = 3513 := by
  calc
    Artifact.submissionArtifact.instructionPC 2629 = Artifact.submissionArtifact.instructionPC 2628 + (Instr.op (.Dup { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2628 (Instr.op (.Dup { idx := 1 })) (by rfl)
    _ = 3513 := by rw [pc2903]; rfl

@[simp] theorem pc2905 : Artifact.submissionArtifact.instructionPC 2630 = 3514 := by
  calc
    Artifact.submissionArtifact.instructionPC 2630 = Artifact.submissionArtifact.instructionPC 2629 + (Instr.op .LT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2629 (Instr.op .LT) (by rfl)
    _ = 3514 := by rw [pc2904]; rfl

@[simp] theorem pc2906 : Artifact.submissionArtifact.instructionPC 2631 = 3515 := by
  calc
    Artifact.submissionArtifact.instructionPC 2631 = Artifact.submissionArtifact.instructionPC 2630 + (Instr.op (.Swap { idx := 2 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2630 (Instr.op (.Swap { idx := 2 })) (by rfl)
    _ = 3515 := by rw [pc2905]; rfl

@[simp] theorem pc2907 : Artifact.submissionArtifact.instructionPC 2632 = 3516 := by
  calc
    Artifact.submissionArtifact.instructionPC 2632 = Artifact.submissionArtifact.instructionPC 2631 + (Instr.op .POP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2631 (Instr.op .POP) (by rfl)
    _ = 3516 := by rw [pc2906]; rfl

@[simp] theorem pc2908 : Artifact.submissionArtifact.instructionPC 2633 = 3517 := by
  calc
    Artifact.submissionArtifact.instructionPC 2633 = Artifact.submissionArtifact.instructionPC 2632 + (Instr.op (.Dup { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2632 (Instr.op (.Dup { idx := 1 })) (by rfl)
    _ = 3517 := by rw [pc2907]; rfl

@[simp] theorem pc2909 : Artifact.submissionArtifact.instructionPC 2634 = 3520 := by
  calc
    Artifact.submissionArtifact.instructionPC 2634 = Artifact.submissionArtifact.instructionPC 2633 + (Instr.push 2 1280).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2633 (Instr.push 2 1280) (by rfl)
    _ = 3520 := by rw [pc2908]; rfl

@[simp] theorem pc2910 : Artifact.submissionArtifact.instructionPC 2635 = 3521 := by
  calc
    Artifact.submissionArtifact.instructionPC 2635 = Artifact.submissionArtifact.instructionPC 2634 + (Instr.op .ADD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2634 (Instr.op .ADD) (by rfl)
    _ = 3521 := by rw [pc2909]; rfl

@[simp] theorem pc2911 : Artifact.submissionArtifact.instructionPC 2636 = 3522 := by
  calc
    Artifact.submissionArtifact.instructionPC 2636 = Artifact.submissionArtifact.instructionPC 2635 + (Instr.op .MSTORE).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2635 (Instr.op .MSTORE) (by rfl)
    _ = 3522 := by rw [pc2910]; rfl

@[simp] theorem pc2912 : Artifact.submissionArtifact.instructionPC 2637 = 3523 := by
  calc
    Artifact.submissionArtifact.instructionPC 2637 = Artifact.submissionArtifact.instructionPC 2636 + (Instr.op (.Dup { idx := 0 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2636 (Instr.op (.Dup { idx := 0 })) (by rfl)
    _ = 3523 := by rw [pc2911]; rfl

@[simp] theorem pc2913 : Artifact.submissionArtifact.instructionPC 2638 = 3524 := by
  calc
    Artifact.submissionArtifact.instructionPC 2638 = Artifact.submissionArtifact.instructionPC 2637 + (Instr.op .ISZERO).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2637 (Instr.op .ISZERO) (by rfl)
    _ = 3524 := by rw [pc2912]; rfl

@[simp] theorem pc2914 : Artifact.submissionArtifact.instructionPC 2639 = 3527 := by
  calc
    Artifact.submissionArtifact.instructionPC 2639 = Artifact.submissionArtifact.instructionPC 2638 + (Instr.push 2 3536).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2638 (Instr.push 2 3536) (by rfl)
    _ = 3527 := by rw [pc2913]; rfl

@[simp] theorem pc2915 : Artifact.submissionArtifact.instructionPC 2640 = 3528 := by
  calc
    Artifact.submissionArtifact.instructionPC 2640 = Artifact.submissionArtifact.instructionPC 2639 + (Instr.op .JUMPI).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2639 (Instr.op .JUMPI) (by rfl)
    _ = 3528 := by rw [pc2914]; rfl

@[simp] theorem pc2915_compact : Artifact.submissionArtifact.instructionPC 2641 = 3530 := by
  calc
    Artifact.submissionArtifact.instructionPC 2641 = Artifact.submissionArtifact.instructionPC 2640 + (Instr.push 1 31).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2640 (Instr.push 1 31) (by rfl)
    _ = 3530 := by rw [pc2915]; rfl

@[simp] theorem pc2916 : Artifact.submissionArtifact.instructionPC 2642 = 3531 := by
  calc
    Artifact.submissionArtifact.instructionPC 2642 = Artifact.submissionArtifact.instructionPC 2641 + (Instr.op .NOT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2641 (Instr.op .NOT) (by rfl)
    _ = 3531 := by rw [pc2915_compact]; rfl

@[simp] theorem pc2917 : Artifact.submissionArtifact.instructionPC 2643 = 3532 := by
  calc
    Artifact.submissionArtifact.instructionPC 2643 = Artifact.submissionArtifact.instructionPC 2642 + (Instr.op .ADD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2642 (Instr.op .ADD) (by rfl)
    _ = 3532 := by rw [pc2916]; rfl

@[simp] theorem pc2918 : Artifact.submissionArtifact.instructionPC 2644 = 3535 := by
  calc
    Artifact.submissionArtifact.instructionPC 2644 = Artifact.submissionArtifact.instructionPC 2643 + (Instr.push 2 3505).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2643 (Instr.push 2 3505) (by rfl)
    _ = 3535 := by rw [pc2917]; rfl

@[simp] theorem pc2919 : Artifact.submissionArtifact.instructionPC 2645 = 3536 := by
  calc
    Artifact.submissionArtifact.instructionPC 2645 = Artifact.submissionArtifact.instructionPC 2644 + (Instr.op .JUMP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2644 (Instr.op .JUMP) (by rfl)
    _ = 3536 := by rw [pc2918]; rfl

@[simp] theorem pc2920 : Artifact.submissionArtifact.instructionPC 2646 = 3537 := by
  calc
    Artifact.submissionArtifact.instructionPC 2646 = Artifact.submissionArtifact.instructionPC 2645 + (Instr.op .JUMPDEST).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2645 (Instr.op .JUMPDEST) (by rfl)
    _ = 3537 := by rw [pc2919]; rfl

@[simp] theorem pc2921 : Artifact.submissionArtifact.instructionPC 2647 = 3538 := by
  calc
    Artifact.submissionArtifact.instructionPC 2647 = Artifact.submissionArtifact.instructionPC 2646 + (Instr.op .POP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2646 (Instr.op .POP) (by rfl)
    _ = 3538 := by rw [pc2920]; rfl

@[simp] theorem pc2922 : Artifact.submissionArtifact.instructionPC 2648 = 3539 := by
  calc
    Artifact.submissionArtifact.instructionPC 2648 = Artifact.submissionArtifact.instructionPC 2647 + (Instr.op .POP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2647 (Instr.op .POP) (by rfl)
    _ = 3539 := by rw [pc2921]; rfl

@[simp] theorem pc2923 : Artifact.submissionArtifact.instructionPC 2649 = 3540 := by
  calc
    Artifact.submissionArtifact.instructionPC 2649 = Artifact.submissionArtifact.instructionPC 2648 + (Instr.push 0 0).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2648 (Instr.push 0 0) (by rfl)
    _ = 3540 := by rw [pc2922]; rfl

@[simp] theorem pc2924 : Artifact.submissionArtifact.instructionPC 2650 = 3541 := by
  calc
    Artifact.submissionArtifact.instructionPC 2650 = Artifact.submissionArtifact.instructionPC 2649 + (Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2649 (Instr.op .MLOAD) (by rfl)
    _ = 3541 := by rw [pc2923]; rfl

@[simp] theorem pc2925 : Artifact.submissionArtifact.instructionPC 2651 = 3542 := by
  calc
    Artifact.submissionArtifact.instructionPC 2651 = Artifact.submissionArtifact.instructionPC 2650 + (Instr.op (.Dup { idx := 0 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2650 (Instr.op (.Dup { idx := 0 })) (by rfl)
    _ = 3542 := by rw [pc2924]; rfl

@[simp] theorem pc2926 : Artifact.submissionArtifact.instructionPC 2652 = 3543 := by
  calc
    Artifact.submissionArtifact.instructionPC 2652 = Artifact.submissionArtifact.instructionPC 2651 + (Instr.push 0 0).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2651 (Instr.push 0 0) (by rfl)
    _ = 3543 := by rw [pc2925]; rfl

@[simp] theorem pc2927 : Artifact.submissionArtifact.instructionPC 2653 = 3544 := by
  calc
    Artifact.submissionArtifact.instructionPC 2653 = Artifact.submissionArtifact.instructionPC 2652 + (Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2652 (Instr.op .SUB) (by rfl)
    _ = 3544 := by rw [pc2926]; rfl

@[simp] theorem pc2928 : Artifact.submissionArtifact.instructionPC 2654 = 3545 := by
  calc
    Artifact.submissionArtifact.instructionPC 2654 = Artifact.submissionArtifact.instructionPC 2653 + (Instr.op (.Dup { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2653 (Instr.op (.Dup { idx := 1 })) (by rfl)
    _ = 3545 := by rw [pc2927]; rfl

@[simp] theorem pc2929 : Artifact.submissionArtifact.instructionPC 2655 = 3546 := by
  calc
    Artifact.submissionArtifact.instructionPC 2655 = Artifact.submissionArtifact.instructionPC 2654 + (Instr.op .AND).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2654 (Instr.op .AND) (by rfl)
    _ = 3546 := by rw [pc2928]; rfl

@[simp] theorem pc2930 : Artifact.submissionArtifact.instructionPC 2656 = 3547 := by
  calc
    Artifact.submissionArtifact.instructionPC 2656 = Artifact.submissionArtifact.instructionPC 2655 + (Instr.op (.Dup { idx := 0 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2655 (Instr.op (.Dup { idx := 0 })) (by rfl)
    _ = 3547 := by rw [pc2929]; rfl

@[simp] theorem pc2931 : Artifact.submissionArtifact.instructionPC 2657 = 3550 := by
  calc
    Artifact.submissionArtifact.instructionPC 2657 = Artifact.submissionArtifact.instructionPC 2656 + (Instr.push 2 1536).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2656 (Instr.push 2 1536) (by rfl)
    _ = 3550 := by rw [pc2930]; rfl

@[simp] theorem pc2932 : Artifact.submissionArtifact.instructionPC 2658 = 3551 := by
  calc
    Artifact.submissionArtifact.instructionPC 2658 = Artifact.submissionArtifact.instructionPC 2657 + (Instr.op .MSTORE).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2657 (Instr.op .MSTORE) (by rfl)
    _ = 3551 := by rw [pc2931]; rfl

@[simp] theorem pc2933 : Artifact.submissionArtifact.instructionPC 2659 = 3552 := by
  calc
    Artifact.submissionArtifact.instructionPC 2659 = Artifact.submissionArtifact.instructionPC 2658 + (Instr.op (.Dup { idx := 0 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2658 (Instr.op (.Dup { idx := 0 })) (by rfl)
    _ = 3552 := by rw [pc2932]; rfl

@[simp] theorem pc2934 : Artifact.submissionArtifact.instructionPC 2660 = 3553 := by
  calc
    Artifact.submissionArtifact.instructionPC 2660 = Artifact.submissionArtifact.instructionPC 2659 + (Instr.op (.Dup { idx := 2 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2659 (Instr.op (.Dup { idx := 2 })) (by rfl)
    _ = 3553 := by rw [pc2933]; rfl

@[simp] theorem pc2935 : Artifact.submissionArtifact.instructionPC 2661 = 3554 := by
  calc
    Artifact.submissionArtifact.instructionPC 2661 = Artifact.submissionArtifact.instructionPC 2660 + (Instr.op .DIV).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2660 (Instr.op .DIV) (by rfl)
    _ = 3554 := by rw [pc2934]; rfl

@[simp] theorem pc2936 : Artifact.submissionArtifact.instructionPC 2662 = 3555 := by
  calc
    Artifact.submissionArtifact.instructionPC 2662 = Artifact.submissionArtifact.instructionPC 2661 + (Instr.op (.Dup { idx := 0 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2661 (Instr.op (.Dup { idx := 0 })) (by rfl)
    _ = 3555 := by rw [pc2935]; rfl

@[simp] theorem pc2937 : Artifact.submissionArtifact.instructionPC 2663 = 3558 := by
  calc
    Artifact.submissionArtifact.instructionPC 2663 = Artifact.submissionArtifact.instructionPC 2662 + (Instr.push 2 1568).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2662 (Instr.push 2 1568) (by rfl)
    _ = 3558 := by rw [pc2936]; rfl

@[simp] theorem pc2938 : Artifact.submissionArtifact.instructionPC 2664 = 3559 := by
  calc
    Artifact.submissionArtifact.instructionPC 2664 = Artifact.submissionArtifact.instructionPC 2663 + (Instr.op .MSTORE).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2663 (Instr.op .MSTORE) (by rfl)
    _ = 3559 := by rw [pc2937]; rfl

@[simp] theorem pc2939 : Artifact.submissionArtifact.instructionPC 2665 = 3560 := by
  calc
    Artifact.submissionArtifact.instructionPC 2665 = Artifact.submissionArtifact.instructionPC 2664 + (Instr.op (.Dup { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2664 (Instr.op (.Dup { idx := 1 })) (by rfl)
    _ = 3560 := by rw [pc2938]; rfl

@[simp] theorem pc2940 : Artifact.submissionArtifact.instructionPC 2666 = 3561 := by
  calc
    Artifact.submissionArtifact.instructionPC 2666 = Artifact.submissionArtifact.instructionPC 2665 + (Instr.push 0 0).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2665 (Instr.push 0 0) (by rfl)
    _ = 3561 := by rw [pc2939]; rfl

@[simp] theorem pc2941 : Artifact.submissionArtifact.instructionPC 2667 = 3562 := by
  calc
    Artifact.submissionArtifact.instructionPC 2667 = Artifact.submissionArtifact.instructionPC 2666 + (Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2666 (Instr.op .SUB) (by rfl)
    _ = 3562 := by rw [pc2940]; rfl

@[simp] theorem pc2942 : Artifact.submissionArtifact.instructionPC 2668 = 3563 := by
  calc
    Artifact.submissionArtifact.instructionPC 2668 = Artifact.submissionArtifact.instructionPC 2667 + (Instr.op (.Dup { idx := 2 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2667 (Instr.op (.Dup { idx := 2 })) (by rfl)
    _ = 3563 := by rw [pc2941]; rfl

@[simp] theorem pc2943 : Artifact.submissionArtifact.instructionPC 2669 = 3564 := by
  calc
    Artifact.submissionArtifact.instructionPC 2669 = Artifact.submissionArtifact.instructionPC 2668 + (Instr.op (.Swap { idx := 0 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2668 (Instr.op (.Swap { idx := 0 })) (by rfl)
    _ = 3564 := by rw [pc2942]; rfl

@[simp] theorem pc2944 : Artifact.submissionArtifact.instructionPC 2670 = 3565 := by
  calc
    Artifact.submissionArtifact.instructionPC 2670 = Artifact.submissionArtifact.instructionPC 2669 + (Instr.op .DIV).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2669 (Instr.op .DIV) (by rfl)
    _ = 3565 := by rw [pc2943]; rfl

@[simp] theorem pc2945 : Artifact.submissionArtifact.instructionPC 2671 = 3567 := by
  calc
    Artifact.submissionArtifact.instructionPC 2671 = Artifact.submissionArtifact.instructionPC 2670 + (Instr.push 1 1).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2670 (Instr.push 1 1) (by rfl)
    _ = 3567 := by rw [pc2944]; rfl

@[simp] theorem pc2946 : Artifact.submissionArtifact.instructionPC 2672 = 3568 := by
  calc
    Artifact.submissionArtifact.instructionPC 2672 = Artifact.submissionArtifact.instructionPC 2671 + (Instr.op .ADD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2671 (Instr.op .ADD) (by rfl)
    _ = 3568 := by rw [pc2945]; rfl

@[simp] theorem pc2947 : Artifact.submissionArtifact.instructionPC 2673 = 3571 := by
  calc
    Artifact.submissionArtifact.instructionPC 2673 = Artifact.submissionArtifact.instructionPC 2672 + (Instr.push 2 1600).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2672 (Instr.push 2 1600) (by rfl)
    _ = 3571 := by rw [pc2946]; rfl

@[simp] theorem pc2948 : Artifact.submissionArtifact.instructionPC 2674 = 3572 := by
  calc
    Artifact.submissionArtifact.instructionPC 2674 = Artifact.submissionArtifact.instructionPC 2673 + (Instr.op .MSTORE).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2673 (Instr.op .MSTORE) (by rfl)
    _ = 3572 := by rw [pc2947]; rfl

@[simp] theorem pc2949 : Artifact.submissionArtifact.instructionPC 2675 = 3573 := by
  calc
    Artifact.submissionArtifact.instructionPC 2675 = Artifact.submissionArtifact.instructionPC 2674 + (Instr.op (.Dup { idx := 0 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2674 (Instr.op (.Dup { idx := 0 })) (by rfl)
    _ = 3573 := by rw [pc2948]; rfl

@[simp] theorem pc2950 : Artifact.submissionArtifact.instructionPC 2676 = 3574 := by
  calc
    Artifact.submissionArtifact.instructionPC 2676 = Artifact.submissionArtifact.instructionPC 2675 + (Instr.push 0 0).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2675 (Instr.push 0 0) (by rfl)
    _ = 3574 := by rw [pc2949]; rfl

@[simp] theorem pc2951 : Artifact.submissionArtifact.instructionPC 2677 = 3575 := by
  calc
    Artifact.submissionArtifact.instructionPC 2677 = Artifact.submissionArtifact.instructionPC 2676 + (Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2676 (Instr.op .SUB) (by rfl)
    _ = 3575 := by rw [pc2950]; rfl

@[simp] theorem pc2952 : Artifact.submissionArtifact.instructionPC 2678 = 3576 := by
  calc
    Artifact.submissionArtifact.instructionPC 2678 = Artifact.submissionArtifact.instructionPC 2677 + (Instr.op (.Dup { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2677 (Instr.op (.Dup { idx := 1 })) (by rfl)
    _ = 3576 := by rw [pc2951]; rfl

@[simp] theorem pc2953 : Artifact.submissionArtifact.instructionPC 2679 = 3577 := by
  calc
    Artifact.submissionArtifact.instructionPC 2679 = Artifact.submissionArtifact.instructionPC 2678 + (Instr.op (.Swap { idx := 0 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2678 (Instr.op (.Swap { idx := 0 })) (by rfl)
    _ = 3577 := by rw [pc2952]; rfl

@[simp] theorem pc2954 : Artifact.submissionArtifact.instructionPC 2680 = 3578 := by
  calc
    Artifact.submissionArtifact.instructionPC 2680 = Artifact.submissionArtifact.instructionPC 2679 + (Instr.op .MOD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2679 (Instr.op .MOD) (by rfl)
    _ = 3578 := by rw [pc2953]; rfl

@[simp] theorem pc2955 : Artifact.submissionArtifact.instructionPC 2681 = 3581 := by
  calc
    Artifact.submissionArtifact.instructionPC 2681 = Artifact.submissionArtifact.instructionPC 2680 + (Instr.push 2 1632).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2680 (Instr.push 2 1632) (by rfl)
    _ = 3581 := by rw [pc2954]; rfl

@[simp] theorem pc2957 : Artifact.submissionArtifact.instructionPC 2682 = 3582 := by
  calc
    Artifact.submissionArtifact.instructionPC 2682 = Artifact.submissionArtifact.instructionPC 2681 + (Instr.op .MSTORE).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2681 (Instr.op .MSTORE) (by rfl)
    _ = 3582 := by rw [pc2955]; rfl

@[simp] theorem pc2958 : Artifact.submissionArtifact.instructionPC 2683 = 3583 := by
  calc
    Artifact.submissionArtifact.instructionPC 2683 = Artifact.submissionArtifact.instructionPC 2682 + (Instr.op (.Dup { idx := 0 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2682 (Instr.op (.Dup { idx := 0 })) (by rfl)
    _ = 3583 := by rw [pc2957]; rfl

@[simp] theorem pc2959 : Artifact.submissionArtifact.instructionPC 2684 = 3585 := by
  calc
    Artifact.submissionArtifact.instructionPC 2684 = Artifact.submissionArtifact.instructionPC 2683 + (Instr.push 1 2).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2683 (Instr.push 1 2) (by rfl)
    _ = 3585 := by rw [pc2958]; rfl

@[simp] theorem pc2964 : Artifact.submissionArtifact.instructionPC 2685 = 3586 := by
  calc
    Artifact.submissionArtifact.instructionPC 2685 = Artifact.submissionArtifact.instructionPC 2684 + (Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2684 (Instr.op .SUB) (by rfl)
    _ = 3586 := by rw [pc2959]; rfl

@[simp] theorem pc2965 : Artifact.submissionArtifact.instructionPC 2686 = 3587 := by
  calc
    Artifact.submissionArtifact.instructionPC 2686 = Artifact.submissionArtifact.instructionPC 2685 + (Instr.op (.Dup { idx := 0 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2685 (Instr.op (.Dup { idx := 0 })) (by rfl)
    _ = 3587 := by rw [pc2964]; rfl

@[simp] theorem pc2966 : Artifact.submissionArtifact.instructionPC 2687 = 3588 := by
  calc
    Artifact.submissionArtifact.instructionPC 2687 = Artifact.submissionArtifact.instructionPC 2686 + (Instr.op (.Dup { idx := 2 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2686 (Instr.op (.Dup { idx := 2 })) (by rfl)
    _ = 3588 := by rw [pc2965]; rfl

@[simp] theorem pc2967 : Artifact.submissionArtifact.instructionPC 2688 = 3589 := by
  calc
    Artifact.submissionArtifact.instructionPC 2688 = Artifact.submissionArtifact.instructionPC 2687 + (Instr.op .MUL).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2687 (Instr.op .MUL) (by rfl)
    _ = 3589 := by rw [pc2966]; rfl

@[simp] theorem pc2968 : Artifact.submissionArtifact.instructionPC 2689 = 3591 := by
  calc
    Artifact.submissionArtifact.instructionPC 2689 = Artifact.submissionArtifact.instructionPC 2688 + (Instr.push 1 2).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2688 (Instr.push 1 2) (by rfl)
    _ = 3591 := by rw [pc2967]; rfl

@[simp] theorem pc2969 : Artifact.submissionArtifact.instructionPC 2690 = 3592 := by
  calc
    Artifact.submissionArtifact.instructionPC 2690 = Artifact.submissionArtifact.instructionPC 2689 + (Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2689 (Instr.op .SUB) (by rfl)
    _ = 3592 := by rw [pc2968]; rfl

@[simp] theorem pc2970 : Artifact.submissionArtifact.instructionPC 2691 = 3593 := by
  calc
    Artifact.submissionArtifact.instructionPC 2691 = Artifact.submissionArtifact.instructionPC 2690 + (Instr.op .MUL).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2690 (Instr.op .MUL) (by rfl)
    _ = 3593 := by rw [pc2969]; rfl

@[simp] theorem pc2971 : Artifact.submissionArtifact.instructionPC 2692 = 3594 := by
  calc
    Artifact.submissionArtifact.instructionPC 2692 = Artifact.submissionArtifact.instructionPC 2691 + (Instr.op (.Dup { idx := 0 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2691 (Instr.op (.Dup { idx := 0 })) (by rfl)
    _ = 3594 := by rw [pc2970]; rfl

@[simp] theorem pc2972 : Artifact.submissionArtifact.instructionPC 2693 = 3595 := by
  calc
    Artifact.submissionArtifact.instructionPC 2693 = Artifact.submissionArtifact.instructionPC 2692 + (Instr.op (.Dup { idx := 2 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2692 (Instr.op (.Dup { idx := 2 })) (by rfl)
    _ = 3595 := by rw [pc2971]; rfl

@[simp] theorem pc2973 : Artifact.submissionArtifact.instructionPC 2694 = 3596 := by
  calc
    Artifact.submissionArtifact.instructionPC 2694 = Artifact.submissionArtifact.instructionPC 2693 + (Instr.op .MUL).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2693 (Instr.op .MUL) (by rfl)
    _ = 3596 := by rw [pc2972]; rfl

@[simp] theorem pc2974 : Artifact.submissionArtifact.instructionPC 2695 = 3598 := by
  calc
    Artifact.submissionArtifact.instructionPC 2695 = Artifact.submissionArtifact.instructionPC 2694 + (Instr.push 1 2).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2694 (Instr.push 1 2) (by rfl)
    _ = 3598 := by rw [pc2973]; rfl

@[simp] theorem pc2975 : Artifact.submissionArtifact.instructionPC 2696 = 3599 := by
  calc
    Artifact.submissionArtifact.instructionPC 2696 = Artifact.submissionArtifact.instructionPC 2695 + (Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2695 (Instr.op .SUB) (by rfl)
    _ = 3599 := by rw [pc2974]; rfl

@[simp] theorem pc2976 : Artifact.submissionArtifact.instructionPC 2697 = 3600 := by
  calc
    Artifact.submissionArtifact.instructionPC 2697 = Artifact.submissionArtifact.instructionPC 2696 + (Instr.op .MUL).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2696 (Instr.op .MUL) (by rfl)
    _ = 3600 := by rw [pc2975]; rfl

@[simp] theorem pc2977 : Artifact.submissionArtifact.instructionPC 2698 = 3601 := by
  calc
    Artifact.submissionArtifact.instructionPC 2698 = Artifact.submissionArtifact.instructionPC 2697 + (Instr.op (.Dup { idx := 0 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2697 (Instr.op (.Dup { idx := 0 })) (by rfl)
    _ = 3601 := by rw [pc2976]; rfl

@[simp] theorem pc2978 : Artifact.submissionArtifact.instructionPC 2699 = 3602 := by
  calc
    Artifact.submissionArtifact.instructionPC 2699 = Artifact.submissionArtifact.instructionPC 2698 + (Instr.op (.Dup { idx := 2 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2698 (Instr.op (.Dup { idx := 2 })) (by rfl)
    _ = 3602 := by rw [pc2977]; rfl

@[simp] theorem pc2979 : Artifact.submissionArtifact.instructionPC 2700 = 3603 := by
  calc
    Artifact.submissionArtifact.instructionPC 2700 = Artifact.submissionArtifact.instructionPC 2699 + (Instr.op .MUL).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2699 (Instr.op .MUL) (by rfl)
    _ = 3603 := by rw [pc2978]; rfl

@[simp] theorem pc2980 : Artifact.submissionArtifact.instructionPC 2701 = 3605 := by
  calc
    Artifact.submissionArtifact.instructionPC 2701 = Artifact.submissionArtifact.instructionPC 2700 + (Instr.push 1 2).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2700 (Instr.push 1 2) (by rfl)
    _ = 3605 := by rw [pc2979]; rfl

@[simp] theorem pc2981 : Artifact.submissionArtifact.instructionPC 2702 = 3606 := by
  calc
    Artifact.submissionArtifact.instructionPC 2702 = Artifact.submissionArtifact.instructionPC 2701 + (Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2701 (Instr.op .SUB) (by rfl)
    _ = 3606 := by rw [pc2980]; rfl

@[simp] theorem pc2983 : Artifact.submissionArtifact.instructionPC 2703 = 3607 := by
  calc
    Artifact.submissionArtifact.instructionPC 2703 = Artifact.submissionArtifact.instructionPC 2702 + (Instr.op .MUL).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2702 (Instr.op .MUL) (by rfl)
    _ = 3607 := by rw [pc2981]; rfl

@[simp] theorem pc2984 : Artifact.submissionArtifact.instructionPC 2704 = 3608 := by
  calc
    Artifact.submissionArtifact.instructionPC 2704 = Artifact.submissionArtifact.instructionPC 2703 + (Instr.op (.Dup { idx := 0 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2703 (Instr.op (.Dup { idx := 0 })) (by rfl)
    _ = 3608 := by rw [pc2983]; rfl

@[simp] theorem pc2985 : Artifact.submissionArtifact.instructionPC 2705 = 3609 := by
  calc
    Artifact.submissionArtifact.instructionPC 2705 = Artifact.submissionArtifact.instructionPC 2704 + (Instr.op (.Dup { idx := 2 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2704 (Instr.op (.Dup { idx := 2 })) (by rfl)
    _ = 3609 := by rw [pc2984]; rfl

@[simp] theorem pc2986 : Artifact.submissionArtifact.instructionPC 2706 = 3610 := by
  calc
    Artifact.submissionArtifact.instructionPC 2706 = Artifact.submissionArtifact.instructionPC 2705 + (Instr.op .MUL).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2705 (Instr.op .MUL) (by rfl)
    _ = 3610 := by rw [pc2985]; rfl

@[simp] theorem pc2987 : Artifact.submissionArtifact.instructionPC 2707 = 3612 := by
  calc
    Artifact.submissionArtifact.instructionPC 2707 = Artifact.submissionArtifact.instructionPC 2706 + (Instr.push 1 2).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2706 (Instr.push 1 2) (by rfl)
    _ = 3612 := by rw [pc2986]; rfl

@[simp] theorem pc2988 : Artifact.submissionArtifact.instructionPC 2708 = 3613 := by
  calc
    Artifact.submissionArtifact.instructionPC 2708 = Artifact.submissionArtifact.instructionPC 2707 + (Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2707 (Instr.op .SUB) (by rfl)
    _ = 3613 := by rw [pc2987]; rfl

@[simp] theorem pc2989 : Artifact.submissionArtifact.instructionPC 2709 = 3614 := by
  calc
    Artifact.submissionArtifact.instructionPC 2709 = Artifact.submissionArtifact.instructionPC 2708 + (Instr.op .MUL).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2708 (Instr.op .MUL) (by rfl)
    _ = 3614 := by rw [pc2988]; rfl

@[simp] theorem pc2990 : Artifact.submissionArtifact.instructionPC 2710 = 3615 := by
  calc
    Artifact.submissionArtifact.instructionPC 2710 = Artifact.submissionArtifact.instructionPC 2709 + (Instr.op (.Dup { idx := 0 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2709 (Instr.op (.Dup { idx := 0 })) (by rfl)
    _ = 3615 := by rw [pc2989]; rfl

@[simp] theorem pc2991 : Artifact.submissionArtifact.instructionPC 2711 = 3616 := by
  calc
    Artifact.submissionArtifact.instructionPC 2711 = Artifact.submissionArtifact.instructionPC 2710 + (Instr.op (.Dup { idx := 2 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2710 (Instr.op (.Dup { idx := 2 })) (by rfl)
    _ = 3616 := by rw [pc2990]; rfl

@[simp] theorem pc2992 : Artifact.submissionArtifact.instructionPC 2712 = 3617 := by
  calc
    Artifact.submissionArtifact.instructionPC 2712 = Artifact.submissionArtifact.instructionPC 2711 + (Instr.op .MUL).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2711 (Instr.op .MUL) (by rfl)
    _ = 3617 := by rw [pc2991]; rfl

@[simp] theorem pc2993 : Artifact.submissionArtifact.instructionPC 2713 = 3619 := by
  calc
    Artifact.submissionArtifact.instructionPC 2713 = Artifact.submissionArtifact.instructionPC 2712 + (Instr.push 1 2).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2712 (Instr.push 1 2) (by rfl)
    _ = 3619 := by rw [pc2992]; rfl

@[simp] theorem pc2994 : Artifact.submissionArtifact.instructionPC 2714 = 3620 := by
  calc
    Artifact.submissionArtifact.instructionPC 2714 = Artifact.submissionArtifact.instructionPC 2713 + (Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2713 (Instr.op .SUB) (by rfl)
    _ = 3620 := by rw [pc2993]; rfl

@[simp] theorem pc2995 : Artifact.submissionArtifact.instructionPC 2715 = 3621 := by
  calc
    Artifact.submissionArtifact.instructionPC 2715 = Artifact.submissionArtifact.instructionPC 2714 + (Instr.op .MUL).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2714 (Instr.op .MUL) (by rfl)
    _ = 3621 := by rw [pc2994]; rfl

@[simp] theorem pc2996 : Artifact.submissionArtifact.instructionPC 2716 = 3622 := by
  calc
    Artifact.submissionArtifact.instructionPC 2716 = Artifact.submissionArtifact.instructionPC 2715 + (Instr.op (.Dup { idx := 0 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2715 (Instr.op (.Dup { idx := 0 })) (by rfl)
    _ = 3622 := by rw [pc2995]; rfl

@[simp] theorem pc2997 : Artifact.submissionArtifact.instructionPC 2717 = 3623 := by
  calc
    Artifact.submissionArtifact.instructionPC 2717 = Artifact.submissionArtifact.instructionPC 2716 + (Instr.op (.Dup { idx := 2 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2716 (Instr.op (.Dup { idx := 2 })) (by rfl)
    _ = 3623 := by rw [pc2996]; rfl

@[simp] theorem pc2998 : Artifact.submissionArtifact.instructionPC 2718 = 3624 := by
  calc
    Artifact.submissionArtifact.instructionPC 2718 = Artifact.submissionArtifact.instructionPC 2717 + (Instr.op .MUL).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2717 (Instr.op .MUL) (by rfl)
    _ = 3624 := by rw [pc2997]; rfl

@[simp] theorem pc2999 : Artifact.submissionArtifact.instructionPC 2719 = 3626 := by
  calc
    Artifact.submissionArtifact.instructionPC 2719 = Artifact.submissionArtifact.instructionPC 2718 + (Instr.push 1 2).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2718 (Instr.push 1 2) (by rfl)
    _ = 3626 := by rw [pc2998]; rfl

@[simp] theorem pc3000 : Artifact.submissionArtifact.instructionPC 2720 = 3627 := by
  calc
    Artifact.submissionArtifact.instructionPC 2720 = Artifact.submissionArtifact.instructionPC 2719 + (Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2719 (Instr.op .SUB) (by rfl)
    _ = 3627 := by rw [pc2999]; rfl

@[simp] theorem pc3001 : Artifact.submissionArtifact.instructionPC 2721 = 3628 := by
  calc
    Artifact.submissionArtifact.instructionPC 2721 = Artifact.submissionArtifact.instructionPC 2720 + (Instr.op .MUL).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2720 (Instr.op .MUL) (by rfl)
    _ = 3628 := by rw [pc3000]; rfl

@[simp] theorem pc3002 : Artifact.submissionArtifact.instructionPC 2722 = 3629 := by
  calc
    Artifact.submissionArtifact.instructionPC 2722 = Artifact.submissionArtifact.instructionPC 2721 + (Instr.op (.Dup { idx := 0 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2721 (Instr.op (.Dup { idx := 0 })) (by rfl)
    _ = 3629 := by rw [pc3001]; rfl

@[simp] theorem pc3003 : Artifact.submissionArtifact.instructionPC 2723 = 3630 := by
  calc
    Artifact.submissionArtifact.instructionPC 2723 = Artifact.submissionArtifact.instructionPC 2722 + (Instr.op (.Dup { idx := 2 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2722 (Instr.op (.Dup { idx := 2 })) (by rfl)
    _ = 3630 := by rw [pc3002]; rfl

@[simp] theorem pc3004 : Artifact.submissionArtifact.instructionPC 2724 = 3631 := by
  calc
    Artifact.submissionArtifact.instructionPC 2724 = Artifact.submissionArtifact.instructionPC 2723 + (Instr.op .MUL).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2723 (Instr.op .MUL) (by rfl)
    _ = 3631 := by rw [pc3003]; rfl

@[simp] theorem pc3005 : Artifact.submissionArtifact.instructionPC 2725 = 3633 := by
  calc
    Artifact.submissionArtifact.instructionPC 2725 = Artifact.submissionArtifact.instructionPC 2724 + (Instr.push 1 2).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2724 (Instr.push 1 2) (by rfl)
    _ = 3633 := by rw [pc3004]; rfl

@[simp] theorem pc3006 : Artifact.submissionArtifact.instructionPC 2726 = 3634 := by
  calc
    Artifact.submissionArtifact.instructionPC 2726 = Artifact.submissionArtifact.instructionPC 2725 + (Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2725 (Instr.op .SUB) (by rfl)
    _ = 3634 := by rw [pc3005]; rfl

@[simp] theorem pc3007 : Artifact.submissionArtifact.instructionPC 2727 = 3635 := by
  calc
    Artifact.submissionArtifact.instructionPC 2727 = Artifact.submissionArtifact.instructionPC 2726 + (Instr.op .MUL).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2726 (Instr.op .MUL) (by rfl)
    _ = 3635 := by rw [pc3006]; rfl

@[simp] theorem pc3008 : Artifact.submissionArtifact.instructionPC 2728 = 3638 := by
  calc
    Artifact.submissionArtifact.instructionPC 2728 = Artifact.submissionArtifact.instructionPC 2727 + (Instr.push 2 1664).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2727 (Instr.push 2 1664) (by rfl)
    _ = 3638 := by rw [pc3007]; rfl

@[simp] theorem pc3009 : Artifact.submissionArtifact.instructionPC 2729 = 3639 := by
  calc
    Artifact.submissionArtifact.instructionPC 2729 = Artifact.submissionArtifact.instructionPC 2728 + (Instr.op .MSTORE).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2728 (Instr.op .MSTORE) (by rfl)
    _ = 3639 := by rw [pc3008]; rfl

@[simp] theorem pc3010 : Artifact.submissionArtifact.instructionPC 2730 = 3640 := by
  calc
    Artifact.submissionArtifact.instructionPC 2730 = Artifact.submissionArtifact.instructionPC 2729 + (Instr.op .POP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2729 (Instr.op .POP) (by rfl)
    _ = 3640 := by rw [pc3009]; rfl

@[simp] theorem pc3011 : Artifact.submissionArtifact.instructionPC 2731 = 3641 := by
  calc
    Artifact.submissionArtifact.instructionPC 2731 = Artifact.submissionArtifact.instructionPC 2730 + (Instr.op .POP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2730 (Instr.op .POP) (by rfl)
    _ = 3641 := by rw [pc3010]; rfl

@[simp] theorem pc3012 : Artifact.submissionArtifact.instructionPC 2732 = 3642 := by
  calc
    Artifact.submissionArtifact.instructionPC 2732 = Artifact.submissionArtifact.instructionPC 2731 + (Instr.op .POP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2731 (Instr.op .POP) (by rfl)
    _ = 3642 := by rw [pc3011]; rfl

@[simp] theorem pc3013 : Artifact.submissionArtifact.instructionPC 2733 = 3643 := by
  calc
    Artifact.submissionArtifact.instructionPC 2733 = Artifact.submissionArtifact.instructionPC 2732 + (Instr.op (.Dup { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2732 (Instr.op (.Dup { idx := 1 })) (by rfl)
    _ = 3643 := by rw [pc3012]; rfl

@[simp] theorem pc3014 : Artifact.submissionArtifact.instructionPC 2734 = 3644 := by
  calc
    Artifact.submissionArtifact.instructionPC 2734 = Artifact.submissionArtifact.instructionPC 2733 + (Instr.op .JUMPDEST).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2733 (Instr.op .JUMPDEST) (by rfl)
    _ = 3644 := by rw [pc3013]; rfl

@[simp] theorem pc3015 : Artifact.submissionArtifact.instructionPC 2735 = 3645 := by
  calc
    Artifact.submissionArtifact.instructionPC 2735 = Artifact.submissionArtifact.instructionPC 2734 + (Instr.op (.Dup { idx := 0 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2734 (Instr.op (.Dup { idx := 0 })) (by rfl)
    _ = 3645 := by rw [pc3014]; rfl

@[simp] theorem pc3016 : Artifact.submissionArtifact.instructionPC 2736 = 3646 := by
  calc
    Artifact.submissionArtifact.instructionPC 2736 = Artifact.submissionArtifact.instructionPC 2735 + (Instr.op .ISZERO).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2735 (Instr.op .ISZERO) (by rfl)
    _ = 3646 := by rw [pc3015]; rfl

@[simp] theorem pc3017 : Artifact.submissionArtifact.instructionPC 2737 = 3649 := by
  calc
    Artifact.submissionArtifact.instructionPC 2737 = Artifact.submissionArtifact.instructionPC 2736 + (Instr.push 2 4050).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2736 (Instr.push 2 4050) (by rfl)
    _ = 3649 := by rw [pc3016]; rfl

@[simp] theorem pc3018 : Artifact.submissionArtifact.instructionPC 2738 = 3650 := by
  calc
    Artifact.submissionArtifact.instructionPC 2738 = Artifact.submissionArtifact.instructionPC 2737 + (Instr.op .JUMPI).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2737 (Instr.op .JUMPI) (by rfl)
    _ = 3650 := by rw [pc3017]; rfl

@[simp] theorem pc3019 : Artifact.submissionArtifact.instructionPC 2739 = 3651 := by
  calc
    Artifact.submissionArtifact.instructionPC 2739 = Artifact.submissionArtifact.instructionPC 2738 + (Instr.op (.Dup { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2738 (Instr.op (.Dup { idx := 1 })) (by rfl)
    _ = 3651 := by rw [pc3018]; rfl

@[simp] theorem pc3020 : Artifact.submissionArtifact.instructionPC 2740 = 3654 := by
  calc
    Artifact.submissionArtifact.instructionPC 2740 = Artifact.submissionArtifact.instructionPC 2739 + (Instr.push 2 512).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2739 (Instr.push 2 512) (by rfl)
    _ = 3654 := by rw [pc3019]; rfl

@[simp] theorem pc3021 : Artifact.submissionArtifact.instructionPC 2741 = 3657 := by
  calc
    Artifact.submissionArtifact.instructionPC 2741 = Artifact.submissionArtifact.instructionPC 2740 + (Instr.push 2 4128).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2740 (Instr.push 2 4128) (by rfl)
    _ = 3657 := by rw [pc3020]; rfl

@[simp] theorem pc3022 : Artifact.submissionArtifact.instructionPC 2742 = 3658 := by
  calc
    Artifact.submissionArtifact.instructionPC 2742 = Artifact.submissionArtifact.instructionPC 2741 + (Instr.op .MCOPY).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2741 (Instr.op .MCOPY) (by rfl)
    _ = 3658 := by rw [pc3021]; rfl

@[simp] theorem pc3023 : Artifact.submissionArtifact.instructionPC 2743 = 3659 := by
  calc
    Artifact.submissionArtifact.instructionPC 2743 = Artifact.submissionArtifact.instructionPC 2742 + (Instr.push 0 0).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2742 (Instr.push 0 0) (by rfl)
    _ = 3659 := by rw [pc3022]; rfl

@[simp] theorem pc3024 : Artifact.submissionArtifact.instructionPC 2744 = 3662 := by
  calc
    Artifact.submissionArtifact.instructionPC 2744 = Artifact.submissionArtifact.instructionPC 2743 + (Instr.push 2 5344).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2743 (Instr.push 2 5344) (by rfl)
    _ = 3662 := by rw [pc3023]; rfl

@[simp] theorem pc3025 : Artifact.submissionArtifact.instructionPC 2745 = 3663 := by
  calc
    Artifact.submissionArtifact.instructionPC 2745 = Artifact.submissionArtifact.instructionPC 2744 + (Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2744 (Instr.op .MLOAD) (by rfl)
    _ = 3663 := by rw [pc3024]; rfl

@[simp] theorem pc3027 : Artifact.submissionArtifact.instructionPC 2746 = 3664 := by
  calc
    Artifact.submissionArtifact.instructionPC 2746 = Artifact.submissionArtifact.instructionPC 2745 + (Instr.op .MSTORE).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2745 (Instr.op .MSTORE) (by rfl)
    _ = 3664 := by rw [pc3025]; rfl

@[simp] theorem pc3028 : Artifact.submissionArtifact.instructionPC 2747 = 3667 := by
  calc
    Artifact.submissionArtifact.instructionPC 2747 = Artifact.submissionArtifact.instructionPC 2746 + (Instr.push 2 512).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2746 (Instr.push 2 512) (by rfl)
    _ = 3667 := by rw [pc3027]; rfl

@[simp] theorem pc3029 : Artifact.submissionArtifact.instructionPC 2748 = 3668 := by
  calc
    Artifact.submissionArtifact.instructionPC 2748 = Artifact.submissionArtifact.instructionPC 2747 + (Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2747 (Instr.op .MLOAD) (by rfl)
    _ = 3668 := by rw [pc3028]; rfl

@[simp] theorem pc3030 : Artifact.submissionArtifact.instructionPC 2749 = 3671 := by
  calc
    Artifact.submissionArtifact.instructionPC 2749 = Artifact.submissionArtifact.instructionPC 2748 + (Instr.push 2 1536).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2748 (Instr.push 2 1536) (by rfl)
    _ = 3671 := by rw [pc3029]; rfl

@[simp] theorem pc3031 : Artifact.submissionArtifact.instructionPC 2750 = 3672 := by
  calc
    Artifact.submissionArtifact.instructionPC 2750 = Artifact.submissionArtifact.instructionPC 2749 + (Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2749 (Instr.op .MLOAD) (by rfl)
    _ = 3672 := by rw [pc3030]; rfl

@[simp] theorem pc3032 : Artifact.submissionArtifact.instructionPC 2751 = 3673 := by
  calc
    Artifact.submissionArtifact.instructionPC 2751 = Artifact.submissionArtifact.instructionPC 2750 + (Instr.op (.Dup { idx := 0 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2750 (Instr.op (.Dup { idx := 0 })) (by rfl)
    _ = 3673 := by rw [pc3031]; rfl

@[simp] theorem pc3034 : Artifact.submissionArtifact.instructionPC 2752 = 3674 := by
  calc
    Artifact.submissionArtifact.instructionPC 2752 = Artifact.submissionArtifact.instructionPC 2751 + (Instr.op (.Dup { idx := 2 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2751 (Instr.op (.Dup { idx := 2 })) (by rfl)
    _ = 3674 := by rw [pc3032]; rfl

@[simp] theorem pc3035 : Artifact.submissionArtifact.instructionPC 2753 = 3675 := by
  calc
    Artifact.submissionArtifact.instructionPC 2753 = Artifact.submissionArtifact.instructionPC 2752 + (Instr.op .DIV).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2752 (Instr.op .DIV) (by rfl)
    _ = 3675 := by rw [pc3034]; rfl

@[simp] theorem pc3036 : Artifact.submissionArtifact.instructionPC 2754 = 3676 := by
  calc
    Artifact.submissionArtifact.instructionPC 2754 = Artifact.submissionArtifact.instructionPC 2753 + (Instr.op (.Swap { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2753 (Instr.op (.Swap { idx := 1 })) (by rfl)
    _ = 3676 := by rw [pc3035]; rfl

@[simp] theorem pc3037 : Artifact.submissionArtifact.instructionPC 2755 = 3677 := by
  calc
    Artifact.submissionArtifact.instructionPC 2755 = Artifact.submissionArtifact.instructionPC 2754 + (Instr.op .MOD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2754 (Instr.op .MOD) (by rfl)
    _ = 3677 := by rw [pc3036]; rfl

@[simp] theorem pc3038 : Artifact.submissionArtifact.instructionPC 2756 = 3680 := by
  calc
    Artifact.submissionArtifact.instructionPC 2756 = Artifact.submissionArtifact.instructionPC 2755 + (Instr.push 2 1600).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2755 (Instr.push 2 1600) (by rfl)
    _ = 3680 := by rw [pc3037]; rfl

@[simp] theorem pc3039 : Artifact.submissionArtifact.instructionPC 2757 = 3681 := by
  calc
    Artifact.submissionArtifact.instructionPC 2757 = Artifact.submissionArtifact.instructionPC 2756 + (Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2756 (Instr.op .MLOAD) (by rfl)
    _ = 3681 := by rw [pc3038]; rfl

@[simp] theorem pc3040 : Artifact.submissionArtifact.instructionPC 2758 = 3682 := by
  calc
    Artifact.submissionArtifact.instructionPC 2758 = Artifact.submissionArtifact.instructionPC 2757 + (Instr.op .MUL).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2757 (Instr.op .MUL) (by rfl)
    _ = 3682 := by rw [pc3039]; rfl

@[simp] theorem pc3041 : Artifact.submissionArtifact.instructionPC 2759 = 3685 := by
  calc
    Artifact.submissionArtifact.instructionPC 2759 = Artifact.submissionArtifact.instructionPC 2758 + (Instr.push 2 544).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2758 (Instr.push 2 544) (by rfl)
    _ = 3685 := by rw [pc3040]; rfl

@[simp] theorem pc3042 : Artifact.submissionArtifact.instructionPC 2760 = 3686 := by
  calc
    Artifact.submissionArtifact.instructionPC 2760 = Artifact.submissionArtifact.instructionPC 2759 + (Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2759 (Instr.op .MLOAD) (by rfl)
    _ = 3686 := by rw [pc3041]; rfl

@[simp] theorem pc3043 : Artifact.submissionArtifact.instructionPC 2761 = 3689 := by
  calc
    Artifact.submissionArtifact.instructionPC 2761 = Artifact.submissionArtifact.instructionPC 2760 + (Instr.push 2 1536).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2760 (Instr.push 2 1536) (by rfl)
    _ = 3689 := by rw [pc3042]; rfl

@[simp] theorem pc3044 : Artifact.submissionArtifact.instructionPC 2762 = 3690 := by
  calc
    Artifact.submissionArtifact.instructionPC 2762 = Artifact.submissionArtifact.instructionPC 2761 + (Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2761 (Instr.op .MLOAD) (by rfl)
    _ = 3690 := by rw [pc3043]; rfl

@[simp] theorem pc3045 : Artifact.submissionArtifact.instructionPC 2763 = 3691 := by
  calc
    Artifact.submissionArtifact.instructionPC 2763 = Artifact.submissionArtifact.instructionPC 2762 + (Instr.op (.Swap { idx := 0 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2762 (Instr.op (.Swap { idx := 0 })) (by rfl)
    _ = 3691 := by rw [pc3044]; rfl

@[simp] theorem pc3046 : Artifact.submissionArtifact.instructionPC 2764 = 3692 := by
  calc
    Artifact.submissionArtifact.instructionPC 2764 = Artifact.submissionArtifact.instructionPC 2763 + (Instr.op .DIV).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2763 (Instr.op .DIV) (by rfl)
    _ = 3692 := by rw [pc3045]; rfl

@[simp] theorem pc3047 : Artifact.submissionArtifact.instructionPC 2765 = 3693 := by
  calc
    Artifact.submissionArtifact.instructionPC 2765 = Artifact.submissionArtifact.instructionPC 2764 + (Instr.op .ADD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2764 (Instr.op .ADD) (by rfl)
    _ = 3693 := by rw [pc3046]; rfl

@[simp] theorem pc3048 : Artifact.submissionArtifact.instructionPC 2766 = 3696 := by
  calc
    Artifact.submissionArtifact.instructionPC 2766 = Artifact.submissionArtifact.instructionPC 2765 + (Instr.push 2 1568).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2765 (Instr.push 2 1568) (by rfl)
    _ = 3696 := by rw [pc3047]; rfl

@[simp] theorem pc3049 : Artifact.submissionArtifact.instructionPC 2767 = 3697 := by
  calc
    Artifact.submissionArtifact.instructionPC 2767 = Artifact.submissionArtifact.instructionPC 2766 + (Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2766 (Instr.op .MLOAD) (by rfl)
    _ = 3697 := by rw [pc3048]; rfl

@[simp] theorem pc3050 : Artifact.submissionArtifact.instructionPC 2768 = 3698 := by
  calc
    Artifact.submissionArtifact.instructionPC 2768 = Artifact.submissionArtifact.instructionPC 2767 + (Instr.op (.Dup { idx := 0 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2767 (Instr.op (.Dup { idx := 0 })) (by rfl)
    _ = 3698 := by rw [pc3049]; rfl

@[simp] theorem pc3051 : Artifact.submissionArtifact.instructionPC 2769 = 3701 := by
  calc
    Artifact.submissionArtifact.instructionPC 2769 = Artifact.submissionArtifact.instructionPC 2768 + (Instr.push 2 1632).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2768 (Instr.push 2 1632) (by rfl)
    _ = 3701 := by rw [pc3050]; rfl

@[simp] theorem pc3052 : Artifact.submissionArtifact.instructionPC 2770 = 3702 := by
  calc
    Artifact.submissionArtifact.instructionPC 2770 = Artifact.submissionArtifact.instructionPC 2769 + (Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2769 (Instr.op .MLOAD) (by rfl)
    _ = 3702 := by rw [pc3051]; rfl

@[simp] theorem pc3053 : Artifact.submissionArtifact.instructionPC 2771 = 3703 := by
  calc
    Artifact.submissionArtifact.instructionPC 2771 = Artifact.submissionArtifact.instructionPC 2770 + (Instr.op (.Dup { idx := 4 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2770 (Instr.op (.Dup { idx := 4 })) (by rfl)
    _ = 3703 := by rw [pc3052]; rfl

@[simp] theorem pc3054 : Artifact.submissionArtifact.instructionPC 2772 = 3704 := by
  calc
    Artifact.submissionArtifact.instructionPC 2772 = Artifact.submissionArtifact.instructionPC 2771 + (Instr.op .MULMOD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2771 (Instr.op .MULMOD) (by rfl)
    _ = 3704 := by rw [pc3053]; rfl

@[simp] theorem pc3056 : Artifact.submissionArtifact.instructionPC 2773 = 3705 := by
  calc
    Artifact.submissionArtifact.instructionPC 2773 = Artifact.submissionArtifact.instructionPC 2772 + (Instr.op (.Dup { idx := 2 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2772 (Instr.op (.Dup { idx := 2 })) (by rfl)
    _ = 3705 := by rw [pc3054]; rfl

@[simp] theorem pc3057 : Artifact.submissionArtifact.instructionPC 2774 = 3706 := by
  calc
    Artifact.submissionArtifact.instructionPC 2774 = Artifact.submissionArtifact.instructionPC 2773 + (Instr.op .ADDMOD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2773 (Instr.op .ADDMOD) (by rfl)
    _ = 3706 := by rw [pc3056]; rfl

@[simp] theorem pc3058 : Artifact.submissionArtifact.instructionPC 2775 = 3707 := by
  calc
    Artifact.submissionArtifact.instructionPC 2775 = Artifact.submissionArtifact.instructionPC 2774 + (Instr.op (.Swap { idx := 0 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2774 (Instr.op (.Swap { idx := 0 })) (by rfl)
    _ = 3707 := by rw [pc3057]; rfl

@[simp] theorem pc3059 : Artifact.submissionArtifact.instructionPC 2776 = 3708 := by
  calc
    Artifact.submissionArtifact.instructionPC 2776 = Artifact.submissionArtifact.instructionPC 2775 + (Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2775 (Instr.op .SUB) (by rfl)
    _ = 3708 := by rw [pc3058]; rfl

@[simp] theorem pc3060 : Artifact.submissionArtifact.instructionPC 2777 = 3711 := by
  calc
    Artifact.submissionArtifact.instructionPC 2777 = Artifact.submissionArtifact.instructionPC 2776 + (Instr.push 2 1664).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2776 (Instr.push 2 1664) (by rfl)
    _ = 3711 := by rw [pc3059]; rfl

@[simp] theorem pc3061 : Artifact.submissionArtifact.instructionPC 2778 = 3712 := by
  calc
    Artifact.submissionArtifact.instructionPC 2778 = Artifact.submissionArtifact.instructionPC 2777 + (Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2777 (Instr.op .MLOAD) (by rfl)
    _ = 3712 := by rw [pc3060]; rfl

@[simp] theorem pc3062 : Artifact.submissionArtifact.instructionPC 2779 = 3713 := by
  calc
    Artifact.submissionArtifact.instructionPC 2779 = Artifact.submissionArtifact.instructionPC 2778 + (Instr.op .MUL).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2778 (Instr.op .MUL) (by rfl)
    _ = 3713 := by rw [pc3061]; rfl

@[simp] theorem pc3063 : Artifact.submissionArtifact.instructionPC 2779 = 3713 := pc3062

@[simp] theorem pc3064 : Artifact.submissionArtifact.instructionPC 2779 = 3713 := pc3062

@[simp] theorem pc3065 : Artifact.submissionArtifact.instructionPC 2779 = 3713 := pc3062

@[simp] theorem pc3066 : Artifact.submissionArtifact.instructionPC 2779 = 3713 := pc3062

@[simp] theorem pc3067 : Artifact.submissionArtifact.instructionPC 2797 = 3736 := by rfl

@[simp] theorem pc3068 : Artifact.submissionArtifact.instructionPC 2798 = 3737 := by
  calc
    Artifact.submissionArtifact.instructionPC 2798 = Artifact.submissionArtifact.instructionPC 2797 + (Instr.op (.Swap { idx := 0 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2797 (Instr.op (.Swap { idx := 0 })) (by rfl)
    _ = 3737 := by rw [pc3067]; rfl

@[simp] theorem pcSaturate2987 : Artifact.submissionArtifact.instructionPC 2799 = 3740 := by
  calc
    Artifact.submissionArtifact.instructionPC 2799 = Artifact.submissionArtifact.instructionPC 2798 + (Instr.push 2 1568).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2798 (Instr.push 2 1568) (by rfl)
    _ = 3740 := by rw [pc3068]; rfl

@[simp] theorem pcSaturate2989 : Artifact.submissionArtifact.instructionPC 2800 = 3741 := by
  calc
    Artifact.submissionArtifact.instructionPC 2800 = Artifact.submissionArtifact.instructionPC 2799 + (Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2799 (Instr.op .MLOAD) (by rfl)
    _ = 3741 := by rw [pcSaturate2987]; rfl

@[simp] theorem pcSaturate2990 : Artifact.submissionArtifact.instructionPC 2801 = 3742 := by
  calc
    Artifact.submissionArtifact.instructionPC 2801 = Artifact.submissionArtifact.instructionPC 2800 + (Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2800 (Instr.op .GT) (by rfl)
    _ = 3742 := by rw [pcSaturate2989]; rfl

@[simp] theorem pcSaturate2991 : Artifact.submissionArtifact.instructionPC 2802 = 3743 := by
  calc
    Artifact.submissionArtifact.instructionPC 2802 = Artifact.submissionArtifact.instructionPC 2801 + (Instr.op .ISZERO).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2801 (Instr.op .ISZERO) (by rfl)
    _ = 3743 := by rw [pcSaturate2990]; rfl

@[simp] theorem pcSaturate2992 : Artifact.submissionArtifact.instructionPC 2803 = 3744 := by
  calc
    Artifact.submissionArtifact.instructionPC 2803 = Artifact.submissionArtifact.instructionPC 2802 + (Instr.push 0 0).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2802 (Instr.push 0 0) (by rfl)
    _ = 3744 := by rw [pcSaturate2991]; rfl

@[simp] theorem pcSaturate2993 : Artifact.submissionArtifact.instructionPC 2804 = 3745 := by
  calc
    Artifact.submissionArtifact.instructionPC 2804 = Artifact.submissionArtifact.instructionPC 2803 + (Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2803 (Instr.op .SUB) (by rfl)
    _ = 3745 := by rw [pcSaturate2992]; rfl

@[simp] theorem mac2PC2828 : Artifact.submissionArtifact.instructionPC 2805 = 3746 := by
  calc
    Artifact.submissionArtifact.instructionPC 2805 = Artifact.submissionArtifact.instructionPC 2804 + (Instr.op .OR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2804 (Instr.op .OR) (by rfl)
    _ = 3746 := by rw [pcSaturate2993]; rfl

@[simp] theorem mac2PC2829 : Artifact.submissionArtifact.instructionPC 2806 = 3748 := by
  calc
    Artifact.submissionArtifact.instructionPC 2806 = Artifact.submissionArtifact.instructionPC 2805 + (Instr.push 1 31).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2805 (Instr.push 1 31) (by rfl)
    _ = 3748 := by rw [mac2PC2828]; rfl

@[simp] theorem mac2PC2830 : Artifact.submissionArtifact.instructionPC 2807 = 3749 := by
  calc
    Artifact.submissionArtifact.instructionPC 2807 = Artifact.submissionArtifact.instructionPC 2806 + (Instr.op .NOT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2806 (Instr.op .NOT) (by rfl)
    _ = 3749 := by rw [mac2PC2829]; rfl

@[simp] theorem pc3070 : Artifact.submissionArtifact.instructionPC 2808 = 3750 := by
  calc
    Artifact.submissionArtifact.instructionPC 2808 = Artifact.submissionArtifact.instructionPC 2807 + (Instr.op (.Swap { idx := 0 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2807 (Instr.op (.Swap { idx := 0 })) (by rfl)
    _ = 3750 := by rw [mac2PC2830]; rfl

@[simp] theorem mac2PC2831 : Artifact.submissionArtifact.instructionPC 2808 = 3750 := pc3070

@[simp] theorem pc3071 : Artifact.submissionArtifact.instructionPC 2809 = 3751 := by
  calc
    Artifact.submissionArtifact.instructionPC 2809 = Artifact.submissionArtifact.instructionPC 2808 + (Instr.push 0 0).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2808 (Instr.push 0 0) (by rfl)
    _ = 3751 := by rw [pc3070]; rfl

@[simp] theorem mac2PC2832 : Artifact.submissionArtifact.instructionPC 2809 = 3751 := pc3071

@[simp] theorem pc3072 : Artifact.submissionArtifact.instructionPC 2810 = 3754 := by
  calc
    Artifact.submissionArtifact.instructionPC 2810 = Artifact.submissionArtifact.instructionPC 2809 + (Instr.push 2 5344).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2809 (Instr.push 2 5344) (by rfl)
    _ = 3754 := by rw [pc3071]; rfl

@[simp] theorem mac2PC2833 : Artifact.submissionArtifact.instructionPC 2810 = 3754 := pc3072

@[simp] theorem pc3073 : Artifact.submissionArtifact.instructionPC 2811 = 3755 := by
  calc
    Artifact.submissionArtifact.instructionPC 2811 = Artifact.submissionArtifact.instructionPC 2810 + (Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2810 (Instr.op .MLOAD) (by rfl)
    _ = 3755 := by rw [pc3072]; rfl

@[simp] theorem mac2PC2834 : Artifact.submissionArtifact.instructionPC 2811 = 3755 := pc3073

@[simp] theorem pc3074 : Artifact.submissionArtifact.instructionPC 2812 = 3758 := by
  calc
    Artifact.submissionArtifact.instructionPC 2812 = Artifact.submissionArtifact.instructionPC 2811 + (Instr.push 2 5312).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2811 (Instr.push 2 5312) (by rfl)
    _ = 3758 := by rw [pc3073]; rfl

@[simp] theorem mac2PC2835 : Artifact.submissionArtifact.instructionPC 2812 = 3758 := pc3074

@[simp] theorem pc3075 : Artifact.submissionArtifact.instructionPC 2813 = 3759 := by
  calc
    Artifact.submissionArtifact.instructionPC 2813 = Artifact.submissionArtifact.instructionPC 2812 + (Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2812 (Instr.op .MLOAD) (by rfl)
    _ = 3759 := by rw [pc3074]; rfl

@[simp] theorem mac2PC2836 : Artifact.submissionArtifact.instructionPC 2813 = 3759 := pc3075

@[simp] theorem pc3076 : Artifact.submissionArtifact.instructionPC 2814 = 3762 := by
  calc
    Artifact.submissionArtifact.instructionPC 2814 = Artifact.submissionArtifact.instructionPC 2813 + (Instr.push 2 1280).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2813 (Instr.push 2 1280) (by rfl)
    _ = 3762 := by rw [pc3075]; rfl

@[simp] theorem mac2PC2837 : Artifact.submissionArtifact.instructionPC 2814 = 3762 := pc3076

@[simp] theorem mac2PC2838 : Artifact.submissionArtifact.instructionPC 2815 = 3763 := by
  calc
    Artifact.submissionArtifact.instructionPC 2815 = Artifact.submissionArtifact.instructionPC 2814 + (Instr.op .ADD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2814 (Instr.op .ADD) (by rfl)
    _ = 3763 := by rw [pc3076]; rfl

@[simp] theorem mac2PC2839 : Artifact.submissionArtifact.instructionPC 2816 = 3764 := by
  calc
    Artifact.submissionArtifact.instructionPC 2816 = Artifact.submissionArtifact.instructionPC 2815 + (Instr.op (.Dup { idx := 0 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2815 (Instr.op (.Dup { idx := 0 })) (by rfl)
    _ = 3764 := by rw [mac2PC2838]; rfl

@[simp] theorem mac2PC2840 : Artifact.submissionArtifact.instructionPC 2817 = 3766 := by
  calc
    Artifact.submissionArtifact.instructionPC 2817 = Artifact.submissionArtifact.instructionPC 2816 + (Instr.push 1 32).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2816 (Instr.push 1 32) (by rfl)
    _ = 3766 := by rw [mac2PC2839]; rfl

@[simp] theorem mac2PC2841 : Artifact.submissionArtifact.instructionPC 2818 = 3767 := by
  calc
    Artifact.submissionArtifact.instructionPC 2818 = Artifact.submissionArtifact.instructionPC 2817 + (Instr.op .AND).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2817 (Instr.op .AND) (by rfl)
    _ = 3767 := by rw [mac2PC2840]; rfl

@[simp] theorem mac2PC2842 : Artifact.submissionArtifact.instructionPC 2819 = 3768 := by
  calc
    Artifact.submissionArtifact.instructionPC 2819 = Artifact.submissionArtifact.instructionPC 2818 + (Instr.op .ISZERO).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2818 (Instr.op .ISZERO) (by rfl)
    _ = 3768 := by rw [mac2PC2841]; rfl

@[simp] theorem mac2PC2843 : Artifact.submissionArtifact.instructionPC 2820 = 3771 := by
  calc
    Artifact.submissionArtifact.instructionPC 2820 = Artifact.submissionArtifact.instructionPC 2819 + (Instr.push 2 3811).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2819 (Instr.push 2 3811) (by rfl)
    _ = 3771 := by rw [mac2PC2842]; rfl

@[simp] theorem pc3077 : Artifact.submissionArtifact.instructionPC 2821 = 3772 := by
  calc
    Artifact.submissionArtifact.instructionPC 2821 = Artifact.submissionArtifact.instructionPC 2820 + (Instr.op .JUMPI).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2820 (Instr.op .JUMPI) (by rfl)
    _ = 3772 := by rw [mac2PC2843]; rfl

@[simp] theorem mac2PC2844 : Artifact.submissionArtifact.instructionPC 2821 = 3772 := pc3077

@[simp] theorem pc3078 : Artifact.submissionArtifact.instructionPC 2822 = 3773 := by
  calc
    Artifact.submissionArtifact.instructionPC 2822 = Artifact.submissionArtifact.instructionPC 2821 + (Instr.op .JUMPDEST).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2821 (Instr.op .JUMPDEST) (by rfl)
    _ = 3773 := by rw [pc3077]; rfl

@[simp] theorem mac2PC2845 : Artifact.submissionArtifact.instructionPC 2822 = 3773 := pc3078

@[simp] theorem pc3079 : Artifact.submissionArtifact.instructionPC 2823 = 3774 := by
  calc
    Artifact.submissionArtifact.instructionPC 2823 = Artifact.submissionArtifact.instructionPC 2822 + (Instr.op (.Dup { idx := 0 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2822 (Instr.op (.Dup { idx := 0 })) (by rfl)
    _ = 3774 := by rw [pc3078]; rfl

@[simp] theorem mac2PC2846 : Artifact.submissionArtifact.instructionPC 2823 = 3774 := pc3079

@[simp] theorem pc3080 : Artifact.submissionArtifact.instructionPC 2824 = 3775 := by
  calc
    Artifact.submissionArtifact.instructionPC 2824 = Artifact.submissionArtifact.instructionPC 2823 + (Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2823 (Instr.op .MLOAD) (by rfl)
    _ = 3775 := by rw [pc3079]; rfl

@[simp] theorem mac2PC2847 : Artifact.submissionArtifact.instructionPC 2824 = 3775 := pc3080

@[simp] theorem earlyExtraPC2880 : Artifact.submissionArtifact.instructionPC 2825 = 3776 := by
  calc
    Artifact.submissionArtifact.instructionPC 2825 = Artifact.submissionArtifact.instructionPC 2824 + (Instr.push 0 0).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2824 (Instr.push 0 0) (by rfl)
    _ = 3776 := by rw [pc3080]; rfl

@[simp] theorem mac2PC2848 : Artifact.submissionArtifact.instructionPC 2825 = 3776 := earlyExtraPC2880

@[simp] theorem pc3081 : Artifact.submissionArtifact.instructionPC 2826 = 3777 := by
  calc
    Artifact.submissionArtifact.instructionPC 2826 = Artifact.submissionArtifact.instructionPC 2825 + (Instr.op .NOT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2825 (Instr.op .NOT) (by rfl)
    _ = 3777 := by rw [earlyExtraPC2880]; rfl

@[simp] theorem compactExtraPC2929 : Artifact.submissionArtifact.instructionPC 2826 = 3777 := pc3081

@[simp] theorem mac2PC2849 : Artifact.submissionArtifact.instructionPC 2826 = 3777 := pc3081

@[simp] theorem pc3082 : Artifact.submissionArtifact.instructionPC 2827 = 3778 := by
  calc
    Artifact.submissionArtifact.instructionPC 2827 = Artifact.submissionArtifact.instructionPC 2826 + (Instr.op (.Dup { idx := 5 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2826 (Instr.op (.Dup { idx := 5 })) (by rfl)
    _ = 3778 := by rw [pc3081]; rfl

@[simp] theorem mac2PC2850 : Artifact.submissionArtifact.instructionPC 2827 = 3778 := pc3082

@[simp] theorem pc3083 : Artifact.submissionArtifact.instructionPC 2828 = 3779 := by
  calc
    Artifact.submissionArtifact.instructionPC 2828 = Artifact.submissionArtifact.instructionPC 2827 + (Instr.op (.Dup { idx := 2 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2827 (Instr.op (.Dup { idx := 2 })) (by rfl)
    _ = 3779 := by rw [pc3082]; rfl

@[simp] theorem mac2PC2851 : Artifact.submissionArtifact.instructionPC 2828 = 3779 := pc3083

@[simp] theorem pc3084 : Artifact.submissionArtifact.instructionPC 2829 = 3780 := by
  calc
    Artifact.submissionArtifact.instructionPC 2829 = Artifact.submissionArtifact.instructionPC 2828 + (Instr.op .MUL).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2828 (Instr.op .MUL) (by rfl)
    _ = 3780 := by rw [pc3083]; rfl

@[simp] theorem mac2PC2852 : Artifact.submissionArtifact.instructionPC 2829 = 3780 := pc3084

@[simp] theorem pc3085 : Artifact.submissionArtifact.instructionPC 2830 = 3781 := by
  calc
    Artifact.submissionArtifact.instructionPC 2830 = Artifact.submissionArtifact.instructionPC 2829 + (Instr.op (.Swap { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2829 (Instr.op (.Swap { idx := 1 })) (by rfl)
    _ = 3781 := by rw [pc3084]; rfl

@[simp] theorem mac2PC2853 : Artifact.submissionArtifact.instructionPC 2830 = 3781 := pc3085

@[simp] theorem pc3086 : Artifact.submissionArtifact.instructionPC 2831 = 3782 := by
  calc
    Artifact.submissionArtifact.instructionPC 2831 = Artifact.submissionArtifact.instructionPC 2830 + (Instr.op (.Dup { idx := 6 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2830 (Instr.op (.Dup { idx := 6 })) (by rfl)
    _ = 3782 := by rw [pc3085]; rfl

@[simp] theorem mac2PC2854 : Artifact.submissionArtifact.instructionPC 2831 = 3782 := pc3086

@[simp] theorem pc3087 : Artifact.submissionArtifact.instructionPC 2832 = 3783 := by
  calc
    Artifact.submissionArtifact.instructionPC 2832 = Artifact.submissionArtifact.instructionPC 2831 + (Instr.op .MULMOD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2831 (Instr.op .MULMOD) (by rfl)
    _ = 3783 := by rw [pc3086]; rfl

@[simp] theorem mac2PC2855 : Artifact.submissionArtifact.instructionPC 2832 = 3783 := pc3087

@[simp] theorem pc3088 : Artifact.submissionArtifact.instructionPC 2833 = 3784 := by
  calc
    Artifact.submissionArtifact.instructionPC 2833 = Artifact.submissionArtifact.instructionPC 2832 + (Instr.op (.Dup { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2832 (Instr.op (.Dup { idx := 1 })) (by rfl)
    _ = 3784 := by rw [pc3087]; rfl

@[simp] theorem mac2PC2856 : Artifact.submissionArtifact.instructionPC 2833 = 3784 := pc3088

@[simp] theorem pc3089 : Artifact.submissionArtifact.instructionPC 2834 = 3785 := by
  calc
    Artifact.submissionArtifact.instructionPC 2834 = Artifact.submissionArtifact.instructionPC 2833 + (Instr.op (.Dup { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2833 (Instr.op (.Dup { idx := 1 })) (by rfl)
    _ = 3785 := by rw [pc3088]; rfl

@[simp] theorem mac2PC2857 : Artifact.submissionArtifact.instructionPC 2834 = 3785 := pc3089

@[simp] theorem pc3090 : Artifact.submissionArtifact.instructionPC 2835 = 3786 := by
  calc
    Artifact.submissionArtifact.instructionPC 2835 = Artifact.submissionArtifact.instructionPC 2834 + (Instr.op .LT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2834 (Instr.op .LT) (by rfl)
    _ = 3786 := by rw [pc3089]; rfl

@[simp] theorem mac2PC2858 : Artifact.submissionArtifact.instructionPC 2835 = 3786 := pc3090

@[simp] theorem pc3091 : Artifact.submissionArtifact.instructionPC 2836 = 3787 := by
  calc
    Artifact.submissionArtifact.instructionPC 2836 = Artifact.submissionArtifact.instructionPC 2835 + (Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2835 (Instr.op .SUB) (by rfl)
    _ = 3787 := by rw [pc3090]; rfl

@[simp] theorem mac2PC2859 : Artifact.submissionArtifact.instructionPC 2836 = 3787 := pc3091

@[simp] theorem pc3092 : Artifact.submissionArtifact.instructionPC 2837 = 3788 := by
  calc
    Artifact.submissionArtifact.instructionPC 2837 = Artifact.submissionArtifact.instructionPC 2836 + (Instr.op (.Dup { idx := 4 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2836 (Instr.op (.Dup { idx := 4 })) (by rfl)
    _ = 3788 := by rw [pc3091]; rfl

@[simp] theorem mac2PC2860 : Artifact.submissionArtifact.instructionPC 2837 = 3788 := pc3092

@[simp] theorem pc3093 : Artifact.submissionArtifact.instructionPC 2838 = 3789 := by
  calc
    Artifact.submissionArtifact.instructionPC 2838 = Artifact.submissionArtifact.instructionPC 2837 + (Instr.op (.Dup { idx := 2 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2837 (Instr.op (.Dup { idx := 2 })) (by rfl)
    _ = 3789 := by rw [pc3092]; rfl

@[simp] theorem mac2PC2861 : Artifact.submissionArtifact.instructionPC 2838 = 3789 := pc3093

@[simp] theorem pc3094 : Artifact.submissionArtifact.instructionPC 2839 = 3790 := by
  calc
    Artifact.submissionArtifact.instructionPC 2839 = Artifact.submissionArtifact.instructionPC 2838 + (Instr.op .ADD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2838 (Instr.op .ADD) (by rfl)
    _ = 3790 := by rw [pc3093]; rfl

@[simp] theorem mac2PC2862 : Artifact.submissionArtifact.instructionPC 2839 = 3790 := pc3094

@[simp] theorem pc3095 : Artifact.submissionArtifact.instructionPC 2840 = 3791 := by
  calc
    Artifact.submissionArtifact.instructionPC 2840 = Artifact.submissionArtifact.instructionPC 2839 + (Instr.op (.Dup { idx := 0 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2839 (Instr.op (.Dup { idx := 0 })) (by rfl)
    _ = 3791 := by rw [pc3094]; rfl

@[simp] theorem mac2PC2863 : Artifact.submissionArtifact.instructionPC 2840 = 3791 := pc3095

@[simp] theorem pc3096 : Artifact.submissionArtifact.instructionPC 2841 = 3792 := by
  calc
    Artifact.submissionArtifact.instructionPC 2841 = Artifact.submissionArtifact.instructionPC 2840 + (Instr.op (.Swap { idx := 5 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2840 (Instr.op (.Swap { idx := 5 })) (by rfl)
    _ = 3792 := by rw [pc3095]; rfl

@[simp] theorem mac2PC2864 : Artifact.submissionArtifact.instructionPC 2841 = 3792 := pc3096

@[simp] theorem pc3097 : Artifact.submissionArtifact.instructionPC 2842 = 3793 := by
  calc
    Artifact.submissionArtifact.instructionPC 2842 = Artifact.submissionArtifact.instructionPC 2841 + (Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2841 (Instr.op .GT) (by rfl)
    _ = 3793 := by rw [pc3096]; rfl

@[simp] theorem mac2PC2865 : Artifact.submissionArtifact.instructionPC 2842 = 3793 := pc3097

@[simp] theorem pc3098 : Artifact.submissionArtifact.instructionPC 2843 = 3794 := by
  calc
    Artifact.submissionArtifact.instructionPC 2843 = Artifact.submissionArtifact.instructionPC 2842 + (Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2842 (Instr.op .SUB) (by rfl)
    _ = 3794 := by rw [pc3097]; rfl

@[simp] theorem mac2PC2866 : Artifact.submissionArtifact.instructionPC 2843 = 3794 := pc3098

@[simp] theorem pc3099 : Artifact.submissionArtifact.instructionPC 2844 = 3795 := by
  calc
    Artifact.submissionArtifact.instructionPC 2844 = Artifact.submissionArtifact.instructionPC 2843 + (Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2843 (Instr.op .SUB) (by rfl)
    _ = 3795 := by rw [pc3098]; rfl

@[simp] theorem mac2PC2867 : Artifact.submissionArtifact.instructionPC 2844 = 3795 := pc3099

@[simp] theorem pc3100 : Artifact.submissionArtifact.instructionPC 2845 = 3796 := by
  calc
    Artifact.submissionArtifact.instructionPC 2845 = Artifact.submissionArtifact.instructionPC 2844 + (Instr.op (.Dup { idx := 3 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2844 (Instr.op (.Dup { idx := 3 })) (by rfl)
    _ = 3796 := by rw [pc3099]; rfl

@[simp] theorem mac2PC2868 : Artifact.submissionArtifact.instructionPC 2845 = 3796 := pc3100

@[simp] theorem pc3101 : Artifact.submissionArtifact.instructionPC 2846 = 3797 := by
  calc
    Artifact.submissionArtifact.instructionPC 2846 = Artifact.submissionArtifact.instructionPC 2845 + (Instr.op (.Dup { idx := 3 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2845 (Instr.op (.Dup { idx := 3 })) (by rfl)
    _ = 3797 := by rw [pc3100]; rfl

@[simp] theorem mac2PC2869 : Artifact.submissionArtifact.instructionPC 2846 = 3797 := pc3101

@[simp] theorem pc3102 : Artifact.submissionArtifact.instructionPC 2847 = 3798 := by
  calc
    Artifact.submissionArtifact.instructionPC 2847 = Artifact.submissionArtifact.instructionPC 2846 + (Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2846 (Instr.op .MLOAD) (by rfl)
    _ = 3798 := by rw [pc3101]; rfl

@[simp] theorem mac2PC2870 : Artifact.submissionArtifact.instructionPC 2847 = 3798 := pc3102

@[simp] theorem pc3103 : Artifact.submissionArtifact.instructionPC 2848 = 3799 := by
  calc
    Artifact.submissionArtifact.instructionPC 2848 = Artifact.submissionArtifact.instructionPC 2847 + (Instr.op .ADD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2847 (Instr.op .ADD) (by rfl)
    _ = 3799 := by rw [pc3102]; rfl

@[simp] theorem mac2PC2871 : Artifact.submissionArtifact.instructionPC 2848 = 3799 := pc3103

@[simp] theorem pc3104 : Artifact.submissionArtifact.instructionPC 2849 = 3800 := by
  calc
    Artifact.submissionArtifact.instructionPC 2849 = Artifact.submissionArtifact.instructionPC 2848 + (Instr.op (.Dup { idx := 0 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2848 (Instr.op (.Dup { idx := 0 })) (by rfl)
    _ = 3800 := by rw [pc3103]; rfl

@[simp] theorem mac2PC2872 : Artifact.submissionArtifact.instructionPC 2849 = 3800 := pc3104

@[simp] theorem pc3105 : Artifact.submissionArtifact.instructionPC 2850 = 3801 := by
  calc
    Artifact.submissionArtifact.instructionPC 2850 = Artifact.submissionArtifact.instructionPC 2849 + (Instr.op (.Swap { idx := 4 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2849 (Instr.op (.Swap { idx := 4 })) (by rfl)
    _ = 3801 := by rw [pc3104]; rfl

@[simp] theorem mac2PC2873 : Artifact.submissionArtifact.instructionPC 2850 = 3801 := pc3105

@[simp] theorem pc3106 : Artifact.submissionArtifact.instructionPC 2851 = 3802 := by
  calc
    Artifact.submissionArtifact.instructionPC 2851 = Artifact.submissionArtifact.instructionPC 2850 + (Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2850 (Instr.op .GT) (by rfl)
    _ = 3802 := by rw [pc3105]; rfl

@[simp] theorem mac2PC2874 : Artifact.submissionArtifact.instructionPC 2851 = 3802 := pc3106

@[simp] theorem pc3107 : Artifact.submissionArtifact.instructionPC 2852 = 3803 := by
  calc
    Artifact.submissionArtifact.instructionPC 2852 = Artifact.submissionArtifact.instructionPC 2851 + (Instr.op .ADD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2851 (Instr.op .ADD) (by rfl)
    _ = 3803 := by rw [pc3106]; rfl

@[simp] theorem mac2PC2875 : Artifact.submissionArtifact.instructionPC 2852 = 3803 := pc3107

@[simp] theorem pc3108 : Artifact.submissionArtifact.instructionPC 2853 = 3804 := by
  calc
    Artifact.submissionArtifact.instructionPC 2853 = Artifact.submissionArtifact.instructionPC 2852 + (Instr.op (.Swap { idx := 2 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2852 (Instr.op (.Swap { idx := 2 })) (by rfl)
    _ = 3804 := by rw [pc3107]; rfl

@[simp] theorem mac2PC2876 : Artifact.submissionArtifact.instructionPC 2853 = 3804 := pc3108

@[simp] theorem pc3109 : Artifact.submissionArtifact.instructionPC 2854 = 3805 := by
  calc
    Artifact.submissionArtifact.instructionPC 2854 = Artifact.submissionArtifact.instructionPC 2853 + (Instr.op (.Dup { idx := 2 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2853 (Instr.op (.Dup { idx := 2 })) (by rfl)
    _ = 3805 := by rw [pc3108]; rfl

@[simp] theorem mac2PC2877 : Artifact.submissionArtifact.instructionPC 2854 = 3805 := pc3109

@[simp] theorem pc3110 : Artifact.submissionArtifact.instructionPC 2855 = 3806 := by
  calc
    Artifact.submissionArtifact.instructionPC 2855 = Artifact.submissionArtifact.instructionPC 2854 + (Instr.op (.Dup { idx := 6 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2854 (Instr.op (.Dup { idx := 6 })) (by rfl)
    _ = 3806 := by rw [pc3109]; rfl

@[simp] theorem compactExtraPC2959 : Artifact.submissionArtifact.instructionPC 2855 = 3806 := pc3110

@[simp] theorem mac2PC2878 : Artifact.submissionArtifact.instructionPC 2855 = 3806 := pc3110

@[simp] theorem pc3111 : Artifact.submissionArtifact.instructionPC 2856 = 3807 := by
  calc
    Artifact.submissionArtifact.instructionPC 2856 = Artifact.submissionArtifact.instructionPC 2855 + (Instr.op .ADD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2855 (Instr.op .ADD) (by rfl)
    _ = 3807 := by rw [pc3110]; rfl

@[simp] theorem mac2PC2879 : Artifact.submissionArtifact.instructionPC 2856 = 3807 := pc3111

@[simp] theorem pc3112 : Artifact.submissionArtifact.instructionPC 2857 = 3808 := by
  calc
    Artifact.submissionArtifact.instructionPC 2857 = Artifact.submissionArtifact.instructionPC 2856 + (Instr.op (.Swap { idx := 2 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2856 (Instr.op (.Swap { idx := 2 })) (by rfl)
    _ = 3808 := by rw [pc3111]; rfl

@[simp] theorem mac2PC2880 : Artifact.submissionArtifact.instructionPC 2857 = 3808 := pc3112

@[simp] theorem pc3113 : Artifact.submissionArtifact.instructionPC 2858 = 3809 := by
  calc
    Artifact.submissionArtifact.instructionPC 2858 = Artifact.submissionArtifact.instructionPC 2857 + (Instr.op .MSTORE).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2857 (Instr.op .MSTORE) (by rfl)
    _ = 3809 := by rw [pc3112]; rfl

@[simp] theorem mac2PC2881 : Artifact.submissionArtifact.instructionPC 2858 = 3809 := pc3113

@[simp] theorem pc3114 : Artifact.submissionArtifact.instructionPC 2859 = 3810 := by
  calc
    Artifact.submissionArtifact.instructionPC 2859 = Artifact.submissionArtifact.instructionPC 2858 + (Instr.op (.Dup { idx := 4 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2858 (Instr.op (.Dup { idx := 4 })) (by rfl)
    _ = 3810 := by rw [pc3113]; rfl

@[simp] theorem compactExtraPC2964 : Artifact.submissionArtifact.instructionPC 2859 = 3810 := pc3114

@[simp] theorem mac2PC2882 : Artifact.submissionArtifact.instructionPC 2859 = 3810 := pc3114

@[simp] theorem mac2PC2883 : Artifact.submissionArtifact.instructionPC 2860 = 3811 := by
  calc
    Artifact.submissionArtifact.instructionPC 2860 = Artifact.submissionArtifact.instructionPC 2859 + (Instr.op .ADD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2859 (Instr.op .ADD) (by rfl)
    _ = 3811 := by rw [pc3114]; rfl

@[simp] theorem mac2PC2884 : Artifact.submissionArtifact.instructionPC 2861 = 3812 := by
  calc
    Artifact.submissionArtifact.instructionPC 2861 = Artifact.submissionArtifact.instructionPC 2860 + (Instr.op .JUMPDEST).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2860 (Instr.op .JUMPDEST) (by rfl)
    _ = 3812 := by rw [mac2PC2883]; rfl

@[simp] theorem mac2PC2885 : Artifact.submissionArtifact.instructionPC 2862 = 3813 := by
  calc
    Artifact.submissionArtifact.instructionPC 2862 = Artifact.submissionArtifact.instructionPC 2861 + (Instr.op (.Dup { idx := 0 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2861 (Instr.op (.Dup { idx := 0 })) (by rfl)
    _ = 3813 := by rw [mac2PC2884]; rfl

@[simp] theorem mac2PC2886 : Artifact.submissionArtifact.instructionPC 2863 = 3814 := by
  calc
    Artifact.submissionArtifact.instructionPC 2863 = Artifact.submissionArtifact.instructionPC 2862 + (Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2862 (Instr.op .MLOAD) (by rfl)
    _ = 3814 := by rw [mac2PC2885]; rfl

@[simp] theorem mac2PC2887 : Artifact.submissionArtifact.instructionPC 2864 = 3815 := by
  calc
    Artifact.submissionArtifact.instructionPC 2864 = Artifact.submissionArtifact.instructionPC 2863 + (Instr.push 0 0).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2863 (Instr.push 0 0) (by rfl)
    _ = 3815 := by rw [mac2PC2886]; rfl

@[simp] theorem mac2PC2888 : Artifact.submissionArtifact.instructionPC 2865 = 3816 := by
  calc
    Artifact.submissionArtifact.instructionPC 2865 = Artifact.submissionArtifact.instructionPC 2864 + (Instr.op .NOT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2864 (Instr.op .NOT) (by rfl)
    _ = 3816 := by rw [mac2PC2887]; rfl

@[simp] theorem mac2PC2889 : Artifact.submissionArtifact.instructionPC 2866 = 3817 := by
  calc
    Artifact.submissionArtifact.instructionPC 2866 = Artifact.submissionArtifact.instructionPC 2865 + (Instr.op (.Dup { idx := 5 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2865 (Instr.op (.Dup { idx := 5 })) (by rfl)
    _ = 3817 := by rw [mac2PC2888]; rfl

@[simp] theorem mac2PC2890 : Artifact.submissionArtifact.instructionPC 2867 = 3818 := by
  calc
    Artifact.submissionArtifact.instructionPC 2867 = Artifact.submissionArtifact.instructionPC 2866 + (Instr.op (.Dup { idx := 2 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2866 (Instr.op (.Dup { idx := 2 })) (by rfl)
    _ = 3818 := by rw [mac2PC2889]; rfl

@[simp] theorem mac2PC2891 : Artifact.submissionArtifact.instructionPC 2868 = 3819 := by
  calc
    Artifact.submissionArtifact.instructionPC 2868 = Artifact.submissionArtifact.instructionPC 2867 + (Instr.op .MUL).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2867 (Instr.op .MUL) (by rfl)
    _ = 3819 := by rw [mac2PC2890]; rfl

@[simp] theorem mac2PC2892 : Artifact.submissionArtifact.instructionPC 2869 = 3820 := by
  calc
    Artifact.submissionArtifact.instructionPC 2869 = Artifact.submissionArtifact.instructionPC 2868 + (Instr.op (.Swap { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2868 (Instr.op (.Swap { idx := 1 })) (by rfl)
    _ = 3820 := by rw [mac2PC2891]; rfl

@[simp] theorem mac2PC2893 : Artifact.submissionArtifact.instructionPC 2870 = 3821 := by
  calc
    Artifact.submissionArtifact.instructionPC 2870 = Artifact.submissionArtifact.instructionPC 2869 + (Instr.op (.Dup { idx := 6 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2869 (Instr.op (.Dup { idx := 6 })) (by rfl)
    _ = 3821 := by rw [mac2PC2892]; rfl

@[simp] theorem mac2PC2894 : Artifact.submissionArtifact.instructionPC 2871 = 3822 := by
  calc
    Artifact.submissionArtifact.instructionPC 2871 = Artifact.submissionArtifact.instructionPC 2870 + (Instr.op .MULMOD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2870 (Instr.op .MULMOD) (by rfl)
    _ = 3822 := by rw [mac2PC2893]; rfl

@[simp] theorem mac2PC2895 : Artifact.submissionArtifact.instructionPC 2872 = 3823 := by
  calc
    Artifact.submissionArtifact.instructionPC 2872 = Artifact.submissionArtifact.instructionPC 2871 + (Instr.op (.Dup { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2871 (Instr.op (.Dup { idx := 1 })) (by rfl)
    _ = 3823 := by rw [mac2PC2894]; rfl

@[simp] theorem mac2PC2896 : Artifact.submissionArtifact.instructionPC 2873 = 3824 := by
  calc
    Artifact.submissionArtifact.instructionPC 2873 = Artifact.submissionArtifact.instructionPC 2872 + (Instr.op (.Dup { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2872 (Instr.op (.Dup { idx := 1 })) (by rfl)
    _ = 3824 := by rw [mac2PC2895]; rfl

@[simp] theorem mac2PC2897 : Artifact.submissionArtifact.instructionPC 2874 = 3825 := by
  calc
    Artifact.submissionArtifact.instructionPC 2874 = Artifact.submissionArtifact.instructionPC 2873 + (Instr.op .LT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2873 (Instr.op .LT) (by rfl)
    _ = 3825 := by rw [mac2PC2896]; rfl

@[simp] theorem mac2PC2898 : Artifact.submissionArtifact.instructionPC 2875 = 3826 := by
  calc
    Artifact.submissionArtifact.instructionPC 2875 = Artifact.submissionArtifact.instructionPC 2874 + (Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2874 (Instr.op .SUB) (by rfl)
    _ = 3826 := by rw [mac2PC2897]; rfl

@[simp] theorem mac2PC2899 : Artifact.submissionArtifact.instructionPC 2876 = 3827 := by
  calc
    Artifact.submissionArtifact.instructionPC 2876 = Artifact.submissionArtifact.instructionPC 2875 + (Instr.op (.Dup { idx := 4 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2875 (Instr.op (.Dup { idx := 4 })) (by rfl)
    _ = 3827 := by rw [mac2PC2898]; rfl

@[simp] theorem mac2PC2900 : Artifact.submissionArtifact.instructionPC 2877 = 3828 := by
  calc
    Artifact.submissionArtifact.instructionPC 2877 = Artifact.submissionArtifact.instructionPC 2876 + (Instr.op (.Dup { idx := 2 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2876 (Instr.op (.Dup { idx := 2 })) (by rfl)
    _ = 3828 := by rw [mac2PC2899]; rfl

@[simp] theorem mac2PC2901 : Artifact.submissionArtifact.instructionPC 2878 = 3829 := by
  calc
    Artifact.submissionArtifact.instructionPC 2878 = Artifact.submissionArtifact.instructionPC 2877 + (Instr.op .ADD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2877 (Instr.op .ADD) (by rfl)
    _ = 3829 := by rw [mac2PC2900]; rfl

@[simp] theorem mac2PC2902 : Artifact.submissionArtifact.instructionPC 2879 = 3830 := by
  calc
    Artifact.submissionArtifact.instructionPC 2879 = Artifact.submissionArtifact.instructionPC 2878 + (Instr.op (.Dup { idx := 0 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2878 (Instr.op (.Dup { idx := 0 })) (by rfl)
    _ = 3830 := by rw [mac2PC2901]; rfl

@[simp] theorem mac2PC2903 : Artifact.submissionArtifact.instructionPC 2880 = 3831 := by
  calc
    Artifact.submissionArtifact.instructionPC 2880 = Artifact.submissionArtifact.instructionPC 2879 + (Instr.op (.Swap { idx := 5 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2879 (Instr.op (.Swap { idx := 5 })) (by rfl)
    _ = 3831 := by rw [mac2PC2902]; rfl

@[simp] theorem mac2PC2904 : Artifact.submissionArtifact.instructionPC 2881 = 3832 := by
  calc
    Artifact.submissionArtifact.instructionPC 2881 = Artifact.submissionArtifact.instructionPC 2880 + (Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2880 (Instr.op .GT) (by rfl)
    _ = 3832 := by rw [mac2PC2903]; rfl

@[simp] theorem mac2PC2905 : Artifact.submissionArtifact.instructionPC 2882 = 3833 := by
  calc
    Artifact.submissionArtifact.instructionPC 2882 = Artifact.submissionArtifact.instructionPC 2881 + (Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2881 (Instr.op .SUB) (by rfl)
    _ = 3833 := by rw [mac2PC2904]; rfl

@[simp] theorem mac2PC2906 : Artifact.submissionArtifact.instructionPC 2883 = 3834 := by
  calc
    Artifact.submissionArtifact.instructionPC 2883 = Artifact.submissionArtifact.instructionPC 2882 + (Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2882 (Instr.op .SUB) (by rfl)
    _ = 3834 := by rw [mac2PC2905]; rfl

@[simp] theorem mac2PC2907 : Artifact.submissionArtifact.instructionPC 2884 = 3835 := by
  calc
    Artifact.submissionArtifact.instructionPC 2884 = Artifact.submissionArtifact.instructionPC 2883 + (Instr.op (.Dup { idx := 3 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2883 (Instr.op (.Dup { idx := 3 })) (by rfl)
    _ = 3835 := by rw [mac2PC2906]; rfl

@[simp] theorem mac2PC2908 : Artifact.submissionArtifact.instructionPC 2885 = 3836 := by
  calc
    Artifact.submissionArtifact.instructionPC 2885 = Artifact.submissionArtifact.instructionPC 2884 + (Instr.op (.Dup { idx := 3 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2884 (Instr.op (.Dup { idx := 3 })) (by rfl)
    _ = 3836 := by rw [mac2PC2907]; rfl

@[simp] theorem mac2PC2909 : Artifact.submissionArtifact.instructionPC 2886 = 3837 := by
  calc
    Artifact.submissionArtifact.instructionPC 2886 = Artifact.submissionArtifact.instructionPC 2885 + (Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2885 (Instr.op .MLOAD) (by rfl)
    _ = 3837 := by rw [mac2PC2908]; rfl

@[simp] theorem mac2PC2910 : Artifact.submissionArtifact.instructionPC 2887 = 3838 := by
  calc
    Artifact.submissionArtifact.instructionPC 2887 = Artifact.submissionArtifact.instructionPC 2886 + (Instr.op .ADD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2886 (Instr.op .ADD) (by rfl)
    _ = 3838 := by rw [mac2PC2909]; rfl

@[simp] theorem mac2PC2911 : Artifact.submissionArtifact.instructionPC 2888 = 3839 := by
  calc
    Artifact.submissionArtifact.instructionPC 2888 = Artifact.submissionArtifact.instructionPC 2887 + (Instr.op (.Dup { idx := 0 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2887 (Instr.op (.Dup { idx := 0 })) (by rfl)
    _ = 3839 := by rw [mac2PC2910]; rfl

@[simp] theorem mac2PC2912 : Artifact.submissionArtifact.instructionPC 2889 = 3840 := by
  calc
    Artifact.submissionArtifact.instructionPC 2889 = Artifact.submissionArtifact.instructionPC 2888 + (Instr.op (.Swap { idx := 4 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2888 (Instr.op (.Swap { idx := 4 })) (by rfl)
    _ = 3840 := by rw [mac2PC2911]; rfl

@[simp] theorem mac2PC2913 : Artifact.submissionArtifact.instructionPC 2890 = 3841 := by
  calc
    Artifact.submissionArtifact.instructionPC 2890 = Artifact.submissionArtifact.instructionPC 2889 + (Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2889 (Instr.op .GT) (by rfl)
    _ = 3841 := by rw [mac2PC2912]; rfl

@[simp] theorem mac2PC2914 : Artifact.submissionArtifact.instructionPC 2891 = 3842 := by
  calc
    Artifact.submissionArtifact.instructionPC 2891 = Artifact.submissionArtifact.instructionPC 2890 + (Instr.op .ADD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2890 (Instr.op .ADD) (by rfl)
    _ = 3842 := by rw [mac2PC2913]; rfl

@[simp] theorem mac2PC2915 : Artifact.submissionArtifact.instructionPC 2892 = 3843 := by
  calc
    Artifact.submissionArtifact.instructionPC 2892 = Artifact.submissionArtifact.instructionPC 2891 + (Instr.op (.Swap { idx := 2 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2891 (Instr.op (.Swap { idx := 2 })) (by rfl)
    _ = 3843 := by rw [mac2PC2914]; rfl

@[simp] theorem mac2PC2916 : Artifact.submissionArtifact.instructionPC 2893 = 3844 := by
  calc
    Artifact.submissionArtifact.instructionPC 2893 = Artifact.submissionArtifact.instructionPC 2892 + (Instr.op (.Dup { idx := 2 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2892 (Instr.op (.Dup { idx := 2 })) (by rfl)
    _ = 3844 := by rw [mac2PC2915]; rfl

@[simp] theorem mac2PC2917 : Artifact.submissionArtifact.instructionPC 2894 = 3845 := by
  calc
    Artifact.submissionArtifact.instructionPC 2894 = Artifact.submissionArtifact.instructionPC 2893 + (Instr.op (.Dup { idx := 6 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2893 (Instr.op (.Dup { idx := 6 })) (by rfl)
    _ = 3845 := by rw [mac2PC2916]; rfl

@[simp] theorem mac2PC2918 : Artifact.submissionArtifact.instructionPC 2895 = 3846 := by
  calc
    Artifact.submissionArtifact.instructionPC 2895 = Artifact.submissionArtifact.instructionPC 2894 + (Instr.op .ADD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2894 (Instr.op .ADD) (by rfl)
    _ = 3846 := by rw [mac2PC2917]; rfl

@[simp] theorem mac2PC2919 : Artifact.submissionArtifact.instructionPC 2896 = 3847 := by
  calc
    Artifact.submissionArtifact.instructionPC 2896 = Artifact.submissionArtifact.instructionPC 2895 + (Instr.op (.Swap { idx := 2 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2895 (Instr.op (.Swap { idx := 2 })) (by rfl)
    _ = 3847 := by rw [mac2PC2918]; rfl

@[simp] theorem mac2PC2920 : Artifact.submissionArtifact.instructionPC 2897 = 3848 := by
  calc
    Artifact.submissionArtifact.instructionPC 2897 = Artifact.submissionArtifact.instructionPC 2896 + (Instr.op .MSTORE).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2896 (Instr.op .MSTORE) (by rfl)
    _ = 3848 := by rw [mac2PC2919]; rfl

@[simp] theorem mac2PC2921 : Artifact.submissionArtifact.instructionPC 2898 = 3849 := by
  calc
    Artifact.submissionArtifact.instructionPC 2898 = Artifact.submissionArtifact.instructionPC 2897 + (Instr.op (.Dup { idx := 4 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2897 (Instr.op (.Dup { idx := 4 })) (by rfl)
    _ = 3849 := by rw [mac2PC2920]; rfl

@[simp] theorem pc3120 : Artifact.submissionArtifact.instructionPC 2899 = 3850 := by
  calc
    Artifact.submissionArtifact.instructionPC 2899 = Artifact.submissionArtifact.instructionPC 2898 + (Instr.op .ADD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2898 (Instr.op .ADD) (by rfl)
    _ = 3850 := by rw [mac2PC2921]; rfl

@[simp] theorem mac2PC2922 : Artifact.submissionArtifact.instructionPC 2899 = 3850 := pc3120

@[simp] theorem pc3121 : Artifact.submissionArtifact.instructionPC 2900 = 3853 := by
  calc
    Artifact.submissionArtifact.instructionPC 2900 = Artifact.submissionArtifact.instructionPC 2899 + (Instr.push 2 4128).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2899 (Instr.push 2 4128) (by rfl)
    _ = 3853 := by rw [pc3120]; rfl

@[simp] theorem mac2PC2923 : Artifact.submissionArtifact.instructionPC 2900 = 3853 := pc3121

@[simp] theorem pc3122 : Artifact.submissionArtifact.instructionPC 2901 = 3854 := by
  calc
    Artifact.submissionArtifact.instructionPC 2901 = Artifact.submissionArtifact.instructionPC 2900 + (Instr.op (.Dup { idx := 2 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2900 (Instr.op (.Dup { idx := 2 })) (by rfl)
    _ = 3854 := by rw [pc3121]; rfl

@[simp] theorem mac2PC2924 : Artifact.submissionArtifact.instructionPC 2901 = 3854 := pc3122

@[simp] theorem pc3123 : Artifact.submissionArtifact.instructionPC 2902 = 3855 := by
  calc
    Artifact.submissionArtifact.instructionPC 2902 = Artifact.submissionArtifact.instructionPC 2901 + (Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2901 (Instr.op .GT) (by rfl)
    _ = 3855 := by rw [pc3122]; rfl

@[simp] theorem mac2PC2925 : Artifact.submissionArtifact.instructionPC 2902 = 3855 := pc3123

@[simp] theorem pc3124 : Artifact.submissionArtifact.instructionPC 2903 = 3858 := by
  calc
    Artifact.submissionArtifact.instructionPC 2903 = Artifact.submissionArtifact.instructionPC 2902 + (Instr.push 2 3772).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2902 (Instr.push 2 3772) (by rfl)
    _ = 3858 := by rw [pc3123]; rfl

@[simp] theorem mac2PC2926 : Artifact.submissionArtifact.instructionPC 2903 = 3858 := pc3124

@[simp] theorem pc3125 : Artifact.submissionArtifact.instructionPC 2904 = 3859 := by
  calc
    Artifact.submissionArtifact.instructionPC 2904 = Artifact.submissionArtifact.instructionPC 2903 + (Instr.op .JUMPI).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2903 (Instr.op .JUMPI) (by rfl)
    _ = 3859 := by rw [pc3124]; rfl

@[simp] theorem mac2PC2927 : Artifact.submissionArtifact.instructionPC 2904 = 3859 := pc3125

@[simp] theorem pc3126 : Artifact.submissionArtifact.instructionPC 2905 = 3860 := by
  calc
    Artifact.submissionArtifact.instructionPC 2905 = Artifact.submissionArtifact.instructionPC 2904 + (Instr.op .POP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2904 (Instr.op .POP) (by rfl)
    _ = 3860 := by rw [pc3125]; rfl

@[simp] theorem mac2PC2928 : Artifact.submissionArtifact.instructionPC 2905 = 3860 := pc3126

@[simp] theorem pc3127 : Artifact.submissionArtifact.instructionPC 2906 = 3861 := by
  calc
    Artifact.submissionArtifact.instructionPC 2906 = Artifact.submissionArtifact.instructionPC 2905 + (Instr.op .POP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2905 (Instr.op .POP) (by rfl)
    _ = 3861 := by rw [pc3126]; rfl

@[simp] theorem mac2PC2929 : Artifact.submissionArtifact.instructionPC 2906 = 3861 := pc3127

@[simp] theorem pc3128 : Artifact.submissionArtifact.instructionPC 2907 = 3864 := by
  calc
    Artifact.submissionArtifact.instructionPC 2907 = Artifact.submissionArtifact.instructionPC 2906 + (Instr.push 2 4128).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2906 (Instr.push 2 4128) (by rfl)
    _ = 3864 := by rw [pc3127]; rfl

@[simp] theorem mac2PC2930 : Artifact.submissionArtifact.instructionPC 2907 = 3864 := pc3128

@[simp] theorem pc3129 : Artifact.submissionArtifact.instructionPC 2908 = 3865 := by
  calc
    Artifact.submissionArtifact.instructionPC 2908 = Artifact.submissionArtifact.instructionPC 2907 + (Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2907 (Instr.op .MLOAD) (by rfl)
    _ = 3865 := by rw [pc3128]; rfl

@[simp] theorem mac2PC2931 : Artifact.submissionArtifact.instructionPC 2908 = 3865 := pc3129

@[simp] theorem pc3130 : Artifact.submissionArtifact.instructionPC 2909 = 3866 := by
  calc
    Artifact.submissionArtifact.instructionPC 2909 = Artifact.submissionArtifact.instructionPC 2908 + (Instr.op (.Dup { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2908 (Instr.op (.Dup { idx := 1 })) (by rfl)
    _ = 3866 := by rw [pc3129]; rfl

@[simp] theorem mac2PC2932 : Artifact.submissionArtifact.instructionPC 2909 = 3866 := pc3130

@[simp] theorem pc3131 : Artifact.submissionArtifact.instructionPC 2910 = 3867 := by
  calc
    Artifact.submissionArtifact.instructionPC 2910 = Artifact.submissionArtifact.instructionPC 2909 + (Instr.op .ADD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2909 (Instr.op .ADD) (by rfl)
    _ = 3867 := by rw [pc3130]; rfl

@[simp] theorem mac2PC2933 : Artifact.submissionArtifact.instructionPC 2910 = 3867 := pc3131

@[simp] theorem pc3132 : Artifact.submissionArtifact.instructionPC 2911 = 3868 := by
  calc
    Artifact.submissionArtifact.instructionPC 2911 = Artifact.submissionArtifact.instructionPC 2910 + (Instr.op (.Dup { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2910 (Instr.op (.Dup { idx := 1 })) (by rfl)
    _ = 3868 := by rw [pc3131]; rfl

@[simp] theorem mac2PC2934 : Artifact.submissionArtifact.instructionPC 2911 = 3868 := pc3132

@[simp] theorem pc3133 : Artifact.submissionArtifact.instructionPC 2912 = 3869 := by
  calc
    Artifact.submissionArtifact.instructionPC 2912 = Artifact.submissionArtifact.instructionPC 2911 + (Instr.op (.Dup { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2911 (Instr.op (.Dup { idx := 1 })) (by rfl)
    _ = 3869 := by rw [pc3132]; rfl

@[simp] theorem mac2PC2935 : Artifact.submissionArtifact.instructionPC 2912 = 3869 := pc3133

@[simp] theorem pc3134 : Artifact.submissionArtifact.instructionPC 2913 = 3870 := by
  calc
    Artifact.submissionArtifact.instructionPC 2913 = Artifact.submissionArtifact.instructionPC 2912 + (Instr.op .LT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2912 (Instr.op .LT) (by rfl)
    _ = 3870 := by rw [pc3133]; rfl

@[simp] theorem mac2PC2936 : Artifact.submissionArtifact.instructionPC 2913 = 3870 := pc3134

@[simp] theorem pc3135 : Artifact.submissionArtifact.instructionPC 2914 = 3871 := by
  calc
    Artifact.submissionArtifact.instructionPC 2914 = Artifact.submissionArtifact.instructionPC 2913 + (Instr.op (.Swap { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2913 (Instr.op (.Swap { idx := 1 })) (by rfl)
    _ = 3871 := by rw [pc3134]; rfl

@[simp] theorem mac2PC2937 : Artifact.submissionArtifact.instructionPC 2914 = 3871 := pc3135

@[simp] theorem pc3136 : Artifact.submissionArtifact.instructionPC 2915 = 3872 := by
  calc
    Artifact.submissionArtifact.instructionPC 2915 = Artifact.submissionArtifact.instructionPC 2914 + (Instr.op .POP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2914 (Instr.op .POP) (by rfl)
    _ = 3872 := by rw [pc3135]; rfl

@[simp] theorem mac2PC2938 : Artifact.submissionArtifact.instructionPC 2915 = 3872 := pc3136

@[simp] theorem pc3137 : Artifact.submissionArtifact.instructionPC 2916 = 3873 := by
  calc
    Artifact.submissionArtifact.instructionPC 2916 = Artifact.submissionArtifact.instructionPC 2915 + (Instr.op (.Dup { idx := 2 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2915 (Instr.op (.Dup { idx := 2 })) (by rfl)
    _ = 3873 := by rw [pc3136]; rfl

@[simp] theorem mac2PC2939 : Artifact.submissionArtifact.instructionPC 2916 = 3873 := pc3137

@[simp] theorem pc3138 : Artifact.submissionArtifact.instructionPC 2917 = 3874 := by
  calc
    Artifact.submissionArtifact.instructionPC 2917 = Artifact.submissionArtifact.instructionPC 2916 + (Instr.op (.Dup { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2916 (Instr.op (.Dup { idx := 1 })) (by rfl)
    _ = 3874 := by rw [pc3137]; rfl

@[simp] theorem mac2PC2940 : Artifact.submissionArtifact.instructionPC 2917 = 3874 := pc3138

@[simp] theorem pc3139 : Artifact.submissionArtifact.instructionPC 2918 = 3875 := by
  calc
    Artifact.submissionArtifact.instructionPC 2918 = Artifact.submissionArtifact.instructionPC 2917 + (Instr.op .LT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2917 (Instr.op .LT) (by rfl)
    _ = 3875 := by rw [pc3138]; rfl

@[simp] theorem mac2PC2941 : Artifact.submissionArtifact.instructionPC 2918 = 3875 := pc3139

@[simp] theorem pc3140 : Artifact.submissionArtifact.instructionPC 2919 = 3876 := by
  calc
    Artifact.submissionArtifact.instructionPC 2919 = Artifact.submissionArtifact.instructionPC 2918 + (Instr.op (.Swap { idx := 0 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2918 (Instr.op (.Swap { idx := 0 })) (by rfl)
    _ = 3876 := by rw [pc3139]; rfl

@[simp] theorem mac2PC2942 : Artifact.submissionArtifact.instructionPC 2919 = 3876 := pc3140

@[simp] theorem pc3141 : Artifact.submissionArtifact.instructionPC 2920 = 3877 := by
  calc
    Artifact.submissionArtifact.instructionPC 2920 = Artifact.submissionArtifact.instructionPC 2919 + (Instr.op (.Dup { idx := 3 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2919 (Instr.op (.Dup { idx := 3 })) (by rfl)
    _ = 3877 := by rw [pc3140]; rfl

@[simp] theorem mac2PC2943 : Artifact.submissionArtifact.instructionPC 2920 = 3877 := pc3141

@[simp] theorem pc3142 : Artifact.submissionArtifact.instructionPC 2921 = 3878 := by
  calc
    Artifact.submissionArtifact.instructionPC 2921 = Artifact.submissionArtifact.instructionPC 2920 + (Instr.op (.Swap { idx := 0 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2920 (Instr.op (.Swap { idx := 0 })) (by rfl)
    _ = 3878 := by rw [pc3141]; rfl

@[simp] theorem mac2PC2944 : Artifact.submissionArtifact.instructionPC 2921 = 3878 := pc3142

@[simp] theorem pc3143 : Artifact.submissionArtifact.instructionPC 2922 = 3879 := by
  calc
    Artifact.submissionArtifact.instructionPC 2922 = Artifact.submissionArtifact.instructionPC 2921 + (Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2921 (Instr.op .SUB) (by rfl)
    _ = 3879 := by rw [pc3142]; rfl

@[simp] theorem mac2PC2945 : Artifact.submissionArtifact.instructionPC 2922 = 3879 := pc3143

@[simp] theorem pc3144 : Artifact.submissionArtifact.instructionPC 2923 = 3880 := by
  calc
    Artifact.submissionArtifact.instructionPC 2923 = Artifact.submissionArtifact.instructionPC 2922 + (Instr.op (.Dup { idx := 0 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2922 (Instr.op (.Dup { idx := 0 })) (by rfl)
    _ = 3880 := by rw [pc3143]; rfl

@[simp] theorem mac2PC2946 : Artifact.submissionArtifact.instructionPC 2923 = 3880 := pc3144

@[simp] theorem pc3145 : Artifact.submissionArtifact.instructionPC 2924 = 3883 := by
  calc
    Artifact.submissionArtifact.instructionPC 2924 = Artifact.submissionArtifact.instructionPC 2923 + (Instr.push 2 4128).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2923 (Instr.push 2 4128) (by rfl)
    _ = 3883 := by rw [pc3144]; rfl

@[simp] theorem mac2PC2947 : Artifact.submissionArtifact.instructionPC 2924 = 3883 := pc3145

@[simp] theorem pc3146 : Artifact.submissionArtifact.instructionPC 2925 = 3884 := by
  calc
    Artifact.submissionArtifact.instructionPC 2925 = Artifact.submissionArtifact.instructionPC 2924 + (Instr.op .MSTORE).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2924 (Instr.op .MSTORE) (by rfl)
    _ = 3884 := by rw [pc3145]; rfl

@[simp] theorem mac2PC2948 : Artifact.submissionArtifact.instructionPC 2925 = 3884 := pc3146

@[simp] theorem pc3147 : Artifact.submissionArtifact.instructionPC 2926 = 3885 := by
  calc
    Artifact.submissionArtifact.instructionPC 2926 = Artifact.submissionArtifact.instructionPC 2925 + (Instr.op .POP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2925 (Instr.op .POP) (by rfl)
    _ = 3885 := by rw [pc3146]; rfl

@[simp] theorem mac2PC2949 : Artifact.submissionArtifact.instructionPC 2926 = 3885 := pc3147

@[simp] theorem pc3148 : Artifact.submissionArtifact.instructionPC 2927 = 3886 := by
  calc
    Artifact.submissionArtifact.instructionPC 2927 = Artifact.submissionArtifact.instructionPC 2926 + (Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2926 (Instr.op .GT) (by rfl)
    _ = 3886 := by rw [pc3147]; rfl

@[simp] theorem mac2PC2950 : Artifact.submissionArtifact.instructionPC 2927 = 3886 := pc3148

@[simp] theorem pc3149 : Artifact.submissionArtifact.instructionPC 2928 = 3887 := by
  calc
    Artifact.submissionArtifact.instructionPC 2928 = Artifact.submissionArtifact.instructionPC 2927 + (Instr.op (.Swap { idx := 0 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2927 (Instr.op (.Swap { idx := 0 })) (by rfl)
    _ = 3887 := by rw [pc3148]; rfl

@[simp] theorem mac2PC2951 : Artifact.submissionArtifact.instructionPC 2928 = 3887 := pc3149

@[simp] theorem mac2PC2952 : Artifact.submissionArtifact.instructionPC 2929 = 3888 := by
  calc
    Artifact.submissionArtifact.instructionPC 2929 = Artifact.submissionArtifact.instructionPC 2928 + (Instr.op .POP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2928 (Instr.op .POP) (by rfl)
    _ = 3888 := by rw [pc3149]; rfl

@[simp] theorem mac2PC2953 : Artifact.submissionArtifact.instructionPC 2930 = 3889 := by
  calc
    Artifact.submissionArtifact.instructionPC 2930 = Artifact.submissionArtifact.instructionPC 2929 + (Instr.op (.Swap { idx := 0 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2929 (Instr.op (.Swap { idx := 0 })) (by rfl)
    _ = 3889 := by rw [mac2PC2952]; rfl

@[simp] theorem pc3150 : Artifact.submissionArtifact.instructionPC 2931 = 3890 := by
  calc
    Artifact.submissionArtifact.instructionPC 2931 = Artifact.submissionArtifact.instructionPC 2930 + (Instr.op .POP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2930 (Instr.op .POP) (by rfl)
    _ = 3890 := by rw [mac2PC2953]; rfl

@[simp] theorem mac2PC2954 : Artifact.submissionArtifact.instructionPC 2931 = 3890 := pc3150

@[simp] theorem pc3151 : Artifact.submissionArtifact.instructionPC 2932 = 3891 := by
  calc
    Artifact.submissionArtifact.instructionPC 2932 = Artifact.submissionArtifact.instructionPC 2931 + (Instr.op .ISZERO).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2931 (Instr.op .ISZERO) (by rfl)
    _ = 3891 := by rw [pc3150]; rfl

@[simp] theorem mac2PC2955 : Artifact.submissionArtifact.instructionPC 2932 = 3891 := pc3151

@[simp] theorem pc3152 : Artifact.submissionArtifact.instructionPC 2933 = 3894 := by
  calc
    Artifact.submissionArtifact.instructionPC 2933 = Artifact.submissionArtifact.instructionPC 2932 + (Instr.push 2 3962).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2932 (Instr.push 2 3962) (by rfl)
    _ = 3894 := by rw [pc3151]; rfl

@[simp] theorem mac2PC2956 : Artifact.submissionArtifact.instructionPC 2933 = 3894 := pc3152

@[simp] theorem pc3153 : Artifact.submissionArtifact.instructionPC 2934 = 3895 := by
  calc
    Artifact.submissionArtifact.instructionPC 2934 = Artifact.submissionArtifact.instructionPC 2933 + (Instr.op .JUMPI).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2933 (Instr.op .JUMPI) (by rfl)
    _ = 3895 := by rw [pc3152]; rfl

@[simp] theorem pc3154 : Artifact.submissionArtifact.instructionPC 2935 = 3896 := by
  calc
    Artifact.submissionArtifact.instructionPC 2935 = Artifact.submissionArtifact.instructionPC 2934 + (Instr.op .JUMPDEST).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2934 (Instr.op .JUMPDEST) (by rfl)
    _ = 3896 := by rw [pc3153]; rfl

@[simp] theorem pc3155 : Artifact.submissionArtifact.instructionPC 2936 = 3897 := by
  calc
    Artifact.submissionArtifact.instructionPC 2936 = Artifact.submissionArtifact.instructionPC 2935 + (Instr.push 0 0).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2935 (Instr.push 0 0) (by rfl)
    _ = 3897 := by rw [pc3154]; rfl

@[simp] theorem pc3156 : Artifact.submissionArtifact.instructionPC 2937 = 3900 := by
  calc
    Artifact.submissionArtifact.instructionPC 2937 = Artifact.submissionArtifact.instructionPC 2936 + (Instr.push 2 5344).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2936 (Instr.push 2 5344) (by rfl)
    _ = 3900 := by rw [pc3155]; rfl

@[simp] theorem pc3157 : Artifact.submissionArtifact.instructionPC 2938 = 3901 := by
  calc
    Artifact.submissionArtifact.instructionPC 2938 = Artifact.submissionArtifact.instructionPC 2937 + (Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2937 (Instr.op .MLOAD) (by rfl)
    _ = 3901 := by rw [pc3156]; rfl

@[simp] theorem pc3158 : Artifact.submissionArtifact.instructionPC 2939 = 3902 := by
  calc
    Artifact.submissionArtifact.instructionPC 2939 = Artifact.submissionArtifact.instructionPC 2938 + (Instr.op .JUMPDEST).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2938 (Instr.op .JUMPDEST) (by rfl)
    _ = 3902 := by rw [pc3157]; rfl

@[simp] theorem pc3159 : Artifact.submissionArtifact.instructionPC 2940 = 3903 := by
  calc
    Artifact.submissionArtifact.instructionPC 2940 = Artifact.submissionArtifact.instructionPC 2939 + (Instr.op (.Dup { idx := 0 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2939 (Instr.op (.Dup { idx := 0 })) (by rfl)
    _ = 3903 := by rw [pc3158]; rfl

@[simp] theorem pc3160 : Artifact.submissionArtifact.instructionPC 2941 = 3904 := by
  calc
    Artifact.submissionArtifact.instructionPC 2941 = Artifact.submissionArtifact.instructionPC 2940 + (Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2940 (Instr.op .MLOAD) (by rfl)
    _ = 3904 := by rw [pc3159]; rfl

@[simp] theorem pc3161 : Artifact.submissionArtifact.instructionPC 2942 = 3905 := by
  calc
    Artifact.submissionArtifact.instructionPC 2942 = Artifact.submissionArtifact.instructionPC 2941 + (Instr.op (.Dup { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2941 (Instr.op (.Dup { idx := 1 })) (by rfl)
    _ = 3905 := by rw [pc3160]; rfl

@[simp] theorem pc3162 : Artifact.submissionArtifact.instructionPC 2943 = 3908 := by
  calc
    Artifact.submissionArtifact.instructionPC 2943 = Artifact.submissionArtifact.instructionPC 2942 + (Instr.push 2 4160).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2942 (Instr.push 2 4160) (by rfl)
    _ = 3908 := by rw [pc3161]; rfl

@[simp] theorem pc3163 : Artifact.submissionArtifact.instructionPC 2944 = 3909 := by
  calc
    Artifact.submissionArtifact.instructionPC 2944 = Artifact.submissionArtifact.instructionPC 2943 + (Instr.op (.Swap { idx := 0 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2943 (Instr.op (.Swap { idx := 0 })) (by rfl)
    _ = 3909 := by rw [pc3162]; rfl

@[simp] theorem pc3164 : Artifact.submissionArtifact.instructionPC 2945 = 3910 := by
  calc
    Artifact.submissionArtifact.instructionPC 2945 = Artifact.submissionArtifact.instructionPC 2944 + (Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2944 (Instr.op .SUB) (by rfl)
    _ = 3910 := by rw [pc3163]; rfl

@[simp] theorem pc3165 : Artifact.submissionArtifact.instructionPC 2946 = 3911 := by
  calc
    Artifact.submissionArtifact.instructionPC 2946 = Artifact.submissionArtifact.instructionPC 2945 + (Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2945 (Instr.op .MLOAD) (by rfl)
    _ = 3911 := by rw [pc3164]; rfl

@[simp] theorem pc3166 : Artifact.submissionArtifact.instructionPC 2947 = 3912 := by
  calc
    Artifact.submissionArtifact.instructionPC 2947 = Artifact.submissionArtifact.instructionPC 2946 + (Instr.op (.Dup { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2946 (Instr.op (.Dup { idx := 1 })) (by rfl)
    _ = 3912 := by rw [pc3165]; rfl

@[simp] theorem pc3167 : Artifact.submissionArtifact.instructionPC 2948 = 3913 := by
  calc
    Artifact.submissionArtifact.instructionPC 2948 = Artifact.submissionArtifact.instructionPC 2947 + (Instr.op .ADD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2947 (Instr.op .ADD) (by rfl)
    _ = 3913 := by rw [pc3166]; rfl

@[simp] theorem pc3168 : Artifact.submissionArtifact.instructionPC 2949 = 3914 := by
  calc
    Artifact.submissionArtifact.instructionPC 2949 = Artifact.submissionArtifact.instructionPC 2948 + (Instr.op (.Dup { idx := 0 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2948 (Instr.op (.Dup { idx := 0 })) (by rfl)
    _ = 3914 := by rw [pc3167]; rfl

@[simp] theorem pc3169 : Artifact.submissionArtifact.instructionPC 2950 = 3915 := by
  calc
    Artifact.submissionArtifact.instructionPC 2950 = Artifact.submissionArtifact.instructionPC 2949 + (Instr.op (.Dup { idx := 2 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2949 (Instr.op (.Dup { idx := 2 })) (by rfl)
    _ = 3915 := by rw [pc3168]; rfl

@[simp] theorem pc3170 : Artifact.submissionArtifact.instructionPC 2951 = 3916 := by
  calc
    Artifact.submissionArtifact.instructionPC 2951 = Artifact.submissionArtifact.instructionPC 2950 + (Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2950 (Instr.op .GT) (by rfl)
    _ = 3916 := by rw [pc3169]; rfl

@[simp] theorem pc3171 : Artifact.submissionArtifact.instructionPC 2952 = 3917 := by
  calc
    Artifact.submissionArtifact.instructionPC 2952 = Artifact.submissionArtifact.instructionPC 2951 + (Instr.op (.Swap { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2951 (Instr.op (.Swap { idx := 1 })) (by rfl)
    _ = 3917 := by rw [pc3170]; rfl

@[simp] theorem pc3172 : Artifact.submissionArtifact.instructionPC 2953 = 3918 := by
  calc
    Artifact.submissionArtifact.instructionPC 2953 = Artifact.submissionArtifact.instructionPC 2952 + (Instr.op .POP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2952 (Instr.op .POP) (by rfl)
    _ = 3918 := by rw [pc3171]; rfl

@[simp] theorem pc3173 : Artifact.submissionArtifact.instructionPC 2954 = 3919 := by
  calc
    Artifact.submissionArtifact.instructionPC 2954 = Artifact.submissionArtifact.instructionPC 2953 + (Instr.op (.Dup { idx := 3 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2953 (Instr.op (.Dup { idx := 3 })) (by rfl)
    _ = 3919 := by rw [pc3172]; rfl

@[simp] theorem pc3174 : Artifact.submissionArtifact.instructionPC 2955 = 3920 := by
  calc
    Artifact.submissionArtifact.instructionPC 2955 = Artifact.submissionArtifact.instructionPC 2954 + (Instr.op .ADD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2954 (Instr.op .ADD) (by rfl)
    _ = 3920 := by rw [pc3173]; rfl

@[simp] theorem pc3175 : Artifact.submissionArtifact.instructionPC 2956 = 3921 := by
  calc
    Artifact.submissionArtifact.instructionPC 2956 = Artifact.submissionArtifact.instructionPC 2955 + (Instr.op (.Dup { idx := 0 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2955 (Instr.op (.Dup { idx := 0 })) (by rfl)
    _ = 3921 := by rw [pc3174]; rfl

@[simp] theorem pc3176 : Artifact.submissionArtifact.instructionPC 2957 = 3922 := by
  calc
    Artifact.submissionArtifact.instructionPC 2957 = Artifact.submissionArtifact.instructionPC 2956 + (Instr.op (.Dup { idx := 4 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2956 (Instr.op (.Dup { idx := 4 })) (by rfl)
    _ = 3922 := by rw [pc3175]; rfl

@[simp] theorem pc3177 : Artifact.submissionArtifact.instructionPC 2958 = 3923 := by
  calc
    Artifact.submissionArtifact.instructionPC 2958 = Artifact.submissionArtifact.instructionPC 2957 + (Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2957 (Instr.op .GT) (by rfl)
    _ = 3923 := by rw [pc3176]; rfl

@[simp] theorem pc3178 : Artifact.submissionArtifact.instructionPC 2959 = 3924 := by
  calc
    Artifact.submissionArtifact.instructionPC 2959 = Artifact.submissionArtifact.instructionPC 2958 + (Instr.op (.Swap { idx := 3 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2958 (Instr.op (.Swap { idx := 3 })) (by rfl)
    _ = 3924 := by rw [pc3177]; rfl

@[simp] theorem pc3179 : Artifact.submissionArtifact.instructionPC 2960 = 3925 := by
  calc
    Artifact.submissionArtifact.instructionPC 2960 = Artifact.submissionArtifact.instructionPC 2959 + (Instr.op .POP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2959 (Instr.op .POP) (by rfl)
    _ = 3925 := by rw [pc3178]; rfl

@[simp] theorem pc3180 : Artifact.submissionArtifact.instructionPC 2961 = 3926 := by
  calc
    Artifact.submissionArtifact.instructionPC 2961 = Artifact.submissionArtifact.instructionPC 2960 + (Instr.op (.Dup { idx := 2 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2960 (Instr.op (.Dup { idx := 2 })) (by rfl)
    _ = 3926 := by rw [pc3179]; rfl

@[simp] theorem pc3181 : Artifact.submissionArtifact.instructionPC 2962 = 3927 := by
  calc
    Artifact.submissionArtifact.instructionPC 2962 = Artifact.submissionArtifact.instructionPC 2961 + (Instr.op .MSTORE).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2961 (Instr.op .MSTORE) (by rfl)
    _ = 3927 := by rw [pc3180]; rfl

@[simp] theorem pc3182 : Artifact.submissionArtifact.instructionPC 2963 = 3928 := by
  calc
    Artifact.submissionArtifact.instructionPC 2963 = Artifact.submissionArtifact.instructionPC 2962 + (Instr.op (.Swap { idx := 0 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2962 (Instr.op (.Swap { idx := 0 })) (by rfl)
    _ = 3928 := by rw [pc3181]; rfl

@[simp] theorem pc3183 : Artifact.submissionArtifact.instructionPC 2964 = 3929 := by
  calc
    Artifact.submissionArtifact.instructionPC 2964 = Artifact.submissionArtifact.instructionPC 2963 + (Instr.op (.Swap { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2963 (Instr.op (.Swap { idx := 1 })) (by rfl)
    _ = 3929 := by rw [pc3182]; rfl

@[simp] theorem pc3184 : Artifact.submissionArtifact.instructionPC 2965 = 3930 := by
  calc
    Artifact.submissionArtifact.instructionPC 2965 = Artifact.submissionArtifact.instructionPC 2964 + (Instr.op .OR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2964 (Instr.op .OR) (by rfl)
    _ = 3930 := by rw [pc3183]; rfl

@[simp] theorem pc3185 : Artifact.submissionArtifact.instructionPC 2966 = 3931 := by
  calc
    Artifact.submissionArtifact.instructionPC 2966 = Artifact.submissionArtifact.instructionPC 2965 + (Instr.op (.Swap { idx := 0 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2965 (Instr.op (.Swap { idx := 0 })) (by rfl)
    _ = 3931 := by rw [pc3184]; rfl

@[simp] theorem pc3185_compact : Artifact.submissionArtifact.instructionPC 2967 = 3933 := by
  calc
    Artifact.submissionArtifact.instructionPC 2967 = Artifact.submissionArtifact.instructionPC 2966 + (Instr.push 1 31).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2966 (Instr.push 1 31) (by rfl)
    _ = 3933 := by rw [pc3185]; rfl

@[simp] theorem pc3186 : Artifact.submissionArtifact.instructionPC 2968 = 3934 := by
  calc
    Artifact.submissionArtifact.instructionPC 2968 = Artifact.submissionArtifact.instructionPC 2967 + (Instr.op .NOT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2967 (Instr.op .NOT) (by rfl)
    _ = 3934 := by rw [pc3185_compact]; rfl

@[simp] theorem pc3187 : Artifact.submissionArtifact.instructionPC 2969 = 3935 := by
  calc
    Artifact.submissionArtifact.instructionPC 2969 = Artifact.submissionArtifact.instructionPC 2968 + (Instr.op .ADD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2968 (Instr.op .ADD) (by rfl)
    _ = 3935 := by rw [pc3186]; rfl

@[simp] theorem pc3188 : Artifact.submissionArtifact.instructionPC 2970 = 3938 := by
  calc
    Artifact.submissionArtifact.instructionPC 2970 = Artifact.submissionArtifact.instructionPC 2969 + (Instr.push 2 4159).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2969 (Instr.push 2 4159) (by rfl)
    _ = 3938 := by rw [pc3187]; rfl

@[simp] theorem pc3189 : Artifact.submissionArtifact.instructionPC 2971 = 3939 := by
  calc
    Artifact.submissionArtifact.instructionPC 2971 = Artifact.submissionArtifact.instructionPC 2970 + (Instr.op (.Dup { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2970 (Instr.op (.Dup { idx := 1 })) (by rfl)
    _ = 3939 := by rw [pc3188]; rfl

@[simp] theorem pc3190 : Artifact.submissionArtifact.instructionPC 2972 = 3940 := by
  calc
    Artifact.submissionArtifact.instructionPC 2972 = Artifact.submissionArtifact.instructionPC 2971 + (Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2971 (Instr.op .GT) (by rfl)
    _ = 3940 := by rw [pc3189]; rfl

@[simp] theorem pc3191 : Artifact.submissionArtifact.instructionPC 2973 = 3943 := by
  calc
    Artifact.submissionArtifact.instructionPC 2973 = Artifact.submissionArtifact.instructionPC 2972 + (Instr.push 2 3901).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2972 (Instr.push 2 3901) (by rfl)
    _ = 3943 := by rw [pc3190]; rfl

@[simp] theorem pc3192 : Artifact.submissionArtifact.instructionPC 2974 = 3944 := by
  calc
    Artifact.submissionArtifact.instructionPC 2974 = Artifact.submissionArtifact.instructionPC 2973 + (Instr.op .JUMPI).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2973 (Instr.op .JUMPI) (by rfl)
    _ = 3944 := by rw [pc3191]; rfl

@[simp] theorem pc3193 : Artifact.submissionArtifact.instructionPC 2975 = 3945 := by
  calc
    Artifact.submissionArtifact.instructionPC 2975 = Artifact.submissionArtifact.instructionPC 2974 + (Instr.op .POP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2974 (Instr.op .POP) (by rfl)
    _ = 3945 := by rw [pc3192]; rfl

@[simp] theorem pc3194 : Artifact.submissionArtifact.instructionPC 2976 = 3948 := by
  calc
    Artifact.submissionArtifact.instructionPC 2976 = Artifact.submissionArtifact.instructionPC 2975 + (Instr.push 2 4128).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2975 (Instr.push 2 4128) (by rfl)
    _ = 3948 := by rw [pc3193]; rfl

@[simp] theorem pc3195 : Artifact.submissionArtifact.instructionPC 2977 = 3949 := by
  calc
    Artifact.submissionArtifact.instructionPC 2977 = Artifact.submissionArtifact.instructionPC 2976 + (Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2976 (Instr.op .MLOAD) (by rfl)
    _ = 3949 := by rw [pc3194]; rfl

@[simp] theorem pc3196 : Artifact.submissionArtifact.instructionPC 2978 = 3950 := by
  calc
    Artifact.submissionArtifact.instructionPC 2978 = Artifact.submissionArtifact.instructionPC 2977 + (Instr.op (.Dup { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2977 (Instr.op (.Dup { idx := 1 })) (by rfl)
    _ = 3950 := by rw [pc3195]; rfl

@[simp] theorem pc3197 : Artifact.submissionArtifact.instructionPC 2979 = 3951 := by
  calc
    Artifact.submissionArtifact.instructionPC 2979 = Artifact.submissionArtifact.instructionPC 2978 + (Instr.op .ADD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2978 (Instr.op .ADD) (by rfl)
    _ = 3951 := by rw [pc3196]; rfl

@[simp] theorem pc3198 : Artifact.submissionArtifact.instructionPC 2980 = 3952 := by
  calc
    Artifact.submissionArtifact.instructionPC 2980 = Artifact.submissionArtifact.instructionPC 2979 + (Instr.op (.Dup { idx := 0 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2979 (Instr.op (.Dup { idx := 0 })) (by rfl)
    _ = 3952 := by rw [pc3197]; rfl

@[simp] theorem pc3199 : Artifact.submissionArtifact.instructionPC 2981 = 3955 := by
  calc
    Artifact.submissionArtifact.instructionPC 2981 = Artifact.submissionArtifact.instructionPC 2980 + (Instr.push 2 4128).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2980 (Instr.push 2 4128) (by rfl)
    _ = 3955 := by rw [pc3198]; rfl

@[simp] theorem pc3200 : Artifact.submissionArtifact.instructionPC 2982 = 3956 := by
  calc
    Artifact.submissionArtifact.instructionPC 2982 = Artifact.submissionArtifact.instructionPC 2981 + (Instr.op .MSTORE).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2981 (Instr.op .MSTORE) (by rfl)
    _ = 3956 := by rw [pc3199]; rfl

@[simp] theorem pc3201 : Artifact.submissionArtifact.instructionPC 2983 = 3957 := by
  calc
    Artifact.submissionArtifact.instructionPC 2983 = Artifact.submissionArtifact.instructionPC 2982 + (Instr.op .LT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2982 (Instr.op .LT) (by rfl)
    _ = 3957 := by rw [pc3200]; rfl

@[simp] theorem pc3202 : Artifact.submissionArtifact.instructionPC 2984 = 3958 := by
  calc
    Artifact.submissionArtifact.instructionPC 2984 = Artifact.submissionArtifact.instructionPC 2983 + (Instr.op .ISZERO).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2983 (Instr.op .ISZERO) (by rfl)
    _ = 3958 := by rw [pc3201]; rfl

@[simp] theorem pc3203 : Artifact.submissionArtifact.instructionPC 2985 = 3961 := by
  calc
    Artifact.submissionArtifact.instructionPC 2985 = Artifact.submissionArtifact.instructionPC 2984 + (Instr.push 2 3895).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2984 (Instr.push 2 3895) (by rfl)
    _ = 3961 := by rw [pc3202]; rfl

@[simp] theorem pc3204 : Artifact.submissionArtifact.instructionPC 2986 = 3962 := by
  calc
    Artifact.submissionArtifact.instructionPC 2986 = Artifact.submissionArtifact.instructionPC 2985 + (Instr.op .JUMPI).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2985 (Instr.op .JUMPI) (by rfl)
    _ = 3962 := by rw [pc3203]; rfl

@[simp] theorem pc3205 : Artifact.submissionArtifact.instructionPC 2987 = 3963 := by
  calc
    Artifact.submissionArtifact.instructionPC 2987 = Artifact.submissionArtifact.instructionPC 2986 + (Instr.op .JUMPDEST).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2986 (Instr.op .JUMPDEST) (by rfl)
    _ = 3963 := by rw [pc3204]; rfl

@[simp] theorem pc3206 : Artifact.submissionArtifact.instructionPC 2988 = 3966 := by
  calc
    Artifact.submissionArtifact.instructionPC 2988 = Artifact.submissionArtifact.instructionPC 2987 + (Instr.push 2 4128).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2987 (Instr.push 2 4128) (by rfl)
    _ = 3966 := by rw [pc3205]; rfl

@[simp] theorem pc3207 : Artifact.submissionArtifact.instructionPC 2989 = 3967 := by
  calc
    Artifact.submissionArtifact.instructionPC 2989 = Artifact.submissionArtifact.instructionPC 2988 + (Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2988 (Instr.op .MLOAD) (by rfl)
    _ = 3967 := by rw [pc3206]; rfl

@[simp] theorem pc3208 : Artifact.submissionArtifact.instructionPC 2990 = 3968 := by
  calc
    Artifact.submissionArtifact.instructionPC 2990 = Artifact.submissionArtifact.instructionPC 2989 + (Instr.op .ISZERO).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2989 (Instr.op .ISZERO) (by rfl)
    _ = 3968 := by rw [pc3207]; rfl

@[simp] theorem pc3209 : Artifact.submissionArtifact.instructionPC 2991 = 3971 := by
  calc
    Artifact.submissionArtifact.instructionPC 2991 = Artifact.submissionArtifact.instructionPC 2990 + (Instr.push 2 4030).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2990 (Instr.push 2 4030) (by rfl)
    _ = 3971 := by rw [pc3208]; rfl

@[simp] theorem pc3210 : Artifact.submissionArtifact.instructionPC 2992 = 3972 := by
  calc
    Artifact.submissionArtifact.instructionPC 2992 = Artifact.submissionArtifact.instructionPC 2991 + (Instr.op .JUMPI).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2991 (Instr.op .JUMPI) (by rfl)
    _ = 3972 := by rw [pc3209]; rfl

@[simp] theorem pc3211 : Artifact.submissionArtifact.instructionPC 2993 = 3973 := by
  calc
    Artifact.submissionArtifact.instructionPC 2993 = Artifact.submissionArtifact.instructionPC 2992 + (Instr.push 0 0).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2992 (Instr.push 0 0) (by rfl)
    _ = 3973 := by rw [pc3210]; rfl

@[simp] theorem pc3212 : Artifact.submissionArtifact.instructionPC 2994 = 3976 := by
  calc
    Artifact.submissionArtifact.instructionPC 2994 = Artifact.submissionArtifact.instructionPC 2993 + (Instr.push 2 5344).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2993 (Instr.push 2 5344) (by rfl)
    _ = 3976 := by rw [pc3211]; rfl

@[simp] theorem pc3213 : Artifact.submissionArtifact.instructionPC 2995 = 3977 := by
  calc
    Artifact.submissionArtifact.instructionPC 2995 = Artifact.submissionArtifact.instructionPC 2994 + (Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2994 (Instr.op .MLOAD) (by rfl)
    _ = 3977 := by rw [pc3212]; rfl

@[simp] theorem pc3214 : Artifact.submissionArtifact.instructionPC 2996 = 3978 := by
  calc
    Artifact.submissionArtifact.instructionPC 2996 = Artifact.submissionArtifact.instructionPC 2995 + (Instr.op .JUMPDEST).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2995 (Instr.op .JUMPDEST) (by rfl)
    _ = 3978 := by rw [pc3213]; rfl

@[simp] theorem pc3215 : Artifact.submissionArtifact.instructionPC 2997 = 3979 := by
  calc
    Artifact.submissionArtifact.instructionPC 2997 = Artifact.submissionArtifact.instructionPC 2996 + (Instr.op (.Dup { idx := 0 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2996 (Instr.op (.Dup { idx := 0 })) (by rfl)
    _ = 3979 := by rw [pc3214]; rfl

@[simp] theorem pc3216 : Artifact.submissionArtifact.instructionPC 2998 = 3980 := by
  calc
    Artifact.submissionArtifact.instructionPC 2998 = Artifact.submissionArtifact.instructionPC 2997 + (Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2997 (Instr.op .MLOAD) (by rfl)
    _ = 3980 := by rw [pc3215]; rfl

@[simp] theorem pc3217 : Artifact.submissionArtifact.instructionPC 2999 = 3983 := by
  calc
    Artifact.submissionArtifact.instructionPC 2999 = Artifact.submissionArtifact.instructionPC 2998 + (Instr.push 2 4160).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2998 (Instr.push 2 4160) (by rfl)
    _ = 3983 := by rw [pc3216]; rfl

@[simp] theorem pc3219 : Artifact.submissionArtifact.instructionPC 3000 = 3984 := by
  calc
    Artifact.submissionArtifact.instructionPC 3000 = Artifact.submissionArtifact.instructionPC 2999 + (Instr.op (.Dup { idx := 2 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2999 (Instr.op (.Dup { idx := 2 })) (by rfl)
    _ = 3984 := by rw [pc3217]; rfl

@[simp] theorem pc3220 : Artifact.submissionArtifact.instructionPC 3001 = 3985 := by
  calc
    Artifact.submissionArtifact.instructionPC 3001 = Artifact.submissionArtifact.instructionPC 3000 + (Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3000 (Instr.op .SUB) (by rfl)
    _ = 3985 := by rw [pc3219]; rfl

@[simp] theorem pc3221 : Artifact.submissionArtifact.instructionPC 3002 = 3986 := by
  calc
    Artifact.submissionArtifact.instructionPC 3002 = Artifact.submissionArtifact.instructionPC 3001 + (Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3001 (Instr.op .MLOAD) (by rfl)
    _ = 3986 := by rw [pc3220]; rfl

@[simp] theorem pc3222 : Artifact.submissionArtifact.instructionPC 3003 = 3987 := by
  calc
    Artifact.submissionArtifact.instructionPC 3003 = Artifact.submissionArtifact.instructionPC 3002 + (Instr.op (.Dup { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3002 (Instr.op (.Dup { idx := 1 })) (by rfl)
    _ = 3987 := by rw [pc3221]; rfl

@[simp] theorem pc3223 : Artifact.submissionArtifact.instructionPC 3004 = 3988 := by
  calc
    Artifact.submissionArtifact.instructionPC 3004 = Artifact.submissionArtifact.instructionPC 3003 + (Instr.op (.Dup { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3003 (Instr.op (.Dup { idx := 1 })) (by rfl)
    _ = 3988 := by rw [pc3222]; rfl

@[simp] theorem pc3224 : Artifact.submissionArtifact.instructionPC 3005 = 3989 := by
  calc
    Artifact.submissionArtifact.instructionPC 3005 = Artifact.submissionArtifact.instructionPC 3004 + (Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3004 (Instr.op .GT) (by rfl)
    _ = 3989 := by rw [pc3223]; rfl

@[simp] theorem pc3225 : Artifact.submissionArtifact.instructionPC 3006 = 3990 := by
  calc
    Artifact.submissionArtifact.instructionPC 3006 = Artifact.submissionArtifact.instructionPC 3005 + (Instr.op (.Swap { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3005 (Instr.op (.Swap { idx := 1 })) (by rfl)
    _ = 3990 := by rw [pc3224]; rfl

@[simp] theorem pc3226 : Artifact.submissionArtifact.instructionPC 3007 = 3991 := by
  calc
    Artifact.submissionArtifact.instructionPC 3007 = Artifact.submissionArtifact.instructionPC 3006 + (Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3006 (Instr.op .SUB) (by rfl)
    _ = 3991 := by rw [pc3225]; rfl

@[simp] theorem pc3227 : Artifact.submissionArtifact.instructionPC 3008 = 3992 := by
  calc
    Artifact.submissionArtifact.instructionPC 3008 = Artifact.submissionArtifact.instructionPC 3007 + (Instr.op (.Dup { idx := 3 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3007 (Instr.op (.Dup { idx := 3 })) (by rfl)
    _ = 3992 := by rw [pc3226]; rfl

@[simp] theorem pc3228 : Artifact.submissionArtifact.instructionPC 3009 = 3993 := by
  calc
    Artifact.submissionArtifact.instructionPC 3009 = Artifact.submissionArtifact.instructionPC 3008 + (Instr.op (.Dup { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3008 (Instr.op (.Dup { idx := 1 })) (by rfl)
    _ = 3993 := by rw [pc3227]; rfl

@[simp] theorem pc3229 : Artifact.submissionArtifact.instructionPC 3010 = 3994 := by
  calc
    Artifact.submissionArtifact.instructionPC 3010 = Artifact.submissionArtifact.instructionPC 3009 + (Instr.op .LT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3009 (Instr.op .LT) (by rfl)
    _ = 3994 := by rw [pc3228]; rfl

@[simp] theorem pc3230 : Artifact.submissionArtifact.instructionPC 3011 = 3995 := by
  calc
    Artifact.submissionArtifact.instructionPC 3011 = Artifact.submissionArtifact.instructionPC 3010 + (Instr.op (.Swap { idx := 0 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3010 (Instr.op (.Swap { idx := 0 })) (by rfl)
    _ = 3995 := by rw [pc3229]; rfl

@[simp] theorem pc3231 : Artifact.submissionArtifact.instructionPC 3012 = 3996 := by
  calc
    Artifact.submissionArtifact.instructionPC 3012 = Artifact.submissionArtifact.instructionPC 3011 + (Instr.op (.Dup { idx := 4 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3011 (Instr.op (.Dup { idx := 4 })) (by rfl)
    _ = 3996 := by rw [pc3230]; rfl

@[simp] theorem pc3232 : Artifact.submissionArtifact.instructionPC 3013 = 3997 := by
  calc
    Artifact.submissionArtifact.instructionPC 3013 = Artifact.submissionArtifact.instructionPC 3012 + (Instr.op (.Swap { idx := 0 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3012 (Instr.op (.Swap { idx := 0 })) (by rfl)
    _ = 3997 := by rw [pc3231]; rfl

@[simp] theorem pc3233 : Artifact.submissionArtifact.instructionPC 3014 = 3998 := by
  calc
    Artifact.submissionArtifact.instructionPC 3014 = Artifact.submissionArtifact.instructionPC 3013 + (Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3013 (Instr.op .SUB) (by rfl)
    _ = 3998 := by rw [pc3232]; rfl

@[simp] theorem pc3234 : Artifact.submissionArtifact.instructionPC 3015 = 3999 := by
  calc
    Artifact.submissionArtifact.instructionPC 3015 = Artifact.submissionArtifact.instructionPC 3014 + (Instr.op (.Dup { idx := 3 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3014 (Instr.op (.Dup { idx := 3 })) (by rfl)
    _ = 3999 := by rw [pc3233]; rfl

@[simp] theorem pc3235 : Artifact.submissionArtifact.instructionPC 3016 = 4000 := by
  calc
    Artifact.submissionArtifact.instructionPC 3016 = Artifact.submissionArtifact.instructionPC 3015 + (Instr.op .MSTORE).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3015 (Instr.op .MSTORE) (by rfl)
    _ = 4000 := by rw [pc3234]; rfl

@[simp] theorem pc3236 : Artifact.submissionArtifact.instructionPC 3017 = 4001 := by
  calc
    Artifact.submissionArtifact.instructionPC 3017 = Artifact.submissionArtifact.instructionPC 3016 + (Instr.op .OR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3016 (Instr.op .OR) (by rfl)
    _ = 4001 := by rw [pc3235]; rfl

@[simp] theorem pc3237 : Artifact.submissionArtifact.instructionPC 3018 = 4002 := by
  calc
    Artifact.submissionArtifact.instructionPC 3018 = Artifact.submissionArtifact.instructionPC 3017 + (Instr.op (.Swap { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3017 (Instr.op (.Swap { idx := 1 })) (by rfl)
    _ = 4002 := by rw [pc3236]; rfl

@[simp] theorem pc3238 : Artifact.submissionArtifact.instructionPC 3019 = 4003 := by
  calc
    Artifact.submissionArtifact.instructionPC 3019 = Artifact.submissionArtifact.instructionPC 3018 + (Instr.op .POP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3018 (Instr.op .POP) (by rfl)
    _ = 4003 := by rw [pc3237]; rfl

@[simp] theorem pc3238_compact : Artifact.submissionArtifact.instructionPC 3020 = 4005 := by
  calc
    Artifact.submissionArtifact.instructionPC 3020 = Artifact.submissionArtifact.instructionPC 3019 + (Instr.push 1 31).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3019 (Instr.push 1 31) (by rfl)
    _ = 4005 := by rw [pc3238]; rfl

@[simp] theorem pc3239 : Artifact.submissionArtifact.instructionPC 3021 = 4006 := by
  calc
    Artifact.submissionArtifact.instructionPC 3021 = Artifact.submissionArtifact.instructionPC 3020 + (Instr.op .NOT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3020 (Instr.op .NOT) (by rfl)
    _ = 4006 := by rw [pc3238_compact]; rfl

@[simp] theorem pc3240 : Artifact.submissionArtifact.instructionPC 3022 = 4007 := by
  calc
    Artifact.submissionArtifact.instructionPC 3022 = Artifact.submissionArtifact.instructionPC 3021 + (Instr.op .ADD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3021 (Instr.op .ADD) (by rfl)
    _ = 4007 := by rw [pc3239]; rfl

@[simp] theorem pc3241 : Artifact.submissionArtifact.instructionPC 3023 = 4010 := by
  calc
    Artifact.submissionArtifact.instructionPC 3023 = Artifact.submissionArtifact.instructionPC 3022 + (Instr.push 2 4159).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3022 (Instr.push 2 4159) (by rfl)
    _ = 4010 := by rw [pc3240]; rfl

@[simp] theorem pc3242 : Artifact.submissionArtifact.instructionPC 3024 = 4011 := by
  calc
    Artifact.submissionArtifact.instructionPC 3024 = Artifact.submissionArtifact.instructionPC 3023 + (Instr.op (.Dup { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3023 (Instr.op (.Dup { idx := 1 })) (by rfl)
    _ = 4011 := by rw [pc3241]; rfl

@[simp] theorem pc3243 : Artifact.submissionArtifact.instructionPC 3025 = 4012 := by
  calc
    Artifact.submissionArtifact.instructionPC 3025 = Artifact.submissionArtifact.instructionPC 3024 + (Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3024 (Instr.op .GT) (by rfl)
    _ = 4012 := by rw [pc3242]; rfl

@[simp] theorem pc3244 : Artifact.submissionArtifact.instructionPC 3026 = 4015 := by
  calc
    Artifact.submissionArtifact.instructionPC 3026 = Artifact.submissionArtifact.instructionPC 3025 + (Instr.push 2 3977).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3025 (Instr.push 2 3977) (by rfl)
    _ = 4015 := by rw [pc3243]; rfl

@[simp] theorem pc3245 : Artifact.submissionArtifact.instructionPC 3027 = 4016 := by
  calc
    Artifact.submissionArtifact.instructionPC 3027 = Artifact.submissionArtifact.instructionPC 3026 + (Instr.op .JUMPI).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3026 (Instr.op .JUMPI) (by rfl)
    _ = 4016 := by rw [pc3244]; rfl

@[simp] theorem pc3246 : Artifact.submissionArtifact.instructionPC 3028 = 4017 := by
  calc
    Artifact.submissionArtifact.instructionPC 3028 = Artifact.submissionArtifact.instructionPC 3027 + (Instr.op .POP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3027 (Instr.op .POP) (by rfl)
    _ = 4017 := by rw [pc3245]; rfl

@[simp] theorem pc3247 : Artifact.submissionArtifact.instructionPC 3029 = 4020 := by
  calc
    Artifact.submissionArtifact.instructionPC 3029 = Artifact.submissionArtifact.instructionPC 3028 + (Instr.push 2 4128).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3028 (Instr.push 2 4128) (by rfl)
    _ = 4020 := by rw [pc3246]; rfl

@[simp] theorem pc3248 : Artifact.submissionArtifact.instructionPC 3030 = 4021 := by
  calc
    Artifact.submissionArtifact.instructionPC 3030 = Artifact.submissionArtifact.instructionPC 3029 + (Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3029 (Instr.op .MLOAD) (by rfl)
    _ = 4021 := by rw [pc3247]; rfl

@[simp] theorem pc3249 : Artifact.submissionArtifact.instructionPC 3031 = 4022 := by
  calc
    Artifact.submissionArtifact.instructionPC 3031 = Artifact.submissionArtifact.instructionPC 3030 + (Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3030 (Instr.op .SUB) (by rfl)
    _ = 4022 := by rw [pc3248]; rfl

@[simp] theorem pc3250 : Artifact.submissionArtifact.instructionPC 3032 = 4025 := by
  calc
    Artifact.submissionArtifact.instructionPC 3032 = Artifact.submissionArtifact.instructionPC 3031 + (Instr.push 2 4128).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3031 (Instr.push 2 4128) (by rfl)
    _ = 4025 := by rw [pc3249]; rfl

@[simp] theorem pc3251 : Artifact.submissionArtifact.instructionPC 3033 = 4026 := by
  calc
    Artifact.submissionArtifact.instructionPC 3033 = Artifact.submissionArtifact.instructionPC 3032 + (Instr.op .MSTORE).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3032 (Instr.op .MSTORE) (by rfl)
    _ = 4026 := by rw [pc3250]; rfl

@[simp] theorem pc3252 : Artifact.submissionArtifact.instructionPC 3034 = 4029 := by
  calc
    Artifact.submissionArtifact.instructionPC 3034 = Artifact.submissionArtifact.instructionPC 3033 + (Instr.push 2 3962).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3033 (Instr.push 2 3962) (by rfl)
    _ = 4029 := by rw [pc3251]; rfl

@[simp] theorem pc3253 : Artifact.submissionArtifact.instructionPC 3035 = 4030 := by
  calc
    Artifact.submissionArtifact.instructionPC 3035 = Artifact.submissionArtifact.instructionPC 3034 + (Instr.op .JUMP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3034 (Instr.op .JUMP) (by rfl)
    _ = 4030 := by rw [pc3252]; rfl

@[simp] theorem pc3254 : Artifact.submissionArtifact.instructionPC 3036 = 4031 := by
  calc
    Artifact.submissionArtifact.instructionPC 3036 = Artifact.submissionArtifact.instructionPC 3035 + (Instr.op .JUMPDEST).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3035 (Instr.op .JUMPDEST) (by rfl)
    _ = 4031 := by rw [pc3253]; rfl

@[simp] theorem pc3255 : Artifact.submissionArtifact.instructionPC 3037 = 4034 := by
  calc
    Artifact.submissionArtifact.instructionPC 3037 = Artifact.submissionArtifact.instructionPC 3036 + (Instr.push 2 4041).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3036 (Instr.push 2 4041) (by rfl)
    _ = 4034 := by rw [pc3254]; rfl

@[simp] theorem pc3256 : Artifact.submissionArtifact.instructionPC 3038 = 4037 := by
  calc
    Artifact.submissionArtifact.instructionPC 3038 = Artifact.submissionArtifact.instructionPC 3037 + (Instr.push 2 512).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3037 (Instr.push 2 512) (by rfl)
    _ = 4037 := by rw [pc3255]; rfl

@[simp] theorem pc3257 : Artifact.submissionArtifact.instructionPC 3039 = 4040 := by
  calc
    Artifact.submissionArtifact.instructionPC 3039 = Artifact.submissionArtifact.instructionPC 3038 + (Instr.push 2 4824).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3038 (Instr.push 2 4824) (by rfl)
    _ = 4040 := by rw [pc3256]; rfl

@[simp] theorem pc3258 : Artifact.submissionArtifact.instructionPC 3040 = 4041 := by
  calc
    Artifact.submissionArtifact.instructionPC 3040 = Artifact.submissionArtifact.instructionPC 3039 + (Instr.op .JUMP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3039 (Instr.op .JUMP) (by rfl)
    _ = 4041 := by rw [pc3257]; rfl

@[simp] theorem pc3259 : Artifact.submissionArtifact.instructionPC 3041 = 4042 := by
  calc
    Artifact.submissionArtifact.instructionPC 3041 = Artifact.submissionArtifact.instructionPC 3040 + (Instr.op .JUMPDEST).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3040 (Instr.op .JUMPDEST) (by rfl)
    _ = 4042 := by rw [pc3258]; rfl

@[simp] theorem pc3260 : Artifact.submissionArtifact.instructionPC 3042 = 4043 := by
  calc
    Artifact.submissionArtifact.instructionPC 3042 = Artifact.submissionArtifact.instructionPC 3041 + (Instr.push 0 0).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3041 (Instr.push 0 0) (by rfl)
    _ = 4043 := by rw [pc3259]; rfl

@[simp] theorem pc3261 : Artifact.submissionArtifact.instructionPC 3043 = 4044 := by
  calc
    Artifact.submissionArtifact.instructionPC 3043 = Artifact.submissionArtifact.instructionPC 3042 + (Instr.op .NOT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3042 (Instr.op .NOT) (by rfl)
    _ = 4044 := by rw [pc3260]; rfl

@[simp] theorem pc3262 : Artifact.submissionArtifact.instructionPC 3044 = 4045 := by
  calc
    Artifact.submissionArtifact.instructionPC 3044 = Artifact.submissionArtifact.instructionPC 3043 + (Instr.op .ADD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3043 (Instr.op .ADD) (by rfl)
    _ = 4045 := by rw [pc3261]; rfl

@[simp] theorem pc3263 : Artifact.submissionArtifact.instructionPC 3045 = 4049 := by
  calc
    Artifact.submissionArtifact.instructionPC 3045 = Artifact.submissionArtifact.instructionPC 3044 + (Instr.push 3 3643).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3044 (Instr.push 3 3643) (by rfl)
    _ = 4049 := by rw [pc3262]; rfl

@[simp] theorem pc3264 : Artifact.submissionArtifact.instructionPC 3046 = 4050 := by
  calc
    Artifact.submissionArtifact.instructionPC 3046 = Artifact.submissionArtifact.instructionPC 3045 + (Instr.op .JUMP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3045 (Instr.op .JUMP) (by rfl)
    _ = 4050 := by rw [pc3263]; rfl

@[simp] theorem pc3265 : Artifact.submissionArtifact.instructionPC 3047 = 4051 := by
  calc
    Artifact.submissionArtifact.instructionPC 3047 = Artifact.submissionArtifact.instructionPC 3046 + (Instr.op .JUMPDEST).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3046 (Instr.op .JUMPDEST) (by rfl)
    _ = 4051 := by rw [pc3264]; rfl

@[simp] theorem pc3265a : Artifact.submissionArtifact.instructionPC 3048 = 4052 := by
  calc
    Artifact.submissionArtifact.instructionPC 3048 = Artifact.submissionArtifact.instructionPC 3047 + (Instr.op .POP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3047 (Instr.op .POP) (by rfl)
    _ = 4052 := by rw [pc3265]; rfl

@[simp] theorem pc3265b : Artifact.submissionArtifact.instructionPC 3049 = 4055 := by
  calc
    Artifact.submissionArtifact.instructionPC 3049 = Artifact.submissionArtifact.instructionPC 3048 + (Instr.push 2 5248).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3048 (Instr.push 2 5248) (by rfl)
    _ = 4055 := by rw [pc3265a]; rfl

@[simp] theorem pc3265c : Artifact.submissionArtifact.instructionPC 3050 = 4056 := by
  calc
    Artifact.submissionArtifact.instructionPC 3050 = Artifact.submissionArtifact.instructionPC 3049 + (Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3049 (Instr.op .MLOAD) (by rfl)
    _ = 4056 := by rw [pc3265b]; rfl

@[simp] theorem pc3265d : Artifact.submissionArtifact.instructionPC 3051 = 4059 := by
  calc
    Artifact.submissionArtifact.instructionPC 3051 = Artifact.submissionArtifact.instructionPC 3050 + (Instr.push 2 1280).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3050 (Instr.push 2 1280) (by rfl)
    _ = 4059 := by rw [pc3265c]; rfl

@[simp] theorem pc3265e : Artifact.submissionArtifact.instructionPC 3052 = 4062 := by
  calc
    Artifact.submissionArtifact.instructionPC 3052 = Artifact.submissionArtifact.instructionPC 3051 + (Instr.push 2 1024).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3051 (Instr.push 2 1024) (by rfl)
    _ = 4062 := by rw [pc3265d]; rfl

@[simp] theorem pc3266 : Artifact.submissionArtifact.instructionPC 3053 = 4063 := by
  calc
    Artifact.submissionArtifact.instructionPC 3053 = Artifact.submissionArtifact.instructionPC 3052 + (Instr.op .MCOPY).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3052 (Instr.op .MCOPY) (by rfl)
    _ = 4063 := by rw [pc3265e]; rfl

@[simp] theorem pc3267 : Artifact.submissionArtifact.instructionPC 3054 = 4066 := by
  calc
    Artifact.submissionArtifact.instructionPC 3054 = Artifact.submissionArtifact.instructionPC 3053 + (Instr.push 2 3273).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3053 (Instr.push 2 3273) (by rfl)
    _ = 4066 := by rw [pc3266]; rfl

@[simp] theorem earlyExtraPC2883 : Artifact.submissionArtifact.instructionPC 3662 = 4824 := by rfl

@[simp] theorem earlyExtraPC2884 : Artifact.submissionArtifact.instructionPC 3663 = 4825 := by
  calc
    Artifact.submissionArtifact.instructionPC 3663 = Artifact.submissionArtifact.instructionPC 3662 + (Instr.op .JUMPDEST).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3662 (Instr.op .JUMPDEST) (by rfl)
    _ = 4825 := by rw [earlyExtraPC2883]; rfl

@[simp] theorem earlyExtraPC2885 : Artifact.submissionArtifact.instructionPC 3664 = 4826 := by
  calc
    Artifact.submissionArtifact.instructionPC 3664 = Artifact.submissionArtifact.instructionPC 3663 + (Instr.push 0 0).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3663 (Instr.push 0 0) (by rfl)
    _ = 4826 := by rw [earlyExtraPC2884]; rfl

@[simp] theorem earlyExtraPC2886 : Artifact.submissionArtifact.instructionPC 3665 = 4827 := by
  calc
    Artifact.submissionArtifact.instructionPC 3665 = Artifact.submissionArtifact.instructionPC 3664 + (Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3664 (Instr.op .MLOAD) (by rfl)
    _ = 4827 := by rw [earlyExtraPC2885]; rfl

@[simp] theorem earlyExtraPC2887 : Artifact.submissionArtifact.instructionPC 3666 = 4830 := by
  calc
    Artifact.submissionArtifact.instructionPC 3666 = Artifact.submissionArtifact.instructionPC 3665 + (Instr.push 2 4160).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3665 (Instr.push 2 4160) (by rfl)
    _ = 4830 := by rw [earlyExtraPC2886]; rfl

@[simp] theorem earlyExtraPC2888 : Artifact.submissionArtifact.instructionPC 3667 = 4831 := by
  calc
    Artifact.submissionArtifact.instructionPC 3667 = Artifact.submissionArtifact.instructionPC 3666 + (Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3666 (Instr.op .MLOAD) (by rfl)
    _ = 4831 := by rw [earlyExtraPC2887]; rfl

@[simp] theorem earlyExtraPC2889 : Artifact.submissionArtifact.instructionPC 3668 = 4832 := by
  calc
    Artifact.submissionArtifact.instructionPC 3668 = Artifact.submissionArtifact.instructionPC 3667 + (Instr.op .LT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3667 (Instr.op .LT) (by rfl)
    _ = 4832 := by rw [earlyExtraPC2888]; rfl

@[simp] theorem earlyExtraPC2890 : Artifact.submissionArtifact.instructionPC 3669 = 4835 := by
  calc
    Artifact.submissionArtifact.instructionPC 3669 = Artifact.submissionArtifact.instructionPC 3668 + (Instr.push 2 4128).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3668 (Instr.push 2 4128) (by rfl)
    _ = 4835 := by rw [earlyExtraPC2889]; rfl

@[simp] theorem earlyExtraPC2891 : Artifact.submissionArtifact.instructionPC 3670 = 4836 := by
  calc
    Artifact.submissionArtifact.instructionPC 3670 = Artifact.submissionArtifact.instructionPC 3669 + (Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3669 (Instr.op .MLOAD) (by rfl)
    _ = 4836 := by rw [earlyExtraPC2890]; rfl

@[simp] theorem earlyExtraPC2892 : Artifact.submissionArtifact.instructionPC 3671 = 4837 := by
  calc
    Artifact.submissionArtifact.instructionPC 3671 = Artifact.submissionArtifact.instructionPC 3670 + (Instr.op .ISZERO).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3670 (Instr.op .ISZERO) (by rfl)
    _ = 4837 := by rw [earlyExtraPC2891]; rfl

@[simp] theorem earlyExtraPC2893 : Artifact.submissionArtifact.instructionPC 3672 = 4838 := by
  calc
    Artifact.submissionArtifact.instructionPC 3672 = Artifact.submissionArtifact.instructionPC 3671 + (Instr.op .AND).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3671 (Instr.op .AND) (by rfl)
    _ = 4838 := by rw [earlyExtraPC2892]; rfl

@[simp] theorem earlyExtraPC2894 : Artifact.submissionArtifact.instructionPC 3673 = 4841 := by
  calc
    Artifact.submissionArtifact.instructionPC 3673 = Artifact.submissionArtifact.instructionPC 3672 + (Instr.push 2 5236).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3672 (Instr.push 2 5236) (by rfl)
    _ = 4841 := by rw [earlyExtraPC2893]; rfl

@[simp] theorem earlyExtraPC2895 : Artifact.submissionArtifact.instructionPC 3674 = 4842 := by
  calc
    Artifact.submissionArtifact.instructionPC 3674 = Artifact.submissionArtifact.instructionPC 3673 + (Instr.op .JUMPI).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3673 (Instr.op .JUMPI) (by rfl)
    _ = 4842 := by rw [earlyExtraPC2894]; rfl

@[simp] theorem earlyExtraPC2896 : Artifact.submissionArtifact.instructionPC 3675 = 4845 := by
  calc
    Artifact.submissionArtifact.instructionPC 3675 = Artifact.submissionArtifact.instructionPC 3674 + (Instr.push 2 4996).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3674 (Instr.push 2 4996) (by rfl)
    _ = 4845 := by rw [earlyExtraPC2895]; rfl

@[simp] theorem earlyExtraPC2930 : Artifact.submissionArtifact.instructionPC 3676 = 4846 := by
  calc
    Artifact.submissionArtifact.instructionPC 3676 = Artifact.submissionArtifact.instructionPC 3675 + (Instr.op .JUMP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3675 (Instr.op .JUMP) (by rfl)
    _ = 4846 := by rw [earlyExtraPC2896]; rfl

@[simp] theorem earlyExtraPC2931 : Artifact.submissionArtifact.instructionPC 3677 = 4847 := by
  calc
    Artifact.submissionArtifact.instructionPC 3677 = Artifact.submissionArtifact.instructionPC 3676 + (Instr.op .JUMPDEST).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3676 (Instr.op .JUMPDEST) (by rfl)
    _ = 4847 := by rw [earlyExtraPC2930]; rfl

@[simp] theorem earlyExtraPC2932 : Artifact.submissionArtifact.instructionPC 3678 = 4850 := by
  calc
    Artifact.submissionArtifact.instructionPC 3678 = Artifact.submissionArtifact.instructionPC 3677 + (Instr.push 2 4256).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3677 (Instr.push 2 4256) (by rfl)
    _ = 4850 := by rw [earlyExtraPC2931]; rfl

@[simp] theorem earlyExtraPC2933 : Artifact.submissionArtifact.instructionPC 3679 = 4851 := by
  calc
    Artifact.submissionArtifact.instructionPC 3679 = Artifact.submissionArtifact.instructionPC 3678 + (Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3678 (Instr.op .MLOAD) (by rfl)
    _ = 4851 := by rw [earlyExtraPC2932]; rfl

@[simp] theorem earlyExtraPC2934 : Artifact.submissionArtifact.instructionPC 3680 = 4853 := by
  calc
    Artifact.submissionArtifact.instructionPC 3680 = Artifact.submissionArtifact.instructionPC 3679 + (Instr.push 1 96).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3679 (Instr.push 1 96) (by rfl)
    _ = 4853 := by rw [earlyExtraPC2933]; rfl

@[simp] theorem earlyExtraPC2935 : Artifact.submissionArtifact.instructionPC 3681 = 4854 := by
  calc
    Artifact.submissionArtifact.instructionPC 3681 = Artifact.submissionArtifact.instructionPC 3680 + (Instr.op .MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3680 (Instr.op .MLOAD) (by rfl)
    _ = 4854 := by rw [earlyExtraPC2934]; rfl

@[simp] theorem earlyExtraPC2936 : Artifact.submissionArtifact.instructionPC 3682 = 4855 := by
  calc
    Artifact.submissionArtifact.instructionPC 3682 = Artifact.submissionArtifact.instructionPC 3681 + (Instr.op (.Dup { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3681 (Instr.op (.Dup { idx := 1 })) (by rfl)
    _ = 4855 := by rw [earlyExtraPC2935]; rfl

@[simp] theorem earlyExtraPC2937 : Artifact.submissionArtifact.instructionPC 3683 = 4856 := by
  calc
    Artifact.submissionArtifact.instructionPC 3683 = Artifact.submissionArtifact.instructionPC 3682 + (Instr.op (.Dup { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3682 (Instr.op (.Dup { idx := 1 })) (by rfl)
    _ = 4856 := by rw [earlyExtraPC2936]; rfl

@[simp] theorem earlyExtraPC2938 : Artifact.submissionArtifact.instructionPC 3684 = 4857 := by
  calc
    Artifact.submissionArtifact.instructionPC 3684 = Artifact.submissionArtifact.instructionPC 3683 + (Instr.op .GT).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3683 (Instr.op .GT) (by rfl)
    _ = 4857 := by rw [earlyExtraPC2937]; rfl

@[simp] theorem earlyExtraPC2939 : Artifact.submissionArtifact.instructionPC 3685 = 4858 := by
  calc
    Artifact.submissionArtifact.instructionPC 3685 = Artifact.submissionArtifact.instructionPC 3684 + (Instr.op (.Swap { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3684 (Instr.op (.Swap { idx := 1 })) (by rfl)
    _ = 4858 := by rw [earlyExtraPC2938]; rfl

@[simp] theorem earlyExtraPC2940 : Artifact.submissionArtifact.instructionPC 3686 = 4859 := by
  calc
    Artifact.submissionArtifact.instructionPC 3686 = Artifact.submissionArtifact.instructionPC 3685 + (Instr.op .SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3685 (Instr.op .SUB) (by rfl)
    _ = 4859 := by rw [earlyExtraPC2939]; rfl

@[simp] theorem earlyExtraPC2941 : Artifact.submissionArtifact.instructionPC 3687 = 4862 := by
  calc
    Artifact.submissionArtifact.instructionPC 3687 = Artifact.submissionArtifact.instructionPC 3686 + (Instr.push 2 3168).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3686 (Instr.push 2 3168) (by rfl)
    _ = 4862 := by rw [earlyExtraPC2940]; rfl

@[simp] theorem earlyExtraPC2942 : Artifact.submissionArtifact.instructionPC 3688 = 4863 := by
  calc
    Artifact.submissionArtifact.instructionPC 3688 = Artifact.submissionArtifact.instructionPC 3687 + (Instr.op .MSTORE).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3687 (Instr.op .MSTORE) (by rfl)
    _ = 4863 := by rw [earlyExtraPC2941]; rfl

@[simp] theorem earlyExtraPC2943 : Artifact.submissionArtifact.instructionPC 3689 = 4866 := by
  calc
    Artifact.submissionArtifact.instructionPC 3689 = Artifact.submissionArtifact.instructionPC 3688 + (Instr.push 2 5153).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3688 (Instr.push 2 5153) (by rfl)
    _ = 4866 := by rw [earlyExtraPC2942]; rfl

end Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs
