import Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
/-!
# Program counters for the appended limb-loop blocks

Instruction indices 2670 .. 2861, one lemma each.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.LoopPCs

open EvmSemantics
open EvmSemantics.EVM

open YulEvmCompiler

private theorem instructionPC_succ
    (p : Challenge.EvmProof.ProgramArtifact) (index : Nat) (instr : Instr)
    (hget : p.instructions[index]? = some instr) :
    p.instructionPC (index + 1) = p.instructionPC index + instr.bytes.length := by
  simp only [Challenge.EvmProof.ProgramArtifact.instructionPC,
    List.take_add_one, hget, Option.toList_some, assembleBytes_append,
    assembleBytes_cons, assembleBytes_nil, List.append_nil, List.length_append]

@[simp] theorem pc2670 : Artifact.submissionArtifact.instructionPC 2429 = 3194 := by rfl
@[simp] theorem pc2671 : Artifact.submissionArtifact.instructionPC 2430 = 3196 := by
  calc
    Artifact.submissionArtifact.instructionPC 2430 =
        Artifact.submissionArtifact.instructionPC 2429 +
          (YulEvmCompiler.Instr.push 1 5).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2429 _ (by rfl)
    _ = 3196 := by rw [pc2670]; rfl
@[simp] theorem pc2672 : Artifact.submissionArtifact.instructionPC 2431 = 3197 := by
  calc
    Artifact.submissionArtifact.instructionPC 2431 =
        Artifact.submissionArtifact.instructionPC 2430 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.SHL).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2430 _ (by rfl)
    _ = 3197 := by rw [pc2671]; rfl
@[simp] theorem pc2673 : Artifact.submissionArtifact.instructionPC 2432 = 3198 := by
  calc
    Artifact.submissionArtifact.instructionPC 2432 =
        Artifact.submissionArtifact.instructionPC 2431 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2431 _ (by rfl)
    _ = 3198 := by rw [pc2672]; rfl
@[simp] theorem pc2674 : Artifact.submissionArtifact.instructionPC 2433 = 3200 := by
  calc
    Artifact.submissionArtifact.instructionPC 2433 =
        Artifact.submissionArtifact.instructionPC 2432 +
          (YulEvmCompiler.Instr.push 1 3).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2432 _ (by rfl)
    _ = 3200 := by rw [pc2673]; rfl
@[simp] theorem pc2675 : Artifact.submissionArtifact.instructionPC 2434 = 3201 := by
  calc
    Artifact.submissionArtifact.instructionPC 2434 =
        Artifact.submissionArtifact.instructionPC 2433 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.SHL).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2433 _ (by rfl)
    _ = 3201 := by rw [pc2674]; rfl
@[simp] theorem pc2676 : Artifact.submissionArtifact.instructionPC 2435 = 3203 := by
  calc
    Artifact.submissionArtifact.instructionPC 2435 =
        Artifact.submissionArtifact.instructionPC 2434 +
          (YulEvmCompiler.Instr.push 1 96).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2434 _ (by rfl)
    _ = 3203 := by rw [pc2675]; rfl
@[simp] theorem pc2677 : Artifact.submissionArtifact.instructionPC 2436 = 3204 := by
  calc
    Artifact.submissionArtifact.instructionPC 2436 =
        Artifact.submissionArtifact.instructionPC 2435 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.CALLDATALOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2435 _ (by rfl)
    _ = 3204 := by rw [pc2676]; rfl
@[simp] theorem pc2678 : Artifact.submissionArtifact.instructionPC 2437 = 3205 := by
  calc
    Artifact.submissionArtifact.instructionPC 2437 =
        Artifact.submissionArtifact.instructionPC 2436 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 0 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2436 _ (by rfl)
    _ = 3205 := by rw [pc2677]; rfl
@[simp] theorem pc2679 : Artifact.submissionArtifact.instructionPC 2438 = 3206 := by
  calc
    Artifact.submissionArtifact.instructionPC 2438 =
        Artifact.submissionArtifact.instructionPC 2437 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.SHR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2437 _ (by rfl)
    _ = 3206 := by rw [pc2678]; rfl
@[simp] theorem pc2680 : Artifact.submissionArtifact.instructionPC 2439 = 3207 := by
  calc
    Artifact.submissionArtifact.instructionPC 2439 =
        Artifact.submissionArtifact.instructionPC 2438 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 2 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2438 _ (by rfl)
    _ = 3207 := by rw [pc2679]; rfl
@[simp] theorem pc2681 : Artifact.submissionArtifact.instructionPC 2440 = 3210 := by
  calc
    Artifact.submissionArtifact.instructionPC 2440 =
        Artifact.submissionArtifact.instructionPC 2439 +
          (YulEvmCompiler.Instr.push 2 992).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2439 _ (by rfl)
    _ = 3210 := by rw [pc2680]; rfl
@[simp] theorem pc2682 : Artifact.submissionArtifact.instructionPC 2441 = 3211 := by
  calc
    Artifact.submissionArtifact.instructionPC 2441 =
        Artifact.submissionArtifact.instructionPC 2440 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.ADD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2440 _ (by rfl)
    _ = 3211 := by rw [pc2681]; rfl
@[simp] theorem pc2683 : Artifact.submissionArtifact.instructionPC 2442 = 3212 := by
  calc
    Artifact.submissionArtifact.instructionPC 2442 =
        Artifact.submissionArtifact.instructionPC 2441 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MSTORE).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2441 _ (by rfl)
    _ = 3212 := by rw [pc2682]; rfl
@[simp] theorem pc2684 : Artifact.submissionArtifact.instructionPC 2443 = 3214 := by
  calc
    Artifact.submissionArtifact.instructionPC 2443 =
        Artifact.submissionArtifact.instructionPC 2442 +
          (YulEvmCompiler.Instr.push 1 1).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2442 _ (by rfl)
    _ = 3214 := by rw [pc2683]; rfl
@[simp] theorem pc2685 : Artifact.submissionArtifact.instructionPC 2444 = 3217 := by
  calc
    Artifact.submissionArtifact.instructionPC 2444 =
        Artifact.submissionArtifact.instructionPC 2443 +
          (YulEvmCompiler.Instr.push 2 1611).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2443 _ (by rfl)
    _ = 3217 := by rw [pc2684]; rfl
@[simp] theorem pc2686 : Artifact.submissionArtifact.instructionPC 2445 = 3218 := by
  calc
    Artifact.submissionArtifact.instructionPC 2445 =
        Artifact.submissionArtifact.instructionPC 2444 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.JUMP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2444 _ (by rfl)
    _ = 3218 := by rw [pc2685]; rfl
@[simp] theorem pc2687 : Artifact.submissionArtifact.instructionPC 2446 = 3219 := by
  calc
    Artifact.submissionArtifact.instructionPC 2446 =
        Artifact.submissionArtifact.instructionPC 2445 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.JUMPDEST).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2445 _ (by rfl)
    _ = 3219 := by rw [pc2686]; rfl
@[simp] theorem pc2688 : Artifact.submissionArtifact.instructionPC 2447 = 3221 := by
  calc
    Artifact.submissionArtifact.instructionPC 2447 =
        Artifact.submissionArtifact.instructionPC 2446 +
          (YulEvmCompiler.Instr.push 1 1).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2446 _ (by rfl)
    _ = 3221 := by rw [pc2687]; rfl
@[simp] theorem pc2689 : Artifact.submissionArtifact.instructionPC 2448 = 3222 := by
  calc
    Artifact.submissionArtifact.instructionPC 2448 =
        Artifact.submissionArtifact.instructionPC 2447 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 6 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2447 _ (by rfl)
    _ = 3222 := by rw [pc2688]; rfl
@[simp] theorem pc2690 : Artifact.submissionArtifact.instructionPC 2449 = 3223 := by
  calc
    Artifact.submissionArtifact.instructionPC 2449 =
        Artifact.submissionArtifact.instructionPC 2448 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2448 _ (by rfl)
    _ = 3223 := by rw [pc2689]; rfl
@[simp] theorem pc2691 : Artifact.submissionArtifact.instructionPC 2450 = 3224 := by
  calc
    Artifact.submissionArtifact.instructionPC 2450 =
        Artifact.submissionArtifact.instructionPC 2449 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 7 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2449 _ (by rfl)
    _ = 3224 := by rw [pc2690]; rfl
@[simp] theorem pc2692 : Artifact.submissionArtifact.instructionPC 2451 = 3226 := by
  calc
    Artifact.submissionArtifact.instructionPC 2451 =
        Artifact.submissionArtifact.instructionPC 2450 +
          (YulEvmCompiler.Instr.push 1 1).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2450 _ (by rfl)
    _ = 3226 := by rw [pc2691]; rfl
@[simp] theorem pc2693 : Artifact.submissionArtifact.instructionPC 2452 = 3227 := by
  calc
    Artifact.submissionArtifact.instructionPC 2452 =
        Artifact.submissionArtifact.instructionPC 2451 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 4 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2451 _ (by rfl)
    _ = 3227 := by rw [pc2692]; rfl
@[simp] theorem pc2694 : Artifact.submissionArtifact.instructionPC 2453 = 3229 := by
  calc
    Artifact.submissionArtifact.instructionPC 2453 =
        Artifact.submissionArtifact.instructionPC 2452 +
          (YulEvmCompiler.Instr.push 1 7).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2452 _ (by rfl)
    _ = 3229 := by rw [pc2693]; rfl
@[simp] theorem pc2695 : Artifact.submissionArtifact.instructionPC 2454 = 3230 := by
  calc
    Artifact.submissionArtifact.instructionPC 2454 =
        Artifact.submissionArtifact.instructionPC 2453 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.SHR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2453 _ (by rfl)
    _ = 3230 := by rw [pc2694]; rfl
@[simp] theorem pc2696 : Artifact.submissionArtifact.instructionPC 2455 = 3231 := by
  calc
    Artifact.submissionArtifact.instructionPC 2455 =
        Artifact.submissionArtifact.instructionPC 2454 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.AND).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2454 _ (by rfl)
    _ = 3231 := by rw [pc2695]; rfl
@[simp] theorem pc2697 : Artifact.submissionArtifact.instructionPC 2456 = 3232 := by
  calc
    Artifact.submissionArtifact.instructionPC 2456 =
        Artifact.submissionArtifact.instructionPC 2455 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 2 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2455 _ (by rfl)
    _ = 3232 := by rw [pc2696]; rfl
@[simp] theorem pc2698 : Artifact.submissionArtifact.instructionPC 2457 = 3233 := by
  calc
    Artifact.submissionArtifact.instructionPC 2457 =
        Artifact.submissionArtifact.instructionPC 2456 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MUL).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2456 _ (by rfl)
    _ = 3233 := by rw [pc2697]; rfl
@[simp] theorem pc2699 : Artifact.submissionArtifact.instructionPC 2458 = 3235 := by
  calc
    Artifact.submissionArtifact.instructionPC 2458 =
        Artifact.submissionArtifact.instructionPC 2457 +
          (YulEvmCompiler.Instr.push 1 1).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2457 _ (by rfl)
    _ = 3235 := by rw [pc2698]; rfl
@[simp] theorem pc2700 : Artifact.submissionArtifact.instructionPC 2459 = 3236 := by
  calc
    Artifact.submissionArtifact.instructionPC 2459 =
        Artifact.submissionArtifact.instructionPC 2458 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.ADD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2458 _ (by rfl)
    _ = 3236 := by rw [pc2699]; rfl
@[simp] theorem pc2701 : Artifact.submissionArtifact.instructionPC 2460 = 3237 := by
  calc
    Artifact.submissionArtifact.instructionPC 2460 =
        Artifact.submissionArtifact.instructionPC 2459 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2459 _ (by rfl)
    _ = 3237 := by rw [pc2700]; rfl
@[simp] theorem pc2702 : Artifact.submissionArtifact.instructionPC 2461 = 3238 := by
  calc
    Artifact.submissionArtifact.instructionPC 2461 =
        Artifact.submissionArtifact.instructionPC 2460 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 8 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2460 _ (by rfl)
    _ = 3238 := by rw [pc2701]; rfl
@[simp] theorem pc2703 : Artifact.submissionArtifact.instructionPC 2462 = 3239 := by
  calc
    Artifact.submissionArtifact.instructionPC 2462 =
        Artifact.submissionArtifact.instructionPC 2461 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 0 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2461 _ (by rfl)
    _ = 3239 := by rw [pc2702]; rfl
@[simp] theorem pc2704 : Artifact.submissionArtifact.instructionPC 2463 = 3240 := by
  calc
    Artifact.submissionArtifact.instructionPC 2463 =
        Artifact.submissionArtifact.instructionPC 2462 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MULMOD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2462 _ (by rfl)
    _ = 3240 := by rw [pc2703]; rfl
@[simp] theorem pc2705 : Artifact.submissionArtifact.instructionPC 2464 = 3241 := by
  calc
    Artifact.submissionArtifact.instructionPC 2464 =
        Artifact.submissionArtifact.instructionPC 2463 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MULMOD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2463 _ (by rfl)
    _ = 3241 := by rw [pc2704]; rfl
@[simp] theorem pc2706 : Artifact.submissionArtifact.instructionPC 2465 = 3242 := by
  calc
    Artifact.submissionArtifact.instructionPC 2465 =
        Artifact.submissionArtifact.instructionPC 2464 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 5 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2464 _ (by rfl)
    _ = 3242 := by rw [pc2705]; rfl
@[simp] theorem pc2707 : Artifact.submissionArtifact.instructionPC 2466 = 3243 := by
  calc
    Artifact.submissionArtifact.instructionPC 2466 =
        Artifact.submissionArtifact.instructionPC 2465 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.POP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2465 _ (by rfl)
    _ = 3243 := by rw [pc2706]; rfl
@[simp] theorem pc2708 : Artifact.submissionArtifact.instructionPC 2467 = 3244 := by
  calc
    Artifact.submissionArtifact.instructionPC 2467 =
        Artifact.submissionArtifact.instructionPC 2466 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 7 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2466 _ (by rfl)
    _ = 3244 := by rw [pc2707]; rfl
@[simp] theorem pc2709 : Artifact.submissionArtifact.instructionPC 2468 = 3246 := by
  calc
    Artifact.submissionArtifact.instructionPC 2468 =
        Artifact.submissionArtifact.instructionPC 2467 +
          (YulEvmCompiler.Instr.push 1 1).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2467 _ (by rfl)
    _ = 3246 := by rw [pc2708]; rfl
@[simp] theorem pc2710 : Artifact.submissionArtifact.instructionPC 2469 = 3247 := by
  calc
    Artifact.submissionArtifact.instructionPC 2469 =
        Artifact.submissionArtifact.instructionPC 2468 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 4 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2468 _ (by rfl)
    _ = 3247 := by rw [pc2709]; rfl
@[simp] theorem pc2711 : Artifact.submissionArtifact.instructionPC 2470 = 3249 := by
  calc
    Artifact.submissionArtifact.instructionPC 2470 =
        Artifact.submissionArtifact.instructionPC 2469 +
          (YulEvmCompiler.Instr.push 1 6).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2469 _ (by rfl)
    _ = 3249 := by rw [pc2710]; rfl
@[simp] theorem pc2712 : Artifact.submissionArtifact.instructionPC 2471 = 3250 := by
  calc
    Artifact.submissionArtifact.instructionPC 2471 =
        Artifact.submissionArtifact.instructionPC 2470 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.SHR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2470 _ (by rfl)
    _ = 3250 := by rw [pc2711]; rfl
@[simp] theorem pc2713 : Artifact.submissionArtifact.instructionPC 2472 = 3251 := by
  calc
    Artifact.submissionArtifact.instructionPC 2472 =
        Artifact.submissionArtifact.instructionPC 2471 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.AND).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2471 _ (by rfl)
    _ = 3251 := by rw [pc2712]; rfl
@[simp] theorem pc2714 : Artifact.submissionArtifact.instructionPC 2473 = 3252 := by
  calc
    Artifact.submissionArtifact.instructionPC 2473 =
        Artifact.submissionArtifact.instructionPC 2472 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 2 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2472 _ (by rfl)
    _ = 3252 := by rw [pc2713]; rfl
@[simp] theorem pc2715 : Artifact.submissionArtifact.instructionPC 2474 = 3253 := by
  calc
    Artifact.submissionArtifact.instructionPC 2474 =
        Artifact.submissionArtifact.instructionPC 2473 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MUL).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2473 _ (by rfl)
    _ = 3253 := by rw [pc2714]; rfl
@[simp] theorem pc2716 : Artifact.submissionArtifact.instructionPC 2475 = 3255 := by
  calc
    Artifact.submissionArtifact.instructionPC 2475 =
        Artifact.submissionArtifact.instructionPC 2474 +
          (YulEvmCompiler.Instr.push 1 1).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2474 _ (by rfl)
    _ = 3255 := by rw [pc2715]; rfl
@[simp] theorem pc2717 : Artifact.submissionArtifact.instructionPC 2476 = 3256 := by
  calc
    Artifact.submissionArtifact.instructionPC 2476 =
        Artifact.submissionArtifact.instructionPC 2475 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.ADD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2475 _ (by rfl)
    _ = 3256 := by rw [pc2716]; rfl
@[simp] theorem pc2718 : Artifact.submissionArtifact.instructionPC 2477 = 3257 := by
  calc
    Artifact.submissionArtifact.instructionPC 2477 =
        Artifact.submissionArtifact.instructionPC 2476 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2476 _ (by rfl)
    _ = 3257 := by rw [pc2717]; rfl
@[simp] theorem pc2719 : Artifact.submissionArtifact.instructionPC 2478 = 3258 := by
  calc
    Artifact.submissionArtifact.instructionPC 2478 =
        Artifact.submissionArtifact.instructionPC 2477 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 8 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2477 _ (by rfl)
    _ = 3258 := by rw [pc2718]; rfl
@[simp] theorem pc2720 : Artifact.submissionArtifact.instructionPC 2479 = 3259 := by
  calc
    Artifact.submissionArtifact.instructionPC 2479 =
        Artifact.submissionArtifact.instructionPC 2478 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 0 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2478 _ (by rfl)
    _ = 3259 := by rw [pc2719]; rfl
@[simp] theorem pc2726 : Artifact.submissionArtifact.instructionPC 2480 = 3260 := by
  calc
    Artifact.submissionArtifact.instructionPC 2480 =
        Artifact.submissionArtifact.instructionPC 2479 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MULMOD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2479 _ (by rfl)
    _ = 3260 := by rw [pc2720]; rfl
@[simp] theorem pc2727 : Artifact.submissionArtifact.instructionPC 2481 = 3261 := by
  calc
    Artifact.submissionArtifact.instructionPC 2481 =
        Artifact.submissionArtifact.instructionPC 2480 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MULMOD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2480 _ (by rfl)
    _ = 3261 := by rw [pc2726]; rfl
@[simp] theorem pc2728 : Artifact.submissionArtifact.instructionPC 2482 = 3262 := by
  calc
    Artifact.submissionArtifact.instructionPC 2482 =
        Artifact.submissionArtifact.instructionPC 2481 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 5 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2481 _ (by rfl)
    _ = 3262 := by rw [pc2727]; rfl
@[simp] theorem pc2729 : Artifact.submissionArtifact.instructionPC 2483 = 3263 := by
  calc
    Artifact.submissionArtifact.instructionPC 2483 =
        Artifact.submissionArtifact.instructionPC 2482 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.POP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2482 _ (by rfl)
    _ = 3263 := by rw [pc2728]; rfl
@[simp] theorem pc2730 : Artifact.submissionArtifact.instructionPC 2484 = 3264 := by
  calc
    Artifact.submissionArtifact.instructionPC 2484 =
        Artifact.submissionArtifact.instructionPC 2483 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 7 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2483 _ (by rfl)
    _ = 3264 := by rw [pc2729]; rfl
@[simp] theorem pc2731 : Artifact.submissionArtifact.instructionPC 2485 = 3266 := by
  calc
    Artifact.submissionArtifact.instructionPC 2485 =
        Artifact.submissionArtifact.instructionPC 2484 +
          (YulEvmCompiler.Instr.push 1 1).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2484 _ (by rfl)
    _ = 3266 := by rw [pc2730]; rfl
@[simp] theorem pc2732 : Artifact.submissionArtifact.instructionPC 2486 = 3267 := by
  calc
    Artifact.submissionArtifact.instructionPC 2486 =
        Artifact.submissionArtifact.instructionPC 2485 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 4 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2485 _ (by rfl)
    _ = 3267 := by rw [pc2731]; rfl
@[simp] theorem pc2733 : Artifact.submissionArtifact.instructionPC 2487 = 3269 := by
  calc
    Artifact.submissionArtifact.instructionPC 2487 =
        Artifact.submissionArtifact.instructionPC 2486 +
          (YulEvmCompiler.Instr.push 1 5).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2486 _ (by rfl)
    _ = 3269 := by rw [pc2732]; rfl
@[simp] theorem pc2734 : Artifact.submissionArtifact.instructionPC 2488 = 3270 := by
  calc
    Artifact.submissionArtifact.instructionPC 2488 =
        Artifact.submissionArtifact.instructionPC 2487 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.SHR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2487 _ (by rfl)
    _ = 3270 := by rw [pc2733]; rfl
@[simp] theorem pc2735 : Artifact.submissionArtifact.instructionPC 2489 = 3271 := by
  calc
    Artifact.submissionArtifact.instructionPC 2489 =
        Artifact.submissionArtifact.instructionPC 2488 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.AND).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2488 _ (by rfl)
    _ = 3271 := by rw [pc2734]; rfl
@[simp] theorem pc2736 : Artifact.submissionArtifact.instructionPC 2490 = 3272 := by
  calc
    Artifact.submissionArtifact.instructionPC 2490 =
        Artifact.submissionArtifact.instructionPC 2489 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 2 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2489 _ (by rfl)
    _ = 3272 := by rw [pc2735]; rfl
@[simp] theorem pc2737 : Artifact.submissionArtifact.instructionPC 2491 = 3273 := by
  calc
    Artifact.submissionArtifact.instructionPC 2491 =
        Artifact.submissionArtifact.instructionPC 2490 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MUL).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2490 _ (by rfl)
    _ = 3273 := by rw [pc2736]; rfl
@[simp] theorem pc2738 : Artifact.submissionArtifact.instructionPC 2492 = 3275 := by
  calc
    Artifact.submissionArtifact.instructionPC 2492 =
        Artifact.submissionArtifact.instructionPC 2491 +
          (YulEvmCompiler.Instr.push 1 1).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2491 _ (by rfl)
    _ = 3275 := by rw [pc2737]; rfl
@[simp] theorem pc2739 : Artifact.submissionArtifact.instructionPC 2493 = 3276 := by
  calc
    Artifact.submissionArtifact.instructionPC 2493 =
        Artifact.submissionArtifact.instructionPC 2492 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.ADD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2492 _ (by rfl)
    _ = 3276 := by rw [pc2738]; rfl
@[simp] theorem pc2740 : Artifact.submissionArtifact.instructionPC 2494 = 3277 := by
  calc
    Artifact.submissionArtifact.instructionPC 2494 =
        Artifact.submissionArtifact.instructionPC 2493 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2493 _ (by rfl)
    _ = 3277 := by rw [pc2739]; rfl
@[simp] theorem pc2741 : Artifact.submissionArtifact.instructionPC 2495 = 3278 := by
  calc
    Artifact.submissionArtifact.instructionPC 2495 =
        Artifact.submissionArtifact.instructionPC 2494 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 8 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2494 _ (by rfl)
    _ = 3278 := by rw [pc2740]; rfl
@[simp] theorem pc2742 : Artifact.submissionArtifact.instructionPC 2496 = 3279 := by
  calc
    Artifact.submissionArtifact.instructionPC 2496 =
        Artifact.submissionArtifact.instructionPC 2495 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 0 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2495 _ (by rfl)
    _ = 3279 := by rw [pc2741]; rfl
@[simp] theorem pc2743 : Artifact.submissionArtifact.instructionPC 2497 = 3280 := by
  calc
    Artifact.submissionArtifact.instructionPC 2497 =
        Artifact.submissionArtifact.instructionPC 2496 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MULMOD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2496 _ (by rfl)
    _ = 3280 := by rw [pc2742]; rfl
@[simp] theorem pc2744 : Artifact.submissionArtifact.instructionPC 2498 = 3281 := by
  calc
    Artifact.submissionArtifact.instructionPC 2498 =
        Artifact.submissionArtifact.instructionPC 2497 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MULMOD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2497 _ (by rfl)
    _ = 3281 := by rw [pc2743]; rfl
@[simp] theorem pc2745 : Artifact.submissionArtifact.instructionPC 2499 = 3282 := by
  calc
    Artifact.submissionArtifact.instructionPC 2499 =
        Artifact.submissionArtifact.instructionPC 2498 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 5 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2498 _ (by rfl)
    _ = 3282 := by rw [pc2744]; rfl
@[simp] theorem pc2746 : Artifact.submissionArtifact.instructionPC 2500 = 3283 := by
  calc
    Artifact.submissionArtifact.instructionPC 2500 =
        Artifact.submissionArtifact.instructionPC 2499 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.POP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2499 _ (by rfl)
    _ = 3283 := by rw [pc2745]; rfl
@[simp] theorem pc2747 : Artifact.submissionArtifact.instructionPC 2501 = 3284 := by
  calc
    Artifact.submissionArtifact.instructionPC 2501 =
        Artifact.submissionArtifact.instructionPC 2500 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 7 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2500 _ (by rfl)
    _ = 3284 := by rw [pc2746]; rfl
@[simp] theorem pc2748 : Artifact.submissionArtifact.instructionPC 2502 = 3286 := by
  calc
    Artifact.submissionArtifact.instructionPC 2502 =
        Artifact.submissionArtifact.instructionPC 2501 +
          (YulEvmCompiler.Instr.push 1 1).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2501 _ (by rfl)
    _ = 3286 := by rw [pc2747]; rfl
@[simp] theorem pc2749 : Artifact.submissionArtifact.instructionPC 2503 = 3287 := by
  calc
    Artifact.submissionArtifact.instructionPC 2503 =
        Artifact.submissionArtifact.instructionPC 2502 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 4 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2502 _ (by rfl)
    _ = 3287 := by rw [pc2748]; rfl
@[simp] theorem pc2750 : Artifact.submissionArtifact.instructionPC 2504 = 3289 := by
  calc
    Artifact.submissionArtifact.instructionPC 2504 =
        Artifact.submissionArtifact.instructionPC 2503 +
          (YulEvmCompiler.Instr.push 1 4).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2503 _ (by rfl)
    _ = 3289 := by rw [pc2749]; rfl
@[simp] theorem pc2751 : Artifact.submissionArtifact.instructionPC 2505 = 3290 := by
  calc
    Artifact.submissionArtifact.instructionPC 2505 =
        Artifact.submissionArtifact.instructionPC 2504 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.SHR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2504 _ (by rfl)
    _ = 3290 := by rw [pc2750]; rfl
@[simp] theorem pc2752 : Artifact.submissionArtifact.instructionPC 2506 = 3291 := by
  calc
    Artifact.submissionArtifact.instructionPC 2506 =
        Artifact.submissionArtifact.instructionPC 2505 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.AND).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2505 _ (by rfl)
    _ = 3291 := by rw [pc2751]; rfl
@[simp] theorem pc2753 : Artifact.submissionArtifact.instructionPC 2507 = 3292 := by
  calc
    Artifact.submissionArtifact.instructionPC 2507 =
        Artifact.submissionArtifact.instructionPC 2506 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 2 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2506 _ (by rfl)
    _ = 3292 := by rw [pc2752]; rfl
@[simp] theorem pc2754 : Artifact.submissionArtifact.instructionPC 2508 = 3293 := by
  calc
    Artifact.submissionArtifact.instructionPC 2508 =
        Artifact.submissionArtifact.instructionPC 2507 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MUL).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2507 _ (by rfl)
    _ = 3293 := by rw [pc2753]; rfl
@[simp] theorem pc2755 : Artifact.submissionArtifact.instructionPC 2509 = 3295 := by
  calc
    Artifact.submissionArtifact.instructionPC 2509 =
        Artifact.submissionArtifact.instructionPC 2508 +
          (YulEvmCompiler.Instr.push 1 1).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2508 _ (by rfl)
    _ = 3295 := by rw [pc2754]; rfl
@[simp] theorem pc2756 : Artifact.submissionArtifact.instructionPC 2510 = 3296 := by
  calc
    Artifact.submissionArtifact.instructionPC 2510 =
        Artifact.submissionArtifact.instructionPC 2509 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.ADD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2509 _ (by rfl)
    _ = 3296 := by rw [pc2755]; rfl
@[simp] theorem pc2757 : Artifact.submissionArtifact.instructionPC 2511 = 3297 := by
  calc
    Artifact.submissionArtifact.instructionPC 2511 =
        Artifact.submissionArtifact.instructionPC 2510 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2510 _ (by rfl)
    _ = 3297 := by rw [pc2756]; rfl
@[simp] theorem pc2758 : Artifact.submissionArtifact.instructionPC 2512 = 3298 := by
  calc
    Artifact.submissionArtifact.instructionPC 2512 =
        Artifact.submissionArtifact.instructionPC 2511 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 8 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2511 _ (by rfl)
    _ = 3298 := by rw [pc2757]; rfl
@[simp] theorem pc2759 : Artifact.submissionArtifact.instructionPC 2513 = 3299 := by
  calc
    Artifact.submissionArtifact.instructionPC 2513 =
        Artifact.submissionArtifact.instructionPC 2512 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 0 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2512 _ (by rfl)
    _ = 3299 := by rw [pc2758]; rfl
@[simp] theorem pc2760 : Artifact.submissionArtifact.instructionPC 2514 = 3300 := by
  calc
    Artifact.submissionArtifact.instructionPC 2514 =
        Artifact.submissionArtifact.instructionPC 2513 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MULMOD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2513 _ (by rfl)
    _ = 3300 := by rw [pc2759]; rfl
@[simp] theorem pc2761 : Artifact.submissionArtifact.instructionPC 2515 = 3301 := by
  calc
    Artifact.submissionArtifact.instructionPC 2515 =
        Artifact.submissionArtifact.instructionPC 2514 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MULMOD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2514 _ (by rfl)
    _ = 3301 := by rw [pc2760]; rfl
@[simp] theorem pc2762 : Artifact.submissionArtifact.instructionPC 2516 = 3302 := by
  calc
    Artifact.submissionArtifact.instructionPC 2516 =
        Artifact.submissionArtifact.instructionPC 2515 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 5 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2515 _ (by rfl)
    _ = 3302 := by rw [pc2761]; rfl
@[simp] theorem pc2763 : Artifact.submissionArtifact.instructionPC 2517 = 3303 := by
  calc
    Artifact.submissionArtifact.instructionPC 2517 =
        Artifact.submissionArtifact.instructionPC 2516 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.POP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2516 _ (by rfl)
    _ = 3303 := by rw [pc2762]; rfl
@[simp] theorem pc2769 : Artifact.submissionArtifact.instructionPC 2518 = 3304 := by
  calc
    Artifact.submissionArtifact.instructionPC 2518 =
        Artifact.submissionArtifact.instructionPC 2517 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 7 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2517 _ (by rfl)
    _ = 3304 := by rw [pc2763]; rfl
@[simp] theorem pc2770 : Artifact.submissionArtifact.instructionPC 2519 = 3306 := by
  calc
    Artifact.submissionArtifact.instructionPC 2519 =
        Artifact.submissionArtifact.instructionPC 2518 +
          (YulEvmCompiler.Instr.push 1 1).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2518 _ (by rfl)
    _ = 3306 := by rw [pc2769]; rfl
@[simp] theorem pc2771 : Artifact.submissionArtifact.instructionPC 2520 = 3307 := by
  calc
    Artifact.submissionArtifact.instructionPC 2520 =
        Artifact.submissionArtifact.instructionPC 2519 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 4 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2519 _ (by rfl)
    _ = 3307 := by rw [pc2770]; rfl
@[simp] theorem pc2772 : Artifact.submissionArtifact.instructionPC 2521 = 3309 := by
  calc
    Artifact.submissionArtifact.instructionPC 2521 =
        Artifact.submissionArtifact.instructionPC 2520 +
          (YulEvmCompiler.Instr.push 1 3).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2520 _ (by rfl)
    _ = 3309 := by rw [pc2771]; rfl
@[simp] theorem pc2773 : Artifact.submissionArtifact.instructionPC 2522 = 3310 := by
  calc
    Artifact.submissionArtifact.instructionPC 2522 =
        Artifact.submissionArtifact.instructionPC 2521 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.SHR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2521 _ (by rfl)
    _ = 3310 := by rw [pc2772]; rfl
@[simp] theorem pc2774 : Artifact.submissionArtifact.instructionPC 2523 = 3311 := by
  calc
    Artifact.submissionArtifact.instructionPC 2523 =
        Artifact.submissionArtifact.instructionPC 2522 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.AND).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2522 _ (by rfl)
    _ = 3311 := by rw [pc2773]; rfl
@[simp] theorem pc2775 : Artifact.submissionArtifact.instructionPC 2524 = 3312 := by
  calc
    Artifact.submissionArtifact.instructionPC 2524 =
        Artifact.submissionArtifact.instructionPC 2523 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 2 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2523 _ (by rfl)
    _ = 3312 := by rw [pc2774]; rfl
@[simp] theorem pc2776 : Artifact.submissionArtifact.instructionPC 2525 = 3313 := by
  calc
    Artifact.submissionArtifact.instructionPC 2525 =
        Artifact.submissionArtifact.instructionPC 2524 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MUL).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2524 _ (by rfl)
    _ = 3313 := by rw [pc2775]; rfl
@[simp] theorem pc2777 : Artifact.submissionArtifact.instructionPC 2526 = 3315 := by
  calc
    Artifact.submissionArtifact.instructionPC 2526 =
        Artifact.submissionArtifact.instructionPC 2525 +
          (YulEvmCompiler.Instr.push 1 1).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2525 _ (by rfl)
    _ = 3315 := by rw [pc2776]; rfl
@[simp] theorem pc2778 : Artifact.submissionArtifact.instructionPC 2527 = 3316 := by
  calc
    Artifact.submissionArtifact.instructionPC 2527 =
        Artifact.submissionArtifact.instructionPC 2526 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.ADD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2526 _ (by rfl)
    _ = 3316 := by rw [pc2777]; rfl
@[simp] theorem pc2779 : Artifact.submissionArtifact.instructionPC 2528 = 3317 := by
  calc
    Artifact.submissionArtifact.instructionPC 2528 =
        Artifact.submissionArtifact.instructionPC 2527 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2527 _ (by rfl)
    _ = 3317 := by rw [pc2778]; rfl
@[simp] theorem pc2780 : Artifact.submissionArtifact.instructionPC 2529 = 3318 := by
  calc
    Artifact.submissionArtifact.instructionPC 2529 =
        Artifact.submissionArtifact.instructionPC 2528 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 8 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2528 _ (by rfl)
    _ = 3318 := by rw [pc2779]; rfl
@[simp] theorem pc2781 : Artifact.submissionArtifact.instructionPC 2530 = 3319 := by
  calc
    Artifact.submissionArtifact.instructionPC 2530 =
        Artifact.submissionArtifact.instructionPC 2529 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 0 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2529 _ (by rfl)
    _ = 3319 := by rw [pc2780]; rfl
@[simp] theorem pc2782 : Artifact.submissionArtifact.instructionPC 2531 = 3320 := by
  calc
    Artifact.submissionArtifact.instructionPC 2531 =
        Artifact.submissionArtifact.instructionPC 2530 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MULMOD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2530 _ (by rfl)
    _ = 3320 := by rw [pc2781]; rfl
@[simp] theorem pc2783 : Artifact.submissionArtifact.instructionPC 2532 = 3321 := by
  calc
    Artifact.submissionArtifact.instructionPC 2532 =
        Artifact.submissionArtifact.instructionPC 2531 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MULMOD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2531 _ (by rfl)
    _ = 3321 := by rw [pc2782]; rfl
@[simp] theorem pc2784 : Artifact.submissionArtifact.instructionPC 2533 = 3322 := by
  calc
    Artifact.submissionArtifact.instructionPC 2533 =
        Artifact.submissionArtifact.instructionPC 2532 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 5 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2532 _ (by rfl)
    _ = 3322 := by rw [pc2783]; rfl
@[simp] theorem pc2785 : Artifact.submissionArtifact.instructionPC 2534 = 3323 := by
  calc
    Artifact.submissionArtifact.instructionPC 2534 =
        Artifact.submissionArtifact.instructionPC 2533 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.POP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2533 _ (by rfl)
    _ = 3323 := by rw [pc2784]; rfl
@[simp] theorem pc2786 : Artifact.submissionArtifact.instructionPC 2535 = 3324 := by
  calc
    Artifact.submissionArtifact.instructionPC 2535 =
        Artifact.submissionArtifact.instructionPC 2534 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 7 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2534 _ (by rfl)
    _ = 3324 := by rw [pc2785]; rfl
@[simp] theorem pc2787 : Artifact.submissionArtifact.instructionPC 2536 = 3326 := by
  calc
    Artifact.submissionArtifact.instructionPC 2536 =
        Artifact.submissionArtifact.instructionPC 2535 +
          (YulEvmCompiler.Instr.push 1 1).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2535 _ (by rfl)
    _ = 3326 := by rw [pc2786]; rfl
@[simp] theorem pc2788 : Artifact.submissionArtifact.instructionPC 2537 = 3327 := by
  calc
    Artifact.submissionArtifact.instructionPC 2537 =
        Artifact.submissionArtifact.instructionPC 2536 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 4 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2536 _ (by rfl)
    _ = 3327 := by rw [pc2787]; rfl
@[simp] theorem pc2789 : Artifact.submissionArtifact.instructionPC 2538 = 3329 := by
  calc
    Artifact.submissionArtifact.instructionPC 2538 =
        Artifact.submissionArtifact.instructionPC 2537 +
          (YulEvmCompiler.Instr.push 1 2).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2537 _ (by rfl)
    _ = 3329 := by rw [pc2788]; rfl
@[simp] theorem pc2790 : Artifact.submissionArtifact.instructionPC 2539 = 3330 := by
  calc
    Artifact.submissionArtifact.instructionPC 2539 =
        Artifact.submissionArtifact.instructionPC 2538 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.SHR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2538 _ (by rfl)
    _ = 3330 := by rw [pc2789]; rfl
@[simp] theorem pc2791 : Artifact.submissionArtifact.instructionPC 2540 = 3331 := by
  calc
    Artifact.submissionArtifact.instructionPC 2540 =
        Artifact.submissionArtifact.instructionPC 2539 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.AND).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2539 _ (by rfl)
    _ = 3331 := by rw [pc2790]; rfl
@[simp] theorem pc2792 : Artifact.submissionArtifact.instructionPC 2541 = 3332 := by
  calc
    Artifact.submissionArtifact.instructionPC 2541 =
        Artifact.submissionArtifact.instructionPC 2540 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 2 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2540 _ (by rfl)
    _ = 3332 := by rw [pc2791]; rfl
@[simp] theorem pc2793 : Artifact.submissionArtifact.instructionPC 2542 = 3333 := by
  calc
    Artifact.submissionArtifact.instructionPC 2542 =
        Artifact.submissionArtifact.instructionPC 2541 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MUL).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2541 _ (by rfl)
    _ = 3333 := by rw [pc2792]; rfl
@[simp] theorem pc2794 : Artifact.submissionArtifact.instructionPC 2543 = 3335 := by
  calc
    Artifact.submissionArtifact.instructionPC 2543 =
        Artifact.submissionArtifact.instructionPC 2542 +
          (YulEvmCompiler.Instr.push 1 1).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2542 _ (by rfl)
    _ = 3335 := by rw [pc2793]; rfl
@[simp] theorem pc2795 : Artifact.submissionArtifact.instructionPC 2544 = 3336 := by
  calc
    Artifact.submissionArtifact.instructionPC 2544 =
        Artifact.submissionArtifact.instructionPC 2543 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.ADD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2543 _ (by rfl)
    _ = 3336 := by rw [pc2794]; rfl
@[simp] theorem pc2796 : Artifact.submissionArtifact.instructionPC 2545 = 3337 := by
  calc
    Artifact.submissionArtifact.instructionPC 2545 =
        Artifact.submissionArtifact.instructionPC 2544 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2544 _ (by rfl)
    _ = 3337 := by rw [pc2795]; rfl
@[simp] theorem pc2797 : Artifact.submissionArtifact.instructionPC 2546 = 3338 := by
  calc
    Artifact.submissionArtifact.instructionPC 2546 =
        Artifact.submissionArtifact.instructionPC 2545 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 8 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2545 _ (by rfl)
    _ = 3338 := by rw [pc2796]; rfl
@[simp] theorem pc2798 : Artifact.submissionArtifact.instructionPC 2547 = 3339 := by
  calc
    Artifact.submissionArtifact.instructionPC 2547 =
        Artifact.submissionArtifact.instructionPC 2546 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 0 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2546 _ (by rfl)
    _ = 3339 := by rw [pc2797]; rfl
@[simp] theorem pc2799 : Artifact.submissionArtifact.instructionPC 2548 = 3340 := by
  calc
    Artifact.submissionArtifact.instructionPC 2548 =
        Artifact.submissionArtifact.instructionPC 2547 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MULMOD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2547 _ (by rfl)
    _ = 3340 := by rw [pc2798]; rfl
@[simp] theorem pc2800 : Artifact.submissionArtifact.instructionPC 2549 = 3341 := by
  calc
    Artifact.submissionArtifact.instructionPC 2549 =
        Artifact.submissionArtifact.instructionPC 2548 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MULMOD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2548 _ (by rfl)
    _ = 3341 := by rw [pc2799]; rfl
@[simp] theorem pc2801 : Artifact.submissionArtifact.instructionPC 2550 = 3342 := by
  calc
    Artifact.submissionArtifact.instructionPC 2550 =
        Artifact.submissionArtifact.instructionPC 2549 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 5 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2549 _ (by rfl)
    _ = 3342 := by rw [pc2800]; rfl
@[simp] theorem pc2802 : Artifact.submissionArtifact.instructionPC 2551 = 3343 := by
  calc
    Artifact.submissionArtifact.instructionPC 2551 =
        Artifact.submissionArtifact.instructionPC 2550 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.POP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2550 _ (by rfl)
    _ = 3343 := by rw [pc2801]; rfl
@[simp] theorem pc2803 : Artifact.submissionArtifact.instructionPC 2552 = 3344 := by
  calc
    Artifact.submissionArtifact.instructionPC 2552 =
        Artifact.submissionArtifact.instructionPC 2551 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 7 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2551 _ (by rfl)
    _ = 3344 := by rw [pc2802]; rfl
@[simp] theorem pc2804 : Artifact.submissionArtifact.instructionPC 2553 = 3346 := by
  calc
    Artifact.submissionArtifact.instructionPC 2553 =
        Artifact.submissionArtifact.instructionPC 2552 +
          (YulEvmCompiler.Instr.push 1 1).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2552 _ (by rfl)
    _ = 3346 := by rw [pc2803]; rfl
@[simp] theorem pc2805 : Artifact.submissionArtifact.instructionPC 2554 = 3347 := by
  calc
    Artifact.submissionArtifact.instructionPC 2554 =
        Artifact.submissionArtifact.instructionPC 2553 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 4 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2553 _ (by rfl)
    _ = 3347 := by rw [pc2804]; rfl
@[simp] theorem pc2806 : Artifact.submissionArtifact.instructionPC 2555 = 3349 := by
  calc
    Artifact.submissionArtifact.instructionPC 2555 =
        Artifact.submissionArtifact.instructionPC 2554 +
          (YulEvmCompiler.Instr.push 1 1).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2554 _ (by rfl)
    _ = 3349 := by rw [pc2805]; rfl
@[simp] theorem pc2812 : Artifact.submissionArtifact.instructionPC 2556 = 3350 := by
  calc
    Artifact.submissionArtifact.instructionPC 2556 =
        Artifact.submissionArtifact.instructionPC 2555 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.SHR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2555 _ (by rfl)
    _ = 3350 := by rw [pc2806]; rfl
@[simp] theorem pc2813 : Artifact.submissionArtifact.instructionPC 2557 = 3351 := by
  calc
    Artifact.submissionArtifact.instructionPC 2557 =
        Artifact.submissionArtifact.instructionPC 2556 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.AND).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2556 _ (by rfl)
    _ = 3351 := by rw [pc2812]; rfl
@[simp] theorem pc2814 : Artifact.submissionArtifact.instructionPC 2558 = 3352 := by
  calc
    Artifact.submissionArtifact.instructionPC 2558 =
        Artifact.submissionArtifact.instructionPC 2557 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 2 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2557 _ (by rfl)
    _ = 3352 := by rw [pc2813]; rfl
@[simp] theorem pc2815 : Artifact.submissionArtifact.instructionPC 2559 = 3353 := by
  calc
    Artifact.submissionArtifact.instructionPC 2559 =
        Artifact.submissionArtifact.instructionPC 2558 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MUL).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2558 _ (by rfl)
    _ = 3353 := by rw [pc2814]; rfl
@[simp] theorem pc2816 : Artifact.submissionArtifact.instructionPC 2560 = 3355 := by
  calc
    Artifact.submissionArtifact.instructionPC 2560 =
        Artifact.submissionArtifact.instructionPC 2559 +
          (YulEvmCompiler.Instr.push 1 1).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2559 _ (by rfl)
    _ = 3355 := by rw [pc2815]; rfl
@[simp] theorem pc2817 : Artifact.submissionArtifact.instructionPC 2561 = 3356 := by
  calc
    Artifact.submissionArtifact.instructionPC 2561 =
        Artifact.submissionArtifact.instructionPC 2560 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.ADD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2560 _ (by rfl)
    _ = 3356 := by rw [pc2816]; rfl
@[simp] theorem pc2818 : Artifact.submissionArtifact.instructionPC 2562 = 3357 := by
  calc
    Artifact.submissionArtifact.instructionPC 2562 =
        Artifact.submissionArtifact.instructionPC 2561 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2561 _ (by rfl)
    _ = 3357 := by rw [pc2817]; rfl
@[simp] theorem pc2819 : Artifact.submissionArtifact.instructionPC 2563 = 3358 := by
  calc
    Artifact.submissionArtifact.instructionPC 2563 =
        Artifact.submissionArtifact.instructionPC 2562 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 8 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2562 _ (by rfl)
    _ = 3358 := by rw [pc2818]; rfl
@[simp] theorem pc2820 : Artifact.submissionArtifact.instructionPC 2564 = 3359 := by
  calc
    Artifact.submissionArtifact.instructionPC 2564 =
        Artifact.submissionArtifact.instructionPC 2563 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 0 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2563 _ (by rfl)
    _ = 3359 := by rw [pc2819]; rfl
@[simp] theorem pc2821 : Artifact.submissionArtifact.instructionPC 2565 = 3360 := by
  calc
    Artifact.submissionArtifact.instructionPC 2565 =
        Artifact.submissionArtifact.instructionPC 2564 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MULMOD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2564 _ (by rfl)
    _ = 3360 := by rw [pc2820]; rfl
@[simp] theorem pc2822 : Artifact.submissionArtifact.instructionPC 2566 = 3361 := by
  calc
    Artifact.submissionArtifact.instructionPC 2566 =
        Artifact.submissionArtifact.instructionPC 2565 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MULMOD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2565 _ (by rfl)
    _ = 3361 := by rw [pc2821]; rfl
@[simp] theorem pc2823 : Artifact.submissionArtifact.instructionPC 2567 = 3362 := by
  calc
    Artifact.submissionArtifact.instructionPC 2567 =
        Artifact.submissionArtifact.instructionPC 2566 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 5 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2566 _ (by rfl)
    _ = 3362 := by rw [pc2822]; rfl
@[simp] theorem pc2824 : Artifact.submissionArtifact.instructionPC 2568 = 3363 := by
  calc
    Artifact.submissionArtifact.instructionPC 2568 =
        Artifact.submissionArtifact.instructionPC 2567 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.POP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2567 _ (by rfl)
    _ = 3363 := by rw [pc2823]; rfl
@[simp] theorem pc2825 : Artifact.submissionArtifact.instructionPC 2569 = 3364 := by
  calc
    Artifact.submissionArtifact.instructionPC 2569 =
        Artifact.submissionArtifact.instructionPC 2568 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 7 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2568 _ (by rfl)
    _ = 3364 := by rw [pc2824]; rfl
@[simp] theorem pc2826 : Artifact.submissionArtifact.instructionPC 2570 = 3366 := by
  calc
    Artifact.submissionArtifact.instructionPC 2570 =
        Artifact.submissionArtifact.instructionPC 2569 +
          (YulEvmCompiler.Instr.push 1 1).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2569 _ (by rfl)
    _ = 3366 := by rw [pc2825]; rfl
@[simp] theorem pc2829 : Artifact.submissionArtifact.instructionPC 2571 = 3367 := by
  calc
    Artifact.submissionArtifact.instructionPC 2571 =
        Artifact.submissionArtifact.instructionPC 2570 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 4 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2570 _ (by rfl)
    _ = 3367 := by rw [pc2826]; rfl
@[simp] theorem pc2830 : Artifact.submissionArtifact.instructionPC 2572 = 3368 := by
  calc
    Artifact.submissionArtifact.instructionPC 2572 =
        Artifact.submissionArtifact.instructionPC 2571 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.AND).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2571 _ (by rfl)
    _ = 3368 := by rw [pc2829]; rfl
@[simp] theorem pc2831 : Artifact.submissionArtifact.instructionPC 2573 = 3369 := by
  calc
    Artifact.submissionArtifact.instructionPC 2573 =
        Artifact.submissionArtifact.instructionPC 2572 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 2 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2572 _ (by rfl)
    _ = 3369 := by rw [pc2830]; rfl
@[simp] theorem pc2832 : Artifact.submissionArtifact.instructionPC 2574 = 3370 := by
  calc
    Artifact.submissionArtifact.instructionPC 2574 =
        Artifact.submissionArtifact.instructionPC 2573 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MUL).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2573 _ (by rfl)
    _ = 3370 := by rw [pc2831]; rfl
@[simp] theorem pc2833 : Artifact.submissionArtifact.instructionPC 2575 = 3372 := by
  calc
    Artifact.submissionArtifact.instructionPC 2575 =
        Artifact.submissionArtifact.instructionPC 2574 +
          (YulEvmCompiler.Instr.push 1 1).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2574 _ (by rfl)
    _ = 3372 := by rw [pc2832]; rfl
@[simp] theorem pc2834 : Artifact.submissionArtifact.instructionPC 2576 = 3373 := by
  calc
    Artifact.submissionArtifact.instructionPC 2576 =
        Artifact.submissionArtifact.instructionPC 2575 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.ADD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2575 _ (by rfl)
    _ = 3373 := by rw [pc2833]; rfl
@[simp] theorem pc2835 : Artifact.submissionArtifact.instructionPC 2577 = 3374 := by
  calc
    Artifact.submissionArtifact.instructionPC 2577 =
        Artifact.submissionArtifact.instructionPC 2576 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2576 _ (by rfl)
    _ = 3374 := by rw [pc2834]; rfl
@[simp] theorem pc2836 : Artifact.submissionArtifact.instructionPC 2578 = 3375 := by
  calc
    Artifact.submissionArtifact.instructionPC 2578 =
        Artifact.submissionArtifact.instructionPC 2577 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 8 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2577 _ (by rfl)
    _ = 3375 := by rw [pc2835]; rfl
@[simp] theorem pc2837 : Artifact.submissionArtifact.instructionPC 2579 = 3376 := by
  calc
    Artifact.submissionArtifact.instructionPC 2579 =
        Artifact.submissionArtifact.instructionPC 2578 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 0 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2578 _ (by rfl)
    _ = 3376 := by rw [pc2836]; rfl
@[simp] theorem pc2838 : Artifact.submissionArtifact.instructionPC 2580 = 3377 := by
  calc
    Artifact.submissionArtifact.instructionPC 2580 =
        Artifact.submissionArtifact.instructionPC 2579 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MULMOD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2579 _ (by rfl)
    _ = 3377 := by rw [pc2837]; rfl
@[simp] theorem pc2839 : Artifact.submissionArtifact.instructionPC 2581 = 3378 := by
  calc
    Artifact.submissionArtifact.instructionPC 2581 =
        Artifact.submissionArtifact.instructionPC 2580 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MULMOD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2580 _ (by rfl)
    _ = 3378 := by rw [pc2838]; rfl
@[simp] theorem pc2840 : Artifact.submissionArtifact.instructionPC 2582 = 3379 := by
  calc
    Artifact.submissionArtifact.instructionPC 2582 =
        Artifact.submissionArtifact.instructionPC 2581 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 5 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2581 _ (by rfl)
    _ = 3379 := by rw [pc2839]; rfl
@[simp] theorem pc2841 : Artifact.submissionArtifact.instructionPC 2583 = 3380 := by
  calc
    Artifact.submissionArtifact.instructionPC 2583 =
        Artifact.submissionArtifact.instructionPC 2582 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.POP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2582 _ (by rfl)
    _ = 3380 := by rw [pc2840]; rfl
@[simp] theorem pc2842 : Artifact.submissionArtifact.instructionPC 2584 = 3381 := by
  calc
    Artifact.submissionArtifact.instructionPC 2584 =
        Artifact.submissionArtifact.instructionPC 2583 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.POP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2583 _ (by rfl)
    _ = 3381 := by rw [pc2841]; rfl
@[simp] theorem pc2843 : Artifact.submissionArtifact.instructionPC 2585 = 3384 := by
  calc
    Artifact.submissionArtifact.instructionPC 2585 =
        Artifact.submissionArtifact.instructionPC 2584 +
          (YulEvmCompiler.Instr.push 2 655).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2584 _ (by rfl)
    _ = 3384 := by rw [pc2842]; rfl
@[simp] theorem pc2844 : Artifact.submissionArtifact.instructionPC 2586 = 3385 := by
  calc
    Artifact.submissionArtifact.instructionPC 2586 =
        Artifact.submissionArtifact.instructionPC 2585 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.JUMP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2585 _ (by rfl)
    _ = 3385 := by rw [pc2843]; rfl
@[simp] theorem pc2845 : Artifact.submissionArtifact.instructionPC 2587 = 3386 := by
  calc
    Artifact.submissionArtifact.instructionPC 2587 =
        Artifact.submissionArtifact.instructionPC 2586 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.JUMPDEST).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2586 _ (by rfl)
    _ = 3386 := by rw [pc2844]; rfl
@[simp] theorem pc2846 : Artifact.submissionArtifact.instructionPC 2588 = 3387 := by
  calc
    Artifact.submissionArtifact.instructionPC 2588 =
        Artifact.submissionArtifact.instructionPC 2587 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2587 _ (by rfl)
    _ = 3387 := by rw [pc2845]; rfl
@[simp] theorem pc2847 : Artifact.submissionArtifact.instructionPC 2589 = 3388 := by
  calc
    Artifact.submissionArtifact.instructionPC 2589 =
        Artifact.submissionArtifact.instructionPC 2588 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.ISZERO).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2588 _ (by rfl)
    _ = 3388 := by rw [pc2846]; rfl
@[simp] theorem pc2848 : Artifact.submissionArtifact.instructionPC 2590 = 3391 := by
  calc
    Artifact.submissionArtifact.instructionPC 2590 =
        Artifact.submissionArtifact.instructionPC 2589 +
          (YulEvmCompiler.Instr.push 2 3407).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2589 _ (by rfl)
    _ = 3391 := by rw [pc2847]; rfl
@[simp] theorem pc2849 : Artifact.submissionArtifact.instructionPC 2591 = 3392 := by
  calc
    Artifact.submissionArtifact.instructionPC 2591 =
        Artifact.submissionArtifact.instructionPC 2590 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.JUMPI).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2590 _ (by rfl)
    _ = 3392 := by rw [pc2848]; rfl
@[simp] theorem pc2855 : Artifact.submissionArtifact.instructionPC 2592 = 3395 := by
  calc
    Artifact.submissionArtifact.instructionPC 2592 =
        Artifact.submissionArtifact.instructionPC 2591 +
          (YulEvmCompiler.Instr.push 2 9344).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2591 _ (by rfl)
    _ = 3395 := by rw [pc2849]; rfl
@[simp] theorem pc2856 : Artifact.submissionArtifact.instructionPC 2593 = 3396 := by
  calc
    Artifact.submissionArtifact.instructionPC 2593 =
        Artifact.submissionArtifact.instructionPC 2592 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MLOAD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2592 _ (by rfl)
    _ = 3396 := by rw [pc2855]; rfl
@[simp] theorem pc2857 : Artifact.submissionArtifact.instructionPC 2594 = 3399 := by
  calc
    Artifact.submissionArtifact.instructionPC 2594 =
        Artifact.submissionArtifact.instructionPC 2593 +
          (YulEvmCompiler.Instr.push 2 2048).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2593 _ (by rfl)
    _ = 3399 := by rw [pc2856]; rfl
@[simp] theorem pc2858 : Artifact.submissionArtifact.instructionPC 2595 = 3402 := by
  calc
    Artifact.submissionArtifact.instructionPC 2595 =
        Artifact.submissionArtifact.instructionPC 2594 +
          (YulEvmCompiler.Instr.push 2 1024).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2594 _ (by rfl)
    _ = 3402 := by rw [pc2857]; rfl
@[simp] theorem pc2859 : Artifact.submissionArtifact.instructionPC 2596 = 3403 := by
  calc
    Artifact.submissionArtifact.instructionPC 2596 =
        Artifact.submissionArtifact.instructionPC 2595 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MCOPY).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2595 _ (by rfl)
    _ = 3403 := by rw [pc2858]; rfl
@[simp] theorem pc2860 : Artifact.submissionArtifact.instructionPC 2597 = 3406 := by
  calc
    Artifact.submissionArtifact.instructionPC 2597 =
        Artifact.submissionArtifact.instructionPC 2596 +
          (YulEvmCompiler.Instr.push 2 1758).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2596 _ (by rfl)
    _ = 3406 := by rw [pc2859]; rfl
@[simp] theorem pc2861 : Artifact.submissionArtifact.instructionPC 2598 = 3407 := by
  calc
    Artifact.submissionArtifact.instructionPC 2598 =
        Artifact.submissionArtifact.instructionPC 2597 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.JUMP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2597 _ (by rfl)
    _ = 3407 := by rw [pc2860]; rfl

end Challenge.Modexp.Submission.Proofs.Bytecode.LoopPCs
