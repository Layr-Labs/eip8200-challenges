import Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
/-!
# Program counters for the unrolled exponent-bit block

The first seven bit bodies retain seventeen instructions each; the last retains fifteen. Certificate names are stable API names, while their indices and PCs bind the selected artifact.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.UnrollPCs

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

@[simp] theorem pc484 : Artifact.submissionArtifact.instructionPC 484 = 606 := by rfl
@[simp] theorem pc485 : Artifact.submissionArtifact.instructionPC 485 = 607 := by
  calc
    Artifact.submissionArtifact.instructionPC 485 =
        Artifact.submissionArtifact.instructionPC 484 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.JUMPDEST).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 484 _ (by rfl)
    _ = 607 := by rw [pc484]; rfl
@[simp] theorem pc486 : Artifact.submissionArtifact.instructionPC 486 = 610 := by
  calc
    Artifact.submissionArtifact.instructionPC 486 =
        Artifact.submissionArtifact.instructionPC 485 +
          (YulEvmCompiler.Instr.push 2 3218).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 485 _ (by rfl)
    _ = 610 := by rw [pc485]; rfl
@[simp] theorem pc2414 : Artifact.submissionArtifact.instructionPC 2445 = 3218 := by rfl
@[simp] theorem pc2415 : Artifact.submissionArtifact.instructionPC 2446 = 3219 := by
  calc
    Artifact.submissionArtifact.instructionPC 2446 =
        Artifact.submissionArtifact.instructionPC 2445 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.JUMPDEST).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2445 _ (by rfl)
    _ = 3219 := by rw [pc2414]; rfl
@[simp] theorem pc2416 : Artifact.submissionArtifact.instructionPC 2447 = 3221 := by
  calc
    Artifact.submissionArtifact.instructionPC 2447 =
        Artifact.submissionArtifact.instructionPC 2446 +
          (YulEvmCompiler.Instr.push 1 1).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2446 _ (by rfl)
    _ = 3221 := by rw [pc2415]; rfl
@[simp] theorem pc2417 : Artifact.submissionArtifact.instructionPC 2448 = 3222 := by
  calc
    Artifact.submissionArtifact.instructionPC 2448 =
        Artifact.submissionArtifact.instructionPC 2447 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 6 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2447 _ (by rfl)
    _ = 3222 := by rw [pc2416]; rfl
@[simp] theorem pc2418 : Artifact.submissionArtifact.instructionPC 2449 = 3223 := by
  calc
    Artifact.submissionArtifact.instructionPC 2449 =
        Artifact.submissionArtifact.instructionPC 2448 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2448 _ (by rfl)
    _ = 3223 := by rw [pc2417]; rfl
@[simp] theorem pc2419 : Artifact.submissionArtifact.instructionPC 2450 = 3224 := by
  calc
    Artifact.submissionArtifact.instructionPC 2450 =
        Artifact.submissionArtifact.instructionPC 2449 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 7 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2449 _ (by rfl)
    _ = 3224 := by rw [pc2418]; rfl
@[simp] theorem pc2420 : Artifact.submissionArtifact.instructionPC 2451 = 3226 := by
  calc
    Artifact.submissionArtifact.instructionPC 2451 =
        Artifact.submissionArtifact.instructionPC 2450 +
          (YulEvmCompiler.Instr.push 1 1).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2450 _ (by rfl)
    _ = 3226 := by rw [pc2419]; rfl
@[simp] theorem pc2421 : Artifact.submissionArtifact.instructionPC 2452 = 3227 := by
  calc
    Artifact.submissionArtifact.instructionPC 2452 =
        Artifact.submissionArtifact.instructionPC 2451 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 4 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2451 _ (by rfl)
    _ = 3227 := by rw [pc2420]; rfl
@[simp] theorem pc2422 : Artifact.submissionArtifact.instructionPC 2453 = 3229 := by
  calc
    Artifact.submissionArtifact.instructionPC 2453 =
        Artifact.submissionArtifact.instructionPC 2452 +
          (YulEvmCompiler.Instr.push 1 7).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2452 _ (by rfl)
    _ = 3229 := by rw [pc2421]; rfl
@[simp] theorem pc2423 : Artifact.submissionArtifact.instructionPC 2454 = 3230 := by
  calc
    Artifact.submissionArtifact.instructionPC 2454 =
        Artifact.submissionArtifact.instructionPC 2453 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.SHR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2453 _ (by rfl)
    _ = 3230 := by rw [pc2422]; rfl
@[simp] theorem pc2424 : Artifact.submissionArtifact.instructionPC 2455 = 3231 := by
  calc
    Artifact.submissionArtifact.instructionPC 2455 =
        Artifact.submissionArtifact.instructionPC 2454 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.AND).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2454 _ (by rfl)
    _ = 3231 := by rw [pc2423]; rfl
@[simp] theorem pc2425 : Artifact.submissionArtifact.instructionPC 2456 = 3232 := by
  calc
    Artifact.submissionArtifact.instructionPC 2456 =
        Artifact.submissionArtifact.instructionPC 2455 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 2 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2455 _ (by rfl)
    _ = 3232 := by rw [pc2424]; rfl
@[simp] theorem pc2426 : Artifact.submissionArtifact.instructionPC 2457 = 3233 := by
  calc
    Artifact.submissionArtifact.instructionPC 2457 =
        Artifact.submissionArtifact.instructionPC 2456 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MUL).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2456 _ (by rfl)
    _ = 3233 := by rw [pc2425]; rfl
@[simp] theorem pc2427 : Artifact.submissionArtifact.instructionPC 2458 = 3235 := by
  calc
    Artifact.submissionArtifact.instructionPC 2458 =
        Artifact.submissionArtifact.instructionPC 2457 +
          (YulEvmCompiler.Instr.push 1 1).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2457 _ (by rfl)
    _ = 3235 := by rw [pc2426]; rfl
@[simp] theorem pc2428 : Artifact.submissionArtifact.instructionPC 2459 = 3236 := by
  calc
    Artifact.submissionArtifact.instructionPC 2459 =
        Artifact.submissionArtifact.instructionPC 2458 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.ADD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2458 _ (by rfl)
    _ = 3236 := by rw [pc2427]; rfl
@[simp] theorem pc2429 : Artifact.submissionArtifact.instructionPC 2460 = 3237 := by
  calc
    Artifact.submissionArtifact.instructionPC 2460 =
        Artifact.submissionArtifact.instructionPC 2459 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2459 _ (by rfl)
    _ = 3237 := by rw [pc2428]; rfl
@[simp] theorem pc2430 : Artifact.submissionArtifact.instructionPC 2461 = 3238 := by
  calc
    Artifact.submissionArtifact.instructionPC 2461 =
        Artifact.submissionArtifact.instructionPC 2460 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 8 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2460 _ (by rfl)
    _ = 3238 := by rw [pc2429]; rfl
@[simp] theorem pc2431 : Artifact.submissionArtifact.instructionPC 2462 = 3239 := by
  calc
    Artifact.submissionArtifact.instructionPC 2462 =
        Artifact.submissionArtifact.instructionPC 2461 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 0 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2461 _ (by rfl)
    _ = 3239 := by rw [pc2430]; rfl
@[simp] theorem pc2432 : Artifact.submissionArtifact.instructionPC 2463 = 3240 := by
  calc
    Artifact.submissionArtifact.instructionPC 2463 =
        Artifact.submissionArtifact.instructionPC 2462 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MULMOD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2462 _ (by rfl)
    _ = 3240 := by rw [pc2431]; rfl
@[simp] theorem pc2433 : Artifact.submissionArtifact.instructionPC 2464 = 3241 := by
  calc
    Artifact.submissionArtifact.instructionPC 2464 =
        Artifact.submissionArtifact.instructionPC 2463 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MULMOD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2463 _ (by rfl)
    _ = 3241 := by rw [pc2432]; rfl
@[simp] theorem pc2434 : Artifact.submissionArtifact.instructionPC 2465 = 3242 := by
  calc
    Artifact.submissionArtifact.instructionPC 2465 =
        Artifact.submissionArtifact.instructionPC 2464 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 5 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2464 _ (by rfl)
    _ = 3242 := by rw [pc2433]; rfl
@[simp] theorem pc2435 : Artifact.submissionArtifact.instructionPC 2466 = 3243 := by
  calc
    Artifact.submissionArtifact.instructionPC 2466 =
        Artifact.submissionArtifact.instructionPC 2465 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.POP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2465 _ (by rfl)
    _ = 3243 := by rw [pc2434]; rfl
@[simp] theorem pc2436 : Artifact.submissionArtifact.instructionPC 2467 = 3244 := by
  calc
    Artifact.submissionArtifact.instructionPC 2467 =
        Artifact.submissionArtifact.instructionPC 2466 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 7 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2466 _ (by rfl)
    _ = 3244 := by rw [pc2435]; rfl
@[simp] theorem pc2437 : Artifact.submissionArtifact.instructionPC 2468 = 3246 := by
  calc
    Artifact.submissionArtifact.instructionPC 2468 =
        Artifact.submissionArtifact.instructionPC 2467 +
          (YulEvmCompiler.Instr.push 1 1).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2467 _ (by rfl)
    _ = 3246 := by rw [pc2436]; rfl
@[simp] theorem pc2438 : Artifact.submissionArtifact.instructionPC 2469 = 3247 := by
  calc
    Artifact.submissionArtifact.instructionPC 2469 =
        Artifact.submissionArtifact.instructionPC 2468 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 4 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2468 _ (by rfl)
    _ = 3247 := by rw [pc2437]; rfl
@[simp] theorem pc2439 : Artifact.submissionArtifact.instructionPC 2470 = 3249 := by
  calc
    Artifact.submissionArtifact.instructionPC 2470 =
        Artifact.submissionArtifact.instructionPC 2469 +
          (YulEvmCompiler.Instr.push 1 6).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2469 _ (by rfl)
    _ = 3249 := by rw [pc2438]; rfl
@[simp] theorem pc2440 : Artifact.submissionArtifact.instructionPC 2471 = 3250 := by
  calc
    Artifact.submissionArtifact.instructionPC 2471 =
        Artifact.submissionArtifact.instructionPC 2470 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.SHR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2470 _ (by rfl)
    _ = 3250 := by rw [pc2439]; rfl
@[simp] theorem pc2441 : Artifact.submissionArtifact.instructionPC 2472 = 3251 := by
  calc
    Artifact.submissionArtifact.instructionPC 2472 =
        Artifact.submissionArtifact.instructionPC 2471 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.AND).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2471 _ (by rfl)
    _ = 3251 := by rw [pc2440]; rfl
@[simp] theorem pc2442 : Artifact.submissionArtifact.instructionPC 2473 = 3252 := by
  calc
    Artifact.submissionArtifact.instructionPC 2473 =
        Artifact.submissionArtifact.instructionPC 2472 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 2 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2472 _ (by rfl)
    _ = 3252 := by rw [pc2441]; rfl
@[simp] theorem pc2443 : Artifact.submissionArtifact.instructionPC 2474 = 3253 := by
  calc
    Artifact.submissionArtifact.instructionPC 2474 =
        Artifact.submissionArtifact.instructionPC 2473 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MUL).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2473 _ (by rfl)
    _ = 3253 := by rw [pc2442]; rfl
@[simp] theorem pc2444 : Artifact.submissionArtifact.instructionPC 2475 = 3255 := by
  calc
    Artifact.submissionArtifact.instructionPC 2475 =
        Artifact.submissionArtifact.instructionPC 2474 +
          (YulEvmCompiler.Instr.push 1 1).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2474 _ (by rfl)
    _ = 3255 := by rw [pc2443]; rfl
@[simp] theorem pc2445 : Artifact.submissionArtifact.instructionPC 2476 = 3256 := by
  calc
    Artifact.submissionArtifact.instructionPC 2476 =
        Artifact.submissionArtifact.instructionPC 2475 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.ADD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2475 _ (by rfl)
    _ = 3256 := by rw [pc2444]; rfl
@[simp] theorem pc2446 : Artifact.submissionArtifact.instructionPC 2477 = 3257 := by
  calc
    Artifact.submissionArtifact.instructionPC 2477 =
        Artifact.submissionArtifact.instructionPC 2476 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2476 _ (by rfl)
    _ = 3257 := by rw [pc2445]; rfl
@[simp] theorem pc2447 : Artifact.submissionArtifact.instructionPC 2478 = 3258 := by
  calc
    Artifact.submissionArtifact.instructionPC 2478 =
        Artifact.submissionArtifact.instructionPC 2477 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 8 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2477 _ (by rfl)
    _ = 3258 := by rw [pc2446]; rfl
@[simp] theorem pc2448 : Artifact.submissionArtifact.instructionPC 2479 = 3259 := by
  calc
    Artifact.submissionArtifact.instructionPC 2479 =
        Artifact.submissionArtifact.instructionPC 2478 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 0 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2478 _ (by rfl)
    _ = 3259 := by rw [pc2447]; rfl
@[simp] theorem pc2449 : Artifact.submissionArtifact.instructionPC 2480 = 3260 := by
  calc
    Artifact.submissionArtifact.instructionPC 2480 =
        Artifact.submissionArtifact.instructionPC 2479 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MULMOD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2479 _ (by rfl)
    _ = 3260 := by rw [pc2448]; rfl
@[simp] theorem pc2450 : Artifact.submissionArtifact.instructionPC 2481 = 3261 := by
  calc
    Artifact.submissionArtifact.instructionPC 2481 =
        Artifact.submissionArtifact.instructionPC 2480 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MULMOD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2480 _ (by rfl)
    _ = 3261 := by rw [pc2449]; rfl
@[simp] theorem pc2451 : Artifact.submissionArtifact.instructionPC 2482 = 3262 := by
  calc
    Artifact.submissionArtifact.instructionPC 2482 =
        Artifact.submissionArtifact.instructionPC 2481 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 5 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2481 _ (by rfl)
    _ = 3262 := by rw [pc2450]; rfl
@[simp] theorem pc2452 : Artifact.submissionArtifact.instructionPC 2483 = 3263 := by
  calc
    Artifact.submissionArtifact.instructionPC 2483 =
        Artifact.submissionArtifact.instructionPC 2482 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.POP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2482 _ (by rfl)
    _ = 3263 := by rw [pc2451]; rfl
@[simp] theorem pc2453 : Artifact.submissionArtifact.instructionPC 2484 = 3264 := by
  calc
    Artifact.submissionArtifact.instructionPC 2484 =
        Artifact.submissionArtifact.instructionPC 2483 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 7 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2483 _ (by rfl)
    _ = 3264 := by rw [pc2452]; rfl
@[simp] theorem pc2454 : Artifact.submissionArtifact.instructionPC 2485 = 3266 := by
  calc
    Artifact.submissionArtifact.instructionPC 2485 =
        Artifact.submissionArtifact.instructionPC 2484 +
          (YulEvmCompiler.Instr.push 1 1).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2484 _ (by rfl)
    _ = 3266 := by rw [pc2453]; rfl
@[simp] theorem pc2455 : Artifact.submissionArtifact.instructionPC 2486 = 3267 := by
  calc
    Artifact.submissionArtifact.instructionPC 2486 =
        Artifact.submissionArtifact.instructionPC 2485 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 4 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2485 _ (by rfl)
    _ = 3267 := by rw [pc2454]; rfl
@[simp] theorem pc2456 : Artifact.submissionArtifact.instructionPC 2487 = 3269 := by
  calc
    Artifact.submissionArtifact.instructionPC 2487 =
        Artifact.submissionArtifact.instructionPC 2486 +
          (YulEvmCompiler.Instr.push 1 5).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2486 _ (by rfl)
    _ = 3269 := by rw [pc2455]; rfl
@[simp] theorem pc2457 : Artifact.submissionArtifact.instructionPC 2488 = 3270 := by
  calc
    Artifact.submissionArtifact.instructionPC 2488 =
        Artifact.submissionArtifact.instructionPC 2487 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.SHR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2487 _ (by rfl)
    _ = 3270 := by rw [pc2456]; rfl
@[simp] theorem pc2458 : Artifact.submissionArtifact.instructionPC 2489 = 3271 := by
  calc
    Artifact.submissionArtifact.instructionPC 2489 =
        Artifact.submissionArtifact.instructionPC 2488 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.AND).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2488 _ (by rfl)
    _ = 3271 := by rw [pc2457]; rfl
@[simp] theorem pc2459 : Artifact.submissionArtifact.instructionPC 2490 = 3272 := by
  calc
    Artifact.submissionArtifact.instructionPC 2490 =
        Artifact.submissionArtifact.instructionPC 2489 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 2 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2489 _ (by rfl)
    _ = 3272 := by rw [pc2458]; rfl
@[simp] theorem pc2460 : Artifact.submissionArtifact.instructionPC 2491 = 3273 := by
  calc
    Artifact.submissionArtifact.instructionPC 2491 =
        Artifact.submissionArtifact.instructionPC 2490 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MUL).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2490 _ (by rfl)
    _ = 3273 := by rw [pc2459]; rfl
@[simp] theorem pc2461 : Artifact.submissionArtifact.instructionPC 2492 = 3275 := by
  calc
    Artifact.submissionArtifact.instructionPC 2492 =
        Artifact.submissionArtifact.instructionPC 2491 +
          (YulEvmCompiler.Instr.push 1 1).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2491 _ (by rfl)
    _ = 3275 := by rw [pc2460]; rfl
@[simp] theorem pc2462 : Artifact.submissionArtifact.instructionPC 2493 = 3276 := by
  calc
    Artifact.submissionArtifact.instructionPC 2493 =
        Artifact.submissionArtifact.instructionPC 2492 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.ADD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2492 _ (by rfl)
    _ = 3276 := by rw [pc2461]; rfl
@[simp] theorem pc2463 : Artifact.submissionArtifact.instructionPC 2494 = 3277 := by
  calc
    Artifact.submissionArtifact.instructionPC 2494 =
        Artifact.submissionArtifact.instructionPC 2493 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2493 _ (by rfl)
    _ = 3277 := by rw [pc2462]; rfl
@[simp] theorem pc2464 : Artifact.submissionArtifact.instructionPC 2495 = 3278 := by
  calc
    Artifact.submissionArtifact.instructionPC 2495 =
        Artifact.submissionArtifact.instructionPC 2494 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 8 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2494 _ (by rfl)
    _ = 3278 := by rw [pc2463]; rfl
@[simp] theorem pc2465 : Artifact.submissionArtifact.instructionPC 2496 = 3279 := by
  calc
    Artifact.submissionArtifact.instructionPC 2496 =
        Artifact.submissionArtifact.instructionPC 2495 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 0 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2495 _ (by rfl)
    _ = 3279 := by rw [pc2464]; rfl
@[simp] theorem pc2466 : Artifact.submissionArtifact.instructionPC 2497 = 3280 := by
  calc
    Artifact.submissionArtifact.instructionPC 2497 =
        Artifact.submissionArtifact.instructionPC 2496 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MULMOD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2496 _ (by rfl)
    _ = 3280 := by rw [pc2465]; rfl
@[simp] theorem pc2467 : Artifact.submissionArtifact.instructionPC 2498 = 3281 := by
  calc
    Artifact.submissionArtifact.instructionPC 2498 =
        Artifact.submissionArtifact.instructionPC 2497 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MULMOD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2497 _ (by rfl)
    _ = 3281 := by rw [pc2466]; rfl
@[simp] theorem pc2468 : Artifact.submissionArtifact.instructionPC 2499 = 3282 := by
  calc
    Artifact.submissionArtifact.instructionPC 2499 =
        Artifact.submissionArtifact.instructionPC 2498 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 5 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2498 _ (by rfl)
    _ = 3282 := by rw [pc2467]; rfl
@[simp] theorem pc2469 : Artifact.submissionArtifact.instructionPC 2500 = 3283 := by
  calc
    Artifact.submissionArtifact.instructionPC 2500 =
        Artifact.submissionArtifact.instructionPC 2499 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.POP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2499 _ (by rfl)
    _ = 3283 := by rw [pc2468]; rfl
@[simp] theorem pc2470 : Artifact.submissionArtifact.instructionPC 2501 = 3284 := by
  calc
    Artifact.submissionArtifact.instructionPC 2501 =
        Artifact.submissionArtifact.instructionPC 2500 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 7 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2500 _ (by rfl)
    _ = 3284 := by rw [pc2469]; rfl
@[simp] theorem pc2471 : Artifact.submissionArtifact.instructionPC 2502 = 3286 := by
  calc
    Artifact.submissionArtifact.instructionPC 2502 =
        Artifact.submissionArtifact.instructionPC 2501 +
          (YulEvmCompiler.Instr.push 1 1).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2501 _ (by rfl)
    _ = 3286 := by rw [pc2470]; rfl
@[simp] theorem pc2472 : Artifact.submissionArtifact.instructionPC 2503 = 3287 := by
  calc
    Artifact.submissionArtifact.instructionPC 2503 =
        Artifact.submissionArtifact.instructionPC 2502 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 4 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2502 _ (by rfl)
    _ = 3287 := by rw [pc2471]; rfl
@[simp] theorem pc2473 : Artifact.submissionArtifact.instructionPC 2504 = 3289 := by
  calc
    Artifact.submissionArtifact.instructionPC 2504 =
        Artifact.submissionArtifact.instructionPC 2503 +
          (YulEvmCompiler.Instr.push 1 4).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2503 _ (by rfl)
    _ = 3289 := by rw [pc2472]; rfl
@[simp] theorem pc2474 : Artifact.submissionArtifact.instructionPC 2505 = 3290 := by
  calc
    Artifact.submissionArtifact.instructionPC 2505 =
        Artifact.submissionArtifact.instructionPC 2504 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.SHR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2504 _ (by rfl)
    _ = 3290 := by rw [pc2473]; rfl
@[simp] theorem pc2475 : Artifact.submissionArtifact.instructionPC 2506 = 3291 := by
  calc
    Artifact.submissionArtifact.instructionPC 2506 =
        Artifact.submissionArtifact.instructionPC 2505 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.AND).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2505 _ (by rfl)
    _ = 3291 := by rw [pc2474]; rfl
@[simp] theorem pc2476 : Artifact.submissionArtifact.instructionPC 2507 = 3292 := by
  calc
    Artifact.submissionArtifact.instructionPC 2507 =
        Artifact.submissionArtifact.instructionPC 2506 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 2 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2506 _ (by rfl)
    _ = 3292 := by rw [pc2475]; rfl
@[simp] theorem pc2477 : Artifact.submissionArtifact.instructionPC 2508 = 3293 := by
  calc
    Artifact.submissionArtifact.instructionPC 2508 =
        Artifact.submissionArtifact.instructionPC 2507 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MUL).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2507 _ (by rfl)
    _ = 3293 := by rw [pc2476]; rfl
@[simp] theorem pc2478 : Artifact.submissionArtifact.instructionPC 2509 = 3295 := by
  calc
    Artifact.submissionArtifact.instructionPC 2509 =
        Artifact.submissionArtifact.instructionPC 2508 +
          (YulEvmCompiler.Instr.push 1 1).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2508 _ (by rfl)
    _ = 3295 := by rw [pc2477]; rfl
@[simp] theorem pc2479 : Artifact.submissionArtifact.instructionPC 2510 = 3296 := by
  calc
    Artifact.submissionArtifact.instructionPC 2510 =
        Artifact.submissionArtifact.instructionPC 2509 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.ADD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2509 _ (by rfl)
    _ = 3296 := by rw [pc2478]; rfl
@[simp] theorem pc2480 : Artifact.submissionArtifact.instructionPC 2511 = 3297 := by
  calc
    Artifact.submissionArtifact.instructionPC 2511 =
        Artifact.submissionArtifact.instructionPC 2510 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2510 _ (by rfl)
    _ = 3297 := by rw [pc2479]; rfl
@[simp] theorem pc2481 : Artifact.submissionArtifact.instructionPC 2512 = 3298 := by
  calc
    Artifact.submissionArtifact.instructionPC 2512 =
        Artifact.submissionArtifact.instructionPC 2511 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 8 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2511 _ (by rfl)
    _ = 3298 := by rw [pc2480]; rfl
@[simp] theorem pc2482 : Artifact.submissionArtifact.instructionPC 2513 = 3299 := by
  calc
    Artifact.submissionArtifact.instructionPC 2513 =
        Artifact.submissionArtifact.instructionPC 2512 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 0 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2512 _ (by rfl)
    _ = 3299 := by rw [pc2481]; rfl
@[simp] theorem pc2483 : Artifact.submissionArtifact.instructionPC 2514 = 3300 := by
  calc
    Artifact.submissionArtifact.instructionPC 2514 =
        Artifact.submissionArtifact.instructionPC 2513 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MULMOD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2513 _ (by rfl)
    _ = 3300 := by rw [pc2482]; rfl
@[simp] theorem pc2484 : Artifact.submissionArtifact.instructionPC 2515 = 3301 := by
  calc
    Artifact.submissionArtifact.instructionPC 2515 =
        Artifact.submissionArtifact.instructionPC 2514 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MULMOD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2514 _ (by rfl)
    _ = 3301 := by rw [pc2483]; rfl
@[simp] theorem pc2485 : Artifact.submissionArtifact.instructionPC 2516 = 3302 := by
  calc
    Artifact.submissionArtifact.instructionPC 2516 =
        Artifact.submissionArtifact.instructionPC 2515 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 5 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2515 _ (by rfl)
    _ = 3302 := by rw [pc2484]; rfl
@[simp] theorem pc2486 : Artifact.submissionArtifact.instructionPC 2517 = 3303 := by
  calc
    Artifact.submissionArtifact.instructionPC 2517 =
        Artifact.submissionArtifact.instructionPC 2516 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.POP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2516 _ (by rfl)
    _ = 3303 := by rw [pc2485]; rfl
@[simp] theorem pc2487 : Artifact.submissionArtifact.instructionPC 2518 = 3304 := by
  calc
    Artifact.submissionArtifact.instructionPC 2518 =
        Artifact.submissionArtifact.instructionPC 2517 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 7 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2517 _ (by rfl)
    _ = 3304 := by rw [pc2486]; rfl
@[simp] theorem pc2488 : Artifact.submissionArtifact.instructionPC 2519 = 3306 := by
  calc
    Artifact.submissionArtifact.instructionPC 2519 =
        Artifact.submissionArtifact.instructionPC 2518 +
          (YulEvmCompiler.Instr.push 1 1).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2518 _ (by rfl)
    _ = 3306 := by rw [pc2487]; rfl
@[simp] theorem pc2489 : Artifact.submissionArtifact.instructionPC 2520 = 3307 := by
  calc
    Artifact.submissionArtifact.instructionPC 2520 =
        Artifact.submissionArtifact.instructionPC 2519 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 4 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2519 _ (by rfl)
    _ = 3307 := by rw [pc2488]; rfl
@[simp] theorem pc2490 : Artifact.submissionArtifact.instructionPC 2521 = 3309 := by
  calc
    Artifact.submissionArtifact.instructionPC 2521 =
        Artifact.submissionArtifact.instructionPC 2520 +
          (YulEvmCompiler.Instr.push 1 3).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2520 _ (by rfl)
    _ = 3309 := by rw [pc2489]; rfl
@[simp] theorem pc2491 : Artifact.submissionArtifact.instructionPC 2522 = 3310 := by
  calc
    Artifact.submissionArtifact.instructionPC 2522 =
        Artifact.submissionArtifact.instructionPC 2521 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.SHR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2521 _ (by rfl)
    _ = 3310 := by rw [pc2490]; rfl
@[simp] theorem pc2492 : Artifact.submissionArtifact.instructionPC 2523 = 3311 := by
  calc
    Artifact.submissionArtifact.instructionPC 2523 =
        Artifact.submissionArtifact.instructionPC 2522 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.AND).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2522 _ (by rfl)
    _ = 3311 := by rw [pc2491]; rfl
@[simp] theorem pc2493 : Artifact.submissionArtifact.instructionPC 2524 = 3312 := by
  calc
    Artifact.submissionArtifact.instructionPC 2524 =
        Artifact.submissionArtifact.instructionPC 2523 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 2 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2523 _ (by rfl)
    _ = 3312 := by rw [pc2492]; rfl
@[simp] theorem pc2494 : Artifact.submissionArtifact.instructionPC 2525 = 3313 := by
  calc
    Artifact.submissionArtifact.instructionPC 2525 =
        Artifact.submissionArtifact.instructionPC 2524 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MUL).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2524 _ (by rfl)
    _ = 3313 := by rw [pc2493]; rfl
@[simp] theorem pc2495 : Artifact.submissionArtifact.instructionPC 2526 = 3315 := by
  calc
    Artifact.submissionArtifact.instructionPC 2526 =
        Artifact.submissionArtifact.instructionPC 2525 +
          (YulEvmCompiler.Instr.push 1 1).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2525 _ (by rfl)
    _ = 3315 := by rw [pc2494]; rfl
@[simp] theorem pc2496 : Artifact.submissionArtifact.instructionPC 2527 = 3316 := by
  calc
    Artifact.submissionArtifact.instructionPC 2527 =
        Artifact.submissionArtifact.instructionPC 2526 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.ADD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2526 _ (by rfl)
    _ = 3316 := by rw [pc2495]; rfl
@[simp] theorem pc2497 : Artifact.submissionArtifact.instructionPC 2528 = 3317 := by
  calc
    Artifact.submissionArtifact.instructionPC 2528 =
        Artifact.submissionArtifact.instructionPC 2527 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2527 _ (by rfl)
    _ = 3317 := by rw [pc2496]; rfl
@[simp] theorem pc2498 : Artifact.submissionArtifact.instructionPC 2529 = 3318 := by
  calc
    Artifact.submissionArtifact.instructionPC 2529 =
        Artifact.submissionArtifact.instructionPC 2528 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 8 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2528 _ (by rfl)
    _ = 3318 := by rw [pc2497]; rfl
@[simp] theorem pc2499 : Artifact.submissionArtifact.instructionPC 2530 = 3319 := by
  calc
    Artifact.submissionArtifact.instructionPC 2530 =
        Artifact.submissionArtifact.instructionPC 2529 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 0 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2529 _ (by rfl)
    _ = 3319 := by rw [pc2498]; rfl
@[simp] theorem pc2500 : Artifact.submissionArtifact.instructionPC 2531 = 3320 := by
  calc
    Artifact.submissionArtifact.instructionPC 2531 =
        Artifact.submissionArtifact.instructionPC 2530 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MULMOD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2530 _ (by rfl)
    _ = 3320 := by rw [pc2499]; rfl
@[simp] theorem pc2501 : Artifact.submissionArtifact.instructionPC 2532 = 3321 := by
  calc
    Artifact.submissionArtifact.instructionPC 2532 =
        Artifact.submissionArtifact.instructionPC 2531 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MULMOD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2531 _ (by rfl)
    _ = 3321 := by rw [pc2500]; rfl
@[simp] theorem pc2502 : Artifact.submissionArtifact.instructionPC 2533 = 3322 := by
  calc
    Artifact.submissionArtifact.instructionPC 2533 =
        Artifact.submissionArtifact.instructionPC 2532 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 5 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2532 _ (by rfl)
    _ = 3322 := by rw [pc2501]; rfl
@[simp] theorem pc2503 : Artifact.submissionArtifact.instructionPC 2534 = 3323 := by
  calc
    Artifact.submissionArtifact.instructionPC 2534 =
        Artifact.submissionArtifact.instructionPC 2533 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.POP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2533 _ (by rfl)
    _ = 3323 := by rw [pc2502]; rfl
@[simp] theorem pc2504 : Artifact.submissionArtifact.instructionPC 2535 = 3324 := by
  calc
    Artifact.submissionArtifact.instructionPC 2535 =
        Artifact.submissionArtifact.instructionPC 2534 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 7 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2534 _ (by rfl)
    _ = 3324 := by rw [pc2503]; rfl
@[simp] theorem pc2505 : Artifact.submissionArtifact.instructionPC 2536 = 3326 := by
  calc
    Artifact.submissionArtifact.instructionPC 2536 =
        Artifact.submissionArtifact.instructionPC 2535 +
          (YulEvmCompiler.Instr.push 1 1).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2535 _ (by rfl)
    _ = 3326 := by rw [pc2504]; rfl
@[simp] theorem pc2506 : Artifact.submissionArtifact.instructionPC 2537 = 3327 := by
  calc
    Artifact.submissionArtifact.instructionPC 2537 =
        Artifact.submissionArtifact.instructionPC 2536 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 4 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2536 _ (by rfl)
    _ = 3327 := by rw [pc2505]; rfl
@[simp] theorem pc2507 : Artifact.submissionArtifact.instructionPC 2538 = 3329 := by
  calc
    Artifact.submissionArtifact.instructionPC 2538 =
        Artifact.submissionArtifact.instructionPC 2537 +
          (YulEvmCompiler.Instr.push 1 2).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2537 _ (by rfl)
    _ = 3329 := by rw [pc2506]; rfl
@[simp] theorem pc2508 : Artifact.submissionArtifact.instructionPC 2539 = 3330 := by
  calc
    Artifact.submissionArtifact.instructionPC 2539 =
        Artifact.submissionArtifact.instructionPC 2538 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.SHR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2538 _ (by rfl)
    _ = 3330 := by rw [pc2507]; rfl
@[simp] theorem pc2509 : Artifact.submissionArtifact.instructionPC 2540 = 3331 := by
  calc
    Artifact.submissionArtifact.instructionPC 2540 =
        Artifact.submissionArtifact.instructionPC 2539 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.AND).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2539 _ (by rfl)
    _ = 3331 := by rw [pc2508]; rfl
@[simp] theorem pc2510 : Artifact.submissionArtifact.instructionPC 2541 = 3332 := by
  calc
    Artifact.submissionArtifact.instructionPC 2541 =
        Artifact.submissionArtifact.instructionPC 2540 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 2 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2540 _ (by rfl)
    _ = 3332 := by rw [pc2509]; rfl
@[simp] theorem pc2511 : Artifact.submissionArtifact.instructionPC 2542 = 3333 := by
  calc
    Artifact.submissionArtifact.instructionPC 2542 =
        Artifact.submissionArtifact.instructionPC 2541 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MUL).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2541 _ (by rfl)
    _ = 3333 := by rw [pc2510]; rfl
@[simp] theorem pc2512 : Artifact.submissionArtifact.instructionPC 2543 = 3335 := by
  calc
    Artifact.submissionArtifact.instructionPC 2543 =
        Artifact.submissionArtifact.instructionPC 2542 +
          (YulEvmCompiler.Instr.push 1 1).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2542 _ (by rfl)
    _ = 3335 := by rw [pc2511]; rfl
@[simp] theorem pc2513 : Artifact.submissionArtifact.instructionPC 2544 = 3336 := by
  calc
    Artifact.submissionArtifact.instructionPC 2544 =
        Artifact.submissionArtifact.instructionPC 2543 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.ADD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2543 _ (by rfl)
    _ = 3336 := by rw [pc2512]; rfl
@[simp] theorem pc2514 : Artifact.submissionArtifact.instructionPC 2545 = 3337 := by
  calc
    Artifact.submissionArtifact.instructionPC 2545 =
        Artifact.submissionArtifact.instructionPC 2544 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2544 _ (by rfl)
    _ = 3337 := by rw [pc2513]; rfl
@[simp] theorem pc2515 : Artifact.submissionArtifact.instructionPC 2546 = 3338 := by
  calc
    Artifact.submissionArtifact.instructionPC 2546 =
        Artifact.submissionArtifact.instructionPC 2545 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 8 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2545 _ (by rfl)
    _ = 3338 := by rw [pc2514]; rfl
@[simp] theorem pc2516 : Artifact.submissionArtifact.instructionPC 2547 = 3339 := by
  calc
    Artifact.submissionArtifact.instructionPC 2547 =
        Artifact.submissionArtifact.instructionPC 2546 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 0 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2546 _ (by rfl)
    _ = 3339 := by rw [pc2515]; rfl
@[simp] theorem pc2517 : Artifact.submissionArtifact.instructionPC 2548 = 3340 := by
  calc
    Artifact.submissionArtifact.instructionPC 2548 =
        Artifact.submissionArtifact.instructionPC 2547 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MULMOD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2547 _ (by rfl)
    _ = 3340 := by rw [pc2516]; rfl
@[simp] theorem pc2518 : Artifact.submissionArtifact.instructionPC 2549 = 3341 := by
  calc
    Artifact.submissionArtifact.instructionPC 2549 =
        Artifact.submissionArtifact.instructionPC 2548 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MULMOD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2548 _ (by rfl)
    _ = 3341 := by rw [pc2517]; rfl
@[simp] theorem pc2519 : Artifact.submissionArtifact.instructionPC 2550 = 3342 := by
  calc
    Artifact.submissionArtifact.instructionPC 2550 =
        Artifact.submissionArtifact.instructionPC 2549 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 5 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2549 _ (by rfl)
    _ = 3342 := by rw [pc2518]; rfl
@[simp] theorem pc2520 : Artifact.submissionArtifact.instructionPC 2551 = 3343 := by
  calc
    Artifact.submissionArtifact.instructionPC 2551 =
        Artifact.submissionArtifact.instructionPC 2550 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.POP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2550 _ (by rfl)
    _ = 3343 := by rw [pc2519]; rfl
@[simp] theorem pc2521 : Artifact.submissionArtifact.instructionPC 2552 = 3344 := by
  calc
    Artifact.submissionArtifact.instructionPC 2552 =
        Artifact.submissionArtifact.instructionPC 2551 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 7 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2551 _ (by rfl)
    _ = 3344 := by rw [pc2520]; rfl
@[simp] theorem pc2522 : Artifact.submissionArtifact.instructionPC 2553 = 3346 := by
  calc
    Artifact.submissionArtifact.instructionPC 2553 =
        Artifact.submissionArtifact.instructionPC 2552 +
          (YulEvmCompiler.Instr.push 1 1).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2552 _ (by rfl)
    _ = 3346 := by rw [pc2521]; rfl
@[simp] theorem pc2523 : Artifact.submissionArtifact.instructionPC 2554 = 3347 := by
  calc
    Artifact.submissionArtifact.instructionPC 2554 =
        Artifact.submissionArtifact.instructionPC 2553 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 4 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2553 _ (by rfl)
    _ = 3347 := by rw [pc2522]; rfl
@[simp] theorem pc2524 : Artifact.submissionArtifact.instructionPC 2555 = 3349 := by
  calc
    Artifact.submissionArtifact.instructionPC 2555 =
        Artifact.submissionArtifact.instructionPC 2554 +
          (YulEvmCompiler.Instr.push 1 1).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2554 _ (by rfl)
    _ = 3349 := by rw [pc2523]; rfl
@[simp] theorem pc2525 : Artifact.submissionArtifact.instructionPC 2556 = 3350 := by
  calc
    Artifact.submissionArtifact.instructionPC 2556 =
        Artifact.submissionArtifact.instructionPC 2555 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.SHR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2555 _ (by rfl)
    _ = 3350 := by rw [pc2524]; rfl
@[simp] theorem pc2526 : Artifact.submissionArtifact.instructionPC 2557 = 3351 := by
  calc
    Artifact.submissionArtifact.instructionPC 2557 =
        Artifact.submissionArtifact.instructionPC 2556 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.AND).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2556 _ (by rfl)
    _ = 3351 := by rw [pc2525]; rfl
@[simp] theorem pc2527 : Artifact.submissionArtifact.instructionPC 2558 = 3352 := by
  calc
    Artifact.submissionArtifact.instructionPC 2558 =
        Artifact.submissionArtifact.instructionPC 2557 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 2 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2557 _ (by rfl)
    _ = 3352 := by rw [pc2526]; rfl
@[simp] theorem pc2528 : Artifact.submissionArtifact.instructionPC 2559 = 3353 := by
  calc
    Artifact.submissionArtifact.instructionPC 2559 =
        Artifact.submissionArtifact.instructionPC 2558 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MUL).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2558 _ (by rfl)
    _ = 3353 := by rw [pc2527]; rfl
@[simp] theorem pc2529 : Artifact.submissionArtifact.instructionPC 2560 = 3355 := by
  calc
    Artifact.submissionArtifact.instructionPC 2560 =
        Artifact.submissionArtifact.instructionPC 2559 +
          (YulEvmCompiler.Instr.push 1 1).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2559 _ (by rfl)
    _ = 3355 := by rw [pc2528]; rfl
@[simp] theorem pc2530 : Artifact.submissionArtifact.instructionPC 2561 = 3356 := by
  calc
    Artifact.submissionArtifact.instructionPC 2561 =
        Artifact.submissionArtifact.instructionPC 2560 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.ADD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2560 _ (by rfl)
    _ = 3356 := by rw [pc2529]; rfl
@[simp] theorem pc2531 : Artifact.submissionArtifact.instructionPC 2562 = 3357 := by
  calc
    Artifact.submissionArtifact.instructionPC 2562 =
        Artifact.submissionArtifact.instructionPC 2561 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2561 _ (by rfl)
    _ = 3357 := by rw [pc2530]; rfl
@[simp] theorem pc2532 : Artifact.submissionArtifact.instructionPC 2563 = 3358 := by
  calc
    Artifact.submissionArtifact.instructionPC 2563 =
        Artifact.submissionArtifact.instructionPC 2562 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 8 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2562 _ (by rfl)
    _ = 3358 := by rw [pc2531]; rfl
@[simp] theorem pc2533 : Artifact.submissionArtifact.instructionPC 2564 = 3359 := by
  calc
    Artifact.submissionArtifact.instructionPC 2564 =
        Artifact.submissionArtifact.instructionPC 2563 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 0 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2563 _ (by rfl)
    _ = 3359 := by rw [pc2532]; rfl
@[simp] theorem pc2534 : Artifact.submissionArtifact.instructionPC 2565 = 3360 := by
  calc
    Artifact.submissionArtifact.instructionPC 2565 =
        Artifact.submissionArtifact.instructionPC 2564 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MULMOD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2564 _ (by rfl)
    _ = 3360 := by rw [pc2533]; rfl
@[simp] theorem pc2535 : Artifact.submissionArtifact.instructionPC 2566 = 3361 := by
  calc
    Artifact.submissionArtifact.instructionPC 2566 =
        Artifact.submissionArtifact.instructionPC 2565 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MULMOD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2565 _ (by rfl)
    _ = 3361 := by rw [pc2534]; rfl
@[simp] theorem pc2536 : Artifact.submissionArtifact.instructionPC 2567 = 3362 := by
  calc
    Artifact.submissionArtifact.instructionPC 2567 =
        Artifact.submissionArtifact.instructionPC 2566 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 5 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2566 _ (by rfl)
    _ = 3362 := by rw [pc2535]; rfl
@[simp] theorem pc2537 : Artifact.submissionArtifact.instructionPC 2568 = 3363 := by
  calc
    Artifact.submissionArtifact.instructionPC 2568 =
        Artifact.submissionArtifact.instructionPC 2567 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.POP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2567 _ (by rfl)
    _ = 3363 := by rw [pc2536]; rfl
@[simp] theorem pc2538 : Artifact.submissionArtifact.instructionPC 2569 = 3364 := by
  calc
    Artifact.submissionArtifact.instructionPC 2569 =
        Artifact.submissionArtifact.instructionPC 2568 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 7 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2568 _ (by rfl)
    _ = 3364 := by rw [pc2537]; rfl
@[simp] theorem pc2539 : Artifact.submissionArtifact.instructionPC 2570 = 3366 := by
  calc
    Artifact.submissionArtifact.instructionPC 2570 =
        Artifact.submissionArtifact.instructionPC 2569 +
          (YulEvmCompiler.Instr.push 1 1).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2569 _ (by rfl)
    _ = 3366 := by rw [pc2538]; rfl
@[simp] theorem pc2542 : Artifact.submissionArtifact.instructionPC 2571 = 3367 := by
  calc
    Artifact.submissionArtifact.instructionPC 2571 =
        Artifact.submissionArtifact.instructionPC 2570 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 4 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2570 _ (by rfl)
    _ = 3367 := by rw [pc2539]; rfl
@[simp] theorem pc2543 : Artifact.submissionArtifact.instructionPC 2572 = 3368 := by
  calc
    Artifact.submissionArtifact.instructionPC 2572 =
        Artifact.submissionArtifact.instructionPC 2571 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.AND).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2571 _ (by rfl)
    _ = 3368 := by rw [pc2542]; rfl
@[simp] theorem pc2544 : Artifact.submissionArtifact.instructionPC 2573 = 3369 := by
  calc
    Artifact.submissionArtifact.instructionPC 2573 =
        Artifact.submissionArtifact.instructionPC 2572 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 2 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2572 _ (by rfl)
    _ = 3369 := by rw [pc2543]; rfl
@[simp] theorem pc2545 : Artifact.submissionArtifact.instructionPC 2574 = 3370 := by
  calc
    Artifact.submissionArtifact.instructionPC 2574 =
        Artifact.submissionArtifact.instructionPC 2573 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MUL).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2573 _ (by rfl)
    _ = 3370 := by rw [pc2544]; rfl
@[simp] theorem pc2546 : Artifact.submissionArtifact.instructionPC 2575 = 3372 := by
  calc
    Artifact.submissionArtifact.instructionPC 2575 =
        Artifact.submissionArtifact.instructionPC 2574 +
          (YulEvmCompiler.Instr.push 1 1).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2574 _ (by rfl)
    _ = 3372 := by rw [pc2545]; rfl
@[simp] theorem pc2547 : Artifact.submissionArtifact.instructionPC 2576 = 3373 := by
  calc
    Artifact.submissionArtifact.instructionPC 2576 =
        Artifact.submissionArtifact.instructionPC 2575 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.ADD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2575 _ (by rfl)
    _ = 3373 := by rw [pc2546]; rfl
@[simp] theorem pc2548 : Artifact.submissionArtifact.instructionPC 2577 = 3374 := by
  calc
    Artifact.submissionArtifact.instructionPC 2577 =
        Artifact.submissionArtifact.instructionPC 2576 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2576 _ (by rfl)
    _ = 3374 := by rw [pc2547]; rfl
@[simp] theorem pc2549 : Artifact.submissionArtifact.instructionPC 2578 = 3375 := by
  calc
    Artifact.submissionArtifact.instructionPC 2578 =
        Artifact.submissionArtifact.instructionPC 2577 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 8 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2577 _ (by rfl)
    _ = 3375 := by rw [pc2548]; rfl
@[simp] theorem pc2550 : Artifact.submissionArtifact.instructionPC 2579 = 3376 := by
  calc
    Artifact.submissionArtifact.instructionPC 2579 =
        Artifact.submissionArtifact.instructionPC 2578 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 0 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2578 _ (by rfl)
    _ = 3376 := by rw [pc2549]; rfl
@[simp] theorem pc2551 : Artifact.submissionArtifact.instructionPC 2580 = 3377 := by
  calc
    Artifact.submissionArtifact.instructionPC 2580 =
        Artifact.submissionArtifact.instructionPC 2579 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MULMOD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2579 _ (by rfl)
    _ = 3377 := by rw [pc2550]; rfl
@[simp] theorem pc2552 : Artifact.submissionArtifact.instructionPC 2581 = 3378 := by
  calc
    Artifact.submissionArtifact.instructionPC 2581 =
        Artifact.submissionArtifact.instructionPC 2580 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MULMOD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2580 _ (by rfl)
    _ = 3378 := by rw [pc2551]; rfl
@[simp] theorem pc2553 : Artifact.submissionArtifact.instructionPC 2582 = 3379 := by
  calc
    Artifact.submissionArtifact.instructionPC 2582 =
        Artifact.submissionArtifact.instructionPC 2581 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 5 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2581 _ (by rfl)
    _ = 3379 := by rw [pc2552]; rfl
@[simp] theorem pc2554 : Artifact.submissionArtifact.instructionPC 2583 = 3380 := by
  calc
    Artifact.submissionArtifact.instructionPC 2583 =
        Artifact.submissionArtifact.instructionPC 2582 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.POP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2582 _ (by rfl)
    _ = 3380 := by rw [pc2553]; rfl
@[simp] theorem pc2555 : Artifact.submissionArtifact.instructionPC 2584 = 3381 := by
  calc
    Artifact.submissionArtifact.instructionPC 2584 =
        Artifact.submissionArtifact.instructionPC 2583 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.POP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2583 _ (by rfl)
    _ = 3381 := by rw [pc2554]; rfl
@[simp] theorem pc2556 : Artifact.submissionArtifact.instructionPC 2585 = 3384 := by
  calc
    Artifact.submissionArtifact.instructionPC 2585 =
        Artifact.submissionArtifact.instructionPC 2584 +
          (YulEvmCompiler.Instr.push 2 655).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2584 _ (by rfl)
    _ = 3384 := by rw [pc2555]; rfl

@[simp] theorem wordBridgePC3418 : Artifact.submissionArtifact.instructionPC 2605 = 3418 := by rfl
@[simp] theorem wordBridgePC3419 : Artifact.submissionArtifact.instructionPC 2606 = 3419 := by
  calc
    Artifact.submissionArtifact.instructionPC 2606 =
        Artifact.submissionArtifact.instructionPC 2605 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.JUMPDEST).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2605 _ (by rfl)
    _ = 3419 := by rw [wordBridgePC3418]; rfl
@[simp] theorem wordBridgePC3422 : Artifact.submissionArtifact.instructionPC 2607 = 3422 := by
  calc
    Artifact.submissionArtifact.instructionPC 2607 =
        Artifact.submissionArtifact.instructionPC 2606 +
          (YulEvmCompiler.Instr.push 2 3218).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2606 _ (by rfl)
    _ = 3422 := by rw [wordBridgePC3419]; rfl

end Challenge.Modexp.Submission.Proofs.Bytecode.UnrollPCs
