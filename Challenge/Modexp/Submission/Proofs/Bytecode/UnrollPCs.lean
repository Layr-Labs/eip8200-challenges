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

@[simp] theorem pc485 : Artifact.submissionArtifact.instructionPC 537 = 688 := by rfl
@[simp] theorem pc486 : Artifact.submissionArtifact.instructionPC 538 = 691 := by
  calc
    Artifact.submissionArtifact.instructionPC 538 =
        Artifact.submissionArtifact.instructionPC 537 +
          (YulEvmCompiler.Instr.push 2 3079).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 537 _ (by rfl)
    _ = 691 := by rw [pc485]; rfl
@[simp] theorem pc2414 : Artifact.submissionArtifact.instructionPC 2350 = 3079 := by rfl
@[simp] theorem pc2415 : Artifact.submissionArtifact.instructionPC 2351 = 3080 := by
  calc
    Artifact.submissionArtifact.instructionPC 2351 =
        Artifact.submissionArtifact.instructionPC 2350 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.JUMPDEST).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2350 _ (by rfl)
    _ = 3080 := by rw [pc2414]; rfl
@[simp] theorem pc2416 : Artifact.submissionArtifact.instructionPC 2352 = 3082 := by
  calc
    Artifact.submissionArtifact.instructionPC 2352 =
        Artifact.submissionArtifact.instructionPC 2351 +
          (YulEvmCompiler.Instr.push 1 1).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2351 _ (by rfl)
    _ = 3082 := by rw [pc2415]; rfl
@[simp] theorem pc2417 : Artifact.submissionArtifact.instructionPC 2353 = 3083 := by
  calc
    Artifact.submissionArtifact.instructionPC 2353 =
        Artifact.submissionArtifact.instructionPC 2352 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 6 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2352 _ (by rfl)
    _ = 3083 := by rw [pc2416]; rfl
@[simp] theorem pc2418 : Artifact.submissionArtifact.instructionPC 2354 = 3084 := by
  calc
    Artifact.submissionArtifact.instructionPC 2354 =
        Artifact.submissionArtifact.instructionPC 2353 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2353 _ (by rfl)
    _ = 3084 := by rw [pc2417]; rfl
@[simp] theorem pc2419 : Artifact.submissionArtifact.instructionPC 2355 = 3085 := by
  calc
    Artifact.submissionArtifact.instructionPC 2355 =
        Artifact.submissionArtifact.instructionPC 2354 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 7 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2354 _ (by rfl)
    _ = 3085 := by rw [pc2418]; rfl
@[simp] theorem pc2420 : Artifact.submissionArtifact.instructionPC 2356 = 3087 := by
  calc
    Artifact.submissionArtifact.instructionPC 2356 =
        Artifact.submissionArtifact.instructionPC 2355 +
          (YulEvmCompiler.Instr.push 1 1).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2355 _ (by rfl)
    _ = 3087 := by rw [pc2419]; rfl
@[simp] theorem pc2421 : Artifact.submissionArtifact.instructionPC 2357 = 3088 := by
  calc
    Artifact.submissionArtifact.instructionPC 2357 =
        Artifact.submissionArtifact.instructionPC 2356 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 4 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2356 _ (by rfl)
    _ = 3088 := by rw [pc2420]; rfl
@[simp] theorem pc2422 : Artifact.submissionArtifact.instructionPC 2358 = 3090 := by
  calc
    Artifact.submissionArtifact.instructionPC 2358 =
        Artifact.submissionArtifact.instructionPC 2357 +
          (YulEvmCompiler.Instr.push 1 7).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2357 _ (by rfl)
    _ = 3090 := by rw [pc2421]; rfl
@[simp] theorem pc2423 : Artifact.submissionArtifact.instructionPC 2359 = 3091 := by
  calc
    Artifact.submissionArtifact.instructionPC 2359 =
        Artifact.submissionArtifact.instructionPC 2358 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.SHR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2358 _ (by rfl)
    _ = 3091 := by rw [pc2422]; rfl
@[simp] theorem pc2424 : Artifact.submissionArtifact.instructionPC 2360 = 3092 := by
  calc
    Artifact.submissionArtifact.instructionPC 2360 =
        Artifact.submissionArtifact.instructionPC 2359 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.AND).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2359 _ (by rfl)
    _ = 3092 := by rw [pc2423]; rfl
@[simp] theorem pc2425 : Artifact.submissionArtifact.instructionPC 2361 = 3093 := by
  calc
    Artifact.submissionArtifact.instructionPC 2361 =
        Artifact.submissionArtifact.instructionPC 2360 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 2 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2360 _ (by rfl)
    _ = 3093 := by rw [pc2424]; rfl
@[simp] theorem pc2426 : Artifact.submissionArtifact.instructionPC 2362 = 3094 := by
  calc
    Artifact.submissionArtifact.instructionPC 2362 =
        Artifact.submissionArtifact.instructionPC 2361 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MUL).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2361 _ (by rfl)
    _ = 3094 := by rw [pc2425]; rfl
@[simp] theorem pc2427 : Artifact.submissionArtifact.instructionPC 2363 = 3096 := by
  calc
    Artifact.submissionArtifact.instructionPC 2363 =
        Artifact.submissionArtifact.instructionPC 2362 +
          (YulEvmCompiler.Instr.push 1 1).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2362 _ (by rfl)
    _ = 3096 := by rw [pc2426]; rfl
@[simp] theorem pc2428 : Artifact.submissionArtifact.instructionPC 2364 = 3097 := by
  calc
    Artifact.submissionArtifact.instructionPC 2364 =
        Artifact.submissionArtifact.instructionPC 2363 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.ADD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2363 _ (by rfl)
    _ = 3097 := by rw [pc2427]; rfl
@[simp] theorem pc2429 : Artifact.submissionArtifact.instructionPC 2365 = 3098 := by
  calc
    Artifact.submissionArtifact.instructionPC 2365 =
        Artifact.submissionArtifact.instructionPC 2364 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2364 _ (by rfl)
    _ = 3098 := by rw [pc2428]; rfl
@[simp] theorem pc2430 : Artifact.submissionArtifact.instructionPC 2366 = 3099 := by
  calc
    Artifact.submissionArtifact.instructionPC 2366 =
        Artifact.submissionArtifact.instructionPC 2365 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 8 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2365 _ (by rfl)
    _ = 3099 := by rw [pc2429]; rfl
@[simp] theorem pc2431 : Artifact.submissionArtifact.instructionPC 2367 = 3100 := by
  calc
    Artifact.submissionArtifact.instructionPC 2367 =
        Artifact.submissionArtifact.instructionPC 2366 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 0 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2366 _ (by rfl)
    _ = 3100 := by rw [pc2430]; rfl
@[simp] theorem pc2432 : Artifact.submissionArtifact.instructionPC 2368 = 3101 := by
  calc
    Artifact.submissionArtifact.instructionPC 2368 =
        Artifact.submissionArtifact.instructionPC 2367 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MULMOD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2367 _ (by rfl)
    _ = 3101 := by rw [pc2431]; rfl
@[simp] theorem pc2433 : Artifact.submissionArtifact.instructionPC 2369 = 3102 := by
  calc
    Artifact.submissionArtifact.instructionPC 2369 =
        Artifact.submissionArtifact.instructionPC 2368 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MULMOD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2368 _ (by rfl)
    _ = 3102 := by rw [pc2432]; rfl
@[simp] theorem pc2434 : Artifact.submissionArtifact.instructionPC 2370 = 3103 := by
  calc
    Artifact.submissionArtifact.instructionPC 2370 =
        Artifact.submissionArtifact.instructionPC 2369 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 5 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2369 _ (by rfl)
    _ = 3103 := by rw [pc2433]; rfl
@[simp] theorem pc2435 : Artifact.submissionArtifact.instructionPC 2371 = 3104 := by
  calc
    Artifact.submissionArtifact.instructionPC 2371 =
        Artifact.submissionArtifact.instructionPC 2370 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.POP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2370 _ (by rfl)
    _ = 3104 := by rw [pc2434]; rfl
@[simp] theorem pc2436 : Artifact.submissionArtifact.instructionPC 2372 = 3105 := by
  calc
    Artifact.submissionArtifact.instructionPC 2372 =
        Artifact.submissionArtifact.instructionPC 2371 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 7 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2371 _ (by rfl)
    _ = 3105 := by rw [pc2435]; rfl
@[simp] theorem pc2437 : Artifact.submissionArtifact.instructionPC 2373 = 3107 := by
  calc
    Artifact.submissionArtifact.instructionPC 2373 =
        Artifact.submissionArtifact.instructionPC 2372 +
          (YulEvmCompiler.Instr.push 1 1).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2372 _ (by rfl)
    _ = 3107 := by rw [pc2436]; rfl
@[simp] theorem pc2438 : Artifact.submissionArtifact.instructionPC 2374 = 3108 := by
  calc
    Artifact.submissionArtifact.instructionPC 2374 =
        Artifact.submissionArtifact.instructionPC 2373 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 4 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2373 _ (by rfl)
    _ = 3108 := by rw [pc2437]; rfl
@[simp] theorem pc2439 : Artifact.submissionArtifact.instructionPC 2375 = 3110 := by
  calc
    Artifact.submissionArtifact.instructionPC 2375 =
        Artifact.submissionArtifact.instructionPC 2374 +
          (YulEvmCompiler.Instr.push 1 6).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2374 _ (by rfl)
    _ = 3110 := by rw [pc2438]; rfl
@[simp] theorem pc2440 : Artifact.submissionArtifact.instructionPC 2376 = 3111 := by
  calc
    Artifact.submissionArtifact.instructionPC 2376 =
        Artifact.submissionArtifact.instructionPC 2375 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.SHR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2375 _ (by rfl)
    _ = 3111 := by rw [pc2439]; rfl
@[simp] theorem pc2441 : Artifact.submissionArtifact.instructionPC 2377 = 3112 := by
  calc
    Artifact.submissionArtifact.instructionPC 2377 =
        Artifact.submissionArtifact.instructionPC 2376 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.AND).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2376 _ (by rfl)
    _ = 3112 := by rw [pc2440]; rfl
@[simp] theorem pc2442 : Artifact.submissionArtifact.instructionPC 2378 = 3113 := by
  calc
    Artifact.submissionArtifact.instructionPC 2378 =
        Artifact.submissionArtifact.instructionPC 2377 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 2 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2377 _ (by rfl)
    _ = 3113 := by rw [pc2441]; rfl
@[simp] theorem pc2443 : Artifact.submissionArtifact.instructionPC 2379 = 3114 := by
  calc
    Artifact.submissionArtifact.instructionPC 2379 =
        Artifact.submissionArtifact.instructionPC 2378 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MUL).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2378 _ (by rfl)
    _ = 3114 := by rw [pc2442]; rfl
@[simp] theorem pc2444 : Artifact.submissionArtifact.instructionPC 2380 = 3116 := by
  calc
    Artifact.submissionArtifact.instructionPC 2380 =
        Artifact.submissionArtifact.instructionPC 2379 +
          (YulEvmCompiler.Instr.push 1 1).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2379 _ (by rfl)
    _ = 3116 := by rw [pc2443]; rfl
@[simp] theorem pc2445 : Artifact.submissionArtifact.instructionPC 2381 = 3117 := by
  calc
    Artifact.submissionArtifact.instructionPC 2381 =
        Artifact.submissionArtifact.instructionPC 2380 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.ADD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2380 _ (by rfl)
    _ = 3117 := by rw [pc2444]; rfl
@[simp] theorem pc2446 : Artifact.submissionArtifact.instructionPC 2382 = 3118 := by
  calc
    Artifact.submissionArtifact.instructionPC 2382 =
        Artifact.submissionArtifact.instructionPC 2381 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2381 _ (by rfl)
    _ = 3118 := by rw [pc2445]; rfl
@[simp] theorem pc2447 : Artifact.submissionArtifact.instructionPC 2383 = 3119 := by
  calc
    Artifact.submissionArtifact.instructionPC 2383 =
        Artifact.submissionArtifact.instructionPC 2382 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 8 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2382 _ (by rfl)
    _ = 3119 := by rw [pc2446]; rfl
@[simp] theorem pc2448 : Artifact.submissionArtifact.instructionPC 2384 = 3120 := by
  calc
    Artifact.submissionArtifact.instructionPC 2384 =
        Artifact.submissionArtifact.instructionPC 2383 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 0 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2383 _ (by rfl)
    _ = 3120 := by rw [pc2447]; rfl
@[simp] theorem pc2449 : Artifact.submissionArtifact.instructionPC 2385 = 3121 := by
  calc
    Artifact.submissionArtifact.instructionPC 2385 =
        Artifact.submissionArtifact.instructionPC 2384 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MULMOD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2384 _ (by rfl)
    _ = 3121 := by rw [pc2448]; rfl
@[simp] theorem pc2450 : Artifact.submissionArtifact.instructionPC 2386 = 3122 := by
  calc
    Artifact.submissionArtifact.instructionPC 2386 =
        Artifact.submissionArtifact.instructionPC 2385 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MULMOD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2385 _ (by rfl)
    _ = 3122 := by rw [pc2449]; rfl
@[simp] theorem pc2451 : Artifact.submissionArtifact.instructionPC 2387 = 3123 := by
  calc
    Artifact.submissionArtifact.instructionPC 2387 =
        Artifact.submissionArtifact.instructionPC 2386 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 5 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2386 _ (by rfl)
    _ = 3123 := by rw [pc2450]; rfl
@[simp] theorem pc2452 : Artifact.submissionArtifact.instructionPC 2388 = 3124 := by
  calc
    Artifact.submissionArtifact.instructionPC 2388 =
        Artifact.submissionArtifact.instructionPC 2387 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.POP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2387 _ (by rfl)
    _ = 3124 := by rw [pc2451]; rfl
@[simp] theorem pc2453 : Artifact.submissionArtifact.instructionPC 2389 = 3125 := by
  calc
    Artifact.submissionArtifact.instructionPC 2389 =
        Artifact.submissionArtifact.instructionPC 2388 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 7 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2388 _ (by rfl)
    _ = 3125 := by rw [pc2452]; rfl
@[simp] theorem pc2454 : Artifact.submissionArtifact.instructionPC 2390 = 3127 := by
  calc
    Artifact.submissionArtifact.instructionPC 2390 =
        Artifact.submissionArtifact.instructionPC 2389 +
          (YulEvmCompiler.Instr.push 1 1).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2389 _ (by rfl)
    _ = 3127 := by rw [pc2453]; rfl
@[simp] theorem pc2455 : Artifact.submissionArtifact.instructionPC 2391 = 3128 := by
  calc
    Artifact.submissionArtifact.instructionPC 2391 =
        Artifact.submissionArtifact.instructionPC 2390 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 4 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2390 _ (by rfl)
    _ = 3128 := by rw [pc2454]; rfl
@[simp] theorem pc2456 : Artifact.submissionArtifact.instructionPC 2392 = 3130 := by
  calc
    Artifact.submissionArtifact.instructionPC 2392 =
        Artifact.submissionArtifact.instructionPC 2391 +
          (YulEvmCompiler.Instr.push 1 5).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2391 _ (by rfl)
    _ = 3130 := by rw [pc2455]; rfl
@[simp] theorem pc2457 : Artifact.submissionArtifact.instructionPC 2393 = 3131 := by
  calc
    Artifact.submissionArtifact.instructionPC 2393 =
        Artifact.submissionArtifact.instructionPC 2392 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.SHR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2392 _ (by rfl)
    _ = 3131 := by rw [pc2456]; rfl
@[simp] theorem pc2458 : Artifact.submissionArtifact.instructionPC 2394 = 3132 := by
  calc
    Artifact.submissionArtifact.instructionPC 2394 =
        Artifact.submissionArtifact.instructionPC 2393 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.AND).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2393 _ (by rfl)
    _ = 3132 := by rw [pc2457]; rfl
@[simp] theorem pc2459 : Artifact.submissionArtifact.instructionPC 2395 = 3133 := by
  calc
    Artifact.submissionArtifact.instructionPC 2395 =
        Artifact.submissionArtifact.instructionPC 2394 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 2 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2394 _ (by rfl)
    _ = 3133 := by rw [pc2458]; rfl
@[simp] theorem pc2460 : Artifact.submissionArtifact.instructionPC 2396 = 3134 := by
  calc
    Artifact.submissionArtifact.instructionPC 2396 =
        Artifact.submissionArtifact.instructionPC 2395 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MUL).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2395 _ (by rfl)
    _ = 3134 := by rw [pc2459]; rfl
@[simp] theorem pc2461 : Artifact.submissionArtifact.instructionPC 2397 = 3136 := by
  calc
    Artifact.submissionArtifact.instructionPC 2397 =
        Artifact.submissionArtifact.instructionPC 2396 +
          (YulEvmCompiler.Instr.push 1 1).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2396 _ (by rfl)
    _ = 3136 := by rw [pc2460]; rfl
@[simp] theorem pc2462 : Artifact.submissionArtifact.instructionPC 2398 = 3137 := by
  calc
    Artifact.submissionArtifact.instructionPC 2398 =
        Artifact.submissionArtifact.instructionPC 2397 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.ADD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2397 _ (by rfl)
    _ = 3137 := by rw [pc2461]; rfl
@[simp] theorem pc2463 : Artifact.submissionArtifact.instructionPC 2399 = 3138 := by
  calc
    Artifact.submissionArtifact.instructionPC 2399 =
        Artifact.submissionArtifact.instructionPC 2398 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2398 _ (by rfl)
    _ = 3138 := by rw [pc2462]; rfl
@[simp] theorem pc2464 : Artifact.submissionArtifact.instructionPC 2400 = 3139 := by
  calc
    Artifact.submissionArtifact.instructionPC 2400 =
        Artifact.submissionArtifact.instructionPC 2399 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 8 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2399 _ (by rfl)
    _ = 3139 := by rw [pc2463]; rfl
@[simp] theorem pc2465 : Artifact.submissionArtifact.instructionPC 2401 = 3140 := by
  calc
    Artifact.submissionArtifact.instructionPC 2401 =
        Artifact.submissionArtifact.instructionPC 2400 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 0 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2400 _ (by rfl)
    _ = 3140 := by rw [pc2464]; rfl
@[simp] theorem pc2466 : Artifact.submissionArtifact.instructionPC 2402 = 3141 := by
  calc
    Artifact.submissionArtifact.instructionPC 2402 =
        Artifact.submissionArtifact.instructionPC 2401 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MULMOD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2401 _ (by rfl)
    _ = 3141 := by rw [pc2465]; rfl
@[simp] theorem pc2467 : Artifact.submissionArtifact.instructionPC 2403 = 3142 := by
  calc
    Artifact.submissionArtifact.instructionPC 2403 =
        Artifact.submissionArtifact.instructionPC 2402 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MULMOD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2402 _ (by rfl)
    _ = 3142 := by rw [pc2466]; rfl
@[simp] theorem pc2468 : Artifact.submissionArtifact.instructionPC 2404 = 3143 := by
  calc
    Artifact.submissionArtifact.instructionPC 2404 =
        Artifact.submissionArtifact.instructionPC 2403 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 5 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2403 _ (by rfl)
    _ = 3143 := by rw [pc2467]; rfl
@[simp] theorem pc2469 : Artifact.submissionArtifact.instructionPC 2405 = 3144 := by
  calc
    Artifact.submissionArtifact.instructionPC 2405 =
        Artifact.submissionArtifact.instructionPC 2404 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.POP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2404 _ (by rfl)
    _ = 3144 := by rw [pc2468]; rfl
@[simp] theorem pc2470 : Artifact.submissionArtifact.instructionPC 2406 = 3145 := by
  calc
    Artifact.submissionArtifact.instructionPC 2406 =
        Artifact.submissionArtifact.instructionPC 2405 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 7 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2405 _ (by rfl)
    _ = 3145 := by rw [pc2469]; rfl
@[simp] theorem pc2471 : Artifact.submissionArtifact.instructionPC 2407 = 3147 := by
  calc
    Artifact.submissionArtifact.instructionPC 2407 =
        Artifact.submissionArtifact.instructionPC 2406 +
          (YulEvmCompiler.Instr.push 1 1).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2406 _ (by rfl)
    _ = 3147 := by rw [pc2470]; rfl
@[simp] theorem pc2472 : Artifact.submissionArtifact.instructionPC 2408 = 3148 := by
  calc
    Artifact.submissionArtifact.instructionPC 2408 =
        Artifact.submissionArtifact.instructionPC 2407 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 4 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2407 _ (by rfl)
    _ = 3148 := by rw [pc2471]; rfl
@[simp] theorem pc2473 : Artifact.submissionArtifact.instructionPC 2409 = 3150 := by
  calc
    Artifact.submissionArtifact.instructionPC 2409 =
        Artifact.submissionArtifact.instructionPC 2408 +
          (YulEvmCompiler.Instr.push 1 4).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2408 _ (by rfl)
    _ = 3150 := by rw [pc2472]; rfl
@[simp] theorem pc2474 : Artifact.submissionArtifact.instructionPC 2410 = 3151 := by
  calc
    Artifact.submissionArtifact.instructionPC 2410 =
        Artifact.submissionArtifact.instructionPC 2409 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.SHR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2409 _ (by rfl)
    _ = 3151 := by rw [pc2473]; rfl
@[simp] theorem pc2475 : Artifact.submissionArtifact.instructionPC 2411 = 3152 := by
  calc
    Artifact.submissionArtifact.instructionPC 2411 =
        Artifact.submissionArtifact.instructionPC 2410 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.AND).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2410 _ (by rfl)
    _ = 3152 := by rw [pc2474]; rfl
@[simp] theorem pc2476 : Artifact.submissionArtifact.instructionPC 2412 = 3153 := by
  calc
    Artifact.submissionArtifact.instructionPC 2412 =
        Artifact.submissionArtifact.instructionPC 2411 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 2 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2411 _ (by rfl)
    _ = 3153 := by rw [pc2475]; rfl
@[simp] theorem pc2477 : Artifact.submissionArtifact.instructionPC 2413 = 3154 := by
  calc
    Artifact.submissionArtifact.instructionPC 2413 =
        Artifact.submissionArtifact.instructionPC 2412 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MUL).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2412 _ (by rfl)
    _ = 3154 := by rw [pc2476]; rfl
@[simp] theorem pc2478 : Artifact.submissionArtifact.instructionPC 2414 = 3156 := by
  calc
    Artifact.submissionArtifact.instructionPC 2414 =
        Artifact.submissionArtifact.instructionPC 2413 +
          (YulEvmCompiler.Instr.push 1 1).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2413 _ (by rfl)
    _ = 3156 := by rw [pc2477]; rfl
@[simp] theorem pc2479 : Artifact.submissionArtifact.instructionPC 2415 = 3157 := by
  calc
    Artifact.submissionArtifact.instructionPC 2415 =
        Artifact.submissionArtifact.instructionPC 2414 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.ADD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2414 _ (by rfl)
    _ = 3157 := by rw [pc2478]; rfl
@[simp] theorem pc2480 : Artifact.submissionArtifact.instructionPC 2416 = 3158 := by
  calc
    Artifact.submissionArtifact.instructionPC 2416 =
        Artifact.submissionArtifact.instructionPC 2415 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2415 _ (by rfl)
    _ = 3158 := by rw [pc2479]; rfl
@[simp] theorem pc2481 : Artifact.submissionArtifact.instructionPC 2417 = 3159 := by
  calc
    Artifact.submissionArtifact.instructionPC 2417 =
        Artifact.submissionArtifact.instructionPC 2416 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 8 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2416 _ (by rfl)
    _ = 3159 := by rw [pc2480]; rfl
@[simp] theorem pc2482 : Artifact.submissionArtifact.instructionPC 2418 = 3160 := by
  calc
    Artifact.submissionArtifact.instructionPC 2418 =
        Artifact.submissionArtifact.instructionPC 2417 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 0 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2417 _ (by rfl)
    _ = 3160 := by rw [pc2481]; rfl
@[simp] theorem pc2483 : Artifact.submissionArtifact.instructionPC 2419 = 3161 := by
  calc
    Artifact.submissionArtifact.instructionPC 2419 =
        Artifact.submissionArtifact.instructionPC 2418 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MULMOD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2418 _ (by rfl)
    _ = 3161 := by rw [pc2482]; rfl
@[simp] theorem pc2484 : Artifact.submissionArtifact.instructionPC 2420 = 3162 := by
  calc
    Artifact.submissionArtifact.instructionPC 2420 =
        Artifact.submissionArtifact.instructionPC 2419 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MULMOD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2419 _ (by rfl)
    _ = 3162 := by rw [pc2483]; rfl
@[simp] theorem pc2485 : Artifact.submissionArtifact.instructionPC 2421 = 3163 := by
  calc
    Artifact.submissionArtifact.instructionPC 2421 =
        Artifact.submissionArtifact.instructionPC 2420 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 5 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2420 _ (by rfl)
    _ = 3163 := by rw [pc2484]; rfl
@[simp] theorem pc2486 : Artifact.submissionArtifact.instructionPC 2422 = 3164 := by
  calc
    Artifact.submissionArtifact.instructionPC 2422 =
        Artifact.submissionArtifact.instructionPC 2421 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.POP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2421 _ (by rfl)
    _ = 3164 := by rw [pc2485]; rfl
@[simp] theorem pc2487 : Artifact.submissionArtifact.instructionPC 2423 = 3165 := by
  calc
    Artifact.submissionArtifact.instructionPC 2423 =
        Artifact.submissionArtifact.instructionPC 2422 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 7 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2422 _ (by rfl)
    _ = 3165 := by rw [pc2486]; rfl
@[simp] theorem pc2488 : Artifact.submissionArtifact.instructionPC 2424 = 3167 := by
  calc
    Artifact.submissionArtifact.instructionPC 2424 =
        Artifact.submissionArtifact.instructionPC 2423 +
          (YulEvmCompiler.Instr.push 1 1).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2423 _ (by rfl)
    _ = 3167 := by rw [pc2487]; rfl
@[simp] theorem pc2489 : Artifact.submissionArtifact.instructionPC 2425 = 3168 := by
  calc
    Artifact.submissionArtifact.instructionPC 2425 =
        Artifact.submissionArtifact.instructionPC 2424 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 4 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2424 _ (by rfl)
    _ = 3168 := by rw [pc2488]; rfl
@[simp] theorem pc2490 : Artifact.submissionArtifact.instructionPC 2426 = 3170 := by
  calc
    Artifact.submissionArtifact.instructionPC 2426 =
        Artifact.submissionArtifact.instructionPC 2425 +
          (YulEvmCompiler.Instr.push 1 3).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2425 _ (by rfl)
    _ = 3170 := by rw [pc2489]; rfl
@[simp] theorem pc2491 : Artifact.submissionArtifact.instructionPC 2427 = 3171 := by
  calc
    Artifact.submissionArtifact.instructionPC 2427 =
        Artifact.submissionArtifact.instructionPC 2426 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.SHR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2426 _ (by rfl)
    _ = 3171 := by rw [pc2490]; rfl
@[simp] theorem pc2492 : Artifact.submissionArtifact.instructionPC 2428 = 3172 := by
  calc
    Artifact.submissionArtifact.instructionPC 2428 =
        Artifact.submissionArtifact.instructionPC 2427 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.AND).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2427 _ (by rfl)
    _ = 3172 := by rw [pc2491]; rfl
@[simp] theorem pc2493 : Artifact.submissionArtifact.instructionPC 2429 = 3173 := by
  calc
    Artifact.submissionArtifact.instructionPC 2429 =
        Artifact.submissionArtifact.instructionPC 2428 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 2 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2428 _ (by rfl)
    _ = 3173 := by rw [pc2492]; rfl
@[simp] theorem pc2494 : Artifact.submissionArtifact.instructionPC 2430 = 3174 := by
  calc
    Artifact.submissionArtifact.instructionPC 2430 =
        Artifact.submissionArtifact.instructionPC 2429 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MUL).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2429 _ (by rfl)
    _ = 3174 := by rw [pc2493]; rfl
@[simp] theorem pc2495 : Artifact.submissionArtifact.instructionPC 2431 = 3176 := by
  calc
    Artifact.submissionArtifact.instructionPC 2431 =
        Artifact.submissionArtifact.instructionPC 2430 +
          (YulEvmCompiler.Instr.push 1 1).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2430 _ (by rfl)
    _ = 3176 := by rw [pc2494]; rfl
@[simp] theorem pc2496 : Artifact.submissionArtifact.instructionPC 2432 = 3177 := by
  calc
    Artifact.submissionArtifact.instructionPC 2432 =
        Artifact.submissionArtifact.instructionPC 2431 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.ADD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2431 _ (by rfl)
    _ = 3177 := by rw [pc2495]; rfl
@[simp] theorem pc2497 : Artifact.submissionArtifact.instructionPC 2433 = 3178 := by
  calc
    Artifact.submissionArtifact.instructionPC 2433 =
        Artifact.submissionArtifact.instructionPC 2432 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2432 _ (by rfl)
    _ = 3178 := by rw [pc2496]; rfl
@[simp] theorem pc2498 : Artifact.submissionArtifact.instructionPC 2434 = 3179 := by
  calc
    Artifact.submissionArtifact.instructionPC 2434 =
        Artifact.submissionArtifact.instructionPC 2433 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 8 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2433 _ (by rfl)
    _ = 3179 := by rw [pc2497]; rfl
@[simp] theorem pc2499 : Artifact.submissionArtifact.instructionPC 2435 = 3180 := by
  calc
    Artifact.submissionArtifact.instructionPC 2435 =
        Artifact.submissionArtifact.instructionPC 2434 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 0 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2434 _ (by rfl)
    _ = 3180 := by rw [pc2498]; rfl
@[simp] theorem pc2500 : Artifact.submissionArtifact.instructionPC 2436 = 3181 := by
  calc
    Artifact.submissionArtifact.instructionPC 2436 =
        Artifact.submissionArtifact.instructionPC 2435 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MULMOD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2435 _ (by rfl)
    _ = 3181 := by rw [pc2499]; rfl
@[simp] theorem pc2501 : Artifact.submissionArtifact.instructionPC 2437 = 3182 := by
  calc
    Artifact.submissionArtifact.instructionPC 2437 =
        Artifact.submissionArtifact.instructionPC 2436 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MULMOD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2436 _ (by rfl)
    _ = 3182 := by rw [pc2500]; rfl
@[simp] theorem pc2502 : Artifact.submissionArtifact.instructionPC 2438 = 3183 := by
  calc
    Artifact.submissionArtifact.instructionPC 2438 =
        Artifact.submissionArtifact.instructionPC 2437 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 5 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2437 _ (by rfl)
    _ = 3183 := by rw [pc2501]; rfl
@[simp] theorem pc2503 : Artifact.submissionArtifact.instructionPC 2439 = 3184 := by
  calc
    Artifact.submissionArtifact.instructionPC 2439 =
        Artifact.submissionArtifact.instructionPC 2438 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.POP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2438 _ (by rfl)
    _ = 3184 := by rw [pc2502]; rfl
@[simp] theorem pc2504 : Artifact.submissionArtifact.instructionPC 2440 = 3185 := by
  calc
    Artifact.submissionArtifact.instructionPC 2440 =
        Artifact.submissionArtifact.instructionPC 2439 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 7 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2439 _ (by rfl)
    _ = 3185 := by rw [pc2503]; rfl
@[simp] theorem pc2505 : Artifact.submissionArtifact.instructionPC 2441 = 3187 := by
  calc
    Artifact.submissionArtifact.instructionPC 2441 =
        Artifact.submissionArtifact.instructionPC 2440 +
          (YulEvmCompiler.Instr.push 1 1).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2440 _ (by rfl)
    _ = 3187 := by rw [pc2504]; rfl
@[simp] theorem pc2506 : Artifact.submissionArtifact.instructionPC 2442 = 3188 := by
  calc
    Artifact.submissionArtifact.instructionPC 2442 =
        Artifact.submissionArtifact.instructionPC 2441 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 4 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2441 _ (by rfl)
    _ = 3188 := by rw [pc2505]; rfl
@[simp] theorem pc2507 : Artifact.submissionArtifact.instructionPC 2443 = 3190 := by
  calc
    Artifact.submissionArtifact.instructionPC 2443 =
        Artifact.submissionArtifact.instructionPC 2442 +
          (YulEvmCompiler.Instr.push 1 2).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2442 _ (by rfl)
    _ = 3190 := by rw [pc2506]; rfl
@[simp] theorem pc2508 : Artifact.submissionArtifact.instructionPC 2444 = 3191 := by
  calc
    Artifact.submissionArtifact.instructionPC 2444 =
        Artifact.submissionArtifact.instructionPC 2443 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.SHR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2443 _ (by rfl)
    _ = 3191 := by rw [pc2507]; rfl
@[simp] theorem pc2509 : Artifact.submissionArtifact.instructionPC 2445 = 3192 := by
  calc
    Artifact.submissionArtifact.instructionPC 2445 =
        Artifact.submissionArtifact.instructionPC 2444 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.AND).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2444 _ (by rfl)
    _ = 3192 := by rw [pc2508]; rfl
@[simp] theorem pc2510 : Artifact.submissionArtifact.instructionPC 2446 = 3193 := by
  calc
    Artifact.submissionArtifact.instructionPC 2446 =
        Artifact.submissionArtifact.instructionPC 2445 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 2 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2445 _ (by rfl)
    _ = 3193 := by rw [pc2509]; rfl
@[simp] theorem pc2511 : Artifact.submissionArtifact.instructionPC 2447 = 3194 := by
  calc
    Artifact.submissionArtifact.instructionPC 2447 =
        Artifact.submissionArtifact.instructionPC 2446 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MUL).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2446 _ (by rfl)
    _ = 3194 := by rw [pc2510]; rfl
@[simp] theorem pc2512 : Artifact.submissionArtifact.instructionPC 2448 = 3196 := by
  calc
    Artifact.submissionArtifact.instructionPC 2448 =
        Artifact.submissionArtifact.instructionPC 2447 +
          (YulEvmCompiler.Instr.push 1 1).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2447 _ (by rfl)
    _ = 3196 := by rw [pc2511]; rfl
@[simp] theorem pc2513 : Artifact.submissionArtifact.instructionPC 2449 = 3197 := by
  calc
    Artifact.submissionArtifact.instructionPC 2449 =
        Artifact.submissionArtifact.instructionPC 2448 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.ADD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2448 _ (by rfl)
    _ = 3197 := by rw [pc2512]; rfl
@[simp] theorem pc2514 : Artifact.submissionArtifact.instructionPC 2450 = 3198 := by
  calc
    Artifact.submissionArtifact.instructionPC 2450 =
        Artifact.submissionArtifact.instructionPC 2449 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2449 _ (by rfl)
    _ = 3198 := by rw [pc2513]; rfl
@[simp] theorem pc2515 : Artifact.submissionArtifact.instructionPC 2451 = 3199 := by
  calc
    Artifact.submissionArtifact.instructionPC 2451 =
        Artifact.submissionArtifact.instructionPC 2450 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 8 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2450 _ (by rfl)
    _ = 3199 := by rw [pc2514]; rfl
@[simp] theorem pc2516 : Artifact.submissionArtifact.instructionPC 2452 = 3200 := by
  calc
    Artifact.submissionArtifact.instructionPC 2452 =
        Artifact.submissionArtifact.instructionPC 2451 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 0 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2451 _ (by rfl)
    _ = 3200 := by rw [pc2515]; rfl
@[simp] theorem pc2517 : Artifact.submissionArtifact.instructionPC 2453 = 3201 := by
  calc
    Artifact.submissionArtifact.instructionPC 2453 =
        Artifact.submissionArtifact.instructionPC 2452 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MULMOD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2452 _ (by rfl)
    _ = 3201 := by rw [pc2516]; rfl
@[simp] theorem pc2518 : Artifact.submissionArtifact.instructionPC 2454 = 3202 := by
  calc
    Artifact.submissionArtifact.instructionPC 2454 =
        Artifact.submissionArtifact.instructionPC 2453 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MULMOD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2453 _ (by rfl)
    _ = 3202 := by rw [pc2517]; rfl
@[simp] theorem pc2519 : Artifact.submissionArtifact.instructionPC 2455 = 3203 := by
  calc
    Artifact.submissionArtifact.instructionPC 2455 =
        Artifact.submissionArtifact.instructionPC 2454 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 5 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2454 _ (by rfl)
    _ = 3203 := by rw [pc2518]; rfl
@[simp] theorem pc2520 : Artifact.submissionArtifact.instructionPC 2456 = 3204 := by
  calc
    Artifact.submissionArtifact.instructionPC 2456 =
        Artifact.submissionArtifact.instructionPC 2455 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.POP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2455 _ (by rfl)
    _ = 3204 := by rw [pc2519]; rfl
@[simp] theorem pc2521 : Artifact.submissionArtifact.instructionPC 2457 = 3205 := by
  calc
    Artifact.submissionArtifact.instructionPC 2457 =
        Artifact.submissionArtifact.instructionPC 2456 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 7 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2456 _ (by rfl)
    _ = 3205 := by rw [pc2520]; rfl
@[simp] theorem pc2522 : Artifact.submissionArtifact.instructionPC 2458 = 3207 := by
  calc
    Artifact.submissionArtifact.instructionPC 2458 =
        Artifact.submissionArtifact.instructionPC 2457 +
          (YulEvmCompiler.Instr.push 1 1).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2457 _ (by rfl)
    _ = 3207 := by rw [pc2521]; rfl
@[simp] theorem pc2523 : Artifact.submissionArtifact.instructionPC 2459 = 3208 := by
  calc
    Artifact.submissionArtifact.instructionPC 2459 =
        Artifact.submissionArtifact.instructionPC 2458 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 4 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2458 _ (by rfl)
    _ = 3208 := by rw [pc2522]; rfl
@[simp] theorem pc2524 : Artifact.submissionArtifact.instructionPC 2460 = 3210 := by
  calc
    Artifact.submissionArtifact.instructionPC 2460 =
        Artifact.submissionArtifact.instructionPC 2459 +
          (YulEvmCompiler.Instr.push 1 1).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2459 _ (by rfl)
    _ = 3210 := by rw [pc2523]; rfl
@[simp] theorem pc2525 : Artifact.submissionArtifact.instructionPC 2461 = 3211 := by
  calc
    Artifact.submissionArtifact.instructionPC 2461 =
        Artifact.submissionArtifact.instructionPC 2460 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.SHR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2460 _ (by rfl)
    _ = 3211 := by rw [pc2524]; rfl
@[simp] theorem pc2526 : Artifact.submissionArtifact.instructionPC 2462 = 3212 := by
  calc
    Artifact.submissionArtifact.instructionPC 2462 =
        Artifact.submissionArtifact.instructionPC 2461 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.AND).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2461 _ (by rfl)
    _ = 3212 := by rw [pc2525]; rfl
@[simp] theorem pc2527 : Artifact.submissionArtifact.instructionPC 2463 = 3213 := by
  calc
    Artifact.submissionArtifact.instructionPC 2463 =
        Artifact.submissionArtifact.instructionPC 2462 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 2 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2462 _ (by rfl)
    _ = 3213 := by rw [pc2526]; rfl
@[simp] theorem pc2528 : Artifact.submissionArtifact.instructionPC 2464 = 3214 := by
  calc
    Artifact.submissionArtifact.instructionPC 2464 =
        Artifact.submissionArtifact.instructionPC 2463 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MUL).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2463 _ (by rfl)
    _ = 3214 := by rw [pc2527]; rfl
@[simp] theorem pc2529 : Artifact.submissionArtifact.instructionPC 2465 = 3216 := by
  calc
    Artifact.submissionArtifact.instructionPC 2465 =
        Artifact.submissionArtifact.instructionPC 2464 +
          (YulEvmCompiler.Instr.push 1 1).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2464 _ (by rfl)
    _ = 3216 := by rw [pc2528]; rfl
@[simp] theorem pc2530 : Artifact.submissionArtifact.instructionPC 2466 = 3217 := by
  calc
    Artifact.submissionArtifact.instructionPC 2466 =
        Artifact.submissionArtifact.instructionPC 2465 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.ADD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2465 _ (by rfl)
    _ = 3217 := by rw [pc2529]; rfl
@[simp] theorem pc2531 : Artifact.submissionArtifact.instructionPC 2467 = 3218 := by
  calc
    Artifact.submissionArtifact.instructionPC 2467 =
        Artifact.submissionArtifact.instructionPC 2466 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2466 _ (by rfl)
    _ = 3218 := by rw [pc2530]; rfl
@[simp] theorem pc2532 : Artifact.submissionArtifact.instructionPC 2468 = 3219 := by
  calc
    Artifact.submissionArtifact.instructionPC 2468 =
        Artifact.submissionArtifact.instructionPC 2467 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 8 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2467 _ (by rfl)
    _ = 3219 := by rw [pc2531]; rfl
@[simp] theorem pc2533 : Artifact.submissionArtifact.instructionPC 2469 = 3220 := by
  calc
    Artifact.submissionArtifact.instructionPC 2469 =
        Artifact.submissionArtifact.instructionPC 2468 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 0 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2468 _ (by rfl)
    _ = 3220 := by rw [pc2532]; rfl
@[simp] theorem pc2534 : Artifact.submissionArtifact.instructionPC 2470 = 3221 := by
  calc
    Artifact.submissionArtifact.instructionPC 2470 =
        Artifact.submissionArtifact.instructionPC 2469 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MULMOD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2469 _ (by rfl)
    _ = 3221 := by rw [pc2533]; rfl
@[simp] theorem pc2535 : Artifact.submissionArtifact.instructionPC 2471 = 3222 := by
  calc
    Artifact.submissionArtifact.instructionPC 2471 =
        Artifact.submissionArtifact.instructionPC 2470 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MULMOD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2470 _ (by rfl)
    _ = 3222 := by rw [pc2534]; rfl
@[simp] theorem pc2536 : Artifact.submissionArtifact.instructionPC 2472 = 3223 := by
  calc
    Artifact.submissionArtifact.instructionPC 2472 =
        Artifact.submissionArtifact.instructionPC 2471 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 5 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2471 _ (by rfl)
    _ = 3223 := by rw [pc2535]; rfl
@[simp] theorem pc2537 : Artifact.submissionArtifact.instructionPC 2473 = 3224 := by
  calc
    Artifact.submissionArtifact.instructionPC 2473 =
        Artifact.submissionArtifact.instructionPC 2472 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.POP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2472 _ (by rfl)
    _ = 3224 := by rw [pc2536]; rfl
@[simp] theorem pc2538 : Artifact.submissionArtifact.instructionPC 2474 = 3225 := by
  calc
    Artifact.submissionArtifact.instructionPC 2474 =
        Artifact.submissionArtifact.instructionPC 2473 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 7 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2473 _ (by rfl)
    _ = 3225 := by rw [pc2537]; rfl
@[simp] theorem pc2539 : Artifact.submissionArtifact.instructionPC 2475 = 3227 := by
  calc
    Artifact.submissionArtifact.instructionPC 2475 =
        Artifact.submissionArtifact.instructionPC 2474 +
          (YulEvmCompiler.Instr.push 1 1).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2474 _ (by rfl)
    _ = 3227 := by rw [pc2538]; rfl
@[simp] theorem pc2542 : Artifact.submissionArtifact.instructionPC 2476 = 3228 := by
  calc
    Artifact.submissionArtifact.instructionPC 2476 =
        Artifact.submissionArtifact.instructionPC 2475 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 4 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2475 _ (by rfl)
    _ = 3228 := by rw [pc2539]; rfl
@[simp] theorem pc2543 : Artifact.submissionArtifact.instructionPC 2477 = 3229 := by
  calc
    Artifact.submissionArtifact.instructionPC 2477 =
        Artifact.submissionArtifact.instructionPC 2476 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.AND).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2476 _ (by rfl)
    _ = 3229 := by rw [pc2542]; rfl
@[simp] theorem pc2544 : Artifact.submissionArtifact.instructionPC 2478 = 3230 := by
  calc
    Artifact.submissionArtifact.instructionPC 2478 =
        Artifact.submissionArtifact.instructionPC 2477 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 2 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2477 _ (by rfl)
    _ = 3230 := by rw [pc2543]; rfl
@[simp] theorem pc2545 : Artifact.submissionArtifact.instructionPC 2479 = 3231 := by
  calc
    Artifact.submissionArtifact.instructionPC 2479 =
        Artifact.submissionArtifact.instructionPC 2478 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MUL).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2478 _ (by rfl)
    _ = 3231 := by rw [pc2544]; rfl
@[simp] theorem pc2546 : Artifact.submissionArtifact.instructionPC 2480 = 3233 := by
  calc
    Artifact.submissionArtifact.instructionPC 2480 =
        Artifact.submissionArtifact.instructionPC 2479 +
          (YulEvmCompiler.Instr.push 1 1).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2479 _ (by rfl)
    _ = 3233 := by rw [pc2545]; rfl
@[simp] theorem pc2547 : Artifact.submissionArtifact.instructionPC 2481 = 3234 := by
  calc
    Artifact.submissionArtifact.instructionPC 2481 =
        Artifact.submissionArtifact.instructionPC 2480 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.ADD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2480 _ (by rfl)
    _ = 3234 := by rw [pc2546]; rfl
@[simp] theorem pc2548 : Artifact.submissionArtifact.instructionPC 2482 = 3235 := by
  calc
    Artifact.submissionArtifact.instructionPC 2482 =
        Artifact.submissionArtifact.instructionPC 2481 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2481 _ (by rfl)
    _ = 3235 := by rw [pc2547]; rfl
@[simp] theorem pc2549 : Artifact.submissionArtifact.instructionPC 2483 = 3236 := by
  calc
    Artifact.submissionArtifact.instructionPC 2483 =
        Artifact.submissionArtifact.instructionPC 2482 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 8 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2482 _ (by rfl)
    _ = 3236 := by rw [pc2548]; rfl
@[simp] theorem pc2550 : Artifact.submissionArtifact.instructionPC 2484 = 3237 := by
  calc
    Artifact.submissionArtifact.instructionPC 2484 =
        Artifact.submissionArtifact.instructionPC 2483 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 0 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2483 _ (by rfl)
    _ = 3237 := by rw [pc2549]; rfl
@[simp] theorem pc2551 : Artifact.submissionArtifact.instructionPC 2485 = 3238 := by
  calc
    Artifact.submissionArtifact.instructionPC 2485 =
        Artifact.submissionArtifact.instructionPC 2484 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MULMOD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2484 _ (by rfl)
    _ = 3238 := by rw [pc2550]; rfl
@[simp] theorem pc2552 : Artifact.submissionArtifact.instructionPC 2486 = 3239 := by
  calc
    Artifact.submissionArtifact.instructionPC 2486 =
        Artifact.submissionArtifact.instructionPC 2485 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MULMOD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2485 _ (by rfl)
    _ = 3239 := by rw [pc2551]; rfl
@[simp] theorem pc2553 : Artifact.submissionArtifact.instructionPC 2487 = 3240 := by
  calc
    Artifact.submissionArtifact.instructionPC 2487 =
        Artifact.submissionArtifact.instructionPC 2486 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 5 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2486 _ (by rfl)
    _ = 3240 := by rw [pc2552]; rfl
@[simp] theorem pc2554 : Artifact.submissionArtifact.instructionPC 2488 = 3241 := by
  calc
    Artifact.submissionArtifact.instructionPC 2488 =
        Artifact.submissionArtifact.instructionPC 2487 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.POP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2487 _ (by rfl)
    _ = 3241 := by rw [pc2553]; rfl
@[simp] theorem pc2555 : Artifact.submissionArtifact.instructionPC 2489 = 3242 := by
  calc
    Artifact.submissionArtifact.instructionPC 2489 =
        Artifact.submissionArtifact.instructionPC 2488 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.POP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2488 _ (by rfl)
    _ = 3242 := by rw [pc2554]; rfl
@[simp] theorem pc2556 : Artifact.submissionArtifact.instructionPC 2490 = 3245 := by
  calc
    Artifact.submissionArtifact.instructionPC 2490 =
        Artifact.submissionArtifact.instructionPC 2489 +
          (YulEvmCompiler.Instr.push 2 692).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2489 _ (by rfl)
    _ = 3245 := by rw [pc2555]; rfl

end Challenge.Modexp.Submission.Proofs.Bytecode.UnrollPCs
