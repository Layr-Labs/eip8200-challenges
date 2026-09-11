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

@[simp] theorem pc485 : Artifact.submissionArtifact.instructionPC 462 = 553 := by rfl
@[simp] theorem pc486 : Artifact.submissionArtifact.instructionPC 463 = 556 := by
  calc
    Artifact.submissionArtifact.instructionPC 463 =
        Artifact.submissionArtifact.instructionPC 462 +
          (YulEvmCompiler.Instr.push 2 2985).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 462 _ (by rfl)
    _ = 556 := by rw [pc485]; rfl
@[simp] theorem pc2414 : Artifact.submissionArtifact.instructionPC 2298 = 2985 := by rfl
@[simp] theorem pc2415 : Artifact.submissionArtifact.instructionPC 2299 = 2986 := by
  calc
    Artifact.submissionArtifact.instructionPC 2299 =
        Artifact.submissionArtifact.instructionPC 2298 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.JUMPDEST).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2298 _ (by rfl)
    _ = 2986 := by rw [pc2414]; rfl
@[simp] theorem pc2416 : Artifact.submissionArtifact.instructionPC 2300 = 2988 := by
  calc
    Artifact.submissionArtifact.instructionPC 2300 =
        Artifact.submissionArtifact.instructionPC 2299 +
          (YulEvmCompiler.Instr.push 1 1).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2299 _ (by rfl)
    _ = 2988 := by rw [pc2415]; rfl
@[simp] theorem pc2417 : Artifact.submissionArtifact.instructionPC 2301 = 2989 := by
  calc
    Artifact.submissionArtifact.instructionPC 2301 =
        Artifact.submissionArtifact.instructionPC 2300 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 6 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2300 _ (by rfl)
    _ = 2989 := by rw [pc2416]; rfl
@[simp] theorem pc2418 : Artifact.submissionArtifact.instructionPC 2302 = 2990 := by
  calc
    Artifact.submissionArtifact.instructionPC 2302 =
        Artifact.submissionArtifact.instructionPC 2301 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2301 _ (by rfl)
    _ = 2990 := by rw [pc2417]; rfl
@[simp] theorem pc2419 : Artifact.submissionArtifact.instructionPC 2303 = 2991 := by
  calc
    Artifact.submissionArtifact.instructionPC 2303 =
        Artifact.submissionArtifact.instructionPC 2302 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 7 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2302 _ (by rfl)
    _ = 2991 := by rw [pc2418]; rfl
@[simp] theorem pc2420 : Artifact.submissionArtifact.instructionPC 2304 = 2993 := by
  calc
    Artifact.submissionArtifact.instructionPC 2304 =
        Artifact.submissionArtifact.instructionPC 2303 +
          (YulEvmCompiler.Instr.push 1 1).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2303 _ (by rfl)
    _ = 2993 := by rw [pc2419]; rfl
@[simp] theorem pc2421 : Artifact.submissionArtifact.instructionPC 2305 = 2994 := by
  calc
    Artifact.submissionArtifact.instructionPC 2305 =
        Artifact.submissionArtifact.instructionPC 2304 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 4 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2304 _ (by rfl)
    _ = 2994 := by rw [pc2420]; rfl
@[simp] theorem pc2422 : Artifact.submissionArtifact.instructionPC 2306 = 2996 := by
  calc
    Artifact.submissionArtifact.instructionPC 2306 =
        Artifact.submissionArtifact.instructionPC 2305 +
          (YulEvmCompiler.Instr.push 1 7).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2305 _ (by rfl)
    _ = 2996 := by rw [pc2421]; rfl
@[simp] theorem pc2423 : Artifact.submissionArtifact.instructionPC 2307 = 2997 := by
  calc
    Artifact.submissionArtifact.instructionPC 2307 =
        Artifact.submissionArtifact.instructionPC 2306 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.SHR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2306 _ (by rfl)
    _ = 2997 := by rw [pc2422]; rfl
@[simp] theorem pc2424 : Artifact.submissionArtifact.instructionPC 2308 = 2998 := by
  calc
    Artifact.submissionArtifact.instructionPC 2308 =
        Artifact.submissionArtifact.instructionPC 2307 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.AND).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2307 _ (by rfl)
    _ = 2998 := by rw [pc2423]; rfl
@[simp] theorem pc2425 : Artifact.submissionArtifact.instructionPC 2309 = 2999 := by
  calc
    Artifact.submissionArtifact.instructionPC 2309 =
        Artifact.submissionArtifact.instructionPC 2308 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 2 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2308 _ (by rfl)
    _ = 2999 := by rw [pc2424]; rfl
@[simp] theorem pc2426 : Artifact.submissionArtifact.instructionPC 2310 = 3000 := by
  calc
    Artifact.submissionArtifact.instructionPC 2310 =
        Artifact.submissionArtifact.instructionPC 2309 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MUL).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2309 _ (by rfl)
    _ = 3000 := by rw [pc2425]; rfl
@[simp] theorem pc2427 : Artifact.submissionArtifact.instructionPC 2311 = 3002 := by
  calc
    Artifact.submissionArtifact.instructionPC 2311 =
        Artifact.submissionArtifact.instructionPC 2310 +
          (YulEvmCompiler.Instr.push 1 1).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2310 _ (by rfl)
    _ = 3002 := by rw [pc2426]; rfl
@[simp] theorem pc2428 : Artifact.submissionArtifact.instructionPC 2312 = 3003 := by
  calc
    Artifact.submissionArtifact.instructionPC 2312 =
        Artifact.submissionArtifact.instructionPC 2311 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.ADD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2311 _ (by rfl)
    _ = 3003 := by rw [pc2427]; rfl
@[simp] theorem pc2429 : Artifact.submissionArtifact.instructionPC 2313 = 3004 := by
  calc
    Artifact.submissionArtifact.instructionPC 2313 =
        Artifact.submissionArtifact.instructionPC 2312 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2312 _ (by rfl)
    _ = 3004 := by rw [pc2428]; rfl
@[simp] theorem pc2430 : Artifact.submissionArtifact.instructionPC 2314 = 3005 := by
  calc
    Artifact.submissionArtifact.instructionPC 2314 =
        Artifact.submissionArtifact.instructionPC 2313 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 8 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2313 _ (by rfl)
    _ = 3005 := by rw [pc2429]; rfl
@[simp] theorem pc2431 : Artifact.submissionArtifact.instructionPC 2315 = 3006 := by
  calc
    Artifact.submissionArtifact.instructionPC 2315 =
        Artifact.submissionArtifact.instructionPC 2314 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 0 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2314 _ (by rfl)
    _ = 3006 := by rw [pc2430]; rfl
@[simp] theorem pc2432 : Artifact.submissionArtifact.instructionPC 2316 = 3007 := by
  calc
    Artifact.submissionArtifact.instructionPC 2316 =
        Artifact.submissionArtifact.instructionPC 2315 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MULMOD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2315 _ (by rfl)
    _ = 3007 := by rw [pc2431]; rfl
@[simp] theorem pc2433 : Artifact.submissionArtifact.instructionPC 2317 = 3008 := by
  calc
    Artifact.submissionArtifact.instructionPC 2317 =
        Artifact.submissionArtifact.instructionPC 2316 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MULMOD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2316 _ (by rfl)
    _ = 3008 := by rw [pc2432]; rfl
@[simp] theorem pc2434 : Artifact.submissionArtifact.instructionPC 2318 = 3009 := by
  calc
    Artifact.submissionArtifact.instructionPC 2318 =
        Artifact.submissionArtifact.instructionPC 2317 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 5 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2317 _ (by rfl)
    _ = 3009 := by rw [pc2433]; rfl
@[simp] theorem pc2435 : Artifact.submissionArtifact.instructionPC 2319 = 3010 := by
  calc
    Artifact.submissionArtifact.instructionPC 2319 =
        Artifact.submissionArtifact.instructionPC 2318 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.POP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2318 _ (by rfl)
    _ = 3010 := by rw [pc2434]; rfl
@[simp] theorem pc2436 : Artifact.submissionArtifact.instructionPC 2320 = 3011 := by
  calc
    Artifact.submissionArtifact.instructionPC 2320 =
        Artifact.submissionArtifact.instructionPC 2319 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 7 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2319 _ (by rfl)
    _ = 3011 := by rw [pc2435]; rfl
@[simp] theorem pc2437 : Artifact.submissionArtifact.instructionPC 2321 = 3013 := by
  calc
    Artifact.submissionArtifact.instructionPC 2321 =
        Artifact.submissionArtifact.instructionPC 2320 +
          (YulEvmCompiler.Instr.push 1 1).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2320 _ (by rfl)
    _ = 3013 := by rw [pc2436]; rfl
@[simp] theorem pc2438 : Artifact.submissionArtifact.instructionPC 2322 = 3014 := by
  calc
    Artifact.submissionArtifact.instructionPC 2322 =
        Artifact.submissionArtifact.instructionPC 2321 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 4 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2321 _ (by rfl)
    _ = 3014 := by rw [pc2437]; rfl
@[simp] theorem pc2439 : Artifact.submissionArtifact.instructionPC 2323 = 3016 := by
  calc
    Artifact.submissionArtifact.instructionPC 2323 =
        Artifact.submissionArtifact.instructionPC 2322 +
          (YulEvmCompiler.Instr.push 1 6).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2322 _ (by rfl)
    _ = 3016 := by rw [pc2438]; rfl
@[simp] theorem pc2440 : Artifact.submissionArtifact.instructionPC 2324 = 3017 := by
  calc
    Artifact.submissionArtifact.instructionPC 2324 =
        Artifact.submissionArtifact.instructionPC 2323 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.SHR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2323 _ (by rfl)
    _ = 3017 := by rw [pc2439]; rfl
@[simp] theorem pc2441 : Artifact.submissionArtifact.instructionPC 2325 = 3018 := by
  calc
    Artifact.submissionArtifact.instructionPC 2325 =
        Artifact.submissionArtifact.instructionPC 2324 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.AND).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2324 _ (by rfl)
    _ = 3018 := by rw [pc2440]; rfl
@[simp] theorem pc2442 : Artifact.submissionArtifact.instructionPC 2326 = 3019 := by
  calc
    Artifact.submissionArtifact.instructionPC 2326 =
        Artifact.submissionArtifact.instructionPC 2325 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 2 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2325 _ (by rfl)
    _ = 3019 := by rw [pc2441]; rfl
@[simp] theorem pc2443 : Artifact.submissionArtifact.instructionPC 2327 = 3020 := by
  calc
    Artifact.submissionArtifact.instructionPC 2327 =
        Artifact.submissionArtifact.instructionPC 2326 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MUL).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2326 _ (by rfl)
    _ = 3020 := by rw [pc2442]; rfl
@[simp] theorem pc2444 : Artifact.submissionArtifact.instructionPC 2328 = 3022 := by
  calc
    Artifact.submissionArtifact.instructionPC 2328 =
        Artifact.submissionArtifact.instructionPC 2327 +
          (YulEvmCompiler.Instr.push 1 1).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2327 _ (by rfl)
    _ = 3022 := by rw [pc2443]; rfl
@[simp] theorem pc2445 : Artifact.submissionArtifact.instructionPC 2329 = 3023 := by
  calc
    Artifact.submissionArtifact.instructionPC 2329 =
        Artifact.submissionArtifact.instructionPC 2328 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.ADD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2328 _ (by rfl)
    _ = 3023 := by rw [pc2444]; rfl
@[simp] theorem pc2446 : Artifact.submissionArtifact.instructionPC 2330 = 3024 := by
  calc
    Artifact.submissionArtifact.instructionPC 2330 =
        Artifact.submissionArtifact.instructionPC 2329 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2329 _ (by rfl)
    _ = 3024 := by rw [pc2445]; rfl
@[simp] theorem pc2447 : Artifact.submissionArtifact.instructionPC 2331 = 3025 := by
  calc
    Artifact.submissionArtifact.instructionPC 2331 =
        Artifact.submissionArtifact.instructionPC 2330 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 8 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2330 _ (by rfl)
    _ = 3025 := by rw [pc2446]; rfl
@[simp] theorem pc2448 : Artifact.submissionArtifact.instructionPC 2332 = 3026 := by
  calc
    Artifact.submissionArtifact.instructionPC 2332 =
        Artifact.submissionArtifact.instructionPC 2331 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 0 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2331 _ (by rfl)
    _ = 3026 := by rw [pc2447]; rfl
@[simp] theorem pc2449 : Artifact.submissionArtifact.instructionPC 2333 = 3027 := by
  calc
    Artifact.submissionArtifact.instructionPC 2333 =
        Artifact.submissionArtifact.instructionPC 2332 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MULMOD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2332 _ (by rfl)
    _ = 3027 := by rw [pc2448]; rfl
@[simp] theorem pc2450 : Artifact.submissionArtifact.instructionPC 2334 = 3028 := by
  calc
    Artifact.submissionArtifact.instructionPC 2334 =
        Artifact.submissionArtifact.instructionPC 2333 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MULMOD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2333 _ (by rfl)
    _ = 3028 := by rw [pc2449]; rfl
@[simp] theorem pc2451 : Artifact.submissionArtifact.instructionPC 2335 = 3029 := by
  calc
    Artifact.submissionArtifact.instructionPC 2335 =
        Artifact.submissionArtifact.instructionPC 2334 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 5 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2334 _ (by rfl)
    _ = 3029 := by rw [pc2450]; rfl
@[simp] theorem pc2452 : Artifact.submissionArtifact.instructionPC 2336 = 3030 := by
  calc
    Artifact.submissionArtifact.instructionPC 2336 =
        Artifact.submissionArtifact.instructionPC 2335 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.POP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2335 _ (by rfl)
    _ = 3030 := by rw [pc2451]; rfl
@[simp] theorem pc2453 : Artifact.submissionArtifact.instructionPC 2337 = 3031 := by
  calc
    Artifact.submissionArtifact.instructionPC 2337 =
        Artifact.submissionArtifact.instructionPC 2336 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 7 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2336 _ (by rfl)
    _ = 3031 := by rw [pc2452]; rfl
@[simp] theorem pc2454 : Artifact.submissionArtifact.instructionPC 2338 = 3033 := by
  calc
    Artifact.submissionArtifact.instructionPC 2338 =
        Artifact.submissionArtifact.instructionPC 2337 +
          (YulEvmCompiler.Instr.push 1 1).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2337 _ (by rfl)
    _ = 3033 := by rw [pc2453]; rfl
@[simp] theorem pc2455 : Artifact.submissionArtifact.instructionPC 2339 = 3034 := by
  calc
    Artifact.submissionArtifact.instructionPC 2339 =
        Artifact.submissionArtifact.instructionPC 2338 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 4 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2338 _ (by rfl)
    _ = 3034 := by rw [pc2454]; rfl
@[simp] theorem pc2456 : Artifact.submissionArtifact.instructionPC 2340 = 3036 := by
  calc
    Artifact.submissionArtifact.instructionPC 2340 =
        Artifact.submissionArtifact.instructionPC 2339 +
          (YulEvmCompiler.Instr.push 1 5).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2339 _ (by rfl)
    _ = 3036 := by rw [pc2455]; rfl
@[simp] theorem pc2457 : Artifact.submissionArtifact.instructionPC 2341 = 3037 := by
  calc
    Artifact.submissionArtifact.instructionPC 2341 =
        Artifact.submissionArtifact.instructionPC 2340 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.SHR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2340 _ (by rfl)
    _ = 3037 := by rw [pc2456]; rfl
@[simp] theorem pc2458 : Artifact.submissionArtifact.instructionPC 2342 = 3038 := by
  calc
    Artifact.submissionArtifact.instructionPC 2342 =
        Artifact.submissionArtifact.instructionPC 2341 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.AND).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2341 _ (by rfl)
    _ = 3038 := by rw [pc2457]; rfl
@[simp] theorem pc2459 : Artifact.submissionArtifact.instructionPC 2343 = 3039 := by
  calc
    Artifact.submissionArtifact.instructionPC 2343 =
        Artifact.submissionArtifact.instructionPC 2342 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 2 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2342 _ (by rfl)
    _ = 3039 := by rw [pc2458]; rfl
@[simp] theorem pc2460 : Artifact.submissionArtifact.instructionPC 2344 = 3040 := by
  calc
    Artifact.submissionArtifact.instructionPC 2344 =
        Artifact.submissionArtifact.instructionPC 2343 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MUL).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2343 _ (by rfl)
    _ = 3040 := by rw [pc2459]; rfl
@[simp] theorem pc2461 : Artifact.submissionArtifact.instructionPC 2345 = 3042 := by
  calc
    Artifact.submissionArtifact.instructionPC 2345 =
        Artifact.submissionArtifact.instructionPC 2344 +
          (YulEvmCompiler.Instr.push 1 1).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2344 _ (by rfl)
    _ = 3042 := by rw [pc2460]; rfl
@[simp] theorem pc2462 : Artifact.submissionArtifact.instructionPC 2346 = 3043 := by
  calc
    Artifact.submissionArtifact.instructionPC 2346 =
        Artifact.submissionArtifact.instructionPC 2345 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.ADD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2345 _ (by rfl)
    _ = 3043 := by rw [pc2461]; rfl
@[simp] theorem pc2463 : Artifact.submissionArtifact.instructionPC 2347 = 3044 := by
  calc
    Artifact.submissionArtifact.instructionPC 2347 =
        Artifact.submissionArtifact.instructionPC 2346 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2346 _ (by rfl)
    _ = 3044 := by rw [pc2462]; rfl
@[simp] theorem pc2464 : Artifact.submissionArtifact.instructionPC 2348 = 3045 := by
  calc
    Artifact.submissionArtifact.instructionPC 2348 =
        Artifact.submissionArtifact.instructionPC 2347 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 8 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2347 _ (by rfl)
    _ = 3045 := by rw [pc2463]; rfl
@[simp] theorem pc2465 : Artifact.submissionArtifact.instructionPC 2349 = 3046 := by
  calc
    Artifact.submissionArtifact.instructionPC 2349 =
        Artifact.submissionArtifact.instructionPC 2348 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 0 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2348 _ (by rfl)
    _ = 3046 := by rw [pc2464]; rfl
@[simp] theorem pc2466 : Artifact.submissionArtifact.instructionPC 2350 = 3047 := by
  calc
    Artifact.submissionArtifact.instructionPC 2350 =
        Artifact.submissionArtifact.instructionPC 2349 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MULMOD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2349 _ (by rfl)
    _ = 3047 := by rw [pc2465]; rfl
@[simp] theorem pc2467 : Artifact.submissionArtifact.instructionPC 2351 = 3048 := by
  calc
    Artifact.submissionArtifact.instructionPC 2351 =
        Artifact.submissionArtifact.instructionPC 2350 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MULMOD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2350 _ (by rfl)
    _ = 3048 := by rw [pc2466]; rfl
@[simp] theorem pc2468 : Artifact.submissionArtifact.instructionPC 2352 = 3049 := by
  calc
    Artifact.submissionArtifact.instructionPC 2352 =
        Artifact.submissionArtifact.instructionPC 2351 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 5 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2351 _ (by rfl)
    _ = 3049 := by rw [pc2467]; rfl
@[simp] theorem pc2469 : Artifact.submissionArtifact.instructionPC 2353 = 3050 := by
  calc
    Artifact.submissionArtifact.instructionPC 2353 =
        Artifact.submissionArtifact.instructionPC 2352 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.POP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2352 _ (by rfl)
    _ = 3050 := by rw [pc2468]; rfl
@[simp] theorem pc2470 : Artifact.submissionArtifact.instructionPC 2354 = 3051 := by
  calc
    Artifact.submissionArtifact.instructionPC 2354 =
        Artifact.submissionArtifact.instructionPC 2353 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 7 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2353 _ (by rfl)
    _ = 3051 := by rw [pc2469]; rfl
@[simp] theorem pc2471 : Artifact.submissionArtifact.instructionPC 2355 = 3053 := by
  calc
    Artifact.submissionArtifact.instructionPC 2355 =
        Artifact.submissionArtifact.instructionPC 2354 +
          (YulEvmCompiler.Instr.push 1 1).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2354 _ (by rfl)
    _ = 3053 := by rw [pc2470]; rfl
@[simp] theorem pc2472 : Artifact.submissionArtifact.instructionPC 2356 = 3054 := by
  calc
    Artifact.submissionArtifact.instructionPC 2356 =
        Artifact.submissionArtifact.instructionPC 2355 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 4 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2355 _ (by rfl)
    _ = 3054 := by rw [pc2471]; rfl
@[simp] theorem pc2473 : Artifact.submissionArtifact.instructionPC 2357 = 3056 := by
  calc
    Artifact.submissionArtifact.instructionPC 2357 =
        Artifact.submissionArtifact.instructionPC 2356 +
          (YulEvmCompiler.Instr.push 1 4).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2356 _ (by rfl)
    _ = 3056 := by rw [pc2472]; rfl
@[simp] theorem pc2474 : Artifact.submissionArtifact.instructionPC 2358 = 3057 := by
  calc
    Artifact.submissionArtifact.instructionPC 2358 =
        Artifact.submissionArtifact.instructionPC 2357 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.SHR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2357 _ (by rfl)
    _ = 3057 := by rw [pc2473]; rfl
@[simp] theorem pc2475 : Artifact.submissionArtifact.instructionPC 2359 = 3058 := by
  calc
    Artifact.submissionArtifact.instructionPC 2359 =
        Artifact.submissionArtifact.instructionPC 2358 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.AND).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2358 _ (by rfl)
    _ = 3058 := by rw [pc2474]; rfl
@[simp] theorem pc2476 : Artifact.submissionArtifact.instructionPC 2360 = 3059 := by
  calc
    Artifact.submissionArtifact.instructionPC 2360 =
        Artifact.submissionArtifact.instructionPC 2359 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 2 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2359 _ (by rfl)
    _ = 3059 := by rw [pc2475]; rfl
@[simp] theorem pc2477 : Artifact.submissionArtifact.instructionPC 2361 = 3060 := by
  calc
    Artifact.submissionArtifact.instructionPC 2361 =
        Artifact.submissionArtifact.instructionPC 2360 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MUL).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2360 _ (by rfl)
    _ = 3060 := by rw [pc2476]; rfl
@[simp] theorem pc2478 : Artifact.submissionArtifact.instructionPC 2362 = 3062 := by
  calc
    Artifact.submissionArtifact.instructionPC 2362 =
        Artifact.submissionArtifact.instructionPC 2361 +
          (YulEvmCompiler.Instr.push 1 1).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2361 _ (by rfl)
    _ = 3062 := by rw [pc2477]; rfl
@[simp] theorem pc2479 : Artifact.submissionArtifact.instructionPC 2363 = 3063 := by
  calc
    Artifact.submissionArtifact.instructionPC 2363 =
        Artifact.submissionArtifact.instructionPC 2362 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.ADD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2362 _ (by rfl)
    _ = 3063 := by rw [pc2478]; rfl
@[simp] theorem pc2480 : Artifact.submissionArtifact.instructionPC 2364 = 3064 := by
  calc
    Artifact.submissionArtifact.instructionPC 2364 =
        Artifact.submissionArtifact.instructionPC 2363 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2363 _ (by rfl)
    _ = 3064 := by rw [pc2479]; rfl
@[simp] theorem pc2481 : Artifact.submissionArtifact.instructionPC 2365 = 3065 := by
  calc
    Artifact.submissionArtifact.instructionPC 2365 =
        Artifact.submissionArtifact.instructionPC 2364 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 8 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2364 _ (by rfl)
    _ = 3065 := by rw [pc2480]; rfl
@[simp] theorem pc2482 : Artifact.submissionArtifact.instructionPC 2366 = 3066 := by
  calc
    Artifact.submissionArtifact.instructionPC 2366 =
        Artifact.submissionArtifact.instructionPC 2365 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 0 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2365 _ (by rfl)
    _ = 3066 := by rw [pc2481]; rfl
@[simp] theorem pc2483 : Artifact.submissionArtifact.instructionPC 2367 = 3067 := by
  calc
    Artifact.submissionArtifact.instructionPC 2367 =
        Artifact.submissionArtifact.instructionPC 2366 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MULMOD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2366 _ (by rfl)
    _ = 3067 := by rw [pc2482]; rfl
@[simp] theorem pc2484 : Artifact.submissionArtifact.instructionPC 2368 = 3068 := by
  calc
    Artifact.submissionArtifact.instructionPC 2368 =
        Artifact.submissionArtifact.instructionPC 2367 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MULMOD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2367 _ (by rfl)
    _ = 3068 := by rw [pc2483]; rfl
@[simp] theorem pc2485 : Artifact.submissionArtifact.instructionPC 2369 = 3069 := by
  calc
    Artifact.submissionArtifact.instructionPC 2369 =
        Artifact.submissionArtifact.instructionPC 2368 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 5 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2368 _ (by rfl)
    _ = 3069 := by rw [pc2484]; rfl
@[simp] theorem pc2486 : Artifact.submissionArtifact.instructionPC 2370 = 3070 := by
  calc
    Artifact.submissionArtifact.instructionPC 2370 =
        Artifact.submissionArtifact.instructionPC 2369 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.POP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2369 _ (by rfl)
    _ = 3070 := by rw [pc2485]; rfl
@[simp] theorem pc2487 : Artifact.submissionArtifact.instructionPC 2371 = 3071 := by
  calc
    Artifact.submissionArtifact.instructionPC 2371 =
        Artifact.submissionArtifact.instructionPC 2370 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 7 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2370 _ (by rfl)
    _ = 3071 := by rw [pc2486]; rfl
@[simp] theorem pc2488 : Artifact.submissionArtifact.instructionPC 2372 = 3073 := by
  calc
    Artifact.submissionArtifact.instructionPC 2372 =
        Artifact.submissionArtifact.instructionPC 2371 +
          (YulEvmCompiler.Instr.push 1 1).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2371 _ (by rfl)
    _ = 3073 := by rw [pc2487]; rfl
@[simp] theorem pc2489 : Artifact.submissionArtifact.instructionPC 2373 = 3074 := by
  calc
    Artifact.submissionArtifact.instructionPC 2373 =
        Artifact.submissionArtifact.instructionPC 2372 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 4 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2372 _ (by rfl)
    _ = 3074 := by rw [pc2488]; rfl
@[simp] theorem pc2490 : Artifact.submissionArtifact.instructionPC 2374 = 3076 := by
  calc
    Artifact.submissionArtifact.instructionPC 2374 =
        Artifact.submissionArtifact.instructionPC 2373 +
          (YulEvmCompiler.Instr.push 1 3).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2373 _ (by rfl)
    _ = 3076 := by rw [pc2489]; rfl
@[simp] theorem pc2491 : Artifact.submissionArtifact.instructionPC 2375 = 3077 := by
  calc
    Artifact.submissionArtifact.instructionPC 2375 =
        Artifact.submissionArtifact.instructionPC 2374 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.SHR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2374 _ (by rfl)
    _ = 3077 := by rw [pc2490]; rfl
@[simp] theorem pc2492 : Artifact.submissionArtifact.instructionPC 2376 = 3078 := by
  calc
    Artifact.submissionArtifact.instructionPC 2376 =
        Artifact.submissionArtifact.instructionPC 2375 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.AND).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2375 _ (by rfl)
    _ = 3078 := by rw [pc2491]; rfl
@[simp] theorem pc2493 : Artifact.submissionArtifact.instructionPC 2377 = 3079 := by
  calc
    Artifact.submissionArtifact.instructionPC 2377 =
        Artifact.submissionArtifact.instructionPC 2376 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 2 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2376 _ (by rfl)
    _ = 3079 := by rw [pc2492]; rfl
@[simp] theorem pc2494 : Artifact.submissionArtifact.instructionPC 2378 = 3080 := by
  calc
    Artifact.submissionArtifact.instructionPC 2378 =
        Artifact.submissionArtifact.instructionPC 2377 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MUL).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2377 _ (by rfl)
    _ = 3080 := by rw [pc2493]; rfl
@[simp] theorem pc2495 : Artifact.submissionArtifact.instructionPC 2379 = 3082 := by
  calc
    Artifact.submissionArtifact.instructionPC 2379 =
        Artifact.submissionArtifact.instructionPC 2378 +
          (YulEvmCompiler.Instr.push 1 1).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2378 _ (by rfl)
    _ = 3082 := by rw [pc2494]; rfl
@[simp] theorem pc2496 : Artifact.submissionArtifact.instructionPC 2380 = 3083 := by
  calc
    Artifact.submissionArtifact.instructionPC 2380 =
        Artifact.submissionArtifact.instructionPC 2379 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.ADD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2379 _ (by rfl)
    _ = 3083 := by rw [pc2495]; rfl
@[simp] theorem pc2497 : Artifact.submissionArtifact.instructionPC 2381 = 3084 := by
  calc
    Artifact.submissionArtifact.instructionPC 2381 =
        Artifact.submissionArtifact.instructionPC 2380 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2380 _ (by rfl)
    _ = 3084 := by rw [pc2496]; rfl
@[simp] theorem pc2498 : Artifact.submissionArtifact.instructionPC 2382 = 3085 := by
  calc
    Artifact.submissionArtifact.instructionPC 2382 =
        Artifact.submissionArtifact.instructionPC 2381 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 8 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2381 _ (by rfl)
    _ = 3085 := by rw [pc2497]; rfl
@[simp] theorem pc2499 : Artifact.submissionArtifact.instructionPC 2383 = 3086 := by
  calc
    Artifact.submissionArtifact.instructionPC 2383 =
        Artifact.submissionArtifact.instructionPC 2382 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 0 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2382 _ (by rfl)
    _ = 3086 := by rw [pc2498]; rfl
@[simp] theorem pc2500 : Artifact.submissionArtifact.instructionPC 2384 = 3087 := by
  calc
    Artifact.submissionArtifact.instructionPC 2384 =
        Artifact.submissionArtifact.instructionPC 2383 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MULMOD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2383 _ (by rfl)
    _ = 3087 := by rw [pc2499]; rfl
@[simp] theorem pc2501 : Artifact.submissionArtifact.instructionPC 2385 = 3088 := by
  calc
    Artifact.submissionArtifact.instructionPC 2385 =
        Artifact.submissionArtifact.instructionPC 2384 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MULMOD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2384 _ (by rfl)
    _ = 3088 := by rw [pc2500]; rfl
@[simp] theorem pc2502 : Artifact.submissionArtifact.instructionPC 2386 = 3089 := by
  calc
    Artifact.submissionArtifact.instructionPC 2386 =
        Artifact.submissionArtifact.instructionPC 2385 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 5 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2385 _ (by rfl)
    _ = 3089 := by rw [pc2501]; rfl
@[simp] theorem pc2503 : Artifact.submissionArtifact.instructionPC 2387 = 3090 := by
  calc
    Artifact.submissionArtifact.instructionPC 2387 =
        Artifact.submissionArtifact.instructionPC 2386 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.POP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2386 _ (by rfl)
    _ = 3090 := by rw [pc2502]; rfl
@[simp] theorem pc2504 : Artifact.submissionArtifact.instructionPC 2388 = 3091 := by
  calc
    Artifact.submissionArtifact.instructionPC 2388 =
        Artifact.submissionArtifact.instructionPC 2387 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 7 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2387 _ (by rfl)
    _ = 3091 := by rw [pc2503]; rfl
@[simp] theorem pc2505 : Artifact.submissionArtifact.instructionPC 2389 = 3093 := by
  calc
    Artifact.submissionArtifact.instructionPC 2389 =
        Artifact.submissionArtifact.instructionPC 2388 +
          (YulEvmCompiler.Instr.push 1 1).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2388 _ (by rfl)
    _ = 3093 := by rw [pc2504]; rfl
@[simp] theorem pc2506 : Artifact.submissionArtifact.instructionPC 2390 = 3094 := by
  calc
    Artifact.submissionArtifact.instructionPC 2390 =
        Artifact.submissionArtifact.instructionPC 2389 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 4 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2389 _ (by rfl)
    _ = 3094 := by rw [pc2505]; rfl
@[simp] theorem pc2507 : Artifact.submissionArtifact.instructionPC 2391 = 3096 := by
  calc
    Artifact.submissionArtifact.instructionPC 2391 =
        Artifact.submissionArtifact.instructionPC 2390 +
          (YulEvmCompiler.Instr.push 1 2).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2390 _ (by rfl)
    _ = 3096 := by rw [pc2506]; rfl
@[simp] theorem pc2508 : Artifact.submissionArtifact.instructionPC 2392 = 3097 := by
  calc
    Artifact.submissionArtifact.instructionPC 2392 =
        Artifact.submissionArtifact.instructionPC 2391 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.SHR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2391 _ (by rfl)
    _ = 3097 := by rw [pc2507]; rfl
@[simp] theorem pc2509 : Artifact.submissionArtifact.instructionPC 2393 = 3098 := by
  calc
    Artifact.submissionArtifact.instructionPC 2393 =
        Artifact.submissionArtifact.instructionPC 2392 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.AND).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2392 _ (by rfl)
    _ = 3098 := by rw [pc2508]; rfl
@[simp] theorem pc2510 : Artifact.submissionArtifact.instructionPC 2394 = 3099 := by
  calc
    Artifact.submissionArtifact.instructionPC 2394 =
        Artifact.submissionArtifact.instructionPC 2393 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 2 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2393 _ (by rfl)
    _ = 3099 := by rw [pc2509]; rfl
@[simp] theorem pc2511 : Artifact.submissionArtifact.instructionPC 2395 = 3100 := by
  calc
    Artifact.submissionArtifact.instructionPC 2395 =
        Artifact.submissionArtifact.instructionPC 2394 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MUL).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2394 _ (by rfl)
    _ = 3100 := by rw [pc2510]; rfl
@[simp] theorem pc2512 : Artifact.submissionArtifact.instructionPC 2396 = 3102 := by
  calc
    Artifact.submissionArtifact.instructionPC 2396 =
        Artifact.submissionArtifact.instructionPC 2395 +
          (YulEvmCompiler.Instr.push 1 1).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2395 _ (by rfl)
    _ = 3102 := by rw [pc2511]; rfl
@[simp] theorem pc2513 : Artifact.submissionArtifact.instructionPC 2397 = 3103 := by
  calc
    Artifact.submissionArtifact.instructionPC 2397 =
        Artifact.submissionArtifact.instructionPC 2396 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.ADD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2396 _ (by rfl)
    _ = 3103 := by rw [pc2512]; rfl
@[simp] theorem pc2514 : Artifact.submissionArtifact.instructionPC 2398 = 3104 := by
  calc
    Artifact.submissionArtifact.instructionPC 2398 =
        Artifact.submissionArtifact.instructionPC 2397 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2397 _ (by rfl)
    _ = 3104 := by rw [pc2513]; rfl
@[simp] theorem pc2515 : Artifact.submissionArtifact.instructionPC 2399 = 3105 := by
  calc
    Artifact.submissionArtifact.instructionPC 2399 =
        Artifact.submissionArtifact.instructionPC 2398 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 8 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2398 _ (by rfl)
    _ = 3105 := by rw [pc2514]; rfl
@[simp] theorem pc2516 : Artifact.submissionArtifact.instructionPC 2400 = 3106 := by
  calc
    Artifact.submissionArtifact.instructionPC 2400 =
        Artifact.submissionArtifact.instructionPC 2399 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 0 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2399 _ (by rfl)
    _ = 3106 := by rw [pc2515]; rfl
@[simp] theorem pc2517 : Artifact.submissionArtifact.instructionPC 2401 = 3107 := by
  calc
    Artifact.submissionArtifact.instructionPC 2401 =
        Artifact.submissionArtifact.instructionPC 2400 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MULMOD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2400 _ (by rfl)
    _ = 3107 := by rw [pc2516]; rfl
@[simp] theorem pc2518 : Artifact.submissionArtifact.instructionPC 2402 = 3108 := by
  calc
    Artifact.submissionArtifact.instructionPC 2402 =
        Artifact.submissionArtifact.instructionPC 2401 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MULMOD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2401 _ (by rfl)
    _ = 3108 := by rw [pc2517]; rfl
@[simp] theorem pc2519 : Artifact.submissionArtifact.instructionPC 2403 = 3109 := by
  calc
    Artifact.submissionArtifact.instructionPC 2403 =
        Artifact.submissionArtifact.instructionPC 2402 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 5 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2402 _ (by rfl)
    _ = 3109 := by rw [pc2518]; rfl
@[simp] theorem pc2520 : Artifact.submissionArtifact.instructionPC 2404 = 3110 := by
  calc
    Artifact.submissionArtifact.instructionPC 2404 =
        Artifact.submissionArtifact.instructionPC 2403 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.POP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2403 _ (by rfl)
    _ = 3110 := by rw [pc2519]; rfl
@[simp] theorem pc2521 : Artifact.submissionArtifact.instructionPC 2405 = 3111 := by
  calc
    Artifact.submissionArtifact.instructionPC 2405 =
        Artifact.submissionArtifact.instructionPC 2404 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 7 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2404 _ (by rfl)
    _ = 3111 := by rw [pc2520]; rfl
@[simp] theorem pc2522 : Artifact.submissionArtifact.instructionPC 2406 = 3113 := by
  calc
    Artifact.submissionArtifact.instructionPC 2406 =
        Artifact.submissionArtifact.instructionPC 2405 +
          (YulEvmCompiler.Instr.push 1 1).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2405 _ (by rfl)
    _ = 3113 := by rw [pc2521]; rfl
@[simp] theorem pc2523 : Artifact.submissionArtifact.instructionPC 2407 = 3114 := by
  calc
    Artifact.submissionArtifact.instructionPC 2407 =
        Artifact.submissionArtifact.instructionPC 2406 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 4 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2406 _ (by rfl)
    _ = 3114 := by rw [pc2522]; rfl
@[simp] theorem pc2524 : Artifact.submissionArtifact.instructionPC 2408 = 3116 := by
  calc
    Artifact.submissionArtifact.instructionPC 2408 =
        Artifact.submissionArtifact.instructionPC 2407 +
          (YulEvmCompiler.Instr.push 1 1).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2407 _ (by rfl)
    _ = 3116 := by rw [pc2523]; rfl
@[simp] theorem pc2525 : Artifact.submissionArtifact.instructionPC 2409 = 3117 := by
  calc
    Artifact.submissionArtifact.instructionPC 2409 =
        Artifact.submissionArtifact.instructionPC 2408 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.SHR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2408 _ (by rfl)
    _ = 3117 := by rw [pc2524]; rfl
@[simp] theorem pc2526 : Artifact.submissionArtifact.instructionPC 2410 = 3118 := by
  calc
    Artifact.submissionArtifact.instructionPC 2410 =
        Artifact.submissionArtifact.instructionPC 2409 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.AND).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2409 _ (by rfl)
    _ = 3118 := by rw [pc2525]; rfl
@[simp] theorem pc2527 : Artifact.submissionArtifact.instructionPC 2411 = 3119 := by
  calc
    Artifact.submissionArtifact.instructionPC 2411 =
        Artifact.submissionArtifact.instructionPC 2410 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 2 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2410 _ (by rfl)
    _ = 3119 := by rw [pc2526]; rfl
@[simp] theorem pc2528 : Artifact.submissionArtifact.instructionPC 2412 = 3120 := by
  calc
    Artifact.submissionArtifact.instructionPC 2412 =
        Artifact.submissionArtifact.instructionPC 2411 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MUL).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2411 _ (by rfl)
    _ = 3120 := by rw [pc2527]; rfl
@[simp] theorem pc2529 : Artifact.submissionArtifact.instructionPC 2413 = 3122 := by
  calc
    Artifact.submissionArtifact.instructionPC 2413 =
        Artifact.submissionArtifact.instructionPC 2412 +
          (YulEvmCompiler.Instr.push 1 1).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2412 _ (by rfl)
    _ = 3122 := by rw [pc2528]; rfl
@[simp] theorem pc2530 : Artifact.submissionArtifact.instructionPC 2414 = 3123 := by
  calc
    Artifact.submissionArtifact.instructionPC 2414 =
        Artifact.submissionArtifact.instructionPC 2413 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.ADD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2413 _ (by rfl)
    _ = 3123 := by rw [pc2529]; rfl
@[simp] theorem pc2531 : Artifact.submissionArtifact.instructionPC 2415 = 3124 := by
  calc
    Artifact.submissionArtifact.instructionPC 2415 =
        Artifact.submissionArtifact.instructionPC 2414 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2414 _ (by rfl)
    _ = 3124 := by rw [pc2530]; rfl
@[simp] theorem pc2532 : Artifact.submissionArtifact.instructionPC 2416 = 3125 := by
  calc
    Artifact.submissionArtifact.instructionPC 2416 =
        Artifact.submissionArtifact.instructionPC 2415 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 8 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2415 _ (by rfl)
    _ = 3125 := by rw [pc2531]; rfl
@[simp] theorem pc2533 : Artifact.submissionArtifact.instructionPC 2417 = 3126 := by
  calc
    Artifact.submissionArtifact.instructionPC 2417 =
        Artifact.submissionArtifact.instructionPC 2416 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 0 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2416 _ (by rfl)
    _ = 3126 := by rw [pc2532]; rfl
@[simp] theorem pc2534 : Artifact.submissionArtifact.instructionPC 2418 = 3127 := by
  calc
    Artifact.submissionArtifact.instructionPC 2418 =
        Artifact.submissionArtifact.instructionPC 2417 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MULMOD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2417 _ (by rfl)
    _ = 3127 := by rw [pc2533]; rfl
@[simp] theorem pc2535 : Artifact.submissionArtifact.instructionPC 2419 = 3128 := by
  calc
    Artifact.submissionArtifact.instructionPC 2419 =
        Artifact.submissionArtifact.instructionPC 2418 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MULMOD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2418 _ (by rfl)
    _ = 3128 := by rw [pc2534]; rfl
@[simp] theorem pc2536 : Artifact.submissionArtifact.instructionPC 2420 = 3129 := by
  calc
    Artifact.submissionArtifact.instructionPC 2420 =
        Artifact.submissionArtifact.instructionPC 2419 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 5 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2419 _ (by rfl)
    _ = 3129 := by rw [pc2535]; rfl
@[simp] theorem pc2537 : Artifact.submissionArtifact.instructionPC 2421 = 3130 := by
  calc
    Artifact.submissionArtifact.instructionPC 2421 =
        Artifact.submissionArtifact.instructionPC 2420 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.POP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2420 _ (by rfl)
    _ = 3130 := by rw [pc2536]; rfl
@[simp] theorem pc2538 : Artifact.submissionArtifact.instructionPC 2422 = 3131 := by
  calc
    Artifact.submissionArtifact.instructionPC 2422 =
        Artifact.submissionArtifact.instructionPC 2421 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 7 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2421 _ (by rfl)
    _ = 3131 := by rw [pc2537]; rfl
@[simp] theorem pc2539 : Artifact.submissionArtifact.instructionPC 2423 = 3133 := by
  calc
    Artifact.submissionArtifact.instructionPC 2423 =
        Artifact.submissionArtifact.instructionPC 2422 +
          (YulEvmCompiler.Instr.push 1 1).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2422 _ (by rfl)
    _ = 3133 := by rw [pc2538]; rfl
@[simp] theorem pc2542 : Artifact.submissionArtifact.instructionPC 2424 = 3134 := by
  calc
    Artifact.submissionArtifact.instructionPC 2424 =
        Artifact.submissionArtifact.instructionPC 2423 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 4 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2423 _ (by rfl)
    _ = 3134 := by rw [pc2539]; rfl
@[simp] theorem pc2543 : Artifact.submissionArtifact.instructionPC 2425 = 3135 := by
  calc
    Artifact.submissionArtifact.instructionPC 2425 =
        Artifact.submissionArtifact.instructionPC 2424 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.AND).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2424 _ (by rfl)
    _ = 3135 := by rw [pc2542]; rfl
@[simp] theorem pc2544 : Artifact.submissionArtifact.instructionPC 2426 = 3136 := by
  calc
    Artifact.submissionArtifact.instructionPC 2426 =
        Artifact.submissionArtifact.instructionPC 2425 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 2 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2425 _ (by rfl)
    _ = 3136 := by rw [pc2543]; rfl
@[simp] theorem pc2545 : Artifact.submissionArtifact.instructionPC 2427 = 3137 := by
  calc
    Artifact.submissionArtifact.instructionPC 2427 =
        Artifact.submissionArtifact.instructionPC 2426 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MUL).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2426 _ (by rfl)
    _ = 3137 := by rw [pc2544]; rfl
@[simp] theorem pc2546 : Artifact.submissionArtifact.instructionPC 2428 = 3139 := by
  calc
    Artifact.submissionArtifact.instructionPC 2428 =
        Artifact.submissionArtifact.instructionPC 2427 +
          (YulEvmCompiler.Instr.push 1 1).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2427 _ (by rfl)
    _ = 3139 := by rw [pc2545]; rfl
@[simp] theorem pc2547 : Artifact.submissionArtifact.instructionPC 2429 = 3140 := by
  calc
    Artifact.submissionArtifact.instructionPC 2429 =
        Artifact.submissionArtifact.instructionPC 2428 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.ADD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2428 _ (by rfl)
    _ = 3140 := by rw [pc2546]; rfl
@[simp] theorem pc2548 : Artifact.submissionArtifact.instructionPC 2430 = 3141 := by
  calc
    Artifact.submissionArtifact.instructionPC 2430 =
        Artifact.submissionArtifact.instructionPC 2429 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2429 _ (by rfl)
    _ = 3141 := by rw [pc2547]; rfl
@[simp] theorem pc2549 : Artifact.submissionArtifact.instructionPC 2431 = 3142 := by
  calc
    Artifact.submissionArtifact.instructionPC 2431 =
        Artifact.submissionArtifact.instructionPC 2430 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 8 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2430 _ (by rfl)
    _ = 3142 := by rw [pc2548]; rfl
@[simp] theorem pc2550 : Artifact.submissionArtifact.instructionPC 2432 = 3143 := by
  calc
    Artifact.submissionArtifact.instructionPC 2432 =
        Artifact.submissionArtifact.instructionPC 2431 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 0 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2431 _ (by rfl)
    _ = 3143 := by rw [pc2549]; rfl
@[simp] theorem pc2551 : Artifact.submissionArtifact.instructionPC 2433 = 3144 := by
  calc
    Artifact.submissionArtifact.instructionPC 2433 =
        Artifact.submissionArtifact.instructionPC 2432 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MULMOD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2432 _ (by rfl)
    _ = 3144 := by rw [pc2550]; rfl
@[simp] theorem pc2552 : Artifact.submissionArtifact.instructionPC 2434 = 3145 := by
  calc
    Artifact.submissionArtifact.instructionPC 2434 =
        Artifact.submissionArtifact.instructionPC 2433 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MULMOD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2433 _ (by rfl)
    _ = 3145 := by rw [pc2551]; rfl
@[simp] theorem pc2553 : Artifact.submissionArtifact.instructionPC 2435 = 3146 := by
  calc
    Artifact.submissionArtifact.instructionPC 2435 =
        Artifact.submissionArtifact.instructionPC 2434 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 5 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2434 _ (by rfl)
    _ = 3146 := by rw [pc2552]; rfl
@[simp] theorem pc2554 : Artifact.submissionArtifact.instructionPC 2436 = 3147 := by
  calc
    Artifact.submissionArtifact.instructionPC 2436 =
        Artifact.submissionArtifact.instructionPC 2435 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.POP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2435 _ (by rfl)
    _ = 3147 := by rw [pc2553]; rfl
@[simp] theorem pc2555 : Artifact.submissionArtifact.instructionPC 2437 = 3148 := by
  calc
    Artifact.submissionArtifact.instructionPC 2437 =
        Artifact.submissionArtifact.instructionPC 2436 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.POP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2436 _ (by rfl)
    _ = 3148 := by rw [pc2554]; rfl
@[simp] theorem pc2556 : Artifact.submissionArtifact.instructionPC 2438 = 3151 := by
  calc
    Artifact.submissionArtifact.instructionPC 2438 =
        Artifact.submissionArtifact.instructionPC 2437 +
          (YulEvmCompiler.Instr.push 2 557).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2437 _ (by rfl)
    _ = 3151 := by rw [pc2555]; rfl

end Challenge.Modexp.Submission.Proofs.Bytecode.UnrollPCs
