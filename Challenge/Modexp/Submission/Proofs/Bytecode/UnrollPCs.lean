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

@[simp] theorem pc484 : Artifact.submissionArtifact.instructionPC 481 = 584 := by rfl
@[simp] theorem pc485 : Artifact.submissionArtifact.instructionPC 482 = 585 := by
  calc
    Artifact.submissionArtifact.instructionPC 482 =
        Artifact.submissionArtifact.instructionPC 481 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.JUMPDEST).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 481 _ (by rfl)
    _ = 585 := by rw [pc484]; rfl
@[simp] theorem pc486 : Artifact.submissionArtifact.instructionPC 483 = 588 := by
  calc
    Artifact.submissionArtifact.instructionPC 483 =
        Artifact.submissionArtifact.instructionPC 482 +
          (YulEvmCompiler.Instr.push 2 3330).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 482 _ (by rfl)
    _ = 588 := by rw [pc485]; rfl
@[simp] theorem pc2414 : Artifact.submissionArtifact.instructionPC 2396 = 3130 := by rfl
@[simp] theorem pc2415 : Artifact.submissionArtifact.instructionPC 2397 = 3131 := by
  calc
    Artifact.submissionArtifact.instructionPC 2397 =
        Artifact.submissionArtifact.instructionPC 2396 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.JUMPDEST).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2396 _ (by rfl)
    _ = 3131 := by rw [pc2414]; rfl
@[simp] theorem pc2416 : Artifact.submissionArtifact.instructionPC 2398 = 3133 := by
  calc
    Artifact.submissionArtifact.instructionPC 2398 =
        Artifact.submissionArtifact.instructionPC 2397 +
          (YulEvmCompiler.Instr.push 1 1).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2397 _ (by rfl)
    _ = 3133 := by rw [pc2415]; rfl
@[simp] theorem pc2417 : Artifact.submissionArtifact.instructionPC 2399 = 3134 := by
  calc
    Artifact.submissionArtifact.instructionPC 2399 =
        Artifact.submissionArtifact.instructionPC 2398 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 6 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2398 _ (by rfl)
    _ = 3134 := by rw [pc2416]; rfl
@[simp] theorem pc2418 : Artifact.submissionArtifact.instructionPC 2400 = 3135 := by
  calc
    Artifact.submissionArtifact.instructionPC 2400 =
        Artifact.submissionArtifact.instructionPC 2399 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2399 _ (by rfl)
    _ = 3135 := by rw [pc2417]; rfl
@[simp] theorem pc2419 : Artifact.submissionArtifact.instructionPC 2401 = 3136 := by
  calc
    Artifact.submissionArtifact.instructionPC 2401 =
        Artifact.submissionArtifact.instructionPC 2400 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 7 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2400 _ (by rfl)
    _ = 3136 := by rw [pc2418]; rfl
@[simp] theorem pc2420 : Artifact.submissionArtifact.instructionPC 2402 = 3138 := by
  calc
    Artifact.submissionArtifact.instructionPC 2402 =
        Artifact.submissionArtifact.instructionPC 2401 +
          (YulEvmCompiler.Instr.push 1 1).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2401 _ (by rfl)
    _ = 3138 := by rw [pc2419]; rfl
@[simp] theorem pc2421 : Artifact.submissionArtifact.instructionPC 2403 = 3139 := by
  calc
    Artifact.submissionArtifact.instructionPC 2403 =
        Artifact.submissionArtifact.instructionPC 2402 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 4 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2402 _ (by rfl)
    _ = 3139 := by rw [pc2420]; rfl
@[simp] theorem pc2422 : Artifact.submissionArtifact.instructionPC 2404 = 3141 := by
  calc
    Artifact.submissionArtifact.instructionPC 2404 =
        Artifact.submissionArtifact.instructionPC 2403 +
          (YulEvmCompiler.Instr.push 1 7).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2403 _ (by rfl)
    _ = 3141 := by rw [pc2421]; rfl
@[simp] theorem pc2423 : Artifact.submissionArtifact.instructionPC 2405 = 3142 := by
  calc
    Artifact.submissionArtifact.instructionPC 2405 =
        Artifact.submissionArtifact.instructionPC 2404 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.SHR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2404 _ (by rfl)
    _ = 3142 := by rw [pc2422]; rfl
@[simp] theorem pc2424 : Artifact.submissionArtifact.instructionPC 2406 = 3143 := by
  calc
    Artifact.submissionArtifact.instructionPC 2406 =
        Artifact.submissionArtifact.instructionPC 2405 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.AND).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2405 _ (by rfl)
    _ = 3143 := by rw [pc2423]; rfl
@[simp] theorem pc2425 : Artifact.submissionArtifact.instructionPC 2407 = 3144 := by
  calc
    Artifact.submissionArtifact.instructionPC 2407 =
        Artifact.submissionArtifact.instructionPC 2406 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 2 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2406 _ (by rfl)
    _ = 3144 := by rw [pc2424]; rfl
@[simp] theorem pc2426 : Artifact.submissionArtifact.instructionPC 2408 = 3145 := by
  calc
    Artifact.submissionArtifact.instructionPC 2408 =
        Artifact.submissionArtifact.instructionPC 2407 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MUL).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2407 _ (by rfl)
    _ = 3145 := by rw [pc2425]; rfl
@[simp] theorem pc2427 : Artifact.submissionArtifact.instructionPC 2409 = 3147 := by
  calc
    Artifact.submissionArtifact.instructionPC 2409 =
        Artifact.submissionArtifact.instructionPC 2408 +
          (YulEvmCompiler.Instr.push 1 1).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2408 _ (by rfl)
    _ = 3147 := by rw [pc2426]; rfl
@[simp] theorem pc2428 : Artifact.submissionArtifact.instructionPC 2410 = 3148 := by
  calc
    Artifact.submissionArtifact.instructionPC 2410 =
        Artifact.submissionArtifact.instructionPC 2409 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.ADD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2409 _ (by rfl)
    _ = 3148 := by rw [pc2427]; rfl
@[simp] theorem pc2429 : Artifact.submissionArtifact.instructionPC 2411 = 3149 := by
  calc
    Artifact.submissionArtifact.instructionPC 2411 =
        Artifact.submissionArtifact.instructionPC 2410 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2410 _ (by rfl)
    _ = 3149 := by rw [pc2428]; rfl
@[simp] theorem pc2430 : Artifact.submissionArtifact.instructionPC 2412 = 3150 := by
  calc
    Artifact.submissionArtifact.instructionPC 2412 =
        Artifact.submissionArtifact.instructionPC 2411 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 8 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2411 _ (by rfl)
    _ = 3150 := by rw [pc2429]; rfl
@[simp] theorem pc2431 : Artifact.submissionArtifact.instructionPC 2413 = 3151 := by
  calc
    Artifact.submissionArtifact.instructionPC 2413 =
        Artifact.submissionArtifact.instructionPC 2412 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 0 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2412 _ (by rfl)
    _ = 3151 := by rw [pc2430]; rfl
@[simp] theorem pc2432 : Artifact.submissionArtifact.instructionPC 2414 = 3152 := by
  calc
    Artifact.submissionArtifact.instructionPC 2414 =
        Artifact.submissionArtifact.instructionPC 2413 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MULMOD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2413 _ (by rfl)
    _ = 3152 := by rw [pc2431]; rfl
@[simp] theorem pc2433 : Artifact.submissionArtifact.instructionPC 2415 = 3153 := by
  calc
    Artifact.submissionArtifact.instructionPC 2415 =
        Artifact.submissionArtifact.instructionPC 2414 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MULMOD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2414 _ (by rfl)
    _ = 3153 := by rw [pc2432]; rfl
@[simp] theorem pc2434 : Artifact.submissionArtifact.instructionPC 2416 = 3154 := by
  calc
    Artifact.submissionArtifact.instructionPC 2416 =
        Artifact.submissionArtifact.instructionPC 2415 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 5 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2415 _ (by rfl)
    _ = 3154 := by rw [pc2433]; rfl
@[simp] theorem pc2435 : Artifact.submissionArtifact.instructionPC 2417 = 3155 := by
  calc
    Artifact.submissionArtifact.instructionPC 2417 =
        Artifact.submissionArtifact.instructionPC 2416 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.POP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2416 _ (by rfl)
    _ = 3155 := by rw [pc2434]; rfl
@[simp] theorem pc2436 : Artifact.submissionArtifact.instructionPC 2418 = 3156 := by
  calc
    Artifact.submissionArtifact.instructionPC 2418 =
        Artifact.submissionArtifact.instructionPC 2417 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 7 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2417 _ (by rfl)
    _ = 3156 := by rw [pc2435]; rfl
@[simp] theorem pc2437 : Artifact.submissionArtifact.instructionPC 2419 = 3158 := by
  calc
    Artifact.submissionArtifact.instructionPC 2419 =
        Artifact.submissionArtifact.instructionPC 2418 +
          (YulEvmCompiler.Instr.push 1 1).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2418 _ (by rfl)
    _ = 3158 := by rw [pc2436]; rfl
@[simp] theorem pc2438 : Artifact.submissionArtifact.instructionPC 2420 = 3159 := by
  calc
    Artifact.submissionArtifact.instructionPC 2420 =
        Artifact.submissionArtifact.instructionPC 2419 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 4 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2419 _ (by rfl)
    _ = 3159 := by rw [pc2437]; rfl
@[simp] theorem pc2439 : Artifact.submissionArtifact.instructionPC 2421 = 3161 := by
  calc
    Artifact.submissionArtifact.instructionPC 2421 =
        Artifact.submissionArtifact.instructionPC 2420 +
          (YulEvmCompiler.Instr.push 1 6).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2420 _ (by rfl)
    _ = 3161 := by rw [pc2438]; rfl
@[simp] theorem pc2440 : Artifact.submissionArtifact.instructionPC 2422 = 3162 := by
  calc
    Artifact.submissionArtifact.instructionPC 2422 =
        Artifact.submissionArtifact.instructionPC 2421 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.SHR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2421 _ (by rfl)
    _ = 3162 := by rw [pc2439]; rfl
@[simp] theorem pc2441 : Artifact.submissionArtifact.instructionPC 2423 = 3163 := by
  calc
    Artifact.submissionArtifact.instructionPC 2423 =
        Artifact.submissionArtifact.instructionPC 2422 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.AND).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2422 _ (by rfl)
    _ = 3163 := by rw [pc2440]; rfl
@[simp] theorem pc2442 : Artifact.submissionArtifact.instructionPC 2424 = 3164 := by
  calc
    Artifact.submissionArtifact.instructionPC 2424 =
        Artifact.submissionArtifact.instructionPC 2423 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 2 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2423 _ (by rfl)
    _ = 3164 := by rw [pc2441]; rfl
@[simp] theorem pc2443 : Artifact.submissionArtifact.instructionPC 2425 = 3165 := by
  calc
    Artifact.submissionArtifact.instructionPC 2425 =
        Artifact.submissionArtifact.instructionPC 2424 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MUL).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2424 _ (by rfl)
    _ = 3165 := by rw [pc2442]; rfl
@[simp] theorem pc2444 : Artifact.submissionArtifact.instructionPC 2426 = 3167 := by
  calc
    Artifact.submissionArtifact.instructionPC 2426 =
        Artifact.submissionArtifact.instructionPC 2425 +
          (YulEvmCompiler.Instr.push 1 1).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2425 _ (by rfl)
    _ = 3167 := by rw [pc2443]; rfl
@[simp] theorem pc2445 : Artifact.submissionArtifact.instructionPC 2427 = 3168 := by
  calc
    Artifact.submissionArtifact.instructionPC 2427 =
        Artifact.submissionArtifact.instructionPC 2426 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.ADD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2426 _ (by rfl)
    _ = 3168 := by rw [pc2444]; rfl
@[simp] theorem pc2446 : Artifact.submissionArtifact.instructionPC 2428 = 3169 := by
  calc
    Artifact.submissionArtifact.instructionPC 2428 =
        Artifact.submissionArtifact.instructionPC 2427 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2427 _ (by rfl)
    _ = 3169 := by rw [pc2445]; rfl
@[simp] theorem pc2447 : Artifact.submissionArtifact.instructionPC 2429 = 3170 := by
  calc
    Artifact.submissionArtifact.instructionPC 2429 =
        Artifact.submissionArtifact.instructionPC 2428 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 8 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2428 _ (by rfl)
    _ = 3170 := by rw [pc2446]; rfl
@[simp] theorem pc2448 : Artifact.submissionArtifact.instructionPC 2430 = 3171 := by
  calc
    Artifact.submissionArtifact.instructionPC 2430 =
        Artifact.submissionArtifact.instructionPC 2429 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 0 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2429 _ (by rfl)
    _ = 3171 := by rw [pc2447]; rfl
@[simp] theorem pc2449 : Artifact.submissionArtifact.instructionPC 2431 = 3172 := by
  calc
    Artifact.submissionArtifact.instructionPC 2431 =
        Artifact.submissionArtifact.instructionPC 2430 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MULMOD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2430 _ (by rfl)
    _ = 3172 := by rw [pc2448]; rfl
@[simp] theorem pc2450 : Artifact.submissionArtifact.instructionPC 2432 = 3173 := by
  calc
    Artifact.submissionArtifact.instructionPC 2432 =
        Artifact.submissionArtifact.instructionPC 2431 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MULMOD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2431 _ (by rfl)
    _ = 3173 := by rw [pc2449]; rfl
@[simp] theorem pc2451 : Artifact.submissionArtifact.instructionPC 2433 = 3174 := by
  calc
    Artifact.submissionArtifact.instructionPC 2433 =
        Artifact.submissionArtifact.instructionPC 2432 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 5 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2432 _ (by rfl)
    _ = 3174 := by rw [pc2450]; rfl
@[simp] theorem pc2452 : Artifact.submissionArtifact.instructionPC 2434 = 3175 := by
  calc
    Artifact.submissionArtifact.instructionPC 2434 =
        Artifact.submissionArtifact.instructionPC 2433 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.POP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2433 _ (by rfl)
    _ = 3175 := by rw [pc2451]; rfl
@[simp] theorem pc2453 : Artifact.submissionArtifact.instructionPC 2435 = 3176 := by
  calc
    Artifact.submissionArtifact.instructionPC 2435 =
        Artifact.submissionArtifact.instructionPC 2434 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 7 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2434 _ (by rfl)
    _ = 3176 := by rw [pc2452]; rfl
@[simp] theorem pc2454 : Artifact.submissionArtifact.instructionPC 2436 = 3178 := by
  calc
    Artifact.submissionArtifact.instructionPC 2436 =
        Artifact.submissionArtifact.instructionPC 2435 +
          (YulEvmCompiler.Instr.push 1 1).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2435 _ (by rfl)
    _ = 3178 := by rw [pc2453]; rfl
@[simp] theorem pc2455 : Artifact.submissionArtifact.instructionPC 2437 = 3179 := by
  calc
    Artifact.submissionArtifact.instructionPC 2437 =
        Artifact.submissionArtifact.instructionPC 2436 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 4 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2436 _ (by rfl)
    _ = 3179 := by rw [pc2454]; rfl
@[simp] theorem pc2456 : Artifact.submissionArtifact.instructionPC 2438 = 3181 := by
  calc
    Artifact.submissionArtifact.instructionPC 2438 =
        Artifact.submissionArtifact.instructionPC 2437 +
          (YulEvmCompiler.Instr.push 1 5).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2437 _ (by rfl)
    _ = 3181 := by rw [pc2455]; rfl
@[simp] theorem pc2457 : Artifact.submissionArtifact.instructionPC 2439 = 3182 := by
  calc
    Artifact.submissionArtifact.instructionPC 2439 =
        Artifact.submissionArtifact.instructionPC 2438 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.SHR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2438 _ (by rfl)
    _ = 3182 := by rw [pc2456]; rfl
@[simp] theorem pc2458 : Artifact.submissionArtifact.instructionPC 2440 = 3183 := by
  calc
    Artifact.submissionArtifact.instructionPC 2440 =
        Artifact.submissionArtifact.instructionPC 2439 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.AND).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2439 _ (by rfl)
    _ = 3183 := by rw [pc2457]; rfl
@[simp] theorem pc2459 : Artifact.submissionArtifact.instructionPC 2441 = 3184 := by
  calc
    Artifact.submissionArtifact.instructionPC 2441 =
        Artifact.submissionArtifact.instructionPC 2440 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 2 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2440 _ (by rfl)
    _ = 3184 := by rw [pc2458]; rfl
@[simp] theorem pc2460 : Artifact.submissionArtifact.instructionPC 2442 = 3185 := by
  calc
    Artifact.submissionArtifact.instructionPC 2442 =
        Artifact.submissionArtifact.instructionPC 2441 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MUL).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2441 _ (by rfl)
    _ = 3185 := by rw [pc2459]; rfl
@[simp] theorem pc2461 : Artifact.submissionArtifact.instructionPC 2443 = 3187 := by
  calc
    Artifact.submissionArtifact.instructionPC 2443 =
        Artifact.submissionArtifact.instructionPC 2442 +
          (YulEvmCompiler.Instr.push 1 1).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2442 _ (by rfl)
    _ = 3187 := by rw [pc2460]; rfl
@[simp] theorem pc2462 : Artifact.submissionArtifact.instructionPC 2444 = 3188 := by
  calc
    Artifact.submissionArtifact.instructionPC 2444 =
        Artifact.submissionArtifact.instructionPC 2443 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.ADD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2443 _ (by rfl)
    _ = 3188 := by rw [pc2461]; rfl
@[simp] theorem pc2463 : Artifact.submissionArtifact.instructionPC 2445 = 3189 := by
  calc
    Artifact.submissionArtifact.instructionPC 2445 =
        Artifact.submissionArtifact.instructionPC 2444 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2444 _ (by rfl)
    _ = 3189 := by rw [pc2462]; rfl
@[simp] theorem pc2464 : Artifact.submissionArtifact.instructionPC 2446 = 3190 := by
  calc
    Artifact.submissionArtifact.instructionPC 2446 =
        Artifact.submissionArtifact.instructionPC 2445 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 8 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2445 _ (by rfl)
    _ = 3190 := by rw [pc2463]; rfl
@[simp] theorem pc2465 : Artifact.submissionArtifact.instructionPC 2447 = 3191 := by
  calc
    Artifact.submissionArtifact.instructionPC 2447 =
        Artifact.submissionArtifact.instructionPC 2446 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 0 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2446 _ (by rfl)
    _ = 3191 := by rw [pc2464]; rfl
@[simp] theorem pc2466 : Artifact.submissionArtifact.instructionPC 2448 = 3192 := by
  calc
    Artifact.submissionArtifact.instructionPC 2448 =
        Artifact.submissionArtifact.instructionPC 2447 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MULMOD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2447 _ (by rfl)
    _ = 3192 := by rw [pc2465]; rfl
@[simp] theorem pc2467 : Artifact.submissionArtifact.instructionPC 2449 = 3193 := by
  calc
    Artifact.submissionArtifact.instructionPC 2449 =
        Artifact.submissionArtifact.instructionPC 2448 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MULMOD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2448 _ (by rfl)
    _ = 3193 := by rw [pc2466]; rfl
@[simp] theorem pc2468 : Artifact.submissionArtifact.instructionPC 2450 = 3194 := by
  calc
    Artifact.submissionArtifact.instructionPC 2450 =
        Artifact.submissionArtifact.instructionPC 2449 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 5 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2449 _ (by rfl)
    _ = 3194 := by rw [pc2467]; rfl
@[simp] theorem pc2469 : Artifact.submissionArtifact.instructionPC 2451 = 3195 := by
  calc
    Artifact.submissionArtifact.instructionPC 2451 =
        Artifact.submissionArtifact.instructionPC 2450 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.POP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2450 _ (by rfl)
    _ = 3195 := by rw [pc2468]; rfl
@[simp] theorem pc2470 : Artifact.submissionArtifact.instructionPC 2452 = 3196 := by
  calc
    Artifact.submissionArtifact.instructionPC 2452 =
        Artifact.submissionArtifact.instructionPC 2451 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 7 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2451 _ (by rfl)
    _ = 3196 := by rw [pc2469]; rfl
@[simp] theorem pc2471 : Artifact.submissionArtifact.instructionPC 2453 = 3198 := by
  calc
    Artifact.submissionArtifact.instructionPC 2453 =
        Artifact.submissionArtifact.instructionPC 2452 +
          (YulEvmCompiler.Instr.push 1 1).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2452 _ (by rfl)
    _ = 3198 := by rw [pc2470]; rfl
@[simp] theorem pc2472 : Artifact.submissionArtifact.instructionPC 2454 = 3199 := by
  calc
    Artifact.submissionArtifact.instructionPC 2454 =
        Artifact.submissionArtifact.instructionPC 2453 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 4 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2453 _ (by rfl)
    _ = 3199 := by rw [pc2471]; rfl
@[simp] theorem pc2473 : Artifact.submissionArtifact.instructionPC 2455 = 3201 := by
  calc
    Artifact.submissionArtifact.instructionPC 2455 =
        Artifact.submissionArtifact.instructionPC 2454 +
          (YulEvmCompiler.Instr.push 1 4).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2454 _ (by rfl)
    _ = 3201 := by rw [pc2472]; rfl
@[simp] theorem pc2474 : Artifact.submissionArtifact.instructionPC 2456 = 3202 := by
  calc
    Artifact.submissionArtifact.instructionPC 2456 =
        Artifact.submissionArtifact.instructionPC 2455 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.SHR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2455 _ (by rfl)
    _ = 3202 := by rw [pc2473]; rfl
@[simp] theorem pc2475 : Artifact.submissionArtifact.instructionPC 2457 = 3203 := by
  calc
    Artifact.submissionArtifact.instructionPC 2457 =
        Artifact.submissionArtifact.instructionPC 2456 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.AND).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2456 _ (by rfl)
    _ = 3203 := by rw [pc2474]; rfl
@[simp] theorem pc2476 : Artifact.submissionArtifact.instructionPC 2458 = 3204 := by
  calc
    Artifact.submissionArtifact.instructionPC 2458 =
        Artifact.submissionArtifact.instructionPC 2457 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 2 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2457 _ (by rfl)
    _ = 3204 := by rw [pc2475]; rfl
@[simp] theorem pc2477 : Artifact.submissionArtifact.instructionPC 2459 = 3205 := by
  calc
    Artifact.submissionArtifact.instructionPC 2459 =
        Artifact.submissionArtifact.instructionPC 2458 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MUL).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2458 _ (by rfl)
    _ = 3205 := by rw [pc2476]; rfl
@[simp] theorem pc2478 : Artifact.submissionArtifact.instructionPC 2460 = 3207 := by
  calc
    Artifact.submissionArtifact.instructionPC 2460 =
        Artifact.submissionArtifact.instructionPC 2459 +
          (YulEvmCompiler.Instr.push 1 1).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2459 _ (by rfl)
    _ = 3207 := by rw [pc2477]; rfl
@[simp] theorem pc2479 : Artifact.submissionArtifact.instructionPC 2461 = 3208 := by
  calc
    Artifact.submissionArtifact.instructionPC 2461 =
        Artifact.submissionArtifact.instructionPC 2460 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.ADD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2460 _ (by rfl)
    _ = 3208 := by rw [pc2478]; rfl
@[simp] theorem pc2480 : Artifact.submissionArtifact.instructionPC 2462 = 3209 := by
  calc
    Artifact.submissionArtifact.instructionPC 2462 =
        Artifact.submissionArtifact.instructionPC 2461 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2461 _ (by rfl)
    _ = 3209 := by rw [pc2479]; rfl
@[simp] theorem pc2481 : Artifact.submissionArtifact.instructionPC 2463 = 3210 := by
  calc
    Artifact.submissionArtifact.instructionPC 2463 =
        Artifact.submissionArtifact.instructionPC 2462 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 8 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2462 _ (by rfl)
    _ = 3210 := by rw [pc2480]; rfl
@[simp] theorem pc2482 : Artifact.submissionArtifact.instructionPC 2464 = 3211 := by
  calc
    Artifact.submissionArtifact.instructionPC 2464 =
        Artifact.submissionArtifact.instructionPC 2463 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 0 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2463 _ (by rfl)
    _ = 3211 := by rw [pc2481]; rfl
@[simp] theorem pc2483 : Artifact.submissionArtifact.instructionPC 2465 = 3212 := by
  calc
    Artifact.submissionArtifact.instructionPC 2465 =
        Artifact.submissionArtifact.instructionPC 2464 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MULMOD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2464 _ (by rfl)
    _ = 3212 := by rw [pc2482]; rfl
@[simp] theorem pc2484 : Artifact.submissionArtifact.instructionPC 2466 = 3213 := by
  calc
    Artifact.submissionArtifact.instructionPC 2466 =
        Artifact.submissionArtifact.instructionPC 2465 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MULMOD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2465 _ (by rfl)
    _ = 3213 := by rw [pc2483]; rfl
@[simp] theorem pc2485 : Artifact.submissionArtifact.instructionPC 2467 = 3214 := by
  calc
    Artifact.submissionArtifact.instructionPC 2467 =
        Artifact.submissionArtifact.instructionPC 2466 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 5 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2466 _ (by rfl)
    _ = 3214 := by rw [pc2484]; rfl
@[simp] theorem pc2486 : Artifact.submissionArtifact.instructionPC 2468 = 3215 := by
  calc
    Artifact.submissionArtifact.instructionPC 2468 =
        Artifact.submissionArtifact.instructionPC 2467 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.POP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2467 _ (by rfl)
    _ = 3215 := by rw [pc2485]; rfl
@[simp] theorem pc2487 : Artifact.submissionArtifact.instructionPC 2469 = 3216 := by
  calc
    Artifact.submissionArtifact.instructionPC 2469 =
        Artifact.submissionArtifact.instructionPC 2468 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 7 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2468 _ (by rfl)
    _ = 3216 := by rw [pc2486]; rfl
@[simp] theorem pc2488 : Artifact.submissionArtifact.instructionPC 2470 = 3218 := by
  calc
    Artifact.submissionArtifact.instructionPC 2470 =
        Artifact.submissionArtifact.instructionPC 2469 +
          (YulEvmCompiler.Instr.push 1 1).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2469 _ (by rfl)
    _ = 3218 := by rw [pc2487]; rfl
@[simp] theorem pc2489 : Artifact.submissionArtifact.instructionPC 2471 = 3219 := by
  calc
    Artifact.submissionArtifact.instructionPC 2471 =
        Artifact.submissionArtifact.instructionPC 2470 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 4 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2470 _ (by rfl)
    _ = 3219 := by rw [pc2488]; rfl
@[simp] theorem pc2490 : Artifact.submissionArtifact.instructionPC 2472 = 3221 := by
  calc
    Artifact.submissionArtifact.instructionPC 2472 =
        Artifact.submissionArtifact.instructionPC 2471 +
          (YulEvmCompiler.Instr.push 1 3).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2471 _ (by rfl)
    _ = 3221 := by rw [pc2489]; rfl
@[simp] theorem pc2491 : Artifact.submissionArtifact.instructionPC 2473 = 3222 := by
  calc
    Artifact.submissionArtifact.instructionPC 2473 =
        Artifact.submissionArtifact.instructionPC 2472 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.SHR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2472 _ (by rfl)
    _ = 3222 := by rw [pc2490]; rfl
@[simp] theorem pc2492 : Artifact.submissionArtifact.instructionPC 2474 = 3223 := by
  calc
    Artifact.submissionArtifact.instructionPC 2474 =
        Artifact.submissionArtifact.instructionPC 2473 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.AND).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2473 _ (by rfl)
    _ = 3223 := by rw [pc2491]; rfl
@[simp] theorem pc2493 : Artifact.submissionArtifact.instructionPC 2475 = 3224 := by
  calc
    Artifact.submissionArtifact.instructionPC 2475 =
        Artifact.submissionArtifact.instructionPC 2474 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 2 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2474 _ (by rfl)
    _ = 3224 := by rw [pc2492]; rfl
@[simp] theorem pc2494 : Artifact.submissionArtifact.instructionPC 2476 = 3225 := by
  calc
    Artifact.submissionArtifact.instructionPC 2476 =
        Artifact.submissionArtifact.instructionPC 2475 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MUL).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2475 _ (by rfl)
    _ = 3225 := by rw [pc2493]; rfl
@[simp] theorem pc2495 : Artifact.submissionArtifact.instructionPC 2477 = 3227 := by
  calc
    Artifact.submissionArtifact.instructionPC 2477 =
        Artifact.submissionArtifact.instructionPC 2476 +
          (YulEvmCompiler.Instr.push 1 1).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2476 _ (by rfl)
    _ = 3227 := by rw [pc2494]; rfl
@[simp] theorem pc2496 : Artifact.submissionArtifact.instructionPC 2478 = 3228 := by
  calc
    Artifact.submissionArtifact.instructionPC 2478 =
        Artifact.submissionArtifact.instructionPC 2477 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.ADD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2477 _ (by rfl)
    _ = 3228 := by rw [pc2495]; rfl
@[simp] theorem pc2497 : Artifact.submissionArtifact.instructionPC 2479 = 3229 := by
  calc
    Artifact.submissionArtifact.instructionPC 2479 =
        Artifact.submissionArtifact.instructionPC 2478 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2478 _ (by rfl)
    _ = 3229 := by rw [pc2496]; rfl
@[simp] theorem pc2498 : Artifact.submissionArtifact.instructionPC 2480 = 3230 := by
  calc
    Artifact.submissionArtifact.instructionPC 2480 =
        Artifact.submissionArtifact.instructionPC 2479 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 8 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2479 _ (by rfl)
    _ = 3230 := by rw [pc2497]; rfl
@[simp] theorem pc2499 : Artifact.submissionArtifact.instructionPC 2481 = 3231 := by
  calc
    Artifact.submissionArtifact.instructionPC 2481 =
        Artifact.submissionArtifact.instructionPC 2480 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 0 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2480 _ (by rfl)
    _ = 3231 := by rw [pc2498]; rfl
@[simp] theorem pc2500 : Artifact.submissionArtifact.instructionPC 2482 = 3232 := by
  calc
    Artifact.submissionArtifact.instructionPC 2482 =
        Artifact.submissionArtifact.instructionPC 2481 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MULMOD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2481 _ (by rfl)
    _ = 3232 := by rw [pc2499]; rfl
@[simp] theorem pc2501 : Artifact.submissionArtifact.instructionPC 2483 = 3233 := by
  calc
    Artifact.submissionArtifact.instructionPC 2483 =
        Artifact.submissionArtifact.instructionPC 2482 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MULMOD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2482 _ (by rfl)
    _ = 3233 := by rw [pc2500]; rfl
@[simp] theorem pc2502 : Artifact.submissionArtifact.instructionPC 2484 = 3234 := by
  calc
    Artifact.submissionArtifact.instructionPC 2484 =
        Artifact.submissionArtifact.instructionPC 2483 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 5 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2483 _ (by rfl)
    _ = 3234 := by rw [pc2501]; rfl
@[simp] theorem pc2503 : Artifact.submissionArtifact.instructionPC 2485 = 3235 := by
  calc
    Artifact.submissionArtifact.instructionPC 2485 =
        Artifact.submissionArtifact.instructionPC 2484 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.POP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2484 _ (by rfl)
    _ = 3235 := by rw [pc2502]; rfl
@[simp] theorem pc2504 : Artifact.submissionArtifact.instructionPC 2486 = 3236 := by
  calc
    Artifact.submissionArtifact.instructionPC 2486 =
        Artifact.submissionArtifact.instructionPC 2485 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 7 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2485 _ (by rfl)
    _ = 3236 := by rw [pc2503]; rfl
@[simp] theorem pc2505 : Artifact.submissionArtifact.instructionPC 2487 = 3238 := by
  calc
    Artifact.submissionArtifact.instructionPC 2487 =
        Artifact.submissionArtifact.instructionPC 2486 +
          (YulEvmCompiler.Instr.push 1 1).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2486 _ (by rfl)
    _ = 3238 := by rw [pc2504]; rfl
@[simp] theorem pc2506 : Artifact.submissionArtifact.instructionPC 2488 = 3239 := by
  calc
    Artifact.submissionArtifact.instructionPC 2488 =
        Artifact.submissionArtifact.instructionPC 2487 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 4 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2487 _ (by rfl)
    _ = 3239 := by rw [pc2505]; rfl
@[simp] theorem pc2507 : Artifact.submissionArtifact.instructionPC 2489 = 3241 := by
  calc
    Artifact.submissionArtifact.instructionPC 2489 =
        Artifact.submissionArtifact.instructionPC 2488 +
          (YulEvmCompiler.Instr.push 1 2).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2488 _ (by rfl)
    _ = 3241 := by rw [pc2506]; rfl
@[simp] theorem pc2508 : Artifact.submissionArtifact.instructionPC 2490 = 3242 := by
  calc
    Artifact.submissionArtifact.instructionPC 2490 =
        Artifact.submissionArtifact.instructionPC 2489 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.SHR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2489 _ (by rfl)
    _ = 3242 := by rw [pc2507]; rfl
@[simp] theorem pc2509 : Artifact.submissionArtifact.instructionPC 2491 = 3243 := by
  calc
    Artifact.submissionArtifact.instructionPC 2491 =
        Artifact.submissionArtifact.instructionPC 2490 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.AND).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2490 _ (by rfl)
    _ = 3243 := by rw [pc2508]; rfl
@[simp] theorem pc2510 : Artifact.submissionArtifact.instructionPC 2492 = 3244 := by
  calc
    Artifact.submissionArtifact.instructionPC 2492 =
        Artifact.submissionArtifact.instructionPC 2491 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 2 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2491 _ (by rfl)
    _ = 3244 := by rw [pc2509]; rfl
@[simp] theorem pc2511 : Artifact.submissionArtifact.instructionPC 2493 = 3245 := by
  calc
    Artifact.submissionArtifact.instructionPC 2493 =
        Artifact.submissionArtifact.instructionPC 2492 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MUL).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2492 _ (by rfl)
    _ = 3245 := by rw [pc2510]; rfl
@[simp] theorem pc2512 : Artifact.submissionArtifact.instructionPC 2494 = 3247 := by
  calc
    Artifact.submissionArtifact.instructionPC 2494 =
        Artifact.submissionArtifact.instructionPC 2493 +
          (YulEvmCompiler.Instr.push 1 1).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2493 _ (by rfl)
    _ = 3247 := by rw [pc2511]; rfl
@[simp] theorem pc2513 : Artifact.submissionArtifact.instructionPC 2495 = 3248 := by
  calc
    Artifact.submissionArtifact.instructionPC 2495 =
        Artifact.submissionArtifact.instructionPC 2494 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.ADD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2494 _ (by rfl)
    _ = 3248 := by rw [pc2512]; rfl
@[simp] theorem pc2514 : Artifact.submissionArtifact.instructionPC 2496 = 3249 := by
  calc
    Artifact.submissionArtifact.instructionPC 2496 =
        Artifact.submissionArtifact.instructionPC 2495 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2495 _ (by rfl)
    _ = 3249 := by rw [pc2513]; rfl
@[simp] theorem pc2515 : Artifact.submissionArtifact.instructionPC 2497 = 3250 := by
  calc
    Artifact.submissionArtifact.instructionPC 2497 =
        Artifact.submissionArtifact.instructionPC 2496 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 8 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2496 _ (by rfl)
    _ = 3250 := by rw [pc2514]; rfl
@[simp] theorem pc2516 : Artifact.submissionArtifact.instructionPC 2498 = 3251 := by
  calc
    Artifact.submissionArtifact.instructionPC 2498 =
        Artifact.submissionArtifact.instructionPC 2497 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 0 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2497 _ (by rfl)
    _ = 3251 := by rw [pc2515]; rfl
@[simp] theorem pc2517 : Artifact.submissionArtifact.instructionPC 2499 = 3252 := by
  calc
    Artifact.submissionArtifact.instructionPC 2499 =
        Artifact.submissionArtifact.instructionPC 2498 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MULMOD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2498 _ (by rfl)
    _ = 3252 := by rw [pc2516]; rfl
@[simp] theorem pc2518 : Artifact.submissionArtifact.instructionPC 2500 = 3253 := by
  calc
    Artifact.submissionArtifact.instructionPC 2500 =
        Artifact.submissionArtifact.instructionPC 2499 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MULMOD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2499 _ (by rfl)
    _ = 3253 := by rw [pc2517]; rfl
@[simp] theorem pc2519 : Artifact.submissionArtifact.instructionPC 2501 = 3254 := by
  calc
    Artifact.submissionArtifact.instructionPC 2501 =
        Artifact.submissionArtifact.instructionPC 2500 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 5 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2500 _ (by rfl)
    _ = 3254 := by rw [pc2518]; rfl
@[simp] theorem pc2520 : Artifact.submissionArtifact.instructionPC 2502 = 3255 := by
  calc
    Artifact.submissionArtifact.instructionPC 2502 =
        Artifact.submissionArtifact.instructionPC 2501 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.POP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2501 _ (by rfl)
    _ = 3255 := by rw [pc2519]; rfl
@[simp] theorem pc2521 : Artifact.submissionArtifact.instructionPC 2503 = 3256 := by
  calc
    Artifact.submissionArtifact.instructionPC 2503 =
        Artifact.submissionArtifact.instructionPC 2502 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 7 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2502 _ (by rfl)
    _ = 3256 := by rw [pc2520]; rfl
@[simp] theorem pc2522 : Artifact.submissionArtifact.instructionPC 2504 = 3258 := by
  calc
    Artifact.submissionArtifact.instructionPC 2504 =
        Artifact.submissionArtifact.instructionPC 2503 +
          (YulEvmCompiler.Instr.push 1 1).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2503 _ (by rfl)
    _ = 3258 := by rw [pc2521]; rfl
@[simp] theorem pc2523 : Artifact.submissionArtifact.instructionPC 2505 = 3259 := by
  calc
    Artifact.submissionArtifact.instructionPC 2505 =
        Artifact.submissionArtifact.instructionPC 2504 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 4 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2504 _ (by rfl)
    _ = 3259 := by rw [pc2522]; rfl
@[simp] theorem pc2524 : Artifact.submissionArtifact.instructionPC 2506 = 3261 := by
  calc
    Artifact.submissionArtifact.instructionPC 2506 =
        Artifact.submissionArtifact.instructionPC 2505 +
          (YulEvmCompiler.Instr.push 1 1).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2505 _ (by rfl)
    _ = 3261 := by rw [pc2523]; rfl
@[simp] theorem pc2525 : Artifact.submissionArtifact.instructionPC 2507 = 3262 := by
  calc
    Artifact.submissionArtifact.instructionPC 2507 =
        Artifact.submissionArtifact.instructionPC 2506 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.SHR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2506 _ (by rfl)
    _ = 3262 := by rw [pc2524]; rfl
@[simp] theorem pc2526 : Artifact.submissionArtifact.instructionPC 2508 = 3263 := by
  calc
    Artifact.submissionArtifact.instructionPC 2508 =
        Artifact.submissionArtifact.instructionPC 2507 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.AND).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2507 _ (by rfl)
    _ = 3263 := by rw [pc2525]; rfl
@[simp] theorem pc2527 : Artifact.submissionArtifact.instructionPC 2509 = 3264 := by
  calc
    Artifact.submissionArtifact.instructionPC 2509 =
        Artifact.submissionArtifact.instructionPC 2508 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 2 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2508 _ (by rfl)
    _ = 3264 := by rw [pc2526]; rfl
@[simp] theorem pc2528 : Artifact.submissionArtifact.instructionPC 2510 = 3265 := by
  calc
    Artifact.submissionArtifact.instructionPC 2510 =
        Artifact.submissionArtifact.instructionPC 2509 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MUL).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2509 _ (by rfl)
    _ = 3265 := by rw [pc2527]; rfl
@[simp] theorem pc2529 : Artifact.submissionArtifact.instructionPC 2511 = 3267 := by
  calc
    Artifact.submissionArtifact.instructionPC 2511 =
        Artifact.submissionArtifact.instructionPC 2510 +
          (YulEvmCompiler.Instr.push 1 1).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2510 _ (by rfl)
    _ = 3267 := by rw [pc2528]; rfl
@[simp] theorem pc2530 : Artifact.submissionArtifact.instructionPC 2512 = 3268 := by
  calc
    Artifact.submissionArtifact.instructionPC 2512 =
        Artifact.submissionArtifact.instructionPC 2511 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.ADD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2511 _ (by rfl)
    _ = 3268 := by rw [pc2529]; rfl
@[simp] theorem pc2531 : Artifact.submissionArtifact.instructionPC 2513 = 3269 := by
  calc
    Artifact.submissionArtifact.instructionPC 2513 =
        Artifact.submissionArtifact.instructionPC 2512 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2512 _ (by rfl)
    _ = 3269 := by rw [pc2530]; rfl
@[simp] theorem pc2532 : Artifact.submissionArtifact.instructionPC 2514 = 3270 := by
  calc
    Artifact.submissionArtifact.instructionPC 2514 =
        Artifact.submissionArtifact.instructionPC 2513 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 8 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2513 _ (by rfl)
    _ = 3270 := by rw [pc2531]; rfl
@[simp] theorem pc2533 : Artifact.submissionArtifact.instructionPC 2515 = 3271 := by
  calc
    Artifact.submissionArtifact.instructionPC 2515 =
        Artifact.submissionArtifact.instructionPC 2514 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 0 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2514 _ (by rfl)
    _ = 3271 := by rw [pc2532]; rfl
@[simp] theorem pc2534 : Artifact.submissionArtifact.instructionPC 2516 = 3272 := by
  calc
    Artifact.submissionArtifact.instructionPC 2516 =
        Artifact.submissionArtifact.instructionPC 2515 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MULMOD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2515 _ (by rfl)
    _ = 3272 := by rw [pc2533]; rfl
@[simp] theorem pc2535 : Artifact.submissionArtifact.instructionPC 2517 = 3273 := by
  calc
    Artifact.submissionArtifact.instructionPC 2517 =
        Artifact.submissionArtifact.instructionPC 2516 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MULMOD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2516 _ (by rfl)
    _ = 3273 := by rw [pc2534]; rfl
@[simp] theorem pc2536 : Artifact.submissionArtifact.instructionPC 2518 = 3274 := by
  calc
    Artifact.submissionArtifact.instructionPC 2518 =
        Artifact.submissionArtifact.instructionPC 2517 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 5 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2517 _ (by rfl)
    _ = 3274 := by rw [pc2535]; rfl
@[simp] theorem pc2537 : Artifact.submissionArtifact.instructionPC 2519 = 3275 := by
  calc
    Artifact.submissionArtifact.instructionPC 2519 =
        Artifact.submissionArtifact.instructionPC 2518 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.POP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2518 _ (by rfl)
    _ = 3275 := by rw [pc2536]; rfl
@[simp] theorem pc2538 : Artifact.submissionArtifact.instructionPC 2520 = 3276 := by
  calc
    Artifact.submissionArtifact.instructionPC 2520 =
        Artifact.submissionArtifact.instructionPC 2519 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 7 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2519 _ (by rfl)
    _ = 3276 := by rw [pc2537]; rfl
@[simp] theorem pc2539 : Artifact.submissionArtifact.instructionPC 2521 = 3278 := by
  calc
    Artifact.submissionArtifact.instructionPC 2521 =
        Artifact.submissionArtifact.instructionPC 2520 +
          (YulEvmCompiler.Instr.push 1 1).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2520 _ (by rfl)
    _ = 3278 := by rw [pc2538]; rfl
@[simp] theorem pc2542 : Artifact.submissionArtifact.instructionPC 2522 = 3279 := by
  calc
    Artifact.submissionArtifact.instructionPC 2522 =
        Artifact.submissionArtifact.instructionPC 2521 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 4 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2521 _ (by rfl)
    _ = 3279 := by rw [pc2539]; rfl
@[simp] theorem pc2543 : Artifact.submissionArtifact.instructionPC 2523 = 3280 := by
  calc
    Artifact.submissionArtifact.instructionPC 2523 =
        Artifact.submissionArtifact.instructionPC 2522 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.AND).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2522 _ (by rfl)
    _ = 3280 := by rw [pc2542]; rfl
@[simp] theorem pc2544 : Artifact.submissionArtifact.instructionPC 2524 = 3281 := by
  calc
    Artifact.submissionArtifact.instructionPC 2524 =
        Artifact.submissionArtifact.instructionPC 2523 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 2 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2523 _ (by rfl)
    _ = 3281 := by rw [pc2543]; rfl
@[simp] theorem pc2545 : Artifact.submissionArtifact.instructionPC 2525 = 3282 := by
  calc
    Artifact.submissionArtifact.instructionPC 2525 =
        Artifact.submissionArtifact.instructionPC 2524 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MUL).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2524 _ (by rfl)
    _ = 3282 := by rw [pc2544]; rfl
@[simp] theorem pc2546 : Artifact.submissionArtifact.instructionPC 2526 = 3284 := by
  calc
    Artifact.submissionArtifact.instructionPC 2526 =
        Artifact.submissionArtifact.instructionPC 2525 +
          (YulEvmCompiler.Instr.push 1 1).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2525 _ (by rfl)
    _ = 3284 := by rw [pc2545]; rfl
@[simp] theorem pc2547 : Artifact.submissionArtifact.instructionPC 2527 = 3285 := by
  calc
    Artifact.submissionArtifact.instructionPC 2527 =
        Artifact.submissionArtifact.instructionPC 2526 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.ADD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2526 _ (by rfl)
    _ = 3285 := by rw [pc2546]; rfl
@[simp] theorem pc2548 : Artifact.submissionArtifact.instructionPC 2528 = 3286 := by
  calc
    Artifact.submissionArtifact.instructionPC 2528 =
        Artifact.submissionArtifact.instructionPC 2527 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2527 _ (by rfl)
    _ = 3286 := by rw [pc2547]; rfl
@[simp] theorem pc2549 : Artifact.submissionArtifact.instructionPC 2529 = 3287 := by
  calc
    Artifact.submissionArtifact.instructionPC 2529 =
        Artifact.submissionArtifact.instructionPC 2528 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 8 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2528 _ (by rfl)
    _ = 3287 := by rw [pc2548]; rfl
@[simp] theorem pc2550 : Artifact.submissionArtifact.instructionPC 2530 = 3288 := by
  calc
    Artifact.submissionArtifact.instructionPC 2530 =
        Artifact.submissionArtifact.instructionPC 2529 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 0 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2529 _ (by rfl)
    _ = 3288 := by rw [pc2549]; rfl
@[simp] theorem pc2551 : Artifact.submissionArtifact.instructionPC 2531 = 3289 := by
  calc
    Artifact.submissionArtifact.instructionPC 2531 =
        Artifact.submissionArtifact.instructionPC 2530 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MULMOD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2530 _ (by rfl)
    _ = 3289 := by rw [pc2550]; rfl
@[simp] theorem pc2552 : Artifact.submissionArtifact.instructionPC 2532 = 3290 := by
  calc
    Artifact.submissionArtifact.instructionPC 2532 =
        Artifact.submissionArtifact.instructionPC 2531 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MULMOD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2531 _ (by rfl)
    _ = 3290 := by rw [pc2551]; rfl
@[simp] theorem pc2553 : Artifact.submissionArtifact.instructionPC 2533 = 3291 := by
  calc
    Artifact.submissionArtifact.instructionPC 2533 =
        Artifact.submissionArtifact.instructionPC 2532 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 5 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2532 _ (by rfl)
    _ = 3291 := by rw [pc2552]; rfl
@[simp] theorem pc2554 : Artifact.submissionArtifact.instructionPC 2534 = 3292 := by
  calc
    Artifact.submissionArtifact.instructionPC 2534 =
        Artifact.submissionArtifact.instructionPC 2533 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.POP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2533 _ (by rfl)
    _ = 3292 := by rw [pc2553]; rfl
@[simp] theorem pc2555 : Artifact.submissionArtifact.instructionPC 2535 = 3293 := by
  calc
    Artifact.submissionArtifact.instructionPC 2535 =
        Artifact.submissionArtifact.instructionPC 2534 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.POP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2534 _ (by rfl)
    _ = 3293 := by rw [pc2554]; rfl
@[simp] theorem pc2556 : Artifact.submissionArtifact.instructionPC 2536 = 3296 := by
  calc
    Artifact.submissionArtifact.instructionPC 2536 =
        Artifact.submissionArtifact.instructionPC 2535 +
          (YulEvmCompiler.Instr.push 2 628).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2535 _ (by rfl)
    _ = 3296 := by rw [pc2555]; rfl

@[simp] theorem wordBridgePC3418 : Artifact.submissionArtifact.instructionPC 2556 = 3330 := by rfl
@[simp] theorem wordBridgePC3419 : Artifact.submissionArtifact.instructionPC 2557 = 3331 := by
  calc
    Artifact.submissionArtifact.instructionPC 2557 =
        Artifact.submissionArtifact.instructionPC 2556 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.JUMPDEST).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2556 _ (by rfl)
    _ = 3331 := by rw [wordBridgePC3418]; rfl
@[simp] theorem wordBridgePC3422 : Artifact.submissionArtifact.instructionPC 2558 = 3334 := by
  calc
    Artifact.submissionArtifact.instructionPC 2558 =
        Artifact.submissionArtifact.instructionPC 2557 +
          (YulEvmCompiler.Instr.push 2 3130).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2557 _ (by rfl)
    _ = 3334 := by rw [wordBridgePC3419]; rfl

end Challenge.Modexp.Submission.Proofs.Bytecode.UnrollPCs
