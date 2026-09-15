import Challenge.Modexp.Submission.Proofs.Bytecode.PCFast
import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
namespace Challenge.Modexp.Submission.Proofs.Fast
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

def csGenericPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3252 .JUMPDEST,
   pushAt 3253 2 2688,
   opAt 3254 .MLOAD,
   pushAt 3255 2 256,
   opAt 3256 .EQ,
   pushAt 3257 2 4343,
   opAt 3258 .JUMPI,
   pushAt 3259 2 2688,
   opAt 3260 .MLOAD,
   pushAt 3261 1 128,
   opAt 3262 .EQ,
   pushAt 3263 2 4153,
   opAt 3264 .JUMPI,
   pushAt 3265 2 2784,
   opAt 3266 .MLOAD,
   pushAt 3267 2 2752,
   opAt 3268 .MLOAD,
   opAt 3269 (.Dup ⟨0, by decide⟩),
   pushAt 3270 2 1792,
   opAt 3271 .ADD,
   opAt 3272 (.Swap ⟨0, by decide⟩),
   pushAt 3273 0 0,
   opAt 3274 (.Swap ⟨2, by decide⟩),
   pushAt 3275 2 1443,
   opAt 3276 .JUMP]

def csFixedEntry8 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3252 .JUMPDEST,
   pushAt 3253 2 2688,
   opAt 3254 .MLOAD,
   pushAt 3255 2 256,
   opAt 3256 .EQ,
   pushAt 3257 2 4343,
   opAt 3258 .JUMPI,
   opAt 3277 .JUMPDEST]

def csFixedEntry4 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3252 .JUMPDEST,
   pushAt 3253 2 2688,
   opAt 3254 .MLOAD,
   pushAt 3255 2 256,
   opAt 3256 .EQ,
   pushAt 3257 2 4343,
   opAt 3258 .JUMPI,
   pushAt 3259 2 2688,
   opAt 3260 .MLOAD,
   pushAt 3261 1 128,
   opAt 3262 .EQ,
   pushAt 3263 2 4153,
   opAt 3264 .JUMPI,
   opAt 3148 .JUMPDEST]

def csFixedStep8_0 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3278 2 2336,
   opAt 3279 .MLOAD,
   pushAt 3280 1 224,
   opAt 3281 .MLOAD,
   opAt 3282 (.Dup ⟨0, by decide⟩),
   opAt 3283 (.Dup ⟨2, by decide⟩),
   opAt 3284 .SUB,
   pushAt 3285 3 2016,
   opAt 3286 .MSTORE,
   opAt 3287 .GT]

def csFixedStep8_1 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3288 1 192,
   opAt 3289 .MLOAD,
   pushAt 3290 2 2304,
   opAt 3291 .MLOAD,
   opAt 3292 (.Dup ⟨1, by decide⟩),
   opAt 3293 (.Dup ⟨1, by decide⟩),
   opAt 3294 .SUB,
   opAt 3295 (.Swap ⟨1, by decide⟩),
   opAt 3296 .GT,
   opAt 3297 (.Swap ⟨1, by decide⟩),
   opAt 3298 (.Dup ⟨0, by decide⟩),
   opAt 3299 (.Dup ⟨2, by decide⟩),
   opAt 3300 .SUB,
   pushAt 3301 3 1984,
   opAt 3302 .MSTORE,
   opAt 3303 .GT,
   opAt 3304 .OR]

def csFixedStep8_2 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3305 1 160,
   opAt 3306 .MLOAD,
   pushAt 3307 2 2272,
   opAt 3308 .MLOAD,
   opAt 3309 (.Dup ⟨1, by decide⟩),
   opAt 3310 (.Dup ⟨1, by decide⟩),
   opAt 3311 .SUB,
   opAt 3312 (.Swap ⟨1, by decide⟩),
   opAt 3313 .GT,
   opAt 3314 (.Swap ⟨1, by decide⟩),
   opAt 3315 (.Dup ⟨0, by decide⟩),
   opAt 3316 (.Dup ⟨2, by decide⟩),
   opAt 3317 .SUB,
   pushAt 3318 3 1952,
   opAt 3319 .MSTORE,
   opAt 3320 .GT,
   opAt 3321 .OR]

def csFixedStep8_3 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3322 1 128,
   opAt 3323 .MLOAD,
   pushAt 3324 2 2240,
   opAt 3325 .MLOAD,
   opAt 3326 (.Dup ⟨1, by decide⟩),
   opAt 3327 (.Dup ⟨1, by decide⟩),
   opAt 3328 .SUB,
   opAt 3329 (.Swap ⟨1, by decide⟩),
   opAt 3330 .GT,
   opAt 3331 (.Swap ⟨1, by decide⟩),
   opAt 3332 (.Dup ⟨0, by decide⟩),
   opAt 3333 (.Dup ⟨2, by decide⟩),
   opAt 3334 .SUB,
   pushAt 3335 3 1920,
   opAt 3336 .MSTORE,
   opAt 3337 .GT,
   opAt 3338 .OR]

def csFixedStep8_4 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3339 1 96,
   opAt 3340 .MLOAD,
   pushAt 3341 2 2208,
   opAt 3342 .MLOAD,
   opAt 3343 (.Dup ⟨1, by decide⟩),
   opAt 3344 (.Dup ⟨1, by decide⟩),
   opAt 3345 .SUB,
   opAt 3346 (.Swap ⟨1, by decide⟩),
   opAt 3347 .GT,
   opAt 3348 (.Swap ⟨1, by decide⟩),
   opAt 3349 (.Dup ⟨0, by decide⟩),
   opAt 3350 (.Dup ⟨2, by decide⟩),
   opAt 3351 .SUB,
   pushAt 3352 3 1888,
   opAt 3353 .MSTORE,
   opAt 3354 .GT,
   opAt 3355 .OR]

def csFixedStep8_5 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3356 .JUMPDEST,
   pushAt 3357 1 64,
   opAt 3358 .MLOAD,
   pushAt 3359 2 2176,
   opAt 3360 .MLOAD,
   opAt 3361 (.Dup ⟨1, by decide⟩),
   opAt 3362 (.Dup ⟨1, by decide⟩),
   opAt 3363 .SUB,
   opAt 3364 (.Swap ⟨1, by decide⟩),
   opAt 3365 .GT,
   opAt 3366 (.Swap ⟨1, by decide⟩),
   opAt 3367 (.Dup ⟨0, by decide⟩),
   opAt 3368 (.Dup ⟨2, by decide⟩),
   opAt 3369 .SUB,
   pushAt 3370 3 1856,
   opAt 3371 .MSTORE,
   opAt 3372 .GT,
   opAt 3373 .OR]

def csFixedStep8_6 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3374 1 32,
   opAt 3375 .MLOAD,
   pushAt 3376 2 2144,
   opAt 3377 .MLOAD,
   opAt 3378 (.Dup ⟨1, by decide⟩),
   opAt 3379 (.Dup ⟨1, by decide⟩),
   opAt 3380 .SUB,
   opAt 3381 (.Swap ⟨1, by decide⟩),
   opAt 3382 .GT,
   opAt 3383 (.Swap ⟨1, by decide⟩),
   opAt 3384 (.Dup ⟨0, by decide⟩),
   opAt 3385 (.Dup ⟨2, by decide⟩),
   opAt 3386 .SUB,
   pushAt 3387 3 1824,
   opAt 3388 .MSTORE,
   opAt 3389 .GT,
   opAt 3390 .OR]

def csFixedStep8_7 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3391 0 0,
   opAt 3392 .MLOAD,
   pushAt 3393 2 2112,
   opAt 3394 .MLOAD,
   opAt 3395 (.Dup ⟨1, by decide⟩),
   opAt 3396 (.Dup ⟨1, by decide⟩),
   opAt 3397 .SUB,
   opAt 3398 (.Swap ⟨1, by decide⟩),
   opAt 3399 .GT,
   opAt 3400 (.Swap ⟨1, by decide⟩),
   opAt 3401 (.Dup ⟨0, by decide⟩),
   opAt 3402 (.Dup ⟨2, by decide⟩),
   opAt 3403 .SUB,
   pushAt 3404 3 1792,
   opAt 3405 .MSTORE,
   opAt 3406 .GT,
   opAt 3407 .OR]

def csFixedTail8 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3408 .ISZERO,
   pushAt 3409 2 2080,
   opAt 3410 .MLOAD,
   opAt 3411 .OR,
   pushAt 3412 2 319,
   opAt 3413 .NOT,
   pushAt 3414 2 4555,
   opAt 3415 .JUMP,
   opAt 3428 .JUMPDEST,
   opAt 3429 .MUL,
   pushAt 3430 2 2112,
   opAt 3431 .ADD,
   pushAt 3432 2 2688,
   opAt 3433 .MLOAD,
   opAt 3434 (.Swap ⟨1, by decide⟩),
   opAt 3435 .MCOPY,
   opAt 3436 .JUMP]

def csFixedStep4_0 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3149 2 2208,
   opAt 3150 .MLOAD,
   pushAt 3151 1 96,
   opAt 3152 .MLOAD,
   opAt 3153 (.Dup ⟨1, by decide⟩),
   opAt 3154 (.Dup ⟨1, by decide⟩),
   opAt 3155 .GT,
   opAt 3156 (.Swap ⟨1, by decide⟩),
   opAt 3157 .SUB,
   pushAt 3158 2 1888,
   opAt 3159 .MSTORE,
   pushAt 3160 2 4452,
   opAt 3161 .JUMP]

def csFixedStep4_1 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3356 .JUMPDEST,
   pushAt 3357 1 64,
   opAt 3358 .MLOAD,
   pushAt 3359 2 2176,
   opAt 3360 .MLOAD,
   opAt 3361 (.Dup ⟨1, by decide⟩),
   opAt 3362 (.Dup ⟨1, by decide⟩),
   opAt 3363 .SUB,
   opAt 3364 (.Swap ⟨1, by decide⟩),
   opAt 3365 .GT,
   opAt 3366 (.Swap ⟨1, by decide⟩),
   opAt 3367 (.Dup ⟨0, by decide⟩),
   opAt 3368 (.Dup ⟨2, by decide⟩),
   opAt 3369 .SUB,
   pushAt 3370 3 1856,
   opAt 3371 .MSTORE,
   opAt 3372 .GT,
   opAt 3373 .OR]

def csFixedStep4_2 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3374 1 32,
   opAt 3375 .MLOAD,
   pushAt 3376 2 2144,
   opAt 3377 .MLOAD,
   opAt 3378 (.Dup ⟨1, by decide⟩),
   opAt 3379 (.Dup ⟨1, by decide⟩),
   opAt 3380 .SUB,
   opAt 3381 (.Swap ⟨1, by decide⟩),
   opAt 3382 .GT,
   opAt 3383 (.Swap ⟨1, by decide⟩),
   opAt 3384 (.Dup ⟨0, by decide⟩),
   opAt 3385 (.Dup ⟨2, by decide⟩),
   opAt 3386 .SUB,
   pushAt 3387 3 1824,
   opAt 3388 .MSTORE,
   opAt 3389 .GT,
   opAt 3390 .OR]

def csFixedStep4_3 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3391 0 0,
   opAt 3392 .MLOAD,
   pushAt 3393 2 2112,
   opAt 3394 .MLOAD,
   opAt 3395 (.Dup ⟨1, by decide⟩),
   opAt 3396 (.Dup ⟨1, by decide⟩),
   opAt 3397 .SUB,
   opAt 3398 (.Swap ⟨1, by decide⟩),
   opAt 3399 .GT,
   opAt 3400 (.Swap ⟨1, by decide⟩),
   opAt 3401 (.Dup ⟨0, by decide⟩),
   opAt 3402 (.Dup ⟨2, by decide⟩),
   opAt 3403 .SUB,
   pushAt 3404 3 1792,
   opAt 3405 .MSTORE,
   opAt 3406 .GT,
   opAt 3407 .OR]

def csFixedTail4 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3408 .ISZERO,
   pushAt 3409 2 2080,
   opAt 3410 .MLOAD,
   opAt 3411 .OR,
   pushAt 3412 2 319,
   opAt 3413 .NOT,
   pushAt 3414 2 4555,
   opAt 3415 .JUMP,
   opAt 3428 .JUMPDEST,
   opAt 3429 .MUL,
   pushAt 3430 2 2112,
   opAt 3431 .ADD,
   pushAt 3432 2 2688,
   opAt 3433 .MLOAD,
   opAt 3434 (.Swap ⟨1, by decide⟩),
   opAt 3435 .MCOPY,
   opAt 3436 .JUMP]

@[simp] theorem fixedPC1618 : Artifact.submissionArtifact.instructionPC 1022 = 1439 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC1619 : Artifact.submissionArtifact.instructionPC 1023 = 1442 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3777 : Artifact.submissionArtifact.instructionPC 3252 = 4299 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedJump4975 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4299 = true := by
  simpa only [Artifact.instructionPC, fixedPC3777] using Artifact.isValidJumpDest_index 3252 (by rfl)

@[simp] theorem fixedPC3778 : Artifact.submissionArtifact.instructionPC 3253 = 4300 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3779 : Artifact.submissionArtifact.instructionPC 3254 = 4303 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3780 : Artifact.submissionArtifact.instructionPC 3255 = 4304 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3781 : Artifact.submissionArtifact.instructionPC 3256 = 4307 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3782 : Artifact.submissionArtifact.instructionPC 3257 = 4308 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3783 : Artifact.submissionArtifact.instructionPC 3258 = 4311 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3784 : Artifact.submissionArtifact.instructionPC 3259 = 4312 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3785 : Artifact.submissionArtifact.instructionPC 3260 = 4315 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3786 : Artifact.submissionArtifact.instructionPC 3261 = 4316 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3787 : Artifact.submissionArtifact.instructionPC 3262 = 4318 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3788 : Artifact.submissionArtifact.instructionPC 3263 = 4319 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3789 : Artifact.submissionArtifact.instructionPC 3264 = 4322 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3790 : Artifact.submissionArtifact.instructionPC 3265 = 4323 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3791 : Artifact.submissionArtifact.instructionPC 3266 = 4326 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3792 : Artifact.submissionArtifact.instructionPC 3267 = 4327 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3793 : Artifact.submissionArtifact.instructionPC 3268 = 4330 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3794 : Artifact.submissionArtifact.instructionPC 3269 = 4331 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3795 : Artifact.submissionArtifact.instructionPC 3270 = 4332 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3796 : Artifact.submissionArtifact.instructionPC 3271 = 4335 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3797 : Artifact.submissionArtifact.instructionPC 3272 = 4336 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3798 : Artifact.submissionArtifact.instructionPC 3272 = 4336 := fixedPC3797

@[simp] theorem fixedPC3799 : Artifact.submissionArtifact.instructionPC 3272 = 4336 := fixedPC3797

@[simp] theorem fixedPC3800 : Artifact.submissionArtifact.instructionPC 3273 = 4337 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3801 : Artifact.submissionArtifact.instructionPC 3274 = 4338 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3802 : Artifact.submissionArtifact.instructionPC 3275 = 4339 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3803 : Artifact.submissionArtifact.instructionPC 3276 = 4342 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3804 : Artifact.submissionArtifact.instructionPC 3277 = 4343 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedJump5023 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4343 = true := by
  simpa only [Artifact.instructionPC, fixedPC3804] using Artifact.isValidJumpDest_index 3277 (by rfl)

@[simp] theorem fixedPC3805 : Artifact.submissionArtifact.instructionPC 3278 = 4344 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3806 : Artifact.submissionArtifact.instructionPC 3279 = 4347 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3807 : Artifact.submissionArtifact.instructionPC 3280 = 4348 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3808 : Artifact.submissionArtifact.instructionPC 3281 = 4350 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3809 : Artifact.submissionArtifact.instructionPC 3282 = 4351 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3810 : Artifact.submissionArtifact.instructionPC 3283 = 4352 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3811 : Artifact.submissionArtifact.instructionPC 3284 = 4353 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3812 : Artifact.submissionArtifact.instructionPC 3285 = 4354 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3813 : Artifact.submissionArtifact.instructionPC 3286 = 4358 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3814 : Artifact.submissionArtifact.instructionPC 3287 = 4359 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3815 : Artifact.submissionArtifact.instructionPC 3288 = 4360 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3816 : Artifact.submissionArtifact.instructionPC 3288 = 4360 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3817 : Artifact.submissionArtifact.instructionPC 3289 = 4362 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3818 : Artifact.submissionArtifact.instructionPC 3290 = 4363 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3819 : Artifact.submissionArtifact.instructionPC 3291 = 4366 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3820 : Artifact.submissionArtifact.instructionPC 3292 = 4367 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3821 : Artifact.submissionArtifact.instructionPC 3293 = 4368 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3822 : Artifact.submissionArtifact.instructionPC 3294 = 4369 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3823 : Artifact.submissionArtifact.instructionPC 3295 = 4370 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3824 : Artifact.submissionArtifact.instructionPC 3296 = 4371 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3825 : Artifact.submissionArtifact.instructionPC 3297 = 4372 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3826 : Artifact.submissionArtifact.instructionPC 3298 = 4373 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3827 : Artifact.submissionArtifact.instructionPC 3299 = 4374 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3828 : Artifact.submissionArtifact.instructionPC 3300 = 4375 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3829 : Artifact.submissionArtifact.instructionPC 3301 = 4376 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3830 : Artifact.submissionArtifact.instructionPC 3302 = 4380 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3831 : Artifact.submissionArtifact.instructionPC 3303 = 4381 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3832 : Artifact.submissionArtifact.instructionPC 3304 = 4382 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3833 : Artifact.submissionArtifact.instructionPC 3305 = 4383 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3834 : Artifact.submissionArtifact.instructionPC 3305 = 4383 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3835 : Artifact.submissionArtifact.instructionPC 3306 = 4385 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3836 : Artifact.submissionArtifact.instructionPC 3307 = 4386 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3837 : Artifact.submissionArtifact.instructionPC 3308 = 4389 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3838 : Artifact.submissionArtifact.instructionPC 3309 = 4390 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3839 : Artifact.submissionArtifact.instructionPC 3310 = 4391 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3840 : Artifact.submissionArtifact.instructionPC 3311 = 4392 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3841 : Artifact.submissionArtifact.instructionPC 3312 = 4393 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3842 : Artifact.submissionArtifact.instructionPC 3313 = 4394 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3843 : Artifact.submissionArtifact.instructionPC 3314 = 4395 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3844 : Artifact.submissionArtifact.instructionPC 3315 = 4396 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3845 : Artifact.submissionArtifact.instructionPC 3316 = 4397 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3846 : Artifact.submissionArtifact.instructionPC 3317 = 4398 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3847 : Artifact.submissionArtifact.instructionPC 3318 = 4399 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3848 : Artifact.submissionArtifact.instructionPC 3319 = 4403 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3849 : Artifact.submissionArtifact.instructionPC 3320 = 4404 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3850 : Artifact.submissionArtifact.instructionPC 3321 = 4405 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3851 : Artifact.submissionArtifact.instructionPC 3322 = 4406 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3852 : Artifact.submissionArtifact.instructionPC 3322 = 4406 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3853 : Artifact.submissionArtifact.instructionPC 3323 = 4408 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3854 : Artifact.submissionArtifact.instructionPC 3324 = 4409 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3855 : Artifact.submissionArtifact.instructionPC 3325 = 4412 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3856 : Artifact.submissionArtifact.instructionPC 3326 = 4413 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3857 : Artifact.submissionArtifact.instructionPC 3327 = 4414 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3858 : Artifact.submissionArtifact.instructionPC 3328 = 4415 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3859 : Artifact.submissionArtifact.instructionPC 3329 = 4416 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3860 : Artifact.submissionArtifact.instructionPC 3330 = 4417 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3861 : Artifact.submissionArtifact.instructionPC 3331 = 4418 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3862 : Artifact.submissionArtifact.instructionPC 3332 = 4419 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3863 : Artifact.submissionArtifact.instructionPC 3333 = 4420 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3864 : Artifact.submissionArtifact.instructionPC 3334 = 4421 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3865 : Artifact.submissionArtifact.instructionPC 3335 = 4422 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3866 : Artifact.submissionArtifact.instructionPC 3336 = 4426 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3867 : Artifact.submissionArtifact.instructionPC 3337 = 4427 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3868 : Artifact.submissionArtifact.instructionPC 3338 = 4428 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3869 : Artifact.submissionArtifact.instructionPC 3339 = 4429 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3871 : Artifact.submissionArtifact.instructionPC 3339 = 4429 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3872 : Artifact.submissionArtifact.instructionPC 3340 = 4431 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3873 : Artifact.submissionArtifact.instructionPC 3341 = 4432 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3874 : Artifact.submissionArtifact.instructionPC 3342 = 4435 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3875 : Artifact.submissionArtifact.instructionPC 3343 = 4436 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3876 : Artifact.submissionArtifact.instructionPC 3344 = 4437 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3877 : Artifact.submissionArtifact.instructionPC 3345 = 4438 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3878 : Artifact.submissionArtifact.instructionPC 3346 = 4439 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3879 : Artifact.submissionArtifact.instructionPC 3347 = 4440 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3880 : Artifact.submissionArtifact.instructionPC 3348 = 4441 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3881 : Artifact.submissionArtifact.instructionPC 3349 = 4442 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3882 : Artifact.submissionArtifact.instructionPC 3350 = 4443 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3883 : Artifact.submissionArtifact.instructionPC 3351 = 4444 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3884 : Artifact.submissionArtifact.instructionPC 3352 = 4445 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3885 : Artifact.submissionArtifact.instructionPC 3353 = 4449 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3886 : Artifact.submissionArtifact.instructionPC 3354 = 4450 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3887 : Artifact.submissionArtifact.instructionPC 3355 = 4451 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3888 : Artifact.submissionArtifact.instructionPC 3356 = 4452 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3889 : Artifact.submissionArtifact.instructionPC 3356 = 4452 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedJump5133 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4452 = true := by
  simpa only [Artifact.instructionPC, fixedPC3889] using Artifact.isValidJumpDest_index 3356 (by rfl)

@[simp] theorem fixedPC3890 : Artifact.submissionArtifact.instructionPC 3357 = 4453 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3891 : Artifact.submissionArtifact.instructionPC 3358 = 4455 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3892 : Artifact.submissionArtifact.instructionPC 3359 = 4456 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3893 : Artifact.submissionArtifact.instructionPC 3360 = 4459 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3894 : Artifact.submissionArtifact.instructionPC 3361 = 4460 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3895 : Artifact.submissionArtifact.instructionPC 3362 = 4461 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3896 : Artifact.submissionArtifact.instructionPC 3363 = 4462 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3897 : Artifact.submissionArtifact.instructionPC 3364 = 4463 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3898 : Artifact.submissionArtifact.instructionPC 3365 = 4464 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3899 : Artifact.submissionArtifact.instructionPC 3366 = 4465 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3900 : Artifact.submissionArtifact.instructionPC 3367 = 4466 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3901 : Artifact.submissionArtifact.instructionPC 3368 = 4467 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3902 : Artifact.submissionArtifact.instructionPC 3369 = 4468 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3903 : Artifact.submissionArtifact.instructionPC 3370 = 4469 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3904 : Artifact.submissionArtifact.instructionPC 3371 = 4473 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3905 : Artifact.submissionArtifact.instructionPC 3372 = 4474 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3906 : Artifact.submissionArtifact.instructionPC 3373 = 4475 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3907 : Artifact.submissionArtifact.instructionPC 3374 = 4476 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3908 : Artifact.submissionArtifact.instructionPC 3374 = 4476 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3909 : Artifact.submissionArtifact.instructionPC 3375 = 4478 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3910 : Artifact.submissionArtifact.instructionPC 3376 = 4479 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3911 : Artifact.submissionArtifact.instructionPC 3377 = 4482 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3912 : Artifact.submissionArtifact.instructionPC 3378 = 4483 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3913 : Artifact.submissionArtifact.instructionPC 3379 = 4484 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3914 : Artifact.submissionArtifact.instructionPC 3380 = 4485 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3915 : Artifact.submissionArtifact.instructionPC 3381 = 4486 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3916 : Artifact.submissionArtifact.instructionPC 3382 = 4487 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3917 : Artifact.submissionArtifact.instructionPC 3383 = 4488 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3918 : Artifact.submissionArtifact.instructionPC 3384 = 4489 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3919 : Artifact.submissionArtifact.instructionPC 3385 = 4490 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3920 : Artifact.submissionArtifact.instructionPC 3386 = 4491 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3921 : Artifact.submissionArtifact.instructionPC 3387 = 4492 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3922 : Artifact.submissionArtifact.instructionPC 3388 = 4496 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3923 : Artifact.submissionArtifact.instructionPC 3389 = 4497 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3924 : Artifact.submissionArtifact.instructionPC 3390 = 4498 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3925 : Artifact.submissionArtifact.instructionPC 3391 = 4499 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3926 : Artifact.submissionArtifact.instructionPC 3391 = 4499 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3927 : Artifact.submissionArtifact.instructionPC 3392 = 4500 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3928 : Artifact.submissionArtifact.instructionPC 3393 = 4501 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3929 : Artifact.submissionArtifact.instructionPC 3394 = 4504 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3930 : Artifact.submissionArtifact.instructionPC 3395 = 4505 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3931 : Artifact.submissionArtifact.instructionPC 3396 = 4506 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3932 : Artifact.submissionArtifact.instructionPC 3397 = 4507 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3933 : Artifact.submissionArtifact.instructionPC 3398 = 4508 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3934 : Artifact.submissionArtifact.instructionPC 3399 = 4509 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3935 : Artifact.submissionArtifact.instructionPC 3400 = 4510 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3936 : Artifact.submissionArtifact.instructionPC 3401 = 4511 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3937 : Artifact.submissionArtifact.instructionPC 3402 = 4512 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3938 : Artifact.submissionArtifact.instructionPC 3403 = 4513 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3939 : Artifact.submissionArtifact.instructionPC 3404 = 4514 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3940 : Artifact.submissionArtifact.instructionPC 3405 = 4518 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3941 : Artifact.submissionArtifact.instructionPC 3406 = 4519 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3942 : Artifact.submissionArtifact.instructionPC 3407 = 4520 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3943 : Artifact.submissionArtifact.instructionPC 3408 = 4521 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3944 : Artifact.submissionArtifact.instructionPC 3408 = 4521 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3945 : Artifact.submissionArtifact.instructionPC 3409 = 4522 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3946 : Artifact.submissionArtifact.instructionPC 3410 = 4525 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3947 : Artifact.submissionArtifact.instructionPC 3411 = 4526 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3948 : Artifact.submissionArtifact.instructionPC 3412 = 4527 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3949 : Artifact.submissionArtifact.instructionPC 3429 = 4556 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3950 : Artifact.submissionArtifact.instructionPC 3429 = 4556 :=
  fixedPC3949

@[simp] theorem fixedPC3951 : Artifact.submissionArtifact.instructionPC 3430 = 4557 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3952 : Artifact.submissionArtifact.instructionPC 3431 = 4560 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3953 : Artifact.submissionArtifact.instructionPC 3432 = 4561 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3954 : Artifact.submissionArtifact.instructionPC 3433 = 4564 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3955 : Artifact.submissionArtifact.instructionPC 3434 = 4565 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3956 : Artifact.submissionArtifact.instructionPC 3435 = 4566 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3957 : Artifact.submissionArtifact.instructionPC 3436 = 4567 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3999 : Artifact.submissionArtifact.instructionPC 3148 = 4153 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedJump5280 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4153 = true := by
  simpa only [Artifact.instructionPC, fixedPC3999] using Artifact.isValidJumpDest_index 3148 (by rfl)

@[simp] theorem fixedPC4000 : Artifact.submissionArtifact.instructionPC 3149 = 4154 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC4001 : Artifact.submissionArtifact.instructionPC 3150 = 4157 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC4002 : Artifact.submissionArtifact.instructionPC 3151 = 4158 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC4003 : Artifact.submissionArtifact.instructionPC 3152 = 4160 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC4004 : Artifact.submissionArtifact.instructionPC 3153 = 4161 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC4005 : Artifact.submissionArtifact.instructionPC 3154 = 4162 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC4006 : Artifact.submissionArtifact.instructionPC 3155 = 4163 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC4007 : Artifact.submissionArtifact.instructionPC 3156 = 4164 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC4008 : Artifact.submissionArtifact.instructionPC 3157 = 4165 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC4009 : Artifact.submissionArtifact.instructionPC 3158 = 4166 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC4010 : Artifact.submissionArtifact.instructionPC 3159 = 4169 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC4011 : Artifact.submissionArtifact.instructionPC 3160 = 4170 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC4012 : Artifact.submissionArtifact.instructionPC 3161 = 4173 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2880 : Artifact.submissionArtifact.instructionPC 2338 = 3107 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2883 : Artifact.submissionArtifact.instructionPC 3135 = 4132 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2884 : Artifact.submissionArtifact.instructionPC 3136 = 4133 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2885 : Artifact.submissionArtifact.instructionPC 3137 = 4134 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2886 : Artifact.submissionArtifact.instructionPC 3138 = 4135 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2887 : Artifact.submissionArtifact.instructionPC 3139 = 4138 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2888 : Artifact.submissionArtifact.instructionPC 3140 = 4139 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2889 : Artifact.submissionArtifact.instructionPC 3141 = 4140 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2890 : Artifact.submissionArtifact.instructionPC 3142 = 4143 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2891 : Artifact.submissionArtifact.instructionPC 3143 = 4144 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2892 : Artifact.submissionArtifact.instructionPC 3144 = 4145 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2893 : Artifact.submissionArtifact.instructionPC 3144 = 4145 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2894 : Artifact.submissionArtifact.instructionPC 3145 = 4148 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2895 : Artifact.submissionArtifact.instructionPC 3146 = 4149 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2896 : Artifact.submissionArtifact.instructionPC 3147 = 4152 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2927 : Artifact.submissionArtifact.instructionPC 2338 = 3107 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2930 : Artifact.submissionArtifact.instructionPC 3148 = 4153 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2931 : Artifact.submissionArtifact.instructionPC 3149 = 4154 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2932 : Artifact.submissionArtifact.instructionPC 3150 = 4157 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2933 : Artifact.submissionArtifact.instructionPC 3151 = 4158 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2934 : Artifact.submissionArtifact.instructionPC 3152 = 4160 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2935 : Artifact.submissionArtifact.instructionPC 3153 = 4161 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2936 : Artifact.submissionArtifact.instructionPC 3154 = 4162 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2937 : Artifact.submissionArtifact.instructionPC 3155 = 4163 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2938 : Artifact.submissionArtifact.instructionPC 3156 = 4164 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2939 : Artifact.submissionArtifact.instructionPC 3157 = 4165 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2940 : Artifact.submissionArtifact.instructionPC 3158 = 4166 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2941 : Artifact.submissionArtifact.instructionPC 3159 = 4169 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2942 : Artifact.submissionArtifact.instructionPC 3160 = 4170 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2943 : Artifact.submissionArtifact.instructionPC 3161 = 4173 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC3918 : Artifact.submissionArtifact.instructionPC 3413 = 4530 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC3919 : Artifact.submissionArtifact.instructionPC 3414 = 4531 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC3920 : Artifact.submissionArtifact.instructionPC 3415 = 4534 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC3921 : Artifact.submissionArtifact.instructionPC 3421 = 4544 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC3922 : Artifact.submissionArtifact.instructionPC 3422 = 4545 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC3923 : Artifact.submissionArtifact.instructionPC 3423 = 4548 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC3924 : Artifact.submissionArtifact.instructionPC 3424 = 4551 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC3925 : Artifact.submissionArtifact.instructionPC 3425 = 4552 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC3926 : Artifact.submissionArtifact.instructionPC 3426 = 4553 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC3927 : Artifact.submissionArtifact.instructionPC 3427 = 4554 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC3928 : Artifact.submissionArtifact.instructionPC 3428 = 4555 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

end Challenge.Modexp.Submission.Proofs.Fast
