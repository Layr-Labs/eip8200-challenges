import Challenge.Modexp.Submission.Proofs.Fast.MonproN8Memory
import Challenge.Modexp.Submission.Proofs.Fast.MonproN8PCs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace Challenge.Modexp.Submission.Proofs.Fast.MonproN8
open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast.Monpro
open Challenge.EvmProof.Word

/-- A boundary changes only pc, memory and the explicitly listed stack. -/
def atState (s : State) (mem : ByteArray) (pc : Nat) (stk : List UInt256) : State :=
  { s with pc := UInt256.ofNat pc, memory := mem, stack := stk }

def l1Next (mem : ByteArray) (bi : UInt256) (pa j : Nat) (c : UInt256) : MacState :=
  let x := MachineState.readWord mem (pa + 32 * (7 - j))
  let t := MachineState.readWord mem (8256 + 32 * (7 - j))
  { memory := MachineState.writeBytes mem
      (Data.Bytes.natToBytesPadded (macSum x bi t c).toNat 32) (8256 + 32 * (7 - j))
    carry := macCarry x bi t c }

def l2Next (mem : ByteArray) (mu : UInt256) (k : Nat) (c : UInt256) : MacState :=
  let x := MachineState.readWord mem (32 * (6 - k))
  let t := MachineState.readWord mem (8256 + 32 * (6 - k))
  { memory := MachineState.writeBytes mem
      (Data.Bytes.natToBytesPadded (macSum x mu t c).toNat 32) (8256 + 32 * (7 - k))
    carry := macCarry x mu t c }

theorem l1Next_eq (mem : ByteArray) (bi : UInt256) (pa j : Nat) :
    l1Next (l1Step mem bi pa 8 j).memory bi pa j (l1Step mem bi pa 8 j).carry =
      l1Step mem bi pa 8 (j + 1) := by rfl

theorem l2Next_eq (mem : ByteArray) (mu c0 : UInt256) (k : Nat) :
    l2Next (l2Step mem mu c0 8 k).memory mu k (l2Step mem mu c0 8 k).carry =
      l2Step mem mu c0 8 (k + 1) := by rfl

def block_l1_0 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3156 2 8480,
   opAt 3157 .MLOAD,
   opAt 3158 (.Dup ⟨3, by decide⟩),
   pushAt 3159 2 256,
   opAt 3160 .ADD,
   opAt 3161 .MLOAD,
   opAt 3162 (.Dup ⟨5, by decide⟩),
   opAt 3163 (.Dup ⟨4, by decide⟩),
   opAt 3164 (.Dup ⟨2, by decide⟩),
   opAt 3165 .MUL,
   opAt 3166 (.Swap ⟨1, by decide⟩),
   opAt 3167 (.Dup ⟨5, by decide⟩),
   opAt 3168 .MULMOD,
   opAt 3169 (.Dup ⟨1, by decide⟩),
   opAt 3170 (.Dup ⟨1, by decide⟩),
   opAt 3171 .LT,
   opAt 3172 .SUB,
   opAt 3173 (.Dup ⟨3, by decide⟩),
   opAt 3174 (.Dup ⟨2, by decide⟩),
   opAt 3175 .ADD,
   opAt 3176 (.Dup ⟨0, by decide⟩),
   opAt 3177 (.Swap ⟨4, by decide⟩),
   opAt 3178 .GT,
   opAt 3179 .SUB,
   opAt 3180 .SUB,
   opAt 3181 (.Swap ⟨0, by decide⟩),
   opAt 3182 (.Dup ⟨2, by decide⟩),
   opAt 3183 .ADD,
   opAt 3184 (.Dup ⟨0, by decide⟩),
   opAt 3185 (.Swap ⟨2, by decide⟩),
   opAt 3186 .GT,
   opAt 3187 .ADD,
   opAt 3188 (.Swap ⟨0, by decide⟩),
   pushAt 3189 2 8480,
   opAt 3190 .MSTORE]

theorem pc_l1_0 : Artifact.instructionPC 3156 = 4664 := by rfl

def block_l1_1 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3191 2 8448,
   opAt 3192 .MLOAD,
   opAt 3193 (.Dup ⟨3, by decide⟩),
   pushAt 3194 1 224,
   opAt 3195 .ADD,
   opAt 3196 .MLOAD,
   opAt 3197 (.Dup ⟨5, by decide⟩),
   opAt 3198 (.Dup ⟨4, by decide⟩),
   opAt 3199 (.Dup ⟨2, by decide⟩),
   opAt 3200 .MUL,
   opAt 3201 (.Swap ⟨1, by decide⟩),
   opAt 3202 (.Dup ⟨5, by decide⟩),
   opAt 3203 .MULMOD,
   opAt 3204 (.Dup ⟨1, by decide⟩),
   opAt 3205 (.Dup ⟨1, by decide⟩),
   opAt 3206 .LT,
   opAt 3207 .SUB,
   opAt 3208 (.Dup ⟨3, by decide⟩),
   opAt 3209 (.Dup ⟨2, by decide⟩),
   opAt 3210 .ADD,
   opAt 3211 (.Dup ⟨0, by decide⟩),
   opAt 3212 (.Swap ⟨4, by decide⟩),
   opAt 3213 .GT,
   opAt 3214 .SUB,
   opAt 3215 .SUB,
   opAt 3216 (.Swap ⟨0, by decide⟩),
   opAt 3217 (.Dup ⟨2, by decide⟩),
   opAt 3218 .ADD,
   opAt 3219 (.Dup ⟨0, by decide⟩),
   opAt 3220 (.Swap ⟨2, by decide⟩),
   opAt 3221 .GT,
   opAt 3222 .ADD,
   opAt 3223 (.Swap ⟨0, by decide⟩),
   pushAt 3224 2 8448,
   opAt 3225 .MSTORE]

theorem pc_l1_1 : Artifact.instructionPC 3191 = 4705 := by rfl

def block_l1_2 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3226 2 8416,
   opAt 3227 .MLOAD,
   opAt 3228 (.Dup ⟨3, by decide⟩),
   pushAt 3229 1 192,
   opAt 3230 .ADD,
   opAt 3231 .MLOAD,
   opAt 3232 (.Dup ⟨5, by decide⟩),
   opAt 3233 (.Dup ⟨4, by decide⟩),
   opAt 3234 (.Dup ⟨2, by decide⟩),
   opAt 3235 .MUL,
   opAt 3236 (.Swap ⟨1, by decide⟩),
   opAt 3237 (.Dup ⟨5, by decide⟩),
   opAt 3238 .MULMOD,
   opAt 3239 (.Dup ⟨1, by decide⟩),
   opAt 3240 (.Dup ⟨1, by decide⟩),
   opAt 3241 .LT,
   opAt 3242 .SUB,
   opAt 3243 (.Dup ⟨3, by decide⟩),
   opAt 3244 (.Dup ⟨2, by decide⟩),
   opAt 3245 .ADD,
   opAt 3246 (.Dup ⟨0, by decide⟩),
   opAt 3247 (.Swap ⟨4, by decide⟩),
   opAt 3248 .GT,
   opAt 3249 .SUB,
   opAt 3250 .SUB,
   opAt 3251 (.Swap ⟨0, by decide⟩),
   opAt 3252 (.Dup ⟨2, by decide⟩),
   opAt 3253 .ADD,
   opAt 3254 (.Dup ⟨0, by decide⟩),
   opAt 3255 (.Swap ⟨2, by decide⟩),
   opAt 3256 .GT,
   opAt 3257 .ADD,
   opAt 3258 (.Swap ⟨0, by decide⟩),
   pushAt 3259 2 8416,
   opAt 3260 .MSTORE]

theorem pc_l1_2 : Artifact.instructionPC 3226 = 4745 := by rfl

def block_l1_3 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3261 2 8384,
   opAt 3262 .MLOAD,
   opAt 3263 (.Dup ⟨3, by decide⟩),
   pushAt 3264 1 160,
   opAt 3265 .ADD,
   opAt 3266 .MLOAD,
   opAt 3267 (.Dup ⟨5, by decide⟩),
   opAt 3268 (.Dup ⟨4, by decide⟩),
   opAt 3269 (.Dup ⟨2, by decide⟩),
   opAt 3270 .MUL,
   opAt 3271 (.Swap ⟨1, by decide⟩),
   opAt 3272 (.Dup ⟨5, by decide⟩),
   opAt 3273 .MULMOD,
   opAt 3274 (.Dup ⟨1, by decide⟩),
   opAt 3275 (.Dup ⟨1, by decide⟩),
   opAt 3276 .LT,
   opAt 3277 .SUB,
   opAt 3278 (.Dup ⟨3, by decide⟩),
   opAt 3279 (.Dup ⟨2, by decide⟩),
   opAt 3280 .ADD,
   opAt 3281 (.Dup ⟨0, by decide⟩),
   opAt 3282 (.Swap ⟨4, by decide⟩),
   opAt 3283 .GT,
   opAt 3284 .SUB,
   opAt 3285 .SUB,
   opAt 3286 (.Swap ⟨0, by decide⟩),
   opAt 3287 (.Dup ⟨2, by decide⟩),
   opAt 3288 .ADD,
   opAt 3289 (.Dup ⟨0, by decide⟩),
   opAt 3290 (.Swap ⟨2, by decide⟩),
   opAt 3291 .GT,
   opAt 3292 .ADD,
   opAt 3293 (.Swap ⟨0, by decide⟩),
   pushAt 3294 2 8384,
   opAt 3295 .MSTORE]

theorem pc_l1_3 : Artifact.instructionPC 3261 = 4785 := by rfl

def block_l1_4 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3296 2 8352,
   opAt 3297 .MLOAD,
   opAt 3298 (.Dup ⟨3, by decide⟩),
   pushAt 3299 1 128,
   opAt 3300 .ADD,
   opAt 3301 .MLOAD,
   opAt 3302 (.Dup ⟨5, by decide⟩),
   opAt 3303 (.Dup ⟨4, by decide⟩),
   opAt 3304 (.Dup ⟨2, by decide⟩),
   opAt 3305 .MUL,
   opAt 3306 (.Swap ⟨1, by decide⟩),
   opAt 3307 (.Dup ⟨5, by decide⟩),
   opAt 3308 .MULMOD,
   opAt 3309 (.Dup ⟨1, by decide⟩),
   opAt 3310 (.Dup ⟨1, by decide⟩),
   opAt 3311 .LT,
   opAt 3312 .SUB,
   opAt 3313 (.Dup ⟨3, by decide⟩),
   opAt 3314 (.Dup ⟨2, by decide⟩),
   opAt 3315 .ADD,
   opAt 3316 (.Dup ⟨0, by decide⟩),
   opAt 3317 (.Swap ⟨4, by decide⟩),
   opAt 3318 .GT,
   opAt 3319 .SUB,
   opAt 3320 .SUB,
   opAt 3321 (.Swap ⟨0, by decide⟩),
   opAt 3322 (.Dup ⟨2, by decide⟩),
   opAt 3323 .ADD,
   opAt 3324 (.Dup ⟨0, by decide⟩),
   opAt 3325 (.Swap ⟨2, by decide⟩),
   opAt 3326 .GT,
   opAt 3327 .ADD,
   opAt 3328 (.Swap ⟨0, by decide⟩),
   pushAt 3329 2 8352,
   opAt 3330 .MSTORE]

theorem pc_l1_4 : Artifact.instructionPC 3296 = 4825 := by rfl

def block_l1_5 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3331 2 8320,
   opAt 3332 .MLOAD,
   opAt 3333 (.Dup ⟨3, by decide⟩),
   pushAt 3334 1 96,
   opAt 3335 .ADD,
   opAt 3336 .MLOAD,
   opAt 3337 (.Dup ⟨5, by decide⟩),
   opAt 3338 (.Dup ⟨4, by decide⟩),
   opAt 3339 (.Dup ⟨2, by decide⟩),
   opAt 3340 .MUL,
   opAt 3341 (.Swap ⟨1, by decide⟩),
   opAt 3342 (.Dup ⟨5, by decide⟩),
   opAt 3343 .MULMOD,
   opAt 3344 (.Dup ⟨1, by decide⟩),
   opAt 3345 (.Dup ⟨1, by decide⟩),
   opAt 3346 .LT,
   opAt 3347 .SUB,
   opAt 3348 (.Dup ⟨3, by decide⟩),
   opAt 3349 (.Dup ⟨2, by decide⟩),
   opAt 3350 .ADD,
   opAt 3351 (.Dup ⟨0, by decide⟩),
   opAt 3352 (.Swap ⟨4, by decide⟩),
   opAt 3353 .GT,
   opAt 3354 .SUB,
   opAt 3355 .SUB,
   opAt 3356 (.Swap ⟨0, by decide⟩),
   opAt 3357 (.Dup ⟨2, by decide⟩),
   opAt 3358 .ADD,
   opAt 3359 (.Dup ⟨0, by decide⟩),
   opAt 3360 (.Swap ⟨2, by decide⟩),
   opAt 3361 .GT,
   opAt 3362 .ADD,
   opAt 3363 (.Swap ⟨0, by decide⟩),
   pushAt 3364 2 8320,
   opAt 3365 .MSTORE]

theorem pc_l1_5 : Artifact.instructionPC 3331 = 4865 := by rfl

def block_l1_6 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3366 2 8288,
   opAt 3367 .MLOAD,
   opAt 3368 (.Dup ⟨3, by decide⟩),
   pushAt 3369 1 64,
   opAt 3370 .ADD,
   opAt 3371 .MLOAD,
   opAt 3372 (.Dup ⟨5, by decide⟩),
   opAt 3373 (.Dup ⟨4, by decide⟩),
   opAt 3374 (.Dup ⟨2, by decide⟩),
   opAt 3375 .MUL,
   opAt 3376 (.Swap ⟨1, by decide⟩),
   opAt 3377 (.Dup ⟨5, by decide⟩),
   opAt 3378 .MULMOD,
   opAt 3379 (.Dup ⟨1, by decide⟩),
   opAt 3380 (.Dup ⟨1, by decide⟩),
   opAt 3381 .LT,
   opAt 3382 .SUB,
   opAt 3383 (.Dup ⟨3, by decide⟩),
   opAt 3384 (.Dup ⟨2, by decide⟩),
   opAt 3385 .ADD,
   opAt 3386 (.Dup ⟨0, by decide⟩),
   opAt 3387 (.Swap ⟨4, by decide⟩),
   opAt 3388 .GT,
   opAt 3389 .SUB,
   opAt 3390 .SUB,
   opAt 3391 (.Swap ⟨0, by decide⟩),
   opAt 3392 (.Dup ⟨2, by decide⟩),
   opAt 3393 .ADD,
   opAt 3394 (.Dup ⟨0, by decide⟩),
   opAt 3395 (.Swap ⟨2, by decide⟩),
   opAt 3396 .GT,
   opAt 3397 .ADD,
   opAt 3398 (.Swap ⟨0, by decide⟩),
   pushAt 3399 2 8288,
   opAt 3400 .MSTORE]

theorem pc_l1_6 : Artifact.instructionPC 3366 = 4905 := by rfl

def block_l1_7 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3401 2 8256,
   opAt 3402 .MLOAD,
   opAt 3403 (.Dup ⟨3, by decide⟩),
   pushAt 3404 1 32,
   opAt 3405 .ADD,
   opAt 3406 .MLOAD,
   opAt 3407 (.Dup ⟨5, by decide⟩),
   opAt 3408 (.Dup ⟨4, by decide⟩),
   opAt 3409 (.Dup ⟨2, by decide⟩),
   opAt 3410 .MUL,
   opAt 3411 (.Swap ⟨1, by decide⟩),
   opAt 3412 (.Dup ⟨5, by decide⟩),
   opAt 3413 .MULMOD,
   opAt 3414 (.Dup ⟨1, by decide⟩),
   opAt 3415 (.Dup ⟨1, by decide⟩),
   opAt 3416 .LT,
   opAt 3417 .SUB,
   opAt 3418 (.Dup ⟨3, by decide⟩),
   opAt 3419 (.Dup ⟨2, by decide⟩),
   opAt 3420 .ADD,
   opAt 3421 (.Dup ⟨0, by decide⟩),
   opAt 3422 (.Swap ⟨4, by decide⟩),
   opAt 3423 .GT,
   opAt 3424 .SUB,
   opAt 3425 .SUB,
   opAt 3426 (.Swap ⟨0, by decide⟩),
   opAt 3427 (.Dup ⟨2, by decide⟩),
   opAt 3428 .ADD,
   opAt 3429 (.Dup ⟨0, by decide⟩),
   opAt 3430 (.Swap ⟨2, by decide⟩),
   opAt 3431 .GT,
   opAt 3432 .ADD,
   opAt 3433 (.Swap ⟨0, by decide⟩),
   pushAt 3434 2 8256,
   opAt 3435 .MSTORE]

theorem pc_l1_7 : Artifact.instructionPC 3401 = 4945 := by rfl

def block_l2_0 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3477 2 8448,
   opAt 3478 .MLOAD,
   pushAt 3479 1 192,
   opAt 3480 .MLOAD,
   opAt 3481 (.Dup ⟨4, by decide⟩),
   opAt 3482 (.Dup ⟨4, by decide⟩),
   opAt 3483 (.Dup ⟨2, by decide⟩),
   opAt 3484 .MUL,
   opAt 3485 (.Swap ⟨1, by decide⟩),
   opAt 3486 (.Dup ⟨5, by decide⟩),
   opAt 3487 .MULMOD,
   opAt 3488 (.Dup ⟨1, by decide⟩),
   opAt 3489 (.Dup ⟨1, by decide⟩),
   opAt 3490 .LT,
   opAt 3491 .SUB,
   opAt 3492 (.Dup ⟨3, by decide⟩),
   opAt 3493 (.Dup ⟨2, by decide⟩),
   opAt 3494 .ADD,
   opAt 3495 (.Dup ⟨0, by decide⟩),
   opAt 3496 (.Swap ⟨4, by decide⟩),
   opAt 3497 .GT,
   opAt 3498 .SUB,
   opAt 3499 .SUB,
   opAt 3500 (.Swap ⟨0, by decide⟩),
   opAt 3501 (.Dup ⟨2, by decide⟩),
   opAt 3502 .ADD,
   opAt 3503 (.Dup ⟨0, by decide⟩),
   opAt 3504 (.Swap ⟨2, by decide⟩),
   opAt 3505 .GT,
   opAt 3506 .ADD,
   opAt 3507 (.Swap ⟨0, by decide⟩),
   pushAt 3508 2 8480,
   opAt 3509 .MSTORE]

theorem pc_l2_0 : Artifact.instructionPC 3477 = 5037 := by rfl

def block_l2_1 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3510 2 8416,
   opAt 3511 .MLOAD,
   pushAt 3512 1 160,
   opAt 3513 .MLOAD,
   opAt 3514 (.Dup ⟨4, by decide⟩),
   opAt 3515 (.Dup ⟨4, by decide⟩),
   opAt 3516 (.Dup ⟨2, by decide⟩),
   opAt 3517 .MUL,
   opAt 3518 (.Swap ⟨1, by decide⟩),
   opAt 3519 (.Dup ⟨5, by decide⟩),
   opAt 3520 .MULMOD,
   opAt 3521 (.Dup ⟨1, by decide⟩),
   opAt 3522 (.Dup ⟨1, by decide⟩),
   opAt 3523 .LT,
   opAt 3524 .SUB,
   opAt 3525 (.Dup ⟨3, by decide⟩),
   opAt 3526 (.Dup ⟨2, by decide⟩),
   opAt 3527 .ADD,
   opAt 3528 (.Dup ⟨0, by decide⟩),
   opAt 3529 (.Swap ⟨4, by decide⟩),
   opAt 3530 .GT,
   opAt 3531 .SUB,
   opAt 3532 .SUB,
   opAt 3533 (.Swap ⟨0, by decide⟩),
   opAt 3534 (.Dup ⟨2, by decide⟩),
   opAt 3535 .ADD,
   opAt 3536 (.Dup ⟨0, by decide⟩),
   opAt 3537 (.Swap ⟨2, by decide⟩),
   opAt 3538 .GT,
   opAt 3539 .ADD,
   opAt 3540 (.Swap ⟨0, by decide⟩),
   pushAt 3541 2 8448,
   opAt 3542 .MSTORE]

theorem pc_l2_1 : Artifact.instructionPC 3510 = 5075 := by rfl

def block_l2_2 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3543 2 8384,
   opAt 3544 .MLOAD,
   pushAt 3545 1 128,
   opAt 3546 .MLOAD,
   opAt 3547 (.Dup ⟨4, by decide⟩),
   opAt 3548 (.Dup ⟨4, by decide⟩),
   opAt 3549 (.Dup ⟨2, by decide⟩),
   opAt 3550 .MUL,
   opAt 3551 (.Swap ⟨1, by decide⟩),
   opAt 3552 (.Dup ⟨5, by decide⟩),
   opAt 3553 .MULMOD,
   opAt 3554 (.Dup ⟨1, by decide⟩),
   opAt 3555 (.Dup ⟨1, by decide⟩),
   opAt 3556 .LT,
   opAt 3557 .SUB,
   opAt 3558 (.Dup ⟨3, by decide⟩),
   opAt 3559 (.Dup ⟨2, by decide⟩),
   opAt 3560 .ADD,
   opAt 3561 (.Dup ⟨0, by decide⟩),
   opAt 3562 (.Swap ⟨4, by decide⟩),
   opAt 3563 .GT,
   opAt 3564 .SUB,
   opAt 3565 .SUB,
   opAt 3566 (.Swap ⟨0, by decide⟩),
   opAt 3567 (.Dup ⟨2, by decide⟩),
   opAt 3568 .ADD,
   opAt 3569 (.Dup ⟨0, by decide⟩),
   opAt 3570 (.Swap ⟨2, by decide⟩),
   opAt 3571 .GT,
   opAt 3572 .ADD,
   opAt 3573 (.Swap ⟨0, by decide⟩),
   pushAt 3574 2 8416,
   opAt 3575 .MSTORE]

theorem pc_l2_2 : Artifact.instructionPC 3543 = 5113 := by rfl

def block_l2_3 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3576 2 8352,
   opAt 3577 .MLOAD,
   pushAt 3578 1 96,
   opAt 3579 .MLOAD,
   opAt 3580 (.Dup ⟨4, by decide⟩),
   opAt 3581 (.Dup ⟨4, by decide⟩),
   opAt 3582 (.Dup ⟨2, by decide⟩),
   opAt 3583 .MUL,
   opAt 3584 (.Swap ⟨1, by decide⟩),
   opAt 3585 (.Dup ⟨5, by decide⟩),
   opAt 3586 .MULMOD,
   opAt 3587 (.Dup ⟨1, by decide⟩),
   opAt 3588 (.Dup ⟨1, by decide⟩),
   opAt 3589 .LT,
   opAt 3590 .SUB,
   opAt 3591 (.Dup ⟨3, by decide⟩),
   opAt 3592 (.Dup ⟨2, by decide⟩),
   opAt 3593 .ADD,
   opAt 3594 (.Dup ⟨0, by decide⟩),
   opAt 3595 (.Swap ⟨4, by decide⟩),
   opAt 3596 .GT,
   opAt 3597 .SUB,
   opAt 3598 .SUB,
   opAt 3599 (.Swap ⟨0, by decide⟩),
   opAt 3600 (.Dup ⟨2, by decide⟩),
   opAt 3601 .ADD,
   opAt 3602 (.Dup ⟨0, by decide⟩),
   opAt 3603 (.Swap ⟨2, by decide⟩),
   opAt 3604 .GT,
   opAt 3605 .ADD,
   opAt 3606 (.Swap ⟨0, by decide⟩),
   pushAt 3607 2 8384,
   opAt 3608 .MSTORE]

theorem pc_l2_3 : Artifact.instructionPC 3576 = 5151 := by rfl

def block_l2_4 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3609 2 8320,
   opAt 3610 .MLOAD,
   pushAt 3611 1 64,
   opAt 3612 .MLOAD,
   opAt 3613 (.Dup ⟨4, by decide⟩),
   opAt 3614 (.Dup ⟨4, by decide⟩),
   opAt 3615 (.Dup ⟨2, by decide⟩),
   opAt 3616 .MUL,
   opAt 3617 (.Swap ⟨1, by decide⟩),
   opAt 3618 (.Dup ⟨5, by decide⟩),
   opAt 3619 .MULMOD,
   opAt 3620 (.Dup ⟨1, by decide⟩),
   opAt 3621 (.Dup ⟨1, by decide⟩),
   opAt 3622 .LT,
   opAt 3623 .SUB,
   opAt 3624 (.Dup ⟨3, by decide⟩),
   opAt 3625 (.Dup ⟨2, by decide⟩),
   opAt 3626 .ADD,
   opAt 3627 (.Dup ⟨0, by decide⟩),
   opAt 3628 (.Swap ⟨4, by decide⟩),
   opAt 3629 .GT,
   opAt 3630 .SUB,
   opAt 3631 .SUB,
   opAt 3632 (.Swap ⟨0, by decide⟩),
   opAt 3633 (.Dup ⟨2, by decide⟩),
   opAt 3634 .ADD,
   opAt 3635 (.Dup ⟨0, by decide⟩),
   opAt 3636 (.Swap ⟨2, by decide⟩),
   opAt 3637 .GT,
   opAt 3638 .ADD,
   opAt 3639 (.Swap ⟨0, by decide⟩),
   pushAt 3640 2 8352,
   opAt 3641 .MSTORE]

theorem pc_l2_4 : Artifact.instructionPC 3609 = 5189 := by rfl

def block_l2_5 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3642 2 8288,
   opAt 3643 .MLOAD,
   pushAt 3644 1 32,
   opAt 3645 .MLOAD,
   opAt 3646 (.Dup ⟨4, by decide⟩),
   opAt 3647 (.Dup ⟨4, by decide⟩),
   opAt 3648 (.Dup ⟨2, by decide⟩),
   opAt 3649 .MUL,
   opAt 3650 (.Swap ⟨1, by decide⟩),
   opAt 3651 (.Dup ⟨5, by decide⟩),
   opAt 3652 .MULMOD,
   opAt 3653 (.Dup ⟨1, by decide⟩),
   opAt 3654 (.Dup ⟨1, by decide⟩),
   opAt 3655 .LT,
   opAt 3656 .SUB,
   opAt 3657 (.Dup ⟨3, by decide⟩),
   opAt 3658 (.Dup ⟨2, by decide⟩),
   opAt 3659 .ADD,
   opAt 3660 (.Dup ⟨0, by decide⟩),
   opAt 3661 (.Swap ⟨4, by decide⟩),
   opAt 3662 .GT,
   opAt 3663 .SUB,
   opAt 3664 .SUB,
   opAt 3665 (.Swap ⟨0, by decide⟩),
   opAt 3666 (.Dup ⟨2, by decide⟩),
   opAt 3667 .ADD,
   opAt 3668 (.Dup ⟨0, by decide⟩),
   opAt 3669 (.Swap ⟨2, by decide⟩),
   opAt 3670 .GT,
   opAt 3671 .ADD,
   opAt 3672 (.Swap ⟨0, by decide⟩),
   pushAt 3673 2 8320,
   opAt 3674 .MSTORE]

theorem pc_l2_5 : Artifact.instructionPC 3642 = 5227 := by rfl

def block_l2_6 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3675 2 8256,
   opAt 3676 .MLOAD,
   pushAt 3677 0 0,
   opAt 3678 .MLOAD,
   opAt 3679 (.Dup ⟨4, by decide⟩),
   opAt 3680 (.Dup ⟨4, by decide⟩),
   opAt 3681 (.Dup ⟨2, by decide⟩),
   opAt 3682 .MUL,
   opAt 3683 (.Swap ⟨1, by decide⟩),
   opAt 3684 (.Dup ⟨5, by decide⟩),
   opAt 3685 .MULMOD,
   opAt 3686 (.Dup ⟨1, by decide⟩),
   opAt 3687 (.Dup ⟨1, by decide⟩),
   opAt 3688 .LT,
   opAt 3689 .SUB,
   opAt 3690 (.Dup ⟨3, by decide⟩),
   opAt 3691 (.Dup ⟨2, by decide⟩),
   opAt 3692 .ADD,
   opAt 3693 (.Dup ⟨0, by decide⟩),
   opAt 3694 (.Swap ⟨4, by decide⟩),
   opAt 3695 .GT,
   opAt 3696 .SUB,
   opAt 3697 .SUB,
   opAt 3698 (.Swap ⟨0, by decide⟩),
   opAt 3699 (.Dup ⟨2, by decide⟩),
   opAt 3700 .ADD,
   opAt 3701 (.Dup ⟨0, by decide⟩),
   opAt 3702 (.Swap ⟨2, by decide⟩),
   opAt 3703 .GT,
   opAt 3704 .ADD,
   opAt 3705 (.Swap ⟨0, by decide⟩),
   pushAt 3706 2 8288,
   opAt 3707 .MSTORE]

theorem pc_l2_6 : Artifact.instructionPC 3675 = 5265 := by rfl

def block_middle : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3436 (.Swap ⟨1, by decide⟩),
   opAt 3437 .POP,
   opAt 3438 .POP,
   pushAt 3439 2 8224,
   opAt 3440 .MLOAD,
   opAt 3441 (.Dup ⟨1, by decide⟩),
   opAt 3442 .ADD,
   opAt 3443 (.Dup ⟨1, by decide⟩),
   opAt 3444 (.Dup ⟨1, by decide⟩),
   opAt 3445 .LT,
   opAt 3446 (.Swap ⟨1, by decide⟩),
   opAt 3447 .POP,
   pushAt 3448 2 8224,
   opAt 3449 .MSTORE,
   pushAt 3450 2 8192,
   opAt 3451 .MSTORE]

theorem pc_middle : Artifact.instructionPC 3436 = 4985 := by rfl

def block_c0 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3452 2 8480,
   opAt 3453 .MLOAD,
   pushAt 3454 2 9376,
   opAt 3455 .MLOAD,
   opAt 3456 (.Swap ⟨0, by decide⟩),
   opAt 3457 .MUL,
   pushAt 3458 1 224,
   opAt 3459 .MLOAD,
   opAt 3460 (.Dup ⟨1, by decide⟩),
   opAt 3461 (.Dup ⟨1, by decide⟩),
   opAt 3462 .MUL,
   opAt 3463 (.Swap ⟨0, by decide⟩),
   opAt 3464 (.Dup ⟨3, by decide⟩),
   opAt 3465 (.Swap ⟨0, by decide⟩),
   opAt 3466 (.Dup ⟨3, by decide⟩),
   opAt 3467 .MULMOD,
   opAt 3468 (.Dup ⟨1, by decide⟩),
   opAt 3469 (.Dup ⟨1, by decide⟩),
   opAt 3470 .LT,
   opAt 3471 .SUB,
   opAt 3472 (.Dup ⟨1, by decide⟩),
   opAt 3473 .ISZERO,
   opAt 3474 .ISZERO,
   opAt 3475 .SUB,
   opAt 3476 .SUB]

theorem pc_c0 : Artifact.instructionPC 3452 = 5007 := by rfl

def block_tail : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3708 (.Swap ⟨0, by decide⟩),
   opAt 3709 .POP,
   pushAt 3710 2 8224,
   opAt 3711 .MLOAD,
   opAt 3712 (.Dup ⟨1, by decide⟩),
   opAt 3713 .ADD,
   opAt 3714 (.Dup ⟨1, by decide⟩),
   opAt 3715 (.Dup ⟨1, by decide⟩),
   opAt 3716 .LT,
   opAt 3717 (.Swap ⟨1, by decide⟩),
   opAt 3718 .POP,
   pushAt 3719 2 8256,
   opAt 3720 .MSTORE,
   pushAt 3721 2 8192,
   opAt 3722 .MLOAD,
   opAt 3723 .ADD,
   pushAt 3724 2 8224,
   opAt 3725 .MSTORE,
   opAt 3726 .POP,
   pushAt 3727 1 31,
   opAt 3728 .NOT,
   opAt 3729 .ADD]

theorem pc_tail : Artifact.instructionPC 3708 = 5302 := by rfl

/-- Exact actual-byte L1 MAC, with the entire suffix and memory. -/
theorem run_l1_0 (s : State) (mem : ByteArray) (bi c : UInt256) (pa : Nat) (rest : List UInt256)
    (hcap : rest.length ≤ 1013) (hrun : s.halt = .Running)
    (hact : 296 ≤ s.activeWords.toNat)
    (hpa : 32 ≤ pa) (hpaFit : pa + 256 ≤ 9472) :
    Challenge.EvmProof.Stepper.runLocatedBlock block_l1_0
      (atState s mem 4664 ([c, bi, UInt256.ofNat (pa - 32), maxWord] ++ rest)) =
      some (atState s (l1Next mem bi pa 0 c).memory 4705 ([(l1Next mem bi pa 0 c).carry, bi, UInt256.ofNat (pa - 32), maxWord] ++ rest)) := by
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have ha0 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat (pa + 224) 32) = s.activeWords :=
    activeWords_fix s _ 32 (by decide) (by omega) hact
  have ha1 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat (8480) 32) = s.activeWords :=
    activeWords_fix s _ 32 (by decide) (by omega) hact
  have hpaN : (pa - 32) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = pa - 32 := Nat.mod_eq_of_lt (by omega)
  have hxN : (256 + (pa - 32)) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = pa + 224 := by
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  simp (config := { maxSteps := 800000 })
    [block_l1_0, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr, atState, maxWord_literal,
      hrun, State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      UInt256.gt, UInt256.isTrue, List.exchange, l1Next, macSum, macCarry, mulHi,
      hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, ha0, ha1, hpaN, hxN]
  constructor
  · simp only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  · simpa only [mulHi, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (MacAlt.macCarryFix (MachineState.readWord mem (pa + 224)) bi (MachineState.readWord mem 8480) c)

/-- Exact actual-byte L1 MAC, with the entire suffix and memory. -/
theorem run_l1_1 (s : State) (mem : ByteArray) (bi c : UInt256) (pa : Nat) (rest : List UInt256)
    (hcap : rest.length ≤ 1013) (hrun : s.halt = .Running)
    (hact : 296 ≤ s.activeWords.toNat)
    (hpa : 32 ≤ pa) (hpaFit : pa + 256 ≤ 9472) :
    Challenge.EvmProof.Stepper.runLocatedBlock block_l1_1
      (atState s mem 4705 ([c, bi, UInt256.ofNat (pa - 32), maxWord] ++ rest)) =
      some (atState s (l1Next mem bi pa 1 c).memory 4745 ([(l1Next mem bi pa 1 c).carry, bi, UInt256.ofNat (pa - 32), maxWord] ++ rest)) := by
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have ha0 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat (pa + 192) 32) = s.activeWords :=
    activeWords_fix s _ 32 (by decide) (by omega) hact
  have ha1 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat (8448) 32) = s.activeWords :=
    activeWords_fix s _ 32 (by decide) (by omega) hact
  have hpaN : (pa - 32) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = pa - 32 := Nat.mod_eq_of_lt (by omega)
  have hxN : (224 + (pa - 32)) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = pa + 192 := by
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  simp (config := { maxSteps := 800000 })
    [block_l1_1, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr, atState, maxWord_literal,
      hrun, State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      UInt256.gt, UInt256.isTrue, List.exchange, l1Next, macSum, macCarry, mulHi,
      hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, ha0, ha1, hpaN, hxN]
  constructor
  · simp only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  · simpa only [mulHi, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (MacAlt.macCarryFix (MachineState.readWord mem (pa + 192)) bi (MachineState.readWord mem 8448) c)

/-- Exact actual-byte L1 MAC, with the entire suffix and memory. -/
theorem run_l1_2 (s : State) (mem : ByteArray) (bi c : UInt256) (pa : Nat) (rest : List UInt256)
    (hcap : rest.length ≤ 1013) (hrun : s.halt = .Running)
    (hact : 296 ≤ s.activeWords.toNat)
    (hpa : 32 ≤ pa) (hpaFit : pa + 256 ≤ 9472) :
    Challenge.EvmProof.Stepper.runLocatedBlock block_l1_2
      (atState s mem 4745 ([c, bi, UInt256.ofNat (pa - 32), maxWord] ++ rest)) =
      some (atState s (l1Next mem bi pa 2 c).memory 4785 ([(l1Next mem bi pa 2 c).carry, bi, UInt256.ofNat (pa - 32), maxWord] ++ rest)) := by
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have ha0 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat (pa + 160) 32) = s.activeWords :=
    activeWords_fix s _ 32 (by decide) (by omega) hact
  have ha1 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat (8416) 32) = s.activeWords :=
    activeWords_fix s _ 32 (by decide) (by omega) hact
  have hpaN : (pa - 32) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = pa - 32 := Nat.mod_eq_of_lt (by omega)
  have hxN : (192 + (pa - 32)) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = pa + 160 := by
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  simp (config := { maxSteps := 800000 })
    [block_l1_2, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr, atState, maxWord_literal,
      hrun, State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      UInt256.gt, UInt256.isTrue, List.exchange, l1Next, macSum, macCarry, mulHi,
      hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, ha0, ha1, hpaN, hxN]
  constructor
  · simp only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  · simpa only [mulHi, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (MacAlt.macCarryFix (MachineState.readWord mem (pa + 160)) bi (MachineState.readWord mem 8416) c)

/-- Exact actual-byte L1 MAC, with the entire suffix and memory. -/
theorem run_l1_3 (s : State) (mem : ByteArray) (bi c : UInt256) (pa : Nat) (rest : List UInt256)
    (hcap : rest.length ≤ 1013) (hrun : s.halt = .Running)
    (hact : 296 ≤ s.activeWords.toNat)
    (hpa : 32 ≤ pa) (hpaFit : pa + 256 ≤ 9472) :
    Challenge.EvmProof.Stepper.runLocatedBlock block_l1_3
      (atState s mem 4785 ([c, bi, UInt256.ofNat (pa - 32), maxWord] ++ rest)) =
      some (atState s (l1Next mem bi pa 3 c).memory 4825 ([(l1Next mem bi pa 3 c).carry, bi, UInt256.ofNat (pa - 32), maxWord] ++ rest)) := by
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have ha0 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat (pa + 128) 32) = s.activeWords :=
    activeWords_fix s _ 32 (by decide) (by omega) hact
  have ha1 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat (8384) 32) = s.activeWords :=
    activeWords_fix s _ 32 (by decide) (by omega) hact
  have hpaN : (pa - 32) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = pa - 32 := Nat.mod_eq_of_lt (by omega)
  have hxN : (160 + (pa - 32)) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = pa + 128 := by
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  simp (config := { maxSteps := 800000 })
    [block_l1_3, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr, atState, maxWord_literal,
      hrun, State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      UInt256.gt, UInt256.isTrue, List.exchange, l1Next, macSum, macCarry, mulHi,
      hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, ha0, ha1, hpaN, hxN]
  constructor
  · simp only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  · simpa only [mulHi, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (MacAlt.macCarryFix (MachineState.readWord mem (pa + 128)) bi (MachineState.readWord mem 8384) c)

/-- Exact actual-byte L1 MAC, with the entire suffix and memory. -/
theorem run_l1_4 (s : State) (mem : ByteArray) (bi c : UInt256) (pa : Nat) (rest : List UInt256)
    (hcap : rest.length ≤ 1013) (hrun : s.halt = .Running)
    (hact : 296 ≤ s.activeWords.toNat)
    (hpa : 32 ≤ pa) (hpaFit : pa + 256 ≤ 9472) :
    Challenge.EvmProof.Stepper.runLocatedBlock block_l1_4
      (atState s mem 4825 ([c, bi, UInt256.ofNat (pa - 32), maxWord] ++ rest)) =
      some (atState s (l1Next mem bi pa 4 c).memory 4865 ([(l1Next mem bi pa 4 c).carry, bi, UInt256.ofNat (pa - 32), maxWord] ++ rest)) := by
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have ha0 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat (pa + 96) 32) = s.activeWords :=
    activeWords_fix s _ 32 (by decide) (by omega) hact
  have ha1 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat (8352) 32) = s.activeWords :=
    activeWords_fix s _ 32 (by decide) (by omega) hact
  have hpaN : (pa - 32) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = pa - 32 := Nat.mod_eq_of_lt (by omega)
  have hxN : (128 + (pa - 32)) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = pa + 96 := by
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  simp (config := { maxSteps := 800000 })
    [block_l1_4, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr, atState, maxWord_literal,
      hrun, State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      UInt256.gt, UInt256.isTrue, List.exchange, l1Next, macSum, macCarry, mulHi,
      hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, ha0, ha1, hpaN, hxN]
  constructor
  · simp only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  · simpa only [mulHi, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (MacAlt.macCarryFix (MachineState.readWord mem (pa + 96)) bi (MachineState.readWord mem 8352) c)

/-- Exact actual-byte L1 MAC, with the entire suffix and memory. -/
theorem run_l1_5 (s : State) (mem : ByteArray) (bi c : UInt256) (pa : Nat) (rest : List UInt256)
    (hcap : rest.length ≤ 1013) (hrun : s.halt = .Running)
    (hact : 296 ≤ s.activeWords.toNat)
    (hpa : 32 ≤ pa) (hpaFit : pa + 256 ≤ 9472) :
    Challenge.EvmProof.Stepper.runLocatedBlock block_l1_5
      (atState s mem 4865 ([c, bi, UInt256.ofNat (pa - 32), maxWord] ++ rest)) =
      some (atState s (l1Next mem bi pa 5 c).memory 4905 ([(l1Next mem bi pa 5 c).carry, bi, UInt256.ofNat (pa - 32), maxWord] ++ rest)) := by
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have ha0 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat (pa + 64) 32) = s.activeWords :=
    activeWords_fix s _ 32 (by decide) (by omega) hact
  have ha1 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat (8320) 32) = s.activeWords :=
    activeWords_fix s _ 32 (by decide) (by omega) hact
  have hpaN : (pa - 32) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = pa - 32 := Nat.mod_eq_of_lt (by omega)
  have hxN : (96 + (pa - 32)) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = pa + 64 := by
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  simp (config := { maxSteps := 800000 })
    [block_l1_5, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr, atState, maxWord_literal,
      hrun, State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      UInt256.gt, UInt256.isTrue, List.exchange, l1Next, macSum, macCarry, mulHi,
      hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, ha0, ha1, hpaN, hxN]
  constructor
  · simp only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  · simpa only [mulHi, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (MacAlt.macCarryFix (MachineState.readWord mem (pa + 64)) bi (MachineState.readWord mem 8320) c)

/-- Exact actual-byte L1 MAC, with the entire suffix and memory. -/
theorem run_l1_6 (s : State) (mem : ByteArray) (bi c : UInt256) (pa : Nat) (rest : List UInt256)
    (hcap : rest.length ≤ 1013) (hrun : s.halt = .Running)
    (hact : 296 ≤ s.activeWords.toNat)
    (hpa : 32 ≤ pa) (hpaFit : pa + 256 ≤ 9472) :
    Challenge.EvmProof.Stepper.runLocatedBlock block_l1_6
      (atState s mem 4905 ([c, bi, UInt256.ofNat (pa - 32), maxWord] ++ rest)) =
      some (atState s (l1Next mem bi pa 6 c).memory 4945 ([(l1Next mem bi pa 6 c).carry, bi, UInt256.ofNat (pa - 32), maxWord] ++ rest)) := by
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have ha0 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat (pa + 32) 32) = s.activeWords :=
    activeWords_fix s _ 32 (by decide) (by omega) hact
  have ha1 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat (8288) 32) = s.activeWords :=
    activeWords_fix s _ 32 (by decide) (by omega) hact
  have hpaN : (pa - 32) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = pa - 32 := Nat.mod_eq_of_lt (by omega)
  have hxN : (64 + (pa - 32)) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = pa + 32 := by
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  simp (config := { maxSteps := 800000 })
    [block_l1_6, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr, atState, maxWord_literal,
      hrun, State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      UInt256.gt, UInt256.isTrue, List.exchange, l1Next, macSum, macCarry, mulHi,
      hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, ha0, ha1, hpaN, hxN]
  constructor
  · simp only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  · simpa only [mulHi, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (MacAlt.macCarryFix (MachineState.readWord mem (pa + 32)) bi (MachineState.readWord mem 8288) c)

/-- Exact actual-byte L1 MAC, with the entire suffix and memory. -/
theorem run_l1_7 (s : State) (mem : ByteArray) (bi c : UInt256) (pa : Nat) (rest : List UInt256)
    (hcap : rest.length ≤ 1013) (hrun : s.halt = .Running)
    (hact : 296 ≤ s.activeWords.toNat)
    (hpa : 32 ≤ pa) (hpaFit : pa + 256 ≤ 9472) :
    Challenge.EvmProof.Stepper.runLocatedBlock block_l1_7
      (atState s mem 4945 ([c, bi, UInt256.ofNat (pa - 32), maxWord] ++ rest)) =
      some (atState s (l1Next mem bi pa 7 c).memory 4985 ([(l1Next mem bi pa 7 c).carry, bi, UInt256.ofNat (pa - 32), maxWord] ++ rest)) := by
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have ha0 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat (pa + 0) 32) = s.activeWords :=
    activeWords_fix s _ 32 (by decide) (by omega) hact
  have ha1 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat (8256) 32) = s.activeWords :=
    activeWords_fix s _ 32 (by decide) (by omega) hact
  have hpaN : (pa - 32) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = pa - 32 := Nat.mod_eq_of_lt (by omega)
  have hxN : (32 + (pa - 32)) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = pa + 0 := by
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  simp (config := { maxSteps := 800000 })
    [block_l1_7, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr, atState, maxWord_literal,
      hrun, State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      UInt256.gt, UInt256.isTrue, List.exchange, l1Next, macSum, macCarry, mulHi,
      hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, ha0, ha1, hpaN, hxN]
  have ha0Nat := congrArg UInt256.toNat ha0
  simp only [Nat.add_zero, Challenge.EvmProof.Word.word_toNat_ofNat] at ha0Nat
  constructor
  · simp only [ha0Nat, ha1, true_and, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  · simpa only [mulHi, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (MacAlt.macCarryFix (MachineState.readWord mem (pa + 0)) bi (MachineState.readWord mem 8256) c)

/-- Exact actual-byte L2 MAC, with the entire suffix and memory. -/
theorem run_l2_0 (s : State) (mem : ByteArray) (mu c : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1013) (hrun : s.halt = .Running)
    (hact : 296 ≤ s.activeWords.toNat) :
    Challenge.EvmProof.Stepper.runLocatedBlock block_l2_0
      (atState s mem 5037 ([c, mu, maxWord] ++ rest)) =
      some (atState s (l2Next mem mu 0 c).memory 5075 ([(l2Next mem mu 0 c).carry, mu, maxWord] ++ rest)) := by
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have ha0 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat (192) 32) = s.activeWords :=
    activeWords_fix s _ 32 (by decide) (by omega) hact
  have ha1 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat (8448) 32) = s.activeWords :=
    activeWords_fix s _ 32 (by decide) (by omega) hact
  have ha2 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat (8480) 32) = s.activeWords :=
    activeWords_fix s _ 32 (by decide) (by omega) hact
  simp (config := { maxSteps := 800000 })
    [block_l2_0, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr, atState, maxWord_literal,
      hrun, State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      UInt256.gt, UInt256.isTrue, List.exchange, l2Next, macSum, macCarry, mulHi,
      hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, ha0, ha1, ha2]
  constructor
  · simp only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  · simpa only [mulHi, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (MacAlt.macCarryFix (MachineState.readWord mem 192) mu (MachineState.readWord mem 8448) c)

/-- Exact actual-byte L2 MAC, with the entire suffix and memory. -/
theorem run_l2_1 (s : State) (mem : ByteArray) (mu c : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1013) (hrun : s.halt = .Running)
    (hact : 296 ≤ s.activeWords.toNat) :
    Challenge.EvmProof.Stepper.runLocatedBlock block_l2_1
      (atState s mem 5075 ([c, mu, maxWord] ++ rest)) =
      some (atState s (l2Next mem mu 1 c).memory 5113 ([(l2Next mem mu 1 c).carry, mu, maxWord] ++ rest)) := by
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have ha0 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat (160) 32) = s.activeWords :=
    activeWords_fix s _ 32 (by decide) (by omega) hact
  have ha1 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat (8416) 32) = s.activeWords :=
    activeWords_fix s _ 32 (by decide) (by omega) hact
  have ha2 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat (8448) 32) = s.activeWords :=
    activeWords_fix s _ 32 (by decide) (by omega) hact
  simp (config := { maxSteps := 800000 })
    [block_l2_1, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr, atState, maxWord_literal,
      hrun, State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      UInt256.gt, UInt256.isTrue, List.exchange, l2Next, macSum, macCarry, mulHi,
      hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, ha0, ha1, ha2]
  constructor
  · simp only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  · simpa only [mulHi, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (MacAlt.macCarryFix (MachineState.readWord mem 160) mu (MachineState.readWord mem 8416) c)

/-- Exact actual-byte L2 MAC, with the entire suffix and memory. -/
theorem run_l2_2 (s : State) (mem : ByteArray) (mu c : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1013) (hrun : s.halt = .Running)
    (hact : 296 ≤ s.activeWords.toNat) :
    Challenge.EvmProof.Stepper.runLocatedBlock block_l2_2
      (atState s mem 5113 ([c, mu, maxWord] ++ rest)) =
      some (atState s (l2Next mem mu 2 c).memory 5151 ([(l2Next mem mu 2 c).carry, mu, maxWord] ++ rest)) := by
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have ha0 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat (128) 32) = s.activeWords :=
    activeWords_fix s _ 32 (by decide) (by omega) hact
  have ha1 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat (8384) 32) = s.activeWords :=
    activeWords_fix s _ 32 (by decide) (by omega) hact
  have ha2 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat (8416) 32) = s.activeWords :=
    activeWords_fix s _ 32 (by decide) (by omega) hact
  simp (config := { maxSteps := 800000 })
    [block_l2_2, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr, atState, maxWord_literal,
      hrun, State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      UInt256.gt, UInt256.isTrue, List.exchange, l2Next, macSum, macCarry, mulHi,
      hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, ha0, ha1, ha2]
  constructor
  · simp only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  · simpa only [mulHi, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (MacAlt.macCarryFix (MachineState.readWord mem 128) mu (MachineState.readWord mem 8384) c)

/-- Exact actual-byte L2 MAC, with the entire suffix and memory. -/
theorem run_l2_3 (s : State) (mem : ByteArray) (mu c : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1013) (hrun : s.halt = .Running)
    (hact : 296 ≤ s.activeWords.toNat) :
    Challenge.EvmProof.Stepper.runLocatedBlock block_l2_3
      (atState s mem 5151 ([c, mu, maxWord] ++ rest)) =
      some (atState s (l2Next mem mu 3 c).memory 5189 ([(l2Next mem mu 3 c).carry, mu, maxWord] ++ rest)) := by
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have ha0 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat (96) 32) = s.activeWords :=
    activeWords_fix s _ 32 (by decide) (by omega) hact
  have ha1 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat (8352) 32) = s.activeWords :=
    activeWords_fix s _ 32 (by decide) (by omega) hact
  have ha2 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat (8384) 32) = s.activeWords :=
    activeWords_fix s _ 32 (by decide) (by omega) hact
  simp (config := { maxSteps := 800000 })
    [block_l2_3, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr, atState, maxWord_literal,
      hrun, State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      UInt256.gt, UInt256.isTrue, List.exchange, l2Next, macSum, macCarry, mulHi,
      hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, ha0, ha1, ha2]
  constructor
  · simp only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  · simpa only [mulHi, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (MacAlt.macCarryFix (MachineState.readWord mem 96) mu (MachineState.readWord mem 8352) c)

/-- Exact actual-byte L2 MAC, with the entire suffix and memory. -/
theorem run_l2_4 (s : State) (mem : ByteArray) (mu c : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1013) (hrun : s.halt = .Running)
    (hact : 296 ≤ s.activeWords.toNat) :
    Challenge.EvmProof.Stepper.runLocatedBlock block_l2_4
      (atState s mem 5189 ([c, mu, maxWord] ++ rest)) =
      some (atState s (l2Next mem mu 4 c).memory 5227 ([(l2Next mem mu 4 c).carry, mu, maxWord] ++ rest)) := by
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have ha0 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat (64) 32) = s.activeWords :=
    activeWords_fix s _ 32 (by decide) (by omega) hact
  have ha1 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat (8320) 32) = s.activeWords :=
    activeWords_fix s _ 32 (by decide) (by omega) hact
  have ha2 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat (8352) 32) = s.activeWords :=
    activeWords_fix s _ 32 (by decide) (by omega) hact
  simp (config := { maxSteps := 800000 })
    [block_l2_4, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr, atState, maxWord_literal,
      hrun, State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      UInt256.gt, UInt256.isTrue, List.exchange, l2Next, macSum, macCarry, mulHi,
      hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, ha0, ha1, ha2]
  constructor
  · simp only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  · simpa only [mulHi, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (MacAlt.macCarryFix (MachineState.readWord mem 64) mu (MachineState.readWord mem 8320) c)

/-- Exact actual-byte L2 MAC, with the entire suffix and memory. -/
theorem run_l2_5 (s : State) (mem : ByteArray) (mu c : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1013) (hrun : s.halt = .Running)
    (hact : 296 ≤ s.activeWords.toNat) :
    Challenge.EvmProof.Stepper.runLocatedBlock block_l2_5
      (atState s mem 5227 ([c, mu, maxWord] ++ rest)) =
      some (atState s (l2Next mem mu 5 c).memory 5265 ([(l2Next mem mu 5 c).carry, mu, maxWord] ++ rest)) := by
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have ha0 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat (32) 32) = s.activeWords :=
    activeWords_fix s _ 32 (by decide) (by omega) hact
  have ha1 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat (8288) 32) = s.activeWords :=
    activeWords_fix s _ 32 (by decide) (by omega) hact
  have ha2 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat (8320) 32) = s.activeWords :=
    activeWords_fix s _ 32 (by decide) (by omega) hact
  simp (config := { maxSteps := 800000 })
    [block_l2_5, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr, atState, maxWord_literal,
      hrun, State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      UInt256.gt, UInt256.isTrue, List.exchange, l2Next, macSum, macCarry, mulHi,
      hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, ha0, ha1, ha2]
  constructor
  · simp only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  · simpa only [mulHi, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (MacAlt.macCarryFix (MachineState.readWord mem 32) mu (MachineState.readWord mem 8288) c)

/-- Exact actual-byte L2 MAC, with the entire suffix and memory. -/
theorem run_l2_6 (s : State) (mem : ByteArray) (mu c : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1013) (hrun : s.halt = .Running)
    (hact : 296 ≤ s.activeWords.toNat) :
    Challenge.EvmProof.Stepper.runLocatedBlock block_l2_6
      (atState s mem 5265 ([c, mu, maxWord] ++ rest)) =
      some (atState s (l2Next mem mu 6 c).memory 5302 ([(l2Next mem mu 6 c).carry, mu, maxWord] ++ rest)) := by
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have ha0 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat (0) 32) = s.activeWords :=
    activeWords_fix s _ 32 (by decide) (by omega) hact
  have ha1 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat (8256) 32) = s.activeWords :=
    activeWords_fix s _ 32 (by decide) (by omega) hact
  have ha2 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat (8288) 32) = s.activeWords :=
    activeWords_fix s _ 32 (by decide) (by omega) hact
  simp (config := { maxSteps := 800000 })
    [block_l2_6, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr, atState, maxWord_literal,
      hrun, State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      UInt256.gt, UInt256.isTrue, List.exchange, l2Next, macSum, macCarry, mulHi,
      hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, ha0, ha1, ha2]
  have ha0Nat := congrArg UInt256.toNat ha0
  simp only [Challenge.EvmProof.Word.word_toNat_ofNat] at ha0Nat
  constructor
  · simp only [ha0Nat, ha1, ha2, true_and, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  · simpa only [mulHi, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (MacAlt.macCarryFix (MachineState.readWord mem 0) mu (MachineState.readWord mem 8256) c)

theorem wordAddComm (x y : UInt256) : x + y = y + x := by
  apply word_ext
  simp only [word_toNat_add]
  rw [Nat.add_comm]

theorem wordMulComm (x y : UInt256) : x * y = y * x := by
  apply word_ext
  simp only [Monpro.word_toNat_mul]
  rw [Nat.mul_comm]

/-- Exact middle boundary; complete scratch and frame are retained. -/
theorem run_middle (s : State) (mem : ByteArray) (c bi ap : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1013) (hrun : s.halt = .Running)
    (hact : 296 ≤ s.activeWords.toNat) :
    Challenge.EvmProof.Stepper.runLocatedBlock block_middle
      (atState s mem 4985 ([c, bi, ap, maxWord] ++ rest)) =
      some (atState s (midMem mem c) 5007 ([maxWord] ++ rest)) := by
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have ha0 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat (8224) 32) = s.activeWords :=
    activeWords_fix s _ 32 (by decide) (by omega) hact
  have ha1 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat (8192) 32) = s.activeWords :=
    activeWords_fix s _ 32 (by decide) (by omega) hact
  simp (config := { maxSteps := 800000 })
    [block_middle, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr, atState, maxWord_literal,
      hrun, State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      UInt256.gt, UInt256.isTrue, List.exchange, midMem, midMem1, wordAddComm, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, ha0, ha1]

/-- Exact c0 boundary; complete scratch and frame are retained. -/
theorem run_c0 (s : State) (mem : ByteArray)  (rest : List UInt256)
    (hcap : rest.length ≤ 1013) (hrun : s.halt = .Running)
    (hact : 296 ≤ s.activeWords.toNat) :
    Challenge.EvmProof.Stepper.runLocatedBlock block_c0
      (atState s mem 5007 ([maxWord] ++ rest)) =
      some (atState s (mem) 5037 ([rowC0 mem 8, rowMu mem 8, maxWord] ++ rest)) := by
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have ha0 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat (8480) 32) = s.activeWords :=
    activeWords_fix s _ 32 (by decide) (by omega) hact
  have ha1 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat (9376) 32) = s.activeWords :=
    activeWords_fix s _ 32 (by decide) (by omega) hact
  have ha2 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat (224) 32) = s.activeWords :=
    activeWords_fix s _ 32 (by decide) (by omega) hact
  simp (config := { maxSteps := 800000 })
    [block_c0, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr, atState, maxWord_literal,
      hrun, State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      UInt256.gt, UInt256.isTrue, List.exchange, rowC0, rowMu, mulHi, wordMulComm, MacAlt.subSubFold, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, ha0, ha1, ha2]

  all_goals simp only [MacAlt.mulMod_comm]

/-- Exact tail boundary; complete scratch and frame are retained. -/
theorem run_tail (s : State) (mem : ByteArray) (c mu pbi : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1013) (hrun : s.halt = .Running)
    (hact : 296 ≤ s.activeWords.toNat) :
    Challenge.EvmProof.Stepper.runLocatedBlock block_tail
      (atState s mem 5302 ([c, mu, maxWord, pbi] ++ rest)) =
      some (atState s (tailMem mem c) 5333 ([UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904 + pbi] ++ rest)) := by
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have ha0 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat (8224) 32) = s.activeWords :=
    activeWords_fix s _ 32 (by decide) (by omega) hact
  have ha1 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat (8256) 32) = s.activeWords :=
    activeWords_fix s _ 32 (by decide) (by omega) hact
  have ha2 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat (8192) 32) = s.activeWords :=
    activeWords_fix s _ 32 (by decide) (by omega) hact
  simp (config := { maxSteps := 800000 })
    [block_tail, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr, atState, maxWord_literal,
      hrun, State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      UInt256.gt, UInt256.isTrue, List.exchange, tailMem, tailMem1, wordAddComm, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, ha0, ha1, ha2]

  all_goals rw [show (UInt256.ofNat 31).lnot = UInt256.ofNat
    115792089237316195423570985008687907853269984665640564039457584007913129639904 from by decide]

/-- Cache the concrete artifact/code conversion once instead of repeating it
at every boundary of the composed row. -/
def gasSteps_cachedBlock (s : State)
    (path : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka))
    {t : State}
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hresult : Challenge.EvmProof.Stepper.runLocatedBlock path s = some t)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps s t :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka path hcode hfork hresult hrun hnp

/-- One full arithmetic row: all eight L1 steps, exact midMem,
seven L2 steps and exact tailMem. The caller suffix is unchanged, and the
outer pointer is decremented. No reducedness or inverse premise is used. -/
def gasSteps_rowArithmetic (s : State) (mem : ByteArray) (pa pb i : Nat)
    (pbi : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1012) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat)
    (hpa : 32 ≤ pa) (hpaFit : pa + 256 ≤ 9472) :
    Challenge.EvmProof.GasSteps
      (atState s mem 4664
        ([UInt256.ofNat 0, rowBi mem pb 8 i, UInt256.ofNat (pa - 32), maxWord, pbi] ++ rest))
      (atState s (rowMem mem pa pb 8 i) 5333
        ([UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904 + pbi] ++ rest)) := by
  let bi := rowBi mem pb 8 i
  let suffix := pbi :: rest
  have hcap' : suffix.length ≤ 1013 := by simp only [suffix, List.length_cons]; omega
  have hL1_0 := gasSteps_cachedBlock
    (s := atState s (l1Step mem bi pa 8 0).memory 4664 ([(l1Step mem bi pa 8 0).carry, bi, UInt256.ofNat (pa - 32), maxWord] ++ suffix)) block_l1_0 hcode hfork
    (run_l1_0 s (l1Step mem bi pa 8 0).memory bi (l1Step mem bi pa 8 0).carry pa suffix
      hcap' hrun hact hpa hpaFit) hrun hnp
  rw [l1Next_eq] at hL1_0
  have hL1_1 := gasSteps_cachedBlock
    (s := atState s (l1Step mem bi pa 8 1).memory 4705 ([(l1Step mem bi pa 8 1).carry, bi, UInt256.ofNat (pa - 32), maxWord] ++ suffix)) block_l1_1 hcode hfork
    (run_l1_1 s (l1Step mem bi pa 8 1).memory bi (l1Step mem bi pa 8 1).carry pa suffix
      hcap' hrun hact hpa hpaFit) hrun hnp
  rw [l1Next_eq] at hL1_1
  have hL1_2 := gasSteps_cachedBlock
    (s := atState s (l1Step mem bi pa 8 2).memory 4745 ([(l1Step mem bi pa 8 2).carry, bi, UInt256.ofNat (pa - 32), maxWord] ++ suffix)) block_l1_2 hcode hfork
    (run_l1_2 s (l1Step mem bi pa 8 2).memory bi (l1Step mem bi pa 8 2).carry pa suffix
      hcap' hrun hact hpa hpaFit) hrun hnp
  rw [l1Next_eq] at hL1_2
  have hL1_3 := gasSteps_cachedBlock
    (s := atState s (l1Step mem bi pa 8 3).memory 4785 ([(l1Step mem bi pa 8 3).carry, bi, UInt256.ofNat (pa - 32), maxWord] ++ suffix)) block_l1_3 hcode hfork
    (run_l1_3 s (l1Step mem bi pa 8 3).memory bi (l1Step mem bi pa 8 3).carry pa suffix
      hcap' hrun hact hpa hpaFit) hrun hnp
  rw [l1Next_eq] at hL1_3
  have hL1_4 := gasSteps_cachedBlock
    (s := atState s (l1Step mem bi pa 8 4).memory 4825 ([(l1Step mem bi pa 8 4).carry, bi, UInt256.ofNat (pa - 32), maxWord] ++ suffix)) block_l1_4 hcode hfork
    (run_l1_4 s (l1Step mem bi pa 8 4).memory bi (l1Step mem bi pa 8 4).carry pa suffix
      hcap' hrun hact hpa hpaFit) hrun hnp
  rw [l1Next_eq] at hL1_4
  have hL1_5 := gasSteps_cachedBlock
    (s := atState s (l1Step mem bi pa 8 5).memory 4865 ([(l1Step mem bi pa 8 5).carry, bi, UInt256.ofNat (pa - 32), maxWord] ++ suffix)) block_l1_5 hcode hfork
    (run_l1_5 s (l1Step mem bi pa 8 5).memory bi (l1Step mem bi pa 8 5).carry pa suffix
      hcap' hrun hact hpa hpaFit) hrun hnp
  rw [l1Next_eq] at hL1_5
  have hL1_6 := gasSteps_cachedBlock
    (s := atState s (l1Step mem bi pa 8 6).memory 4905 ([(l1Step mem bi pa 8 6).carry, bi, UInt256.ofNat (pa - 32), maxWord] ++ suffix)) block_l1_6 hcode hfork
    (run_l1_6 s (l1Step mem bi pa 8 6).memory bi (l1Step mem bi pa 8 6).carry pa suffix
      hcap' hrun hact hpa hpaFit) hrun hnp
  rw [l1Next_eq] at hL1_6
  have hL1_7 := gasSteps_cachedBlock
    (s := atState s (l1Step mem bi pa 8 7).memory 4945 ([(l1Step mem bi pa 8 7).carry, bi, UInt256.ofNat (pa - 32), maxWord] ++ suffix)) block_l1_7 hcode hfork
    (run_l1_7 s (l1Step mem bi pa 8 7).memory bi (l1Step mem bi pa 8 7).carry pa suffix
      hcap' hrun hact hpa hpaFit) hrun hnp
  rw [l1Next_eq] at hL1_7
  let first := l1Step mem bi pa 8 8
  let middle := midMem first.memory first.carry
  have hMid := gasSteps_cachedBlock
    (s := atState s first.memory 4985
      ([first.carry, bi, UInt256.ofNat (pa - 32), maxWord] ++ suffix))
    block_middle hcode hfork
    (run_middle s first.memory first.carry bi (UInt256.ofNat (pa - 32)) suffix hcap' hrun hact) hrun hnp
  have hC0 := gasSteps_cachedBlock
    (s := atState s middle 5007 ([maxWord] ++ suffix))
    block_c0 hcode hfork
    (run_c0 s middle suffix hcap' hrun hact) hrun hnp
  have hmu : rowMu middle 8 = rowMu first.memory 8 := rowMu_midMem8 _ _
  have hc0 : rowC0 middle 8 = rowC0 first.memory 8 := rowC0_midMem8 _ _
  rw [hmu, hc0] at hC0
  let mu := rowMu first.memory 8
  let c0 := rowC0 first.memory 8
  have hL2_0 := gasSteps_cachedBlock
    (s := atState s (l2Step middle mu c0 8 0).memory 5037 ([(l2Step middle mu c0 8 0).carry, mu, maxWord] ++ suffix)) block_l2_0 hcode hfork
    (run_l2_0 s (l2Step middle mu c0 8 0).memory mu (l2Step middle mu c0 8 0).carry suffix
      hcap' hrun hact) hrun hnp
  rw [l2Next_eq] at hL2_0
  have hL2_1 := gasSteps_cachedBlock
    (s := atState s (l2Step middle mu c0 8 1).memory 5075 ([(l2Step middle mu c0 8 1).carry, mu, maxWord] ++ suffix)) block_l2_1 hcode hfork
    (run_l2_1 s (l2Step middle mu c0 8 1).memory mu (l2Step middle mu c0 8 1).carry suffix
      hcap' hrun hact) hrun hnp
  rw [l2Next_eq] at hL2_1
  have hL2_2 := gasSteps_cachedBlock
    (s := atState s (l2Step middle mu c0 8 2).memory 5113 ([(l2Step middle mu c0 8 2).carry, mu, maxWord] ++ suffix)) block_l2_2 hcode hfork
    (run_l2_2 s (l2Step middle mu c0 8 2).memory mu (l2Step middle mu c0 8 2).carry suffix
      hcap' hrun hact) hrun hnp
  rw [l2Next_eq] at hL2_2
  have hL2_3 := gasSteps_cachedBlock
    (s := atState s (l2Step middle mu c0 8 3).memory 5151 ([(l2Step middle mu c0 8 3).carry, mu, maxWord] ++ suffix)) block_l2_3 hcode hfork
    (run_l2_3 s (l2Step middle mu c0 8 3).memory mu (l2Step middle mu c0 8 3).carry suffix
      hcap' hrun hact) hrun hnp
  rw [l2Next_eq] at hL2_3
  have hL2_4 := gasSteps_cachedBlock
    (s := atState s (l2Step middle mu c0 8 4).memory 5189 ([(l2Step middle mu c0 8 4).carry, mu, maxWord] ++ suffix)) block_l2_4 hcode hfork
    (run_l2_4 s (l2Step middle mu c0 8 4).memory mu (l2Step middle mu c0 8 4).carry suffix
      hcap' hrun hact) hrun hnp
  rw [l2Next_eq] at hL2_4
  have hL2_5 := gasSteps_cachedBlock
    (s := atState s (l2Step middle mu c0 8 5).memory 5227 ([(l2Step middle mu c0 8 5).carry, mu, maxWord] ++ suffix)) block_l2_5 hcode hfork
    (run_l2_5 s (l2Step middle mu c0 8 5).memory mu (l2Step middle mu c0 8 5).carry suffix
      hcap' hrun hact) hrun hnp
  rw [l2Next_eq] at hL2_5
  have hL2_6 := gasSteps_cachedBlock
    (s := atState s (l2Step middle mu c0 8 6).memory 5265 ([(l2Step middle mu c0 8 6).carry, mu, maxWord] ++ suffix)) block_l2_6 hcode hfork
    (run_l2_6 s (l2Step middle mu c0 8 6).memory mu (l2Step middle mu c0 8 6).carry suffix
      hcap' hrun hact) hrun hnp
  rw [l2Next_eq] at hL2_6
  let second := l2Step middle mu c0 8 7
  have hTail := gasSteps_cachedBlock
    (s := atState s second.memory 5302 ([second.carry, mu, maxWord, pbi] ++ rest))
    block_tail hcode hfork
    (run_tail s second.memory second.carry mu pbi rest (by omega) hrun hact) hrun hnp
  exact hL1_0.trans (hL1_1.trans (hL1_2.trans (hL1_3.trans (hL1_4.trans (hL1_5.trans (hL1_6.trans (hL1_7.trans (hMid.trans (hC0.trans (hL2_0.trans (hL2_1.trans (hL2_2.trans (hL2_3.trans (hL2_4.trans (hL2_5.trans (hL2_6.trans (hTail)))))))))))))))))

end Challenge.Modexp.Submission.Proofs.Fast.MonproN8
