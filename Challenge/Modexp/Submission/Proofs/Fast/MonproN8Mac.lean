import Challenge.Modexp.Submission.Proofs.Fast.MonproN8Memory
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
  [pushAt 3131 2 8480,
   opAt 3132 .MLOAD,
   opAt 3133 (.Dup ⟨3, by decide⟩),
   pushAt 3134 2 256,
   opAt 3135 .ADD,
   opAt 3136 .MLOAD,
   opAt 3137 (.Dup ⟨5, by decide⟩),
   opAt 3138 (.Dup ⟨4, by decide⟩),
   opAt 3139 (.Dup ⟨2, by decide⟩),
   opAt 3140 .MUL,
   opAt 3141 (.Swap ⟨1, by decide⟩),
   opAt 3142 (.Dup ⟨5, by decide⟩),
   opAt 3143 .MULMOD,
   opAt 3144 (.Dup ⟨1, by decide⟩),
   opAt 3145 (.Dup ⟨1, by decide⟩),
   opAt 3146 .LT,
   opAt 3147 .SUB,
   opAt 3148 (.Dup ⟨3, by decide⟩),
   opAt 3149 (.Dup ⟨2, by decide⟩),
   opAt 3150 .ADD,
   opAt 3151 (.Dup ⟨0, by decide⟩),
   opAt 3152 (.Swap ⟨4, by decide⟩),
   opAt 3153 .GT,
   opAt 3154 .SUB,
   opAt 3155 .SUB,
   opAt 3156 (.Swap ⟨0, by decide⟩),
   opAt 3157 (.Dup ⟨2, by decide⟩),
   opAt 3158 .ADD,
   opAt 3159 (.Dup ⟨0, by decide⟩),
   opAt 3160 (.Swap ⟨2, by decide⟩),
   opAt 3161 .GT,
   opAt 3162 .ADD,
   opAt 3163 (.Swap ⟨0, by decide⟩),
   pushAt 3164 2 8480,
   opAt 3165 .MSTORE]

theorem pc_l1_0 : Artifact.instructionPC 3131 = 5414 := by rfl

def block_l1_1 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3166 2 8448,
   opAt 3167 .MLOAD,
   opAt 3168 (.Dup ⟨3, by decide⟩),
   pushAt 3169 1 224,
   opAt 3170 .ADD,
   opAt 3171 .MLOAD,
   opAt 3172 (.Dup ⟨5, by decide⟩),
   opAt 3173 (.Dup ⟨4, by decide⟩),
   opAt 3174 (.Dup ⟨2, by decide⟩),
   opAt 3175 .MUL,
   opAt 3176 (.Swap ⟨1, by decide⟩),
   opAt 3177 (.Dup ⟨5, by decide⟩),
   opAt 3178 .MULMOD,
   opAt 3179 (.Dup ⟨1, by decide⟩),
   opAt 3180 (.Dup ⟨1, by decide⟩),
   opAt 3181 .LT,
   opAt 3182 .SUB,
   opAt 3183 (.Dup ⟨3, by decide⟩),
   opAt 3184 (.Dup ⟨2, by decide⟩),
   opAt 3185 .ADD,
   opAt 3186 (.Dup ⟨0, by decide⟩),
   opAt 3187 (.Swap ⟨4, by decide⟩),
   opAt 3188 .GT,
   opAt 3189 .SUB,
   opAt 3190 .SUB,
   opAt 3191 (.Swap ⟨0, by decide⟩),
   opAt 3192 (.Dup ⟨2, by decide⟩),
   opAt 3193 .ADD,
   opAt 3194 (.Dup ⟨0, by decide⟩),
   opAt 3195 (.Swap ⟨2, by decide⟩),
   opAt 3196 .GT,
   opAt 3197 .ADD,
   opAt 3198 (.Swap ⟨0, by decide⟩),
   pushAt 3199 2 8448,
   opAt 3200 .MSTORE]

theorem pc_l1_1 : Artifact.instructionPC 3166 = 5455 := by rfl

def block_l1_2 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3201 2 8416,
   opAt 3202 .MLOAD,
   opAt 3203 (.Dup ⟨3, by decide⟩),
   pushAt 3204 1 192,
   opAt 3205 .ADD,
   opAt 3206 .MLOAD,
   opAt 3207 (.Dup ⟨5, by decide⟩),
   opAt 3208 (.Dup ⟨4, by decide⟩),
   opAt 3209 (.Dup ⟨2, by decide⟩),
   opAt 3210 .MUL,
   opAt 3211 (.Swap ⟨1, by decide⟩),
   opAt 3212 (.Dup ⟨5, by decide⟩),
   opAt 3213 .MULMOD,
   opAt 3214 (.Dup ⟨1, by decide⟩),
   opAt 3215 (.Dup ⟨1, by decide⟩),
   opAt 3216 .LT,
   opAt 3217 .SUB,
   opAt 3218 (.Dup ⟨3, by decide⟩),
   opAt 3219 (.Dup ⟨2, by decide⟩),
   opAt 3220 .ADD,
   opAt 3221 (.Dup ⟨0, by decide⟩),
   opAt 3222 (.Swap ⟨4, by decide⟩),
   opAt 3223 .GT,
   opAt 3224 .SUB,
   opAt 3225 .SUB,
   opAt 3226 (.Swap ⟨0, by decide⟩),
   opAt 3227 (.Dup ⟨2, by decide⟩),
   opAt 3228 .ADD,
   opAt 3229 (.Dup ⟨0, by decide⟩),
   opAt 3230 (.Swap ⟨2, by decide⟩),
   opAt 3231 .GT,
   opAt 3232 .ADD,
   opAt 3233 (.Swap ⟨0, by decide⟩),
   pushAt 3234 2 8416,
   opAt 3235 .MSTORE]

theorem pc_l1_2 : Artifact.instructionPC 3201 = 5495 := by rfl

def block_l1_3 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3236 2 8384,
   opAt 3237 .MLOAD,
   opAt 3238 (.Dup ⟨3, by decide⟩),
   pushAt 3239 1 160,
   opAt 3240 .ADD,
   opAt 3241 .MLOAD,
   opAt 3242 (.Dup ⟨5, by decide⟩),
   opAt 3243 (.Dup ⟨4, by decide⟩),
   opAt 3244 (.Dup ⟨2, by decide⟩),
   opAt 3245 .MUL,
   opAt 3246 (.Swap ⟨1, by decide⟩),
   opAt 3247 (.Dup ⟨5, by decide⟩),
   opAt 3248 .MULMOD,
   opAt 3249 (.Dup ⟨1, by decide⟩),
   opAt 3250 (.Dup ⟨1, by decide⟩),
   opAt 3251 .LT,
   opAt 3252 .SUB,
   opAt 3253 (.Dup ⟨3, by decide⟩),
   opAt 3254 (.Dup ⟨2, by decide⟩),
   opAt 3255 .ADD,
   opAt 3256 (.Dup ⟨0, by decide⟩),
   opAt 3257 (.Swap ⟨4, by decide⟩),
   opAt 3258 .GT,
   opAt 3259 .SUB,
   opAt 3260 .SUB,
   opAt 3261 (.Swap ⟨0, by decide⟩),
   opAt 3262 (.Dup ⟨2, by decide⟩),
   opAt 3263 .ADD,
   opAt 3264 (.Dup ⟨0, by decide⟩),
   opAt 3265 (.Swap ⟨2, by decide⟩),
   opAt 3266 .GT,
   opAt 3267 .ADD,
   opAt 3268 (.Swap ⟨0, by decide⟩),
   pushAt 3269 2 8384,
   opAt 3270 .MSTORE]

theorem pc_l1_3 : Artifact.instructionPC 3236 = 5535 := by rfl

def block_l1_4 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3271 2 8352,
   opAt 3272 .MLOAD,
   opAt 3273 (.Dup ⟨3, by decide⟩),
   pushAt 3274 1 128,
   opAt 3275 .ADD,
   opAt 3276 .MLOAD,
   opAt 3277 (.Dup ⟨5, by decide⟩),
   opAt 3278 (.Dup ⟨4, by decide⟩),
   opAt 3279 (.Dup ⟨2, by decide⟩),
   opAt 3280 .MUL,
   opAt 3281 (.Swap ⟨1, by decide⟩),
   opAt 3282 (.Dup ⟨5, by decide⟩),
   opAt 3283 .MULMOD,
   opAt 3284 (.Dup ⟨1, by decide⟩),
   opAt 3285 (.Dup ⟨1, by decide⟩),
   opAt 3286 .LT,
   opAt 3287 .SUB,
   opAt 3288 (.Dup ⟨3, by decide⟩),
   opAt 3289 (.Dup ⟨2, by decide⟩),
   opAt 3290 .ADD,
   opAt 3291 (.Dup ⟨0, by decide⟩),
   opAt 3292 (.Swap ⟨4, by decide⟩),
   opAt 3293 .GT,
   opAt 3294 .SUB,
   opAt 3295 .SUB,
   opAt 3296 (.Swap ⟨0, by decide⟩),
   opAt 3297 (.Dup ⟨2, by decide⟩),
   opAt 3298 .ADD,
   opAt 3299 (.Dup ⟨0, by decide⟩),
   opAt 3300 (.Swap ⟨2, by decide⟩),
   opAt 3301 .GT,
   opAt 3302 .ADD,
   opAt 3303 (.Swap ⟨0, by decide⟩),
   pushAt 3304 2 8352,
   opAt 3305 .MSTORE]

theorem pc_l1_4 : Artifact.instructionPC 3271 = 5575 := by rfl

def block_l1_5 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3306 2 8320,
   opAt 3307 .MLOAD,
   opAt 3308 (.Dup ⟨3, by decide⟩),
   pushAt 3309 1 96,
   opAt 3310 .ADD,
   opAt 3311 .MLOAD,
   opAt 3312 (.Dup ⟨5, by decide⟩),
   opAt 3313 (.Dup ⟨4, by decide⟩),
   opAt 3314 (.Dup ⟨2, by decide⟩),
   opAt 3315 .MUL,
   opAt 3316 (.Swap ⟨1, by decide⟩),
   opAt 3317 (.Dup ⟨5, by decide⟩),
   opAt 3318 .MULMOD,
   opAt 3319 (.Dup ⟨1, by decide⟩),
   opAt 3320 (.Dup ⟨1, by decide⟩),
   opAt 3321 .LT,
   opAt 3322 .SUB,
   opAt 3323 (.Dup ⟨3, by decide⟩),
   opAt 3324 (.Dup ⟨2, by decide⟩),
   opAt 3325 .ADD,
   opAt 3326 (.Dup ⟨0, by decide⟩),
   opAt 3327 (.Swap ⟨4, by decide⟩),
   opAt 3328 .GT,
   opAt 3329 .SUB,
   opAt 3330 .SUB,
   opAt 3331 (.Swap ⟨0, by decide⟩),
   opAt 3332 (.Dup ⟨2, by decide⟩),
   opAt 3333 .ADD,
   opAt 3334 (.Dup ⟨0, by decide⟩),
   opAt 3335 (.Swap ⟨2, by decide⟩),
   opAt 3336 .GT,
   opAt 3337 .ADD,
   opAt 3338 (.Swap ⟨0, by decide⟩),
   pushAt 3339 2 8320,
   opAt 3340 .MSTORE]

theorem pc_l1_5 : Artifact.instructionPC 3306 = 5615 := by rfl

def block_l1_6 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3341 2 8288,
   opAt 3342 .MLOAD,
   opAt 3343 (.Dup ⟨3, by decide⟩),
   pushAt 3344 1 64,
   opAt 3345 .ADD,
   opAt 3346 .MLOAD,
   opAt 3347 (.Dup ⟨5, by decide⟩),
   opAt 3348 (.Dup ⟨4, by decide⟩),
   opAt 3349 (.Dup ⟨2, by decide⟩),
   opAt 3350 .MUL,
   opAt 3351 (.Swap ⟨1, by decide⟩),
   opAt 3352 (.Dup ⟨5, by decide⟩),
   opAt 3353 .MULMOD,
   opAt 3354 (.Dup ⟨1, by decide⟩),
   opAt 3355 (.Dup ⟨1, by decide⟩),
   opAt 3356 .LT,
   opAt 3357 .SUB,
   opAt 3358 (.Dup ⟨3, by decide⟩),
   opAt 3359 (.Dup ⟨2, by decide⟩),
   opAt 3360 .ADD,
   opAt 3361 (.Dup ⟨0, by decide⟩),
   opAt 3362 (.Swap ⟨4, by decide⟩),
   opAt 3363 .GT,
   opAt 3364 .SUB,
   opAt 3365 .SUB,
   opAt 3366 (.Swap ⟨0, by decide⟩),
   opAt 3367 (.Dup ⟨2, by decide⟩),
   opAt 3368 .ADD,
   opAt 3369 (.Dup ⟨0, by decide⟩),
   opAt 3370 (.Swap ⟨2, by decide⟩),
   opAt 3371 .GT,
   opAt 3372 .ADD,
   opAt 3373 (.Swap ⟨0, by decide⟩),
   pushAt 3374 2 8288,
   opAt 3375 .MSTORE]

theorem pc_l1_6 : Artifact.instructionPC 3341 = 5655 := by rfl

def block_l1_7 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3376 2 8256,
   opAt 3377 .MLOAD,
   opAt 3378 (.Dup ⟨3, by decide⟩),
   pushAt 3379 1 32,
   opAt 3380 .ADD,
   opAt 3381 .MLOAD,
   opAt 3382 (.Dup ⟨5, by decide⟩),
   opAt 3383 (.Dup ⟨4, by decide⟩),
   opAt 3384 (.Dup ⟨2, by decide⟩),
   opAt 3385 .MUL,
   opAt 3386 (.Swap ⟨1, by decide⟩),
   opAt 3387 (.Dup ⟨5, by decide⟩),
   opAt 3388 .MULMOD,
   opAt 3389 (.Dup ⟨1, by decide⟩),
   opAt 3390 (.Dup ⟨1, by decide⟩),
   opAt 3391 .LT,
   opAt 3392 .SUB,
   opAt 3393 (.Dup ⟨3, by decide⟩),
   opAt 3394 (.Dup ⟨2, by decide⟩),
   opAt 3395 .ADD,
   opAt 3396 (.Dup ⟨0, by decide⟩),
   opAt 3397 (.Swap ⟨4, by decide⟩),
   opAt 3398 .GT,
   opAt 3399 .SUB,
   opAt 3400 .SUB,
   opAt 3401 (.Swap ⟨0, by decide⟩),
   opAt 3402 (.Dup ⟨2, by decide⟩),
   opAt 3403 .ADD,
   opAt 3404 (.Dup ⟨0, by decide⟩),
   opAt 3405 (.Swap ⟨2, by decide⟩),
   opAt 3406 .GT,
   opAt 3407 .ADD,
   opAt 3408 (.Swap ⟨0, by decide⟩),
   pushAt 3409 2 8256,
   opAt 3410 .MSTORE]

theorem pc_l1_7 : Artifact.instructionPC 3376 = 5695 := by rfl

def block_l2_0 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3452 2 8448,
   opAt 3453 .MLOAD,
   pushAt 3454 1 192,
   opAt 3455 .MLOAD,
   opAt 3456 (.Dup ⟨4, by decide⟩),
   opAt 3457 (.Dup ⟨4, by decide⟩),
   opAt 3458 (.Dup ⟨2, by decide⟩),
   opAt 3459 .MUL,
   opAt 3460 (.Swap ⟨1, by decide⟩),
   opAt 3461 (.Dup ⟨5, by decide⟩),
   opAt 3462 .MULMOD,
   opAt 3463 (.Dup ⟨1, by decide⟩),
   opAt 3464 (.Dup ⟨1, by decide⟩),
   opAt 3465 .LT,
   opAt 3466 .SUB,
   opAt 3467 (.Dup ⟨3, by decide⟩),
   opAt 3468 (.Dup ⟨2, by decide⟩),
   opAt 3469 .ADD,
   opAt 3470 (.Dup ⟨0, by decide⟩),
   opAt 3471 (.Swap ⟨4, by decide⟩),
   opAt 3472 .GT,
   opAt 3473 .SUB,
   opAt 3474 .SUB,
   opAt 3475 (.Swap ⟨0, by decide⟩),
   opAt 3476 (.Dup ⟨2, by decide⟩),
   opAt 3477 .ADD,
   opAt 3478 (.Dup ⟨0, by decide⟩),
   opAt 3479 (.Swap ⟨2, by decide⟩),
   opAt 3480 .GT,
   opAt 3481 .ADD,
   opAt 3482 (.Swap ⟨0, by decide⟩),
   pushAt 3483 2 8480,
   opAt 3484 .MSTORE]

theorem pc_l2_0 : Artifact.instructionPC 3452 = 5787 := by rfl

def block_l2_1 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3485 2 8416,
   opAt 3486 .MLOAD,
   pushAt 3487 1 160,
   opAt 3488 .MLOAD,
   opAt 3489 (.Dup ⟨4, by decide⟩),
   opAt 3490 (.Dup ⟨4, by decide⟩),
   opAt 3491 (.Dup ⟨2, by decide⟩),
   opAt 3492 .MUL,
   opAt 3493 (.Swap ⟨1, by decide⟩),
   opAt 3494 (.Dup ⟨5, by decide⟩),
   opAt 3495 .MULMOD,
   opAt 3496 (.Dup ⟨1, by decide⟩),
   opAt 3497 (.Dup ⟨1, by decide⟩),
   opAt 3498 .LT,
   opAt 3499 .SUB,
   opAt 3500 (.Dup ⟨3, by decide⟩),
   opAt 3501 (.Dup ⟨2, by decide⟩),
   opAt 3502 .ADD,
   opAt 3503 (.Dup ⟨0, by decide⟩),
   opAt 3504 (.Swap ⟨4, by decide⟩),
   opAt 3505 .GT,
   opAt 3506 .SUB,
   opAt 3507 .SUB,
   opAt 3508 (.Swap ⟨0, by decide⟩),
   opAt 3509 (.Dup ⟨2, by decide⟩),
   opAt 3510 .ADD,
   opAt 3511 (.Dup ⟨0, by decide⟩),
   opAt 3512 (.Swap ⟨2, by decide⟩),
   opAt 3513 .GT,
   opAt 3514 .ADD,
   opAt 3515 (.Swap ⟨0, by decide⟩),
   pushAt 3516 2 8448,
   opAt 3517 .MSTORE]

theorem pc_l2_1 : Artifact.instructionPC 3485 = 5825 := by rfl

def block_l2_2 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3518 2 8384,
   opAt 3519 .MLOAD,
   pushAt 3520 1 128,
   opAt 3521 .MLOAD,
   opAt 3522 (.Dup ⟨4, by decide⟩),
   opAt 3523 (.Dup ⟨4, by decide⟩),
   opAt 3524 (.Dup ⟨2, by decide⟩),
   opAt 3525 .MUL,
   opAt 3526 (.Swap ⟨1, by decide⟩),
   opAt 3527 (.Dup ⟨5, by decide⟩),
   opAt 3528 .MULMOD,
   opAt 3529 (.Dup ⟨1, by decide⟩),
   opAt 3530 (.Dup ⟨1, by decide⟩),
   opAt 3531 .LT,
   opAt 3532 .SUB,
   opAt 3533 (.Dup ⟨3, by decide⟩),
   opAt 3534 (.Dup ⟨2, by decide⟩),
   opAt 3535 .ADD,
   opAt 3536 (.Dup ⟨0, by decide⟩),
   opAt 3537 (.Swap ⟨4, by decide⟩),
   opAt 3538 .GT,
   opAt 3539 .SUB,
   opAt 3540 .SUB,
   opAt 3541 (.Swap ⟨0, by decide⟩),
   opAt 3542 (.Dup ⟨2, by decide⟩),
   opAt 3543 .ADD,
   opAt 3544 (.Dup ⟨0, by decide⟩),
   opAt 3545 (.Swap ⟨2, by decide⟩),
   opAt 3546 .GT,
   opAt 3547 .ADD,
   opAt 3548 (.Swap ⟨0, by decide⟩),
   pushAt 3549 2 8416,
   opAt 3550 .MSTORE]

theorem pc_l2_2 : Artifact.instructionPC 3518 = 5863 := by rfl

def block_l2_3 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3551 2 8352,
   opAt 3552 .MLOAD,
   pushAt 3553 1 96,
   opAt 3554 .MLOAD,
   opAt 3555 (.Dup ⟨4, by decide⟩),
   opAt 3556 (.Dup ⟨4, by decide⟩),
   opAt 3557 (.Dup ⟨2, by decide⟩),
   opAt 3558 .MUL,
   opAt 3559 (.Swap ⟨1, by decide⟩),
   opAt 3560 (.Dup ⟨5, by decide⟩),
   opAt 3561 .MULMOD,
   opAt 3562 (.Dup ⟨1, by decide⟩),
   opAt 3563 (.Dup ⟨1, by decide⟩),
   opAt 3564 .LT,
   opAt 3565 .SUB,
   opAt 3566 (.Dup ⟨3, by decide⟩),
   opAt 3567 (.Dup ⟨2, by decide⟩),
   opAt 3568 .ADD,
   opAt 3569 (.Dup ⟨0, by decide⟩),
   opAt 3570 (.Swap ⟨4, by decide⟩),
   opAt 3571 .GT,
   opAt 3572 .SUB,
   opAt 3573 .SUB,
   opAt 3574 (.Swap ⟨0, by decide⟩),
   opAt 3575 (.Dup ⟨2, by decide⟩),
   opAt 3576 .ADD,
   opAt 3577 (.Dup ⟨0, by decide⟩),
   opAt 3578 (.Swap ⟨2, by decide⟩),
   opAt 3579 .GT,
   opAt 3580 .ADD,
   opAt 3581 (.Swap ⟨0, by decide⟩),
   pushAt 3582 2 8384,
   opAt 3583 .MSTORE]

theorem pc_l2_3 : Artifact.instructionPC 3551 = 5901 := by rfl

def block_l2_4 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3584 2 8320,
   opAt 3585 .MLOAD,
   pushAt 3586 1 64,
   opAt 3587 .MLOAD,
   opAt 3588 (.Dup ⟨4, by decide⟩),
   opAt 3589 (.Dup ⟨4, by decide⟩),
   opAt 3590 (.Dup ⟨2, by decide⟩),
   opAt 3591 .MUL,
   opAt 3592 (.Swap ⟨1, by decide⟩),
   opAt 3593 (.Dup ⟨5, by decide⟩),
   opAt 3594 .MULMOD,
   opAt 3595 (.Dup ⟨1, by decide⟩),
   opAt 3596 (.Dup ⟨1, by decide⟩),
   opAt 3597 .LT,
   opAt 3598 .SUB,
   opAt 3599 (.Dup ⟨3, by decide⟩),
   opAt 3600 (.Dup ⟨2, by decide⟩),
   opAt 3601 .ADD,
   opAt 3602 (.Dup ⟨0, by decide⟩),
   opAt 3603 (.Swap ⟨4, by decide⟩),
   opAt 3604 .GT,
   opAt 3605 .SUB,
   opAt 3606 .SUB,
   opAt 3607 (.Swap ⟨0, by decide⟩),
   opAt 3608 (.Dup ⟨2, by decide⟩),
   opAt 3609 .ADD,
   opAt 3610 (.Dup ⟨0, by decide⟩),
   opAt 3611 (.Swap ⟨2, by decide⟩),
   opAt 3612 .GT,
   opAt 3613 .ADD,
   opAt 3614 (.Swap ⟨0, by decide⟩),
   pushAt 3615 2 8352,
   opAt 3616 .MSTORE]

theorem pc_l2_4 : Artifact.instructionPC 3584 = 5939 := by rfl

def block_l2_5 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3617 2 8288,
   opAt 3618 .MLOAD,
   pushAt 3619 1 32,
   opAt 3620 .MLOAD,
   opAt 3621 (.Dup ⟨4, by decide⟩),
   opAt 3622 (.Dup ⟨4, by decide⟩),
   opAt 3623 (.Dup ⟨2, by decide⟩),
   opAt 3624 .MUL,
   opAt 3625 (.Swap ⟨1, by decide⟩),
   opAt 3626 (.Dup ⟨5, by decide⟩),
   opAt 3627 .MULMOD,
   opAt 3628 (.Dup ⟨1, by decide⟩),
   opAt 3629 (.Dup ⟨1, by decide⟩),
   opAt 3630 .LT,
   opAt 3631 .SUB,
   opAt 3632 (.Dup ⟨3, by decide⟩),
   opAt 3633 (.Dup ⟨2, by decide⟩),
   opAt 3634 .ADD,
   opAt 3635 (.Dup ⟨0, by decide⟩),
   opAt 3636 (.Swap ⟨4, by decide⟩),
   opAt 3637 .GT,
   opAt 3638 .SUB,
   opAt 3639 .SUB,
   opAt 3640 (.Swap ⟨0, by decide⟩),
   opAt 3641 (.Dup ⟨2, by decide⟩),
   opAt 3642 .ADD,
   opAt 3643 (.Dup ⟨0, by decide⟩),
   opAt 3644 (.Swap ⟨2, by decide⟩),
   opAt 3645 .GT,
   opAt 3646 .ADD,
   opAt 3647 (.Swap ⟨0, by decide⟩),
   pushAt 3648 2 8320,
   opAt 3649 .MSTORE]

theorem pc_l2_5 : Artifact.instructionPC 3617 = 5977 := by rfl

def block_l2_6 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3650 2 8256,
   opAt 3651 .MLOAD,
   pushAt 3652 0 0,
   opAt 3653 .MLOAD,
   opAt 3654 (.Dup ⟨4, by decide⟩),
   opAt 3655 (.Dup ⟨4, by decide⟩),
   opAt 3656 (.Dup ⟨2, by decide⟩),
   opAt 3657 .MUL,
   opAt 3658 (.Swap ⟨1, by decide⟩),
   opAt 3659 (.Dup ⟨5, by decide⟩),
   opAt 3660 .MULMOD,
   opAt 3661 (.Dup ⟨1, by decide⟩),
   opAt 3662 (.Dup ⟨1, by decide⟩),
   opAt 3663 .LT,
   opAt 3664 .SUB,
   opAt 3665 (.Dup ⟨3, by decide⟩),
   opAt 3666 (.Dup ⟨2, by decide⟩),
   opAt 3667 .ADD,
   opAt 3668 (.Dup ⟨0, by decide⟩),
   opAt 3669 (.Swap ⟨4, by decide⟩),
   opAt 3670 .GT,
   opAt 3671 .SUB,
   opAt 3672 .SUB,
   opAt 3673 (.Swap ⟨0, by decide⟩),
   opAt 3674 (.Dup ⟨2, by decide⟩),
   opAt 3675 .ADD,
   opAt 3676 (.Dup ⟨0, by decide⟩),
   opAt 3677 (.Swap ⟨2, by decide⟩),
   opAt 3678 .GT,
   opAt 3679 .ADD,
   opAt 3680 (.Swap ⟨0, by decide⟩),
   pushAt 3681 2 8288,
   opAt 3682 .MSTORE]

theorem pc_l2_6 : Artifact.instructionPC 3650 = 6015 := by rfl

def block_middle : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3411 (.Swap ⟨1, by decide⟩),
   opAt 3412 .POP,
   opAt 3413 .POP,
   pushAt 3414 2 8224,
   opAt 3415 .MLOAD,
   opAt 3416 (.Dup ⟨1, by decide⟩),
   opAt 3417 .ADD,
   opAt 3418 (.Dup ⟨1, by decide⟩),
   opAt 3419 (.Dup ⟨1, by decide⟩),
   opAt 3420 .LT,
   opAt 3421 (.Swap ⟨1, by decide⟩),
   opAt 3422 .POP,
   pushAt 3423 2 8224,
   opAt 3424 .MSTORE,
   pushAt 3425 2 8192,
   opAt 3426 .MSTORE]

theorem pc_middle : Artifact.instructionPC 3411 = 5735 := by rfl

def block_c0 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3427 2 8480,
   opAt 3428 .MLOAD,
   pushAt 3429 2 9376,
   opAt 3430 .MLOAD,
   opAt 3431 (.Swap ⟨0, by decide⟩),
   opAt 3432 .MUL,
   pushAt 3433 1 224,
   opAt 3434 .MLOAD,
   opAt 3435 (.Dup ⟨1, by decide⟩),
   opAt 3436 (.Dup ⟨1, by decide⟩),
   opAt 3437 .MUL,
   opAt 3438 (.Swap ⟨0, by decide⟩),
   opAt 3439 (.Dup ⟨3, by decide⟩),
   opAt 3440 (.Swap ⟨0, by decide⟩),
   opAt 3441 (.Dup ⟨3, by decide⟩),
   opAt 3442 .MULMOD,
   opAt 3443 (.Dup ⟨1, by decide⟩),
   opAt 3444 (.Dup ⟨1, by decide⟩),
   opAt 3445 .LT,
   opAt 3446 .SUB,
   opAt 3447 (.Dup ⟨1, by decide⟩),
   opAt 3448 .ISZERO,
   opAt 3449 .ISZERO,
   opAt 3450 .SUB,
   opAt 3451 .SUB]

theorem pc_c0 : Artifact.instructionPC 3427 = 5757 := by rfl

def block_tail : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3683 (.Swap ⟨0, by decide⟩),
   opAt 3684 .POP,
   pushAt 3685 2 8224,
   opAt 3686 .MLOAD,
   opAt 3687 (.Dup ⟨1, by decide⟩),
   opAt 3688 .ADD,
   opAt 3689 (.Dup ⟨1, by decide⟩),
   opAt 3690 (.Dup ⟨1, by decide⟩),
   opAt 3691 .LT,
   opAt 3692 (.Swap ⟨1, by decide⟩),
   opAt 3693 .POP,
   pushAt 3694 2 8256,
   opAt 3695 .MSTORE,
   pushAt 3696 2 8192,
   opAt 3697 .MLOAD,
   opAt 3698 .ADD,
   pushAt 3699 2 8224,
   opAt 3700 .MSTORE,
   opAt 3701 .POP,
   pushAt 3702 1 31,
   opAt 3703 .NOT,
   opAt 3704 .ADD]

theorem pc_tail : Artifact.instructionPC 3683 = 6052 := by rfl

/-- Exact actual-byte L1 MAC, with the entire suffix and memory. -/
theorem run_l1_0 (s : State) (mem : ByteArray) (bi c : UInt256) (pa : Nat) (rest : List UInt256)
    (hcap : rest.length ≤ 1013) (hrun : s.halt = .Running)
    (hact : 296 ≤ s.activeWords.toNat)
    (hpa : 32 ≤ pa) (hpaFit : pa + 256 ≤ 9472) :
    Challenge.EvmProof.Stepper.runLocatedBlock block_l1_0
      (atState s mem 5414 ([c, bi, UInt256.ofNat (pa - 32), maxWord] ++ rest)) =
      some (atState s (l1Next mem bi pa 0 c).memory 5455 ([(l1Next mem bi pa 0 c).carry, bi, UInt256.ofNat (pa - 32), maxWord] ++ rest)) := by
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
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      UInt256.gt, UInt256.isTrue, List.exchange, l1Next, macSum, macCarry, mulHi,
      hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, ha0, ha1, hpaN, hxN]
  all_goals first
    | exact MacAlt.macCarryFix _ _ _ _
    | (refine ⟨?_, MacAlt.macCarryFix _ _ _ _⟩; rw [MacAlt.macSumNat])
    | rw [MacAlt.macSumNat]

/-- Exact actual-byte L1 MAC, with the entire suffix and memory. -/
theorem run_l1_1 (s : State) (mem : ByteArray) (bi c : UInt256) (pa : Nat) (rest : List UInt256)
    (hcap : rest.length ≤ 1013) (hrun : s.halt = .Running)
    (hact : 296 ≤ s.activeWords.toNat)
    (hpa : 32 ≤ pa) (hpaFit : pa + 256 ≤ 9472) :
    Challenge.EvmProof.Stepper.runLocatedBlock block_l1_1
      (atState s mem 5455 ([c, bi, UInt256.ofNat (pa - 32), maxWord] ++ rest)) =
      some (atState s (l1Next mem bi pa 1 c).memory 5495 ([(l1Next mem bi pa 1 c).carry, bi, UInt256.ofNat (pa - 32), maxWord] ++ rest)) := by
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
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      UInt256.gt, UInt256.isTrue, List.exchange, l1Next, macSum, macCarry, mulHi,
      hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, ha0, ha1, hpaN, hxN]
  all_goals first
    | exact MacAlt.macCarryFix _ _ _ _
    | (refine ⟨?_, MacAlt.macCarryFix _ _ _ _⟩; rw [MacAlt.macSumNat])
    | rw [MacAlt.macSumNat]

/-- Exact actual-byte L1 MAC, with the entire suffix and memory. -/
theorem run_l1_2 (s : State) (mem : ByteArray) (bi c : UInt256) (pa : Nat) (rest : List UInt256)
    (hcap : rest.length ≤ 1013) (hrun : s.halt = .Running)
    (hact : 296 ≤ s.activeWords.toNat)
    (hpa : 32 ≤ pa) (hpaFit : pa + 256 ≤ 9472) :
    Challenge.EvmProof.Stepper.runLocatedBlock block_l1_2
      (atState s mem 5495 ([c, bi, UInt256.ofNat (pa - 32), maxWord] ++ rest)) =
      some (atState s (l1Next mem bi pa 2 c).memory 5535 ([(l1Next mem bi pa 2 c).carry, bi, UInt256.ofNat (pa - 32), maxWord] ++ rest)) := by
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
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      UInt256.gt, UInt256.isTrue, List.exchange, l1Next, macSum, macCarry, mulHi,
      hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, ha0, ha1, hpaN, hxN]
  all_goals first
    | exact MacAlt.macCarryFix _ _ _ _
    | (refine ⟨?_, MacAlt.macCarryFix _ _ _ _⟩; rw [MacAlt.macSumNat])
    | rw [MacAlt.macSumNat]

/-- Exact actual-byte L1 MAC, with the entire suffix and memory. -/
theorem run_l1_3 (s : State) (mem : ByteArray) (bi c : UInt256) (pa : Nat) (rest : List UInt256)
    (hcap : rest.length ≤ 1013) (hrun : s.halt = .Running)
    (hact : 296 ≤ s.activeWords.toNat)
    (hpa : 32 ≤ pa) (hpaFit : pa + 256 ≤ 9472) :
    Challenge.EvmProof.Stepper.runLocatedBlock block_l1_3
      (atState s mem 5535 ([c, bi, UInt256.ofNat (pa - 32), maxWord] ++ rest)) =
      some (atState s (l1Next mem bi pa 3 c).memory 5575 ([(l1Next mem bi pa 3 c).carry, bi, UInt256.ofNat (pa - 32), maxWord] ++ rest)) := by
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
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      UInt256.gt, UInt256.isTrue, List.exchange, l1Next, macSum, macCarry, mulHi,
      hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, ha0, ha1, hpaN, hxN]
  all_goals first
    | exact MacAlt.macCarryFix _ _ _ _
    | (refine ⟨?_, MacAlt.macCarryFix _ _ _ _⟩; rw [MacAlt.macSumNat])
    | rw [MacAlt.macSumNat]

/-- Exact actual-byte L1 MAC, with the entire suffix and memory. -/
theorem run_l1_4 (s : State) (mem : ByteArray) (bi c : UInt256) (pa : Nat) (rest : List UInt256)
    (hcap : rest.length ≤ 1013) (hrun : s.halt = .Running)
    (hact : 296 ≤ s.activeWords.toNat)
    (hpa : 32 ≤ pa) (hpaFit : pa + 256 ≤ 9472) :
    Challenge.EvmProof.Stepper.runLocatedBlock block_l1_4
      (atState s mem 5575 ([c, bi, UInt256.ofNat (pa - 32), maxWord] ++ rest)) =
      some (atState s (l1Next mem bi pa 4 c).memory 5615 ([(l1Next mem bi pa 4 c).carry, bi, UInt256.ofNat (pa - 32), maxWord] ++ rest)) := by
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
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      UInt256.gt, UInt256.isTrue, List.exchange, l1Next, macSum, macCarry, mulHi,
      hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, ha0, ha1, hpaN, hxN]
  all_goals first
    | exact MacAlt.macCarryFix _ _ _ _
    | (refine ⟨?_, MacAlt.macCarryFix _ _ _ _⟩; rw [MacAlt.macSumNat])
    | rw [MacAlt.macSumNat]

/-- Exact actual-byte L1 MAC, with the entire suffix and memory. -/
theorem run_l1_5 (s : State) (mem : ByteArray) (bi c : UInt256) (pa : Nat) (rest : List UInt256)
    (hcap : rest.length ≤ 1013) (hrun : s.halt = .Running)
    (hact : 296 ≤ s.activeWords.toNat)
    (hpa : 32 ≤ pa) (hpaFit : pa + 256 ≤ 9472) :
    Challenge.EvmProof.Stepper.runLocatedBlock block_l1_5
      (atState s mem 5615 ([c, bi, UInt256.ofNat (pa - 32), maxWord] ++ rest)) =
      some (atState s (l1Next mem bi pa 5 c).memory 5655 ([(l1Next mem bi pa 5 c).carry, bi, UInt256.ofNat (pa - 32), maxWord] ++ rest)) := by
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
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      UInt256.gt, UInt256.isTrue, List.exchange, l1Next, macSum, macCarry, mulHi,
      hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, ha0, ha1, hpaN, hxN]
  all_goals first
    | exact MacAlt.macCarryFix _ _ _ _
    | (refine ⟨?_, MacAlt.macCarryFix _ _ _ _⟩; rw [MacAlt.macSumNat])
    | rw [MacAlt.macSumNat]

/-- Exact actual-byte L1 MAC, with the entire suffix and memory. -/
theorem run_l1_6 (s : State) (mem : ByteArray) (bi c : UInt256) (pa : Nat) (rest : List UInt256)
    (hcap : rest.length ≤ 1013) (hrun : s.halt = .Running)
    (hact : 296 ≤ s.activeWords.toNat)
    (hpa : 32 ≤ pa) (hpaFit : pa + 256 ≤ 9472) :
    Challenge.EvmProof.Stepper.runLocatedBlock block_l1_6
      (atState s mem 5655 ([c, bi, UInt256.ofNat (pa - 32), maxWord] ++ rest)) =
      some (atState s (l1Next mem bi pa 6 c).memory 5695 ([(l1Next mem bi pa 6 c).carry, bi, UInt256.ofNat (pa - 32), maxWord] ++ rest)) := by
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
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      UInt256.gt, UInt256.isTrue, List.exchange, l1Next, macSum, macCarry, mulHi,
      hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, ha0, ha1, hpaN, hxN]
  all_goals first
    | exact MacAlt.macCarryFix _ _ _ _
    | (refine ⟨?_, MacAlt.macCarryFix _ _ _ _⟩; rw [MacAlt.macSumNat])
    | rw [MacAlt.macSumNat]

/-- Exact actual-byte L1 MAC, with the entire suffix and memory. -/
theorem run_l1_7 (s : State) (mem : ByteArray) (bi c : UInt256) (pa : Nat) (rest : List UInt256)
    (hcap : rest.length ≤ 1013) (hrun : s.halt = .Running)
    (hact : 296 ≤ s.activeWords.toNat)
    (hpa : 32 ≤ pa) (hpaFit : pa + 256 ≤ 9472) :
    Challenge.EvmProof.Stepper.runLocatedBlock block_l1_7
      (atState s mem 5695 ([c, bi, UInt256.ofNat (pa - 32), maxWord] ++ rest)) =
      some (atState s (l1Next mem bi pa 7 c).memory 5735 ([(l1Next mem bi pa 7 c).carry, bi, UInt256.ofNat (pa - 32), maxWord] ++ rest)) := by
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
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      UInt256.gt, UInt256.isTrue, List.exchange, l1Next, macSum, macCarry, mulHi,
      hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, ha0, ha1, hpaN, hxN]
  all_goals first
    | exact MacAlt.macCarryFix _ _ _ _
    | (refine ⟨?_, MacAlt.macCarryFix _ _ _ _⟩; rw [MacAlt.macSumNat])
    | rw [MacAlt.macSumNat]

/-- Exact actual-byte L2 MAC, with the entire suffix and memory. -/
theorem run_l2_0 (s : State) (mem : ByteArray) (mu c : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1013) (hrun : s.halt = .Running)
    (hact : 296 ≤ s.activeWords.toNat) :
    Challenge.EvmProof.Stepper.runLocatedBlock block_l2_0
      (atState s mem 5787 ([c, mu, maxWord] ++ rest)) =
      some (atState s (l2Next mem mu 0 c).memory 5825 ([(l2Next mem mu 0 c).carry, mu, maxWord] ++ rest)) := by
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
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      UInt256.gt, UInt256.isTrue, List.exchange, l2Next, macSum, macCarry, mulHi,
      hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, ha0, ha1, ha2]
  all_goals first
    | exact MacAlt.macCarryFix _ _ _ _
    | (refine ⟨?_, MacAlt.macCarryFix _ _ _ _⟩; rw [MacAlt.macSumNat])
    | rw [MacAlt.macSumNat]

/-- Exact actual-byte L2 MAC, with the entire suffix and memory. -/
theorem run_l2_1 (s : State) (mem : ByteArray) (mu c : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1013) (hrun : s.halt = .Running)
    (hact : 296 ≤ s.activeWords.toNat) :
    Challenge.EvmProof.Stepper.runLocatedBlock block_l2_1
      (atState s mem 5825 ([c, mu, maxWord] ++ rest)) =
      some (atState s (l2Next mem mu 1 c).memory 5863 ([(l2Next mem mu 1 c).carry, mu, maxWord] ++ rest)) := by
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
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      UInt256.gt, UInt256.isTrue, List.exchange, l2Next, macSum, macCarry, mulHi,
      hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, ha0, ha1, ha2]
  all_goals first
    | exact MacAlt.macCarryFix _ _ _ _
    | (refine ⟨?_, MacAlt.macCarryFix _ _ _ _⟩; rw [MacAlt.macSumNat])
    | rw [MacAlt.macSumNat]

/-- Exact actual-byte L2 MAC, with the entire suffix and memory. -/
theorem run_l2_2 (s : State) (mem : ByteArray) (mu c : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1013) (hrun : s.halt = .Running)
    (hact : 296 ≤ s.activeWords.toNat) :
    Challenge.EvmProof.Stepper.runLocatedBlock block_l2_2
      (atState s mem 5863 ([c, mu, maxWord] ++ rest)) =
      some (atState s (l2Next mem mu 2 c).memory 5901 ([(l2Next mem mu 2 c).carry, mu, maxWord] ++ rest)) := by
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
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      UInt256.gt, UInt256.isTrue, List.exchange, l2Next, macSum, macCarry, mulHi,
      hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, ha0, ha1, ha2]
  all_goals first
    | exact MacAlt.macCarryFix _ _ _ _
    | (refine ⟨?_, MacAlt.macCarryFix _ _ _ _⟩; rw [MacAlt.macSumNat])
    | rw [MacAlt.macSumNat]

/-- Exact actual-byte L2 MAC, with the entire suffix and memory. -/
theorem run_l2_3 (s : State) (mem : ByteArray) (mu c : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1013) (hrun : s.halt = .Running)
    (hact : 296 ≤ s.activeWords.toNat) :
    Challenge.EvmProof.Stepper.runLocatedBlock block_l2_3
      (atState s mem 5901 ([c, mu, maxWord] ++ rest)) =
      some (atState s (l2Next mem mu 3 c).memory 5939 ([(l2Next mem mu 3 c).carry, mu, maxWord] ++ rest)) := by
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
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      UInt256.gt, UInt256.isTrue, List.exchange, l2Next, macSum, macCarry, mulHi,
      hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, ha0, ha1, ha2]
  all_goals first
    | exact MacAlt.macCarryFix _ _ _ _
    | (refine ⟨?_, MacAlt.macCarryFix _ _ _ _⟩; rw [MacAlt.macSumNat])
    | rw [MacAlt.macSumNat]

/-- Exact actual-byte L2 MAC, with the entire suffix and memory. -/
theorem run_l2_4 (s : State) (mem : ByteArray) (mu c : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1013) (hrun : s.halt = .Running)
    (hact : 296 ≤ s.activeWords.toNat) :
    Challenge.EvmProof.Stepper.runLocatedBlock block_l2_4
      (atState s mem 5939 ([c, mu, maxWord] ++ rest)) =
      some (atState s (l2Next mem mu 4 c).memory 5977 ([(l2Next mem mu 4 c).carry, mu, maxWord] ++ rest)) := by
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
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      UInt256.gt, UInt256.isTrue, List.exchange, l2Next, macSum, macCarry, mulHi,
      hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, ha0, ha1, ha2]
  all_goals first
    | exact MacAlt.macCarryFix _ _ _ _
    | (refine ⟨?_, MacAlt.macCarryFix _ _ _ _⟩; rw [MacAlt.macSumNat])
    | rw [MacAlt.macSumNat]

/-- Exact actual-byte L2 MAC, with the entire suffix and memory. -/
theorem run_l2_5 (s : State) (mem : ByteArray) (mu c : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1013) (hrun : s.halt = .Running)
    (hact : 296 ≤ s.activeWords.toNat) :
    Challenge.EvmProof.Stepper.runLocatedBlock block_l2_5
      (atState s mem 5977 ([c, mu, maxWord] ++ rest)) =
      some (atState s (l2Next mem mu 5 c).memory 6015 ([(l2Next mem mu 5 c).carry, mu, maxWord] ++ rest)) := by
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
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      UInt256.gt, UInt256.isTrue, List.exchange, l2Next, macSum, macCarry, mulHi,
      hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, ha0, ha1, ha2]
  all_goals first
    | exact MacAlt.macCarryFix _ _ _ _
    | (refine ⟨?_, MacAlt.macCarryFix _ _ _ _⟩; rw [MacAlt.macSumNat])
    | rw [MacAlt.macSumNat]

/-- Exact actual-byte L2 MAC, with the entire suffix and memory. -/
theorem run_l2_6 (s : State) (mem : ByteArray) (mu c : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1013) (hrun : s.halt = .Running)
    (hact : 296 ≤ s.activeWords.toNat) :
    Challenge.EvmProof.Stepper.runLocatedBlock block_l2_6
      (atState s mem 6015 ([c, mu, maxWord] ++ rest)) =
      some (atState s (l2Next mem mu 6 c).memory 6052 ([(l2Next mem mu 6 c).carry, mu, maxWord] ++ rest)) := by
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
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      UInt256.gt, UInt256.isTrue, List.exchange, l2Next, macSum, macCarry, mulHi,
      hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, ha0, ha1, ha2]
  all_goals first
    | exact MacAlt.macCarryFix _ _ _ _
    | (refine ⟨?_, MacAlt.macCarryFix _ _ _ _⟩; rw [MacAlt.macSumNat])
    | rw [MacAlt.macSumNat]

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
      (atState s mem 5735 ([c, bi, ap, maxWord] ++ rest)) =
      some (atState s (midMem mem c) 5757 ([maxWord] ++ rest)) := by
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
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      UInt256.gt, UInt256.isTrue, List.exchange, midMem, midMem1, wordAddComm, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, ha0, ha1]

/-- Exact c0 boundary; complete scratch and frame are retained. -/
theorem run_c0 (s : State) (mem : ByteArray)  (rest : List UInt256)
    (hcap : rest.length ≤ 1013) (hrun : s.halt = .Running)
    (hact : 296 ≤ s.activeWords.toNat) :
    Challenge.EvmProof.Stepper.runLocatedBlock block_c0
      (atState s mem 5757 ([maxWord] ++ rest)) =
      some (atState s (mem) 5787 ([rowC0 mem 8, rowMu mem 8, maxWord] ++ rest)) := by
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
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      UInt256.gt, UInt256.isTrue, List.exchange, rowC0, rowMu, mulHi, wordMulComm, MacAlt.subSubFold, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, ha0, ha1, ha2]

/-- Exact tail boundary; complete scratch and frame are retained. -/
theorem run_tail (s : State) (mem : ByteArray) (c mu pbi : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1013) (hrun : s.halt = .Running)
    (hact : 296 ≤ s.activeWords.toNat) :
    Challenge.EvmProof.Stepper.runLocatedBlock block_tail
      (atState s mem 6052 ([c, mu, maxWord, pbi] ++ rest)) =
      some (atState s (tailMem mem c) 6083 ([UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904 + pbi] ++ rest)) := by
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
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      UInt256.gt, UInt256.isTrue, List.exchange, tailMem, tailMem1, wordAddComm, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, ha0, ha1, ha2]

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
      (atState s mem 5414
        ([UInt256.ofNat 0, rowBi mem pb 8 i, UInt256.ofNat (pa - 32), maxWord, pbi] ++ rest))
      (atState s (rowMem mem pa pb 8 i) 6083
        ([UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904 + pbi] ++ rest)) := by
  let bi := rowBi mem pb 8 i
  let suffix := pbi :: rest
  have hcap' : suffix.length ≤ 1013 := by simp only [suffix, List.length_cons]; omega
  have hL1_0 := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    (s := atState s (l1Step mem bi pa 8 0).memory 5414 ([(l1Step mem bi pa 8 0).carry, bi, UInt256.ofNat (pa - 32), maxWord] ++ suffix)) Artifact.submissionArtifact .Osaka block_l1_0 hcode hfork
    (run_l1_0 s (l1Step mem bi pa 8 0).memory bi (l1Step mem bi pa 8 0).carry pa suffix
      hcap' hrun hact hpa hpaFit) hrun hnp
  simp only [l1Next_eq] at hL1_0
  have hL1_1 := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    (s := atState s (l1Step mem bi pa 8 1).memory 5455 ([(l1Step mem bi pa 8 1).carry, bi, UInt256.ofNat (pa - 32), maxWord] ++ suffix)) Artifact.submissionArtifact .Osaka block_l1_1 hcode hfork
    (run_l1_1 s (l1Step mem bi pa 8 1).memory bi (l1Step mem bi pa 8 1).carry pa suffix
      hcap' hrun hact hpa hpaFit) hrun hnp
  simp only [l1Next_eq] at hL1_1
  have hL1_2 := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    (s := atState s (l1Step mem bi pa 8 2).memory 5495 ([(l1Step mem bi pa 8 2).carry, bi, UInt256.ofNat (pa - 32), maxWord] ++ suffix)) Artifact.submissionArtifact .Osaka block_l1_2 hcode hfork
    (run_l1_2 s (l1Step mem bi pa 8 2).memory bi (l1Step mem bi pa 8 2).carry pa suffix
      hcap' hrun hact hpa hpaFit) hrun hnp
  simp only [l1Next_eq] at hL1_2
  have hL1_3 := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    (s := atState s (l1Step mem bi pa 8 3).memory 5535 ([(l1Step mem bi pa 8 3).carry, bi, UInt256.ofNat (pa - 32), maxWord] ++ suffix)) Artifact.submissionArtifact .Osaka block_l1_3 hcode hfork
    (run_l1_3 s (l1Step mem bi pa 8 3).memory bi (l1Step mem bi pa 8 3).carry pa suffix
      hcap' hrun hact hpa hpaFit) hrun hnp
  simp only [l1Next_eq] at hL1_3
  have hL1_4 := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    (s := atState s (l1Step mem bi pa 8 4).memory 5575 ([(l1Step mem bi pa 8 4).carry, bi, UInt256.ofNat (pa - 32), maxWord] ++ suffix)) Artifact.submissionArtifact .Osaka block_l1_4 hcode hfork
    (run_l1_4 s (l1Step mem bi pa 8 4).memory bi (l1Step mem bi pa 8 4).carry pa suffix
      hcap' hrun hact hpa hpaFit) hrun hnp
  simp only [l1Next_eq] at hL1_4
  have hL1_5 := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    (s := atState s (l1Step mem bi pa 8 5).memory 5615 ([(l1Step mem bi pa 8 5).carry, bi, UInt256.ofNat (pa - 32), maxWord] ++ suffix)) Artifact.submissionArtifact .Osaka block_l1_5 hcode hfork
    (run_l1_5 s (l1Step mem bi pa 8 5).memory bi (l1Step mem bi pa 8 5).carry pa suffix
      hcap' hrun hact hpa hpaFit) hrun hnp
  simp only [l1Next_eq] at hL1_5
  have hL1_6 := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    (s := atState s (l1Step mem bi pa 8 6).memory 5655 ([(l1Step mem bi pa 8 6).carry, bi, UInt256.ofNat (pa - 32), maxWord] ++ suffix)) Artifact.submissionArtifact .Osaka block_l1_6 hcode hfork
    (run_l1_6 s (l1Step mem bi pa 8 6).memory bi (l1Step mem bi pa 8 6).carry pa suffix
      hcap' hrun hact hpa hpaFit) hrun hnp
  simp only [l1Next_eq] at hL1_6
  have hL1_7 := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    (s := atState s (l1Step mem bi pa 8 7).memory 5695 ([(l1Step mem bi pa 8 7).carry, bi, UInt256.ofNat (pa - 32), maxWord] ++ suffix)) Artifact.submissionArtifact .Osaka block_l1_7 hcode hfork
    (run_l1_7 s (l1Step mem bi pa 8 7).memory bi (l1Step mem bi pa 8 7).carry pa suffix
      hcap' hrun hact hpa hpaFit) hrun hnp
  simp only [l1Next_eq] at hL1_7
  let first := l1Step mem bi pa 8 8
  let middle := midMem first.memory first.carry
  have hMid := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    (s := atState s first.memory 5735
      ([first.carry, bi, UInt256.ofNat (pa - 32), maxWord] ++ suffix))
    Artifact.submissionArtifact .Osaka block_middle hcode hfork
    (run_middle s first.memory first.carry bi (UInt256.ofNat (pa - 32)) suffix hcap' hrun hact) hrun hnp
  have hC0 := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    (s := atState s middle 5757 ([maxWord] ++ suffix))
    Artifact.submissionArtifact .Osaka block_c0 hcode hfork
    (run_c0 s middle suffix hcap' hrun hact) hrun hnp
  have hmu : rowMu middle 8 = rowMu first.memory 8 := rowMu_midMem8 _ _
  have hc0 : rowC0 middle 8 = rowC0 first.memory 8 := rowC0_midMem8 _ _
  rw [hmu, hc0] at hC0
  let mu := rowMu first.memory 8
  let c0 := rowC0 first.memory 8
  have hL2_0 := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    (s := atState s (l2Step middle mu c0 8 0).memory 5787 ([(l2Step middle mu c0 8 0).carry, mu, maxWord] ++ suffix)) Artifact.submissionArtifact .Osaka block_l2_0 hcode hfork
    (run_l2_0 s (l2Step middle mu c0 8 0).memory mu (l2Step middle mu c0 8 0).carry suffix
      hcap' hrun hact) hrun hnp
  simp only [l2Next_eq] at hL2_0
  have hL2_1 := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    (s := atState s (l2Step middle mu c0 8 1).memory 5825 ([(l2Step middle mu c0 8 1).carry, mu, maxWord] ++ suffix)) Artifact.submissionArtifact .Osaka block_l2_1 hcode hfork
    (run_l2_1 s (l2Step middle mu c0 8 1).memory mu (l2Step middle mu c0 8 1).carry suffix
      hcap' hrun hact) hrun hnp
  simp only [l2Next_eq] at hL2_1
  have hL2_2 := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    (s := atState s (l2Step middle mu c0 8 2).memory 5863 ([(l2Step middle mu c0 8 2).carry, mu, maxWord] ++ suffix)) Artifact.submissionArtifact .Osaka block_l2_2 hcode hfork
    (run_l2_2 s (l2Step middle mu c0 8 2).memory mu (l2Step middle mu c0 8 2).carry suffix
      hcap' hrun hact) hrun hnp
  simp only [l2Next_eq] at hL2_2
  have hL2_3 := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    (s := atState s (l2Step middle mu c0 8 3).memory 5901 ([(l2Step middle mu c0 8 3).carry, mu, maxWord] ++ suffix)) Artifact.submissionArtifact .Osaka block_l2_3 hcode hfork
    (run_l2_3 s (l2Step middle mu c0 8 3).memory mu (l2Step middle mu c0 8 3).carry suffix
      hcap' hrun hact) hrun hnp
  simp only [l2Next_eq] at hL2_3
  have hL2_4 := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    (s := atState s (l2Step middle mu c0 8 4).memory 5939 ([(l2Step middle mu c0 8 4).carry, mu, maxWord] ++ suffix)) Artifact.submissionArtifact .Osaka block_l2_4 hcode hfork
    (run_l2_4 s (l2Step middle mu c0 8 4).memory mu (l2Step middle mu c0 8 4).carry suffix
      hcap' hrun hact) hrun hnp
  simp only [l2Next_eq] at hL2_4
  have hL2_5 := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    (s := atState s (l2Step middle mu c0 8 5).memory 5977 ([(l2Step middle mu c0 8 5).carry, mu, maxWord] ++ suffix)) Artifact.submissionArtifact .Osaka block_l2_5 hcode hfork
    (run_l2_5 s (l2Step middle mu c0 8 5).memory mu (l2Step middle mu c0 8 5).carry suffix
      hcap' hrun hact) hrun hnp
  simp only [l2Next_eq] at hL2_5
  have hL2_6 := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    (s := atState s (l2Step middle mu c0 8 6).memory 6015 ([(l2Step middle mu c0 8 6).carry, mu, maxWord] ++ suffix)) Artifact.submissionArtifact .Osaka block_l2_6 hcode hfork
    (run_l2_6 s (l2Step middle mu c0 8 6).memory mu (l2Step middle mu c0 8 6).carry suffix
      hcap' hrun hact) hrun hnp
  simp only [l2Next_eq] at hL2_6
  let second := l2Step middle mu c0 8 7
  have hTail := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    (s := atState s second.memory 6052 ([second.carry, mu, maxWord, pbi] ++ rest))
    Artifact.submissionArtifact .Osaka block_tail hcode hfork
    (run_tail s second.memory second.carry mu pbi rest (by omega) hrun hact) hrun hnp
  exact hL1_0.trans (hL1_1.trans (hL1_2.trans (hL1_3.trans (hL1_4.trans (hL1_5.trans (hL1_6.trans (hL1_7.trans (hMid.trans (hC0.trans (hL2_0.trans (hL2_1.trans (hL2_2.trans (hL2_3.trans (hL2_4.trans (hL2_5.trans (hL2_6.trans (hTail)))))))))))))))))

end Challenge.Modexp.Submission.Proofs.Fast.MonproN8
