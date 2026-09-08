import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths for the appended shift-reduce base conversion (generated). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 2862..2873, pc 4643..4657. -/
def blk2862 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3128 .JUMPDEST,
   opAt 3129 (.Dup ⟨0, by decide⟩),
   opAt 3130 (.Dup ⟨3, by decide⟩),
   opAt 3131 .EQ,
   pushAt 3132 0 0,
   opAt 3133 .MLOAD,
   pushAt 3134 1 255,
   opAt 3135 .SHR,
   opAt 3136 .AND,
   opAt 3137 .ISZERO,
   pushAt 3138 2 4448,
   opAt 3139 .JUMPI]

/-- Instructions 2874..2888, pc 4658..4686. -/
def blk2874 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3140 (.Dup ⟨0, by decide⟩),
   pushAt 3141 1 96,
   pushAt 3142 2 1024,
   opAt 3143 .CALLDATACOPY,
   opAt 3144 (.Dup ⟨0, by decide⟩),
   pushAt 3145 1 96,
   pushAt 3146 2 8256,
   opAt 3147 .CALLDATACOPY,
   pushAt 3148 0 0,
   pushAt 3149 2 8224,
   opAt 3150 .MSTORE,
   pushAt 3151 2 4453,
   pushAt 3152 2 2048,
   pushAt 3153 2 2655,
   opAt 3154 .JUMP]

/-- Instructions 2889..2891, pc 4687..4691. -/
def blk2889 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3155 .JUMPDEST,
   pushAt 3156 2 1533,
   opAt 3157 .JUMP]

/-- Instructions 2892..2895, pc 4692..4698. -/
def blk2892 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3158 .JUMPDEST,
   pushAt 3159 1 1,
   pushAt 3160 2 9408,
   opAt 3161 .MLOAD]

/-- Instructions 2896..2914, pc 4699..4721. -/
def blk2896 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3162 .JUMPDEST,
   opAt 3163 (.Dup ⟨0, by decide⟩),
   opAt 3164 .MLOAD,
   opAt 3165 .NOT,
   opAt 3166 (.Dup ⟨2, by decide⟩),
   opAt 3167 .ADD,
   opAt 3168 (.Dup ⟨2, by decide⟩),
   opAt 3169 (.Dup ⟨1, by decide⟩),
   opAt 3170 .LT,
   opAt 3171 (.Swap ⟨2, by decide⟩),
   opAt 3172 .POP,
   opAt 3173 (.Dup ⟨1, by decide⟩),
   pushAt 3174 2 5120,
   opAt 3175 .ADD,
   opAt 3176 .MSTORE,
   opAt 3177 (.Dup ⟨0, by decide⟩),
   opAt 3178 .ISZERO,
   pushAt 3179 2 4521,
   opAt 3180 .JUMPI]

/-- Instructions 2915..2918, pc 4722..4759. -/
def blk2915 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3181 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3182 .ADD,
   pushAt 3183 2 4460,
   opAt 3184 .JUMP]

/-- Instructions 2919..2955, pc 4760..4805. -/
def blk2919 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3185 .JUMPDEST,
   opAt 3186 .POP,
   opAt 3187 .POP,
   pushAt 3188 0 0,
   opAt 3189 .MLOAD,
   opAt 3190 (.Dup ⟨0, by decide⟩),
   pushAt 3191 0 0,
   opAt 3192 .SUB,
   opAt 3193 (.Dup ⟨1, by decide⟩),
   opAt 3194 .AND,
   opAt 3195 (.Dup ⟨0, by decide⟩),
   pushAt 3196 2 6144,
   opAt 3197 .MSTORE,
   opAt 3198 (.Dup ⟨0, by decide⟩),
   opAt 3199 (.Dup ⟨2, by decide⟩),
   opAt 3200 .DIV,
   opAt 3201 (.Dup ⟨0, by decide⟩),
   pushAt 3202 2 6176,
   opAt 3203 .MSTORE,
   opAt 3204 (.Dup ⟨1, by decide⟩),
   pushAt 3205 0 0,
   opAt 3206 .SUB,
   opAt 3207 (.Dup ⟨2, by decide⟩),
   opAt 3208 (.Swap ⟨0, by decide⟩),
   opAt 3209 .DIV,
   pushAt 3210 1 1,
   opAt 3211 .ADD,
   pushAt 3212 2 6208,
   opAt 3213 .MSTORE,
   opAt 3214 (.Dup ⟨0, by decide⟩),
   pushAt 3215 0 0,
   opAt 3216 .SUB,
   opAt 3217 (.Dup ⟨1, by decide⟩),
   opAt 3218 (.Swap ⟨0, by decide⟩),
   opAt 3219 .MOD,
   pushAt 3220 2 6240,
   opAt 3221 .MSTORE]

/-- Instructions 2956..2981, pc 4806..4836. -/
def blk2956 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3222 .JUMPDEST,
   pushAt 3223 1 1,
   opAt 3224 (.Dup ⟨0, by decide⟩),
   opAt 3225 (.Dup ⟨2, by decide⟩),
   opAt 3226 .MUL,
   pushAt 3227 1 2,
   opAt 3228 .SUB,
   opAt 3229 .MUL,
   opAt 3230 (.Dup ⟨0, by decide⟩),
   opAt 3231 (.Dup ⟨2, by decide⟩),
   opAt 3232 .MUL,
   pushAt 3233 1 2,
   opAt 3234 .SUB,
   opAt 3235 .MUL,
   opAt 3236 (.Dup ⟨0, by decide⟩),
   opAt 3237 (.Dup ⟨2, by decide⟩),
   opAt 3238 .MUL,
   pushAt 3239 1 2,
   opAt 3240 .SUB,
   opAt 3241 .MUL,
   opAt 3242 (.Dup ⟨0, by decide⟩),
   opAt 3243 (.Dup ⟨2, by decide⟩),
   opAt 3244 .MUL,
   pushAt 3245 1 2,
   opAt 3246 .SUB,
   opAt 3247 .MUL]

/-- Instructions 2982..3012, pc 4837..4873. -/
def blk2982 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3248 .JUMPDEST,
   opAt 3249 (.Dup ⟨0, by decide⟩),
   opAt 3250 (.Dup ⟨2, by decide⟩),
   opAt 3251 .MUL,
   pushAt 3252 1 2,
   opAt 3253 .SUB,
   opAt 3254 .MUL,
   opAt 3255 (.Dup ⟨0, by decide⟩),
   opAt 3256 (.Dup ⟨2, by decide⟩),
   opAt 3257 .MUL,
   pushAt 3258 1 2,
   opAt 3259 .SUB,
   opAt 3260 .MUL,
   opAt 3261 (.Dup ⟨0, by decide⟩),
   opAt 3262 (.Dup ⟨2, by decide⟩),
   opAt 3263 .MUL,
   pushAt 3264 1 2,
   opAt 3265 .SUB,
   opAt 3266 .MUL,
   opAt 3267 (.Dup ⟨0, by decide⟩),
   opAt 3268 (.Dup ⟨2, by decide⟩),
   opAt 3269 .MUL,
   pushAt 3270 1 2,
   opAt 3271 .SUB,
   opAt 3272 .MUL,
   pushAt 3273 2 6272,
   opAt 3274 .MSTORE,
   opAt 3275 .POP,
   opAt 3276 .POP,
   opAt 3277 .POP,
   opAt 3278 (.Dup ⟨1, by decide⟩)]

/-- Instructions 3013..3017, pc 4874..4880. -/
def blk3013 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3279 .JUMPDEST,
   opAt 3280 (.Dup ⟨0, by decide⟩),
   opAt 3281 .ISZERO,
   pushAt 3282 2 5131,
   opAt 3283 .JUMPI]

/-- Instructions 3018..3025, pc 4881..4894. -/
def blk3018 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3284 (.Dup ⟨1, by decide⟩),
   pushAt 3285 2 2048,
   pushAt 3286 2 8224,
   opAt 3287 .MCOPY,
   pushAt 3288 0 0,
   pushAt 3289 2 9440,
   opAt 3290 .MLOAD,
   opAt 3291 .MSTORE]

/-- Instructions 3026..3068, pc 4895..4953. -/
def blk3026 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3292 .JUMPDEST,
   pushAt 3293 2 2048,
   opAt 3294 .MLOAD,
   pushAt 3295 2 6144,
   opAt 3296 .MLOAD,
   opAt 3297 (.Dup ⟨1, by decide⟩),
   opAt 3298 (.Dup ⟨1, by decide⟩),
   opAt 3299 (.Swap ⟨0, by decide⟩),
   opAt 3300 .DIV,
   opAt 3301 (.Swap ⟨1, by decide⟩),
   opAt 3302 .MOD,
   pushAt 3303 2 6208,
   opAt 3304 .MLOAD,
   opAt 3305 .MUL,
   pushAt 3306 2 2080,
   opAt 3307 .MLOAD,
   pushAt 3308 2 6144,
   opAt 3309 .MLOAD,
   opAt 3310 (.Swap ⟨0, by decide⟩),
   opAt 3311 .DIV,
   opAt 3312 .ADD,
   pushAt 3313 2 6176,
   opAt 3314 .MLOAD,
   opAt 3315 (.Dup ⟨0, by decide⟩),
   pushAt 3316 2 6240,
   opAt 3317 .MLOAD,
   opAt 3318 (.Dup ⟨4, by decide⟩),
   opAt 3319 .MULMOD,
   opAt 3320 (.Dup ⟨2, by decide⟩),
   opAt 3321 (.Swap ⟨0, by decide⟩),
   opAt 3322 .ADDMOD,
   opAt 3323 (.Swap ⟨0, by decide⟩),
   opAt 3324 .SUB,
   pushAt 3325 2 6272,
   opAt 3326 .MLOAD,
   opAt 3327 .MUL,
   opAt 3328 (.Dup ⟨0, by decide⟩),
   pushAt 3329 0 0,
   opAt 3330 .LT,
   opAt 3331 (.Swap ⟨0, by decide⟩),
   opAt 3332 .SUB,
   opAt 3333 (.Swap ⟨0, by decide⟩),
   pushAt 3334 2 6176,
   opAt 3335 .MLOAD,
   opAt 3336 .JUMPDEST,
   opAt 3337 .GT,
   opAt 3338 .ISZERO,
   pushAt 3339 0 0,
   opAt 3340 .SUB,
   opAt 3341 .OR]

/-- Instructions 3069..3076, pc 4954..4967. -/
def blk3069 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3342 .JUMPDEST,
   pushAt 3343 0 0,
   pushAt 3344 2 9440,
   opAt 3345 .MLOAD,
   pushAt 3346 2 9408,
   opAt 3347 .MLOAD,
   pushAt 3348 2 5120,
   opAt 3349 .ADD]

/-- Instructions 3077..3124, pc 4968..5115. -/
def blk3077 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3350 .JUMPDEST,
   opAt 3351 (.Dup ⟨0, by decide⟩),
   opAt 3352 .MLOAD,
   pushAt 3353 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 3354 (.Dup ⟨5, by decide⟩),
   opAt 3355 (.Dup ⟨2, by decide⟩),
   opAt 3356 .MUL,
   opAt 3357 (.Swap ⟨1, by decide⟩),
   opAt 3358 (.Dup ⟨6, by decide⟩),
   opAt 3359 .MULMOD,
   opAt 3360 (.Dup ⟨1, by decide⟩),
   opAt 3361 (.Dup ⟨1, by decide⟩),
   opAt 3362 .LT,
   opAt 3363 .SUB,
   opAt 3364 (.Dup ⟨4, by decide⟩),
   opAt 3365 (.Dup ⟨2, by decide⟩),
   opAt 3366 .ADD,
   opAt 3367 (.Dup ⟨0, by decide⟩),
   opAt 3368 (.Swap ⟨5, by decide⟩),
   opAt 3369 .GT,
   opAt 3370 .SUB,
   opAt 3371 .SUB,
   opAt 3372 (.Dup ⟨3, by decide⟩),
   opAt 3373 (.Dup ⟨3, by decide⟩),
   opAt 3374 .MLOAD,
   opAt 3375 .ADD,
   opAt 3376 (.Dup ⟨0, by decide⟩),
   opAt 3377 (.Swap ⟨4, by decide⟩),
   opAt 3378 .GT,
   opAt 3379 .ADD,
   opAt 3380 (.Swap ⟨2, by decide⟩),
   opAt 3381 (.Dup ⟨2, by decide⟩),
   pushAt 3382 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3383 .ADD,
   opAt 3384 (.Swap ⟨2, by decide⟩),
   opAt 3385 .MSTORE,
   pushAt 3386 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3387 .ADD,
   pushAt 3388 2 8224,
   opAt 3389 (.Dup ⟨2, by decide⟩),
   opAt 3390 .GT,
   pushAt 3391 2 4738,
   opAt 3392 .JUMPI]

/-- Instructions 3125..3152, pc 5116..5149. -/
def blk3125 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3393 .POP,
   opAt 3394 .POP,
   pushAt 3395 2 8224,
   opAt 3396 .MLOAD,
   opAt 3397 (.Dup ⟨1, by decide⟩),
   opAt 3398 .ADD,
   opAt 3399 (.Dup ⟨1, by decide⟩),
   opAt 3400 (.Dup ⟨1, by decide⟩),
   opAt 3401 .LT,
   opAt 3402 (.Swap ⟨1, by decide⟩),
   opAt 3403 .POP,
   opAt 3404 (.Dup ⟨2, by decide⟩),
   opAt 3405 (.Dup ⟨1, by decide⟩),
   opAt 3406 .LT,
   opAt 3407 (.Swap ⟨0, by decide⟩),
   opAt 3408 (.Dup ⟨3, by decide⟩),
   opAt 3409 (.Swap ⟨0, by decide⟩),
   opAt 3410 .SUB,
   opAt 3411 (.Dup ⟨0, by decide⟩),
   pushAt 3412 2 8224,
   opAt 3413 .MSTORE,
   opAt 3414 .POP,
   opAt 3415 .GT,
   opAt 3416 (.Swap ⟨0, by decide⟩),
   opAt 3417 .POP,
   opAt 3418 .ISZERO,
   pushAt 3419 2 5012,
   opAt 3420 .JUMPI]

/-- Instructions 3153..3156, pc 5150..5155. -/
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3421 .JUMPDEST,
   pushAt 3422 0 0,
   pushAt 3423 2 9440,
   opAt 3424 .MLOAD]

/-- Instructions 3157..3191, pc 5156..5228. -/
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3425 .JUMPDEST,
   opAt 3426 (.Dup ⟨0, by decide⟩),
   opAt 3427 .MLOAD,
   opAt 3428 (.Dup ⟨1, by decide⟩),
   pushAt 3429 2 8256,
   opAt 3430 (.Swap ⟨0, by decide⟩),
   opAt 3431 .SUB,
   opAt 3432 .MLOAD,
   opAt 3433 (.Dup ⟨1, by decide⟩),
   opAt 3434 .ADD,
   opAt 3435 (.Dup ⟨0, by decide⟩),
   opAt 3436 (.Dup ⟨2, by decide⟩),
   opAt 3437 .GT,
   opAt 3438 (.Swap ⟨1, by decide⟩),
   opAt 3439 .POP,
   opAt 3440 (.Dup ⟨3, by decide⟩),
   opAt 3441 .ADD,
   opAt 3442 (.Dup ⟨0, by decide⟩),
   opAt 3443 (.Dup ⟨4, by decide⟩),
   opAt 3444 .GT,
   opAt 3445 (.Swap ⟨3, by decide⟩),
   opAt 3446 .POP,
   opAt 3447 (.Dup ⟨2, by decide⟩),
   opAt 3448 .MSTORE,
   opAt 3449 (.Swap ⟨0, by decide⟩),
   opAt 3450 (.Swap ⟨1, by decide⟩),
   opAt 3451 .OR,
   opAt 3452 (.Swap ⟨0, by decide⟩),
   pushAt 3453 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3454 .ADD,
   pushAt 3455 2 8255,
   opAt 3456 (.Dup ⟨1, by decide⟩),
   opAt 3457 .GT,
   pushAt 3458 2 4921,
   opAt 3459 .JUMPI]

/-- Instructions 3192..3203, pc 5229..5246. -/
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3460 .POP,
   pushAt 3461 2 8224,
   opAt 3462 .MLOAD,
   opAt 3463 (.Dup ⟨1, by decide⟩),
   opAt 3464 .ADD,
   opAt 3465 (.Dup ⟨0, by decide⟩),
   pushAt 3466 2 8224,
   opAt 3467 .MSTORE,
   opAt 3468 .LT,
   opAt 3469 .ISZERO,
   pushAt 3470 2 4915,
   opAt 3471 .JUMPI]

/-- Instructions 3204..3209, pc 5247..5256. -/
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3472 .JUMPDEST,
   pushAt 3473 2 8224,
   opAt 3474 .MLOAD,
   opAt 3475 .ISZERO,
   pushAt 3476 2 5111,
   opAt 3477 .JUMPI]

/-- Instructions 3210..3212, pc 5257..5261. -/
def blk3210 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3478 0 0,
   pushAt 3479 2 9440,
   opAt 3480 .MLOAD]

/-- Instructions 3213..3244, pc 5262..5331. -/
def blk3213 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3481 .JUMPDEST,
   opAt 3482 (.Dup ⟨0, by decide⟩),
   opAt 3483 .MLOAD,
   opAt 3484 (.Dup ⟨1, by decide⟩),
   pushAt 3485 2 8256,
   opAt 3486 (.Swap ⟨0, by decide⟩),
   opAt 3487 .SUB,
   opAt 3488 .MLOAD,
   opAt 3489 (.Dup ⟨1, by decide⟩),
   opAt 3490 (.Dup ⟨1, by decide⟩),
   opAt 3491 .GT,
   opAt 3492 (.Swap ⟨1, by decide⟩),
   opAt 3493 .SUB,
   opAt 3494 (.Dup ⟨3, by decide⟩),
   opAt 3495 (.Dup ⟨1, by decide⟩),
   opAt 3496 .LT,
   opAt 3497 (.Swap ⟨0, by decide⟩),
   opAt 3498 (.Dup ⟨4, by decide⟩),
   opAt 3499 (.Swap ⟨0, by decide⟩),
   opAt 3500 .SUB,
   opAt 3501 (.Dup ⟨3, by decide⟩),
   opAt 3502 .MSTORE,
   opAt 3503 .OR,
   opAt 3504 (.Swap ⟨1, by decide⟩),
   opAt 3505 .POP,
   pushAt 3506 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3507 .ADD,
   pushAt 3508 2 8255,
   opAt 3509 (.Dup ⟨1, by decide⟩),
   opAt 3510 .GT,
   pushAt 3511 2 5027,
   opAt 3512 .JUMPI]

/-- Instructions 3245..3252, pc 5332..5345. -/
def blk3245 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3513 .POP,
   pushAt 3514 2 8224,
   opAt 3515 .MLOAD,
   opAt 3516 .SUB,
   pushAt 3517 2 8224,
   opAt 3518 .MSTORE,
   pushAt 3519 2 5012,
   opAt 3520 .JUMP]

/-- Instructions 3253..3257, pc 5346..5356. -/
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3521 .JUMPDEST,
   pushAt 3522 2 5122,
   pushAt 3523 2 2048,
   pushAt 3524 2 2655,
   opAt 3525 .JUMP]

/-- Instructions 3258..3263, pc 5357..5365. -/
def blk3258 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3526 .JUMPDEST,
   pushAt 3527 1 1,
   opAt 3528 (.Swap ⟨0, by decide⟩),
   opAt 3529 .SUB,
   pushAt 3530 2 4635,
   opAt 3531 .JUMP]

/-- Instructions 3264..3267, pc 5366..5371. -/
def blk3264 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3532 .JUMPDEST,
   opAt 3533 .POP,
   pushAt 3534 2 1756,
   opAt 3535 .JUMP]

theorem jumpDest4643 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4404 = true :=
  Artifact.isValidJumpDest_index 3128 (by rfl)

theorem jumpDest4687 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4448 = true :=
  Artifact.isValidJumpDest_index 3155 (by rfl)

theorem jumpDest4692 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4453 = true :=
  Artifact.isValidJumpDest_index 3158 (by rfl)

theorem jumpDest4699 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4460 = true :=
  Artifact.isValidJumpDest_index 3162 (by rfl)

theorem jumpDest4760 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4521 = true :=
  Artifact.isValidJumpDest_index 3185 (by rfl)

theorem jumpDest4806 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4567 = true :=
  Artifact.isValidJumpDest_index 3222 (by rfl)

theorem jumpDest4837 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4598 = true :=
  Artifact.isValidJumpDest_index 3248 (by rfl)

theorem jumpDest4874 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4635 = true :=
  Artifact.isValidJumpDest_index 3279 (by rfl)

theorem jumpDest4895 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4656 = true :=
  Artifact.isValidJumpDest_index 3292 (by rfl)

theorem jumpDest4954 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4724 = true :=
  Artifact.isValidJumpDest_index 3342 (by rfl)

theorem jumpDest4968 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4738 = true :=
  Artifact.isValidJumpDest_index 3350 (by rfl)

theorem jumpDest5150 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4915 = true :=
  Artifact.isValidJumpDest_index 3421 (by rfl)

theorem jumpDest5156 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4921 = true :=
  Artifact.isValidJumpDest_index 3425 (by rfl)

theorem jumpDest5247 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5012 = true :=
  Artifact.isValidJumpDest_index 3472 (by rfl)

theorem jumpDest5262 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5027 = true :=
  Artifact.isValidJumpDest_index 3481 (by rfl)

theorem jumpDest5346 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5111 = true :=
  Artifact.isValidJumpDest_index 3521 (by rfl)

theorem jumpDest5357 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5122 = true :=
  Artifact.isValidJumpDest_index 3526 (by rfl)

theorem jumpDest5366 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5131 = true :=
  Artifact.isValidJumpDest_index 3532 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
