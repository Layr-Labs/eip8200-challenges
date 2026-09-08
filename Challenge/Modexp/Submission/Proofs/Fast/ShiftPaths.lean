import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths for the appended shift-reduce base conversion (generated). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 2790..2801, pc 4686..4700. -/
def blk2862 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3097 .JUMPDEST,
   opAt 3098 (.Dup ⟨0, by decide⟩),
   opAt 3099 (.Dup ⟨3, by decide⟩),
   opAt 3100 .EQ,
   pushAt 3101 0 0,
   opAt 3102 .MLOAD,
   pushAt 3103 1 255,
   opAt 3104 .SHR,
   opAt 3105 .AND,
   opAt 3106 .ISZERO,
   pushAt 3107 2 4730,
   opAt 3108 .JUMPI]

/-- Instructions 2802..2816, pc 4701..4729. -/
def blk2874 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3109 (.Dup ⟨0, by decide⟩),
   pushAt 3110 1 96,
   pushAt 3111 2 1024,
   opAt 3112 .CALLDATACOPY,
   opAt 3113 (.Dup ⟨0, by decide⟩),
   pushAt 3114 1 96,
   pushAt 3115 2 8256,
   opAt 3116 .CALLDATACOPY,
   pushAt 3117 0 0,
   pushAt 3118 2 8224,
   opAt 3119 .MSTORE,
   pushAt 3120 2 4735,
   pushAt 3121 2 2048,
   pushAt 3122 2 2642,
   opAt 3123 .JUMP]

/-- Instructions 2817..2819, pc 4730..4734. -/
def blk2889 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3124 .JUMPDEST,
   pushAt 3125 2 1533,
   opAt 3126 .JUMP]

/-- Instructions 2820..2823, pc 4735..4741. -/
def blk2892 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3127 .JUMPDEST,
   pushAt 3128 1 1,
   pushAt 3129 2 9408,
   opAt 3130 .MLOAD]

/-- Instructions 2824..2842, pc 4742..4764. -/
def blk2896 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3131 .JUMPDEST,
   opAt 3132 (.Dup ⟨0, by decide⟩),
   opAt 3133 .MLOAD,
   opAt 3134 .NOT,
   opAt 3135 (.Dup ⟨2, by decide⟩),
   opAt 3136 .ADD,
   opAt 3137 (.Dup ⟨2, by decide⟩),
   opAt 3138 (.Dup ⟨1, by decide⟩),
   opAt 3139 .LT,
   opAt 3140 (.Swap ⟨2, by decide⟩),
   opAt 3141 .POP,
   opAt 3142 (.Dup ⟨1, by decide⟩),
   pushAt 3143 2 5120,
   opAt 3144 .ADD,
   opAt 3145 .MSTORE,
   opAt 3146 (.Dup ⟨0, by decide⟩),
   opAt 3147 .ISZERO,
   pushAt 3148 2 4803,
   opAt 3149 .JUMPI]

/-- Instructions 2843..2846, pc 4765..4802. -/
def blk2915 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3150 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3151 .ADD,
   pushAt 3152 2 4742,
   opAt 3153 .JUMP]

/-- Instructions 2847..2883, pc 4803..4848. -/
def blk2919 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3154 .JUMPDEST,
   opAt 3155 .POP,
   opAt 3156 .POP,
   pushAt 3157 0 0,
   opAt 3158 .MLOAD,
   opAt 3159 (.Dup ⟨0, by decide⟩),
   pushAt 3160 0 0,
   opAt 3161 .SUB,
   opAt 3162 (.Dup ⟨1, by decide⟩),
   opAt 3163 .AND,
   opAt 3164 (.Dup ⟨0, by decide⟩),
   pushAt 3165 2 6144,
   opAt 3166 .MSTORE,
   opAt 3167 (.Dup ⟨0, by decide⟩),
   opAt 3168 (.Dup ⟨2, by decide⟩),
   opAt 3169 .DIV,
   opAt 3170 (.Dup ⟨0, by decide⟩),
   pushAt 3171 2 6176,
   opAt 3172 .MSTORE,
   opAt 3173 (.Dup ⟨1, by decide⟩),
   pushAt 3174 0 0,
   opAt 3175 .SUB,
   opAt 3176 (.Dup ⟨2, by decide⟩),
   opAt 3177 (.Swap ⟨0, by decide⟩),
   opAt 3178 .DIV,
   pushAt 3179 1 1,
   opAt 3180 .ADD,
   pushAt 3181 2 6208,
   opAt 3182 .MSTORE,
   opAt 3183 (.Dup ⟨0, by decide⟩),
   pushAt 3184 0 0,
   opAt 3185 .SUB,
   opAt 3186 (.Dup ⟨1, by decide⟩),
   opAt 3187 (.Swap ⟨0, by decide⟩),
   opAt 3188 .MOD,
   pushAt 3189 2 6240,
   opAt 3190 .MSTORE]

/-- Instructions 2884..2909, pc 4849..4879. -/
def blk2956 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3191 .JUMPDEST,
   pushAt 3192 1 1,
   opAt 3193 (.Dup ⟨0, by decide⟩),
   opAt 3194 (.Dup ⟨2, by decide⟩),
   opAt 3195 .MUL,
   pushAt 3196 1 2,
   opAt 3197 .SUB,
   opAt 3198 .MUL,
   opAt 3199 (.Dup ⟨0, by decide⟩),
   opAt 3200 (.Dup ⟨2, by decide⟩),
   opAt 3201 .MUL,
   pushAt 3202 1 2,
   opAt 3203 .SUB,
   opAt 3204 .MUL,
   opAt 3205 (.Dup ⟨0, by decide⟩),
   opAt 3206 (.Dup ⟨2, by decide⟩),
   opAt 3207 .MUL,
   pushAt 3208 1 2,
   opAt 3209 .SUB,
   opAt 3210 .MUL,
   opAt 3211 (.Dup ⟨0, by decide⟩),
   opAt 3212 (.Dup ⟨2, by decide⟩),
   opAt 3213 .MUL,
   pushAt 3214 1 2,
   opAt 3215 .SUB,
   opAt 3216 .MUL]

/-- Instructions 2910..2940, pc 4880..4916. -/
def blk2982 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3217 .JUMPDEST,
   opAt 3218 (.Dup ⟨0, by decide⟩),
   opAt 3219 (.Dup ⟨2, by decide⟩),
   opAt 3220 .MUL,
   pushAt 3221 1 2,
   opAt 3222 .SUB,
   opAt 3223 .MUL,
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
   pushAt 3242 2 6272,
   opAt 3243 .MSTORE,
   opAt 3244 .POP,
   opAt 3245 .POP,
   opAt 3246 .POP,
   opAt 3247 (.Dup ⟨1, by decide⟩)]

/-- Instructions 2941..2945, pc 4917..4923. -/
def blk3013 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3248 .JUMPDEST,
   opAt 3249 (.Dup ⟨0, by decide⟩),
   opAt 3250 .ISZERO,
   pushAt 3251 2 5419,
   opAt 3252 .JUMPI]

/-- Instructions 2946..2953, pc 4924..4937. -/
def blk3018 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3253 (.Dup ⟨1, by decide⟩),
   pushAt 3254 2 2048,
   pushAt 3255 2 8224,
   opAt 3256 .MCOPY,
   pushAt 3257 0 0,
   pushAt 3258 2 9440,
   opAt 3259 .MLOAD,
   opAt 3260 .MSTORE]

/-- Instructions 2954..2996, pc 4938..5006. -/
def blk3026 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3261 .JUMPDEST,
   pushAt 3262 2 2048,
   opAt 3263 .MLOAD,
   pushAt 3264 2 6144,
   opAt 3265 .MLOAD,
   opAt 3266 (.Dup ⟨1, by decide⟩),
   opAt 3267 (.Dup ⟨1, by decide⟩),
   opAt 3268 (.Swap ⟨0, by decide⟩),
   opAt 3269 .DIV,
   opAt 3270 (.Swap ⟨1, by decide⟩),
   opAt 3271 .MOD,
   pushAt 3272 2 6208,
   opAt 3273 .MLOAD,
   opAt 3274 .MUL,
   pushAt 3275 2 2080,
   opAt 3276 .MLOAD,
   pushAt 3277 2 6144,
   opAt 3278 .MLOAD,
   opAt 3279 (.Swap ⟨0, by decide⟩),
   opAt 3280 .DIV,
   opAt 3281 .ADD,
   pushAt 3282 2 6176,
   opAt 3283 .MLOAD,
   opAt 3284 (.Dup ⟨0, by decide⟩),
   pushAt 3285 2 6240,
   opAt 3286 .MLOAD,
   opAt 3287 (.Dup ⟨4, by decide⟩),
   opAt 3288 .MULMOD,
   opAt 3289 (.Dup ⟨2, by decide⟩),
   opAt 3290 (.Swap ⟨0, by decide⟩),
   opAt 3291 .ADDMOD,
   opAt 3292 (.Swap ⟨0, by decide⟩),
   opAt 3293 .SUB,
   pushAt 3294 2 6272,
   opAt 3295 .MLOAD,
   opAt 3296 .MUL,
   opAt 3297 (.Dup ⟨0, by decide⟩),
   opAt 3298 .ISZERO,
   opAt 3299 .ISZERO,
   opAt 3300 (.Swap ⟨0, by decide⟩),
   opAt 3301 .SUB,
   opAt 3302 (.Dup ⟨1, by decide⟩),
   pushAt 3303 2 6176,
   opAt 3304 .MLOAD,
   opAt 3305 .GT,
   opAt 3306 .ISZERO,
   pushAt 3307 0 0,
   opAt 3308 .SUB,
   opAt 3309 .OR,
   opAt 3310 (.Swap ⟨0, by decide⟩),
   opAt 3311 .POP]

/-- Instructions 2997..3004, pc 5007..5020. -/
def blk3069 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3312 .JUMPDEST,
   pushAt 3313 0 0,
   pushAt 3314 2 9440,
   opAt 3315 .MLOAD,
   pushAt 3316 2 9408,
   opAt 3317 .MLOAD,
   pushAt 3318 2 5120,
   opAt 3319 .ADD]

/-- Instructions 3005..3052, pc 5021..5168. -/
def blk3077 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3320 .JUMPDEST,
   opAt 3321 (.Dup ⟨3, by decide⟩),
   opAt 3322 (.Dup ⟨1, by decide⟩),
   opAt 3323 .MLOAD,
   opAt 3324 (.Dup ⟨1, by decide⟩),
   opAt 3325 (.Dup ⟨1, by decide⟩),
   opAt 3326 .MUL,
   opAt 3327 (.Swap ⟨1, by decide⟩),
   pushAt 3328 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 3329 (.Swap ⟨1, by decide⟩),
   opAt 3330 .MULMOD,
   opAt 3331 (.Dup ⟨1, by decide⟩),
   opAt 3332 (.Dup ⟨1, by decide⟩),
   opAt 3333 .LT,
   opAt 3334 (.Dup ⟨2, by decide⟩),
   opAt 3335 .ADD,
   opAt 3336 (.Swap ⟨0, by decide⟩),
   opAt 3337 .SUB,
   opAt 3338 (.Dup ⟨3, by decide⟩),
   opAt 3339 .MLOAD,
   opAt 3340 (.Swap ⟨1, by decide⟩),
   opAt 3341 (.Dup ⟨2, by decide⟩),
   opAt 3342 .ADD,
   opAt 3343 (.Swap ⟨1, by decide⟩),
   opAt 3344 (.Dup ⟨2, by decide⟩),
   opAt 3345 .LT,
   opAt 3346 .ADD,
   opAt 3347 (.Swap ⟨0, by decide⟩),
   opAt 3348 (.Dup ⟨4, by decide⟩),
   opAt 3349 .ADD,
   opAt 3350 (.Swap ⟨3, by decide⟩),
   opAt 3351 (.Dup ⟨4, by decide⟩),
   opAt 3352 .LT,
   opAt 3353 .ADD,
   opAt 3354 (.Swap ⟨2, by decide⟩),
   opAt 3355 (.Dup ⟨2, by decide⟩),
   opAt 3356 .MSTORE,
   pushAt 3357 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3358 .ADD,
   opAt 3359 (.Swap ⟨0, by decide⟩),
   pushAt 3360 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3361 .ADD,
   opAt 3362 (.Swap ⟨0, by decide⟩),
   pushAt 3363 2 8224,
   opAt 3364 (.Dup ⟨2, by decide⟩),
   opAt 3365 .GT,
   pushAt 3366 2 5021,
   opAt 3367 .JUMPI]

/-- Instructions 3053..3080, pc 5169..5202. -/
def blk3125 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3368 .POP,
   opAt 3369 .POP,
   pushAt 3370 2 8224,
   opAt 3371 .MLOAD,
   opAt 3372 (.Dup ⟨1, by decide⟩),
   opAt 3373 .ADD,
   opAt 3374 (.Dup ⟨1, by decide⟩),
   opAt 3375 (.Dup ⟨1, by decide⟩),
   opAt 3376 .LT,
   opAt 3377 (.Swap ⟨1, by decide⟩),
   opAt 3378 .POP,
   opAt 3379 (.Dup ⟨2, by decide⟩),
   opAt 3380 (.Dup ⟨1, by decide⟩),
   opAt 3381 .LT,
   opAt 3382 (.Swap ⟨0, by decide⟩),
   opAt 3383 (.Dup ⟨3, by decide⟩),
   opAt 3384 (.Swap ⟨0, by decide⟩),
   opAt 3385 .SUB,
   opAt 3386 (.Dup ⟨0, by decide⟩),
   pushAt 3387 2 8224,
   opAt 3388 .MSTORE,
   opAt 3389 .POP,
   opAt 3390 .GT,
   opAt 3391 (.Swap ⟨0, by decide⟩),
   opAt 3392 .POP,
   opAt 3393 .ISZERO,
   pushAt 3394 2 5300,
   opAt 3395 .JUMPI]

/-- Instructions 3081..3084, pc 5203..5208. -/
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3396 .JUMPDEST,
   pushAt 3397 0 0,
   pushAt 3398 2 9440,
   opAt 3399 .MLOAD]

/-- Instructions 3085..3119, pc 5209..5281. -/
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3400 .JUMPDEST,
   opAt 3401 (.Dup ⟨0, by decide⟩),
   opAt 3402 .MLOAD,
   opAt 3403 (.Dup ⟨1, by decide⟩),
   pushAt 3404 2 8256,
   opAt 3405 (.Swap ⟨0, by decide⟩),
   opAt 3406 .SUB,
   opAt 3407 .MLOAD,
   opAt 3408 (.Dup ⟨1, by decide⟩),
   opAt 3409 .ADD,
   opAt 3410 (.Dup ⟨0, by decide⟩),
   opAt 3411 (.Dup ⟨2, by decide⟩),
   opAt 3412 .GT,
   opAt 3413 (.Swap ⟨1, by decide⟩),
   opAt 3414 .POP,
   opAt 3415 (.Dup ⟨3, by decide⟩),
   opAt 3416 .ADD,
   opAt 3417 (.Dup ⟨0, by decide⟩),
   opAt 3418 (.Dup ⟨4, by decide⟩),
   opAt 3419 .GT,
   opAt 3420 (.Swap ⟨3, by decide⟩),
   opAt 3421 .POP,
   opAt 3422 (.Dup ⟨2, by decide⟩),
   opAt 3423 .MSTORE,
   opAt 3424 (.Swap ⟨0, by decide⟩),
   opAt 3425 (.Swap ⟨1, by decide⟩),
   opAt 3426 .OR,
   opAt 3427 (.Swap ⟨0, by decide⟩),
   pushAt 3428 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3429 .ADD,
   pushAt 3430 2 8255,
   opAt 3431 (.Dup ⟨1, by decide⟩),
   opAt 3432 .GT,
   pushAt 3433 2 5209,
   opAt 3434 .JUMPI]

/-- Instructions 3120..3131, pc 5282..5299. -/
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3435 .POP,
   pushAt 3436 2 8224,
   opAt 3437 .MLOAD,
   opAt 3438 (.Dup ⟨1, by decide⟩),
   opAt 3439 .ADD,
   opAt 3440 (.Dup ⟨0, by decide⟩),
   pushAt 3441 2 8224,
   opAt 3442 .MSTORE,
   opAt 3443 .LT,
   opAt 3444 .ISZERO,
   pushAt 3445 2 5203,
   opAt 3446 .JUMPI]

/-- Instructions 3132..3137, pc 5300..5309. -/
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3447 .JUMPDEST,
   pushAt 3448 2 8224,
   opAt 3449 .MLOAD,
   opAt 3450 .ISZERO,
   pushAt 3451 2 5399,
   opAt 3452 .JUMPI]

/-- Instructions 3138..3140, pc 5310..5314. -/
def blk3210 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3453 0 0,
   pushAt 3454 2 9440,
   opAt 3455 .MLOAD]

/-- Instructions 3141..3172, pc 5315..5384. -/
def blk3213 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3456 .JUMPDEST,
   opAt 3457 (.Dup ⟨0, by decide⟩),
   opAt 3458 .MLOAD,
   opAt 3459 (.Dup ⟨1, by decide⟩),
   pushAt 3460 2 8256,
   opAt 3461 (.Swap ⟨0, by decide⟩),
   opAt 3462 .SUB,
   opAt 3463 .MLOAD,
   opAt 3464 (.Dup ⟨1, by decide⟩),
   opAt 3465 (.Dup ⟨1, by decide⟩),
   opAt 3466 .GT,
   opAt 3467 (.Swap ⟨1, by decide⟩),
   opAt 3468 .SUB,
   opAt 3469 (.Dup ⟨3, by decide⟩),
   opAt 3470 (.Dup ⟨1, by decide⟩),
   opAt 3471 .LT,
   opAt 3472 (.Swap ⟨0, by decide⟩),
   opAt 3473 (.Dup ⟨4, by decide⟩),
   opAt 3474 (.Swap ⟨0, by decide⟩),
   opAt 3475 .SUB,
   opAt 3476 (.Dup ⟨3, by decide⟩),
   opAt 3477 .MSTORE,
   opAt 3478 .OR,
   opAt 3479 (.Swap ⟨1, by decide⟩),
   opAt 3480 .POP,
   pushAt 3481 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3482 .ADD,
   pushAt 3483 2 8255,
   opAt 3484 (.Dup ⟨1, by decide⟩),
   opAt 3485 .GT,
   pushAt 3486 2 5315,
   opAt 3487 .JUMPI]

/-- Instructions 3173..3180, pc 5385..5398. -/
def blk3245 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3488 .POP,
   pushAt 3489 2 8224,
   opAt 3490 .MLOAD,
   opAt 3491 .SUB,
   pushAt 3492 2 8224,
   opAt 3493 .MSTORE,
   pushAt 3494 2 5300,
   opAt 3495 .JUMP]

/-- Instructions 3181..3185, pc 5399..5409. -/
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3496 .JUMPDEST,
   pushAt 3497 2 5410,
   pushAt 3498 2 2048,
   pushAt 3499 2 2642,
   opAt 3500 .JUMP]

/-- Instructions 3186..3191, pc 5410..5418. -/
def blk3258 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3501 .JUMPDEST,
   pushAt 3502 1 1,
   opAt 3503 (.Swap ⟨0, by decide⟩),
   opAt 3504 .SUB,
   pushAt 3505 2 4917,
   opAt 3506 .JUMP]

/-- Instructions 3192..3195, pc 5419..5424. -/
def blk3264 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3507 .JUMPDEST,
   opAt 3508 .POP,
   pushAt 3509 2 1756,
   opAt 3510 .JUMP]

theorem jumpDest4643 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4686 = true :=
  Artifact.isValidJumpDest_index 3097 (by rfl)

theorem jumpDest4687 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4730 = true :=
  Artifact.isValidJumpDest_index 3124 (by rfl)

theorem jumpDest4692 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4735 = true :=
  Artifact.isValidJumpDest_index 3127 (by rfl)

theorem jumpDest4699 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4742 = true :=
  Artifact.isValidJumpDest_index 3131 (by rfl)

theorem jumpDest4760 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4803 = true :=
  Artifact.isValidJumpDest_index 3154 (by rfl)

theorem jumpDest4806 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4849 = true :=
  Artifact.isValidJumpDest_index 3191 (by rfl)

theorem jumpDest4837 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4880 = true :=
  Artifact.isValidJumpDest_index 3217 (by rfl)

theorem jumpDest4874 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4917 = true :=
  Artifact.isValidJumpDest_index 3248 (by rfl)

theorem jumpDest4895 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4938 = true :=
  Artifact.isValidJumpDest_index 3261 (by rfl)

theorem jumpDest4954 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5007 = true :=
  Artifact.isValidJumpDest_index 3312 (by rfl)

theorem jumpDest4968 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5021 = true :=
  Artifact.isValidJumpDest_index 3320 (by rfl)

theorem jumpDest5150 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5203 = true :=
  Artifact.isValidJumpDest_index 3396 (by rfl)

theorem jumpDest5156 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5209 = true :=
  Artifact.isValidJumpDest_index 3400 (by rfl)

theorem jumpDest5247 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5300 = true :=
  Artifact.isValidJumpDest_index 3447 (by rfl)

theorem jumpDest5262 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5315 = true :=
  Artifact.isValidJumpDest_index 3456 (by rfl)

theorem jumpDest5346 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5399 = true :=
  Artifact.isValidJumpDest_index 3496 (by rfl)

theorem jumpDest5357 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5410 = true :=
  Artifact.isValidJumpDest_index 3501 (by rfl)

theorem jumpDest5366 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5419 = true :=
  Artifact.isValidJumpDest_index 3507 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
