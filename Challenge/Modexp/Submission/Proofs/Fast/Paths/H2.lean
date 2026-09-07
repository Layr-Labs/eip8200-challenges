import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

abbrev H2Path :=
  List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka)

/-! Exact cloned H2 paths in the combined artifact.  The middle and tail
paths intentionally start with POP, and the L1/L2 cores intentionally start
with DUP4; these are not generic block copies. -/

def h2Entry4 : H2Path :=
  [
   opAt 3103 .JUMPDEST,
   opAt 3104 .POP
  ]

def h2Out4 : H2Path :=
  [
   opAt 3105 .JUMPDEST,
   opAt 3106 (.Dup ⟨0, by decide⟩),
   opAt 3107 .MLOAD,
   pushAt 3108 0 0,
   opAt 3109 (.Dup ⟨7, by decide⟩),
   opAt 3110 (.Dup ⟨4, by decide⟩),
   pushAt 3111 2 9344,
   opAt 3112 .MLOAD,
   opAt 3113 .ADD
  ]

def h2L1Core4_0 : H2Path :=
  [
   opAt 3114 (.Dup ⟨3, by decide⟩),
   opAt 3115 (.Dup ⟨1, by decide⟩),
   opAt 3116 .MLOAD,
   opAt 3117 (.Dup ⟨1, by decide⟩),
   opAt 3118 (.Dup ⟨1, by decide⟩),
   opAt 3119 .MUL,
   opAt 3120 (.Swap ⟨1, by decide⟩),
   pushAt 3121 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 3122 (.Swap ⟨1, by decide⟩),
   opAt 3123 .MULMOD,
   opAt 3124 (.Dup ⟨1, by decide⟩),
   opAt 3125 (.Dup ⟨1, by decide⟩),
   opAt 3126 .LT,
   opAt 3127 (.Dup ⟨2, by decide⟩),
   opAt 3128 .ADD,
   opAt 3129 (.Swap ⟨0, by decide⟩),
   opAt 3130 .SUB,
   opAt 3131 (.Dup ⟨3, by decide⟩),
   opAt 3132 .MLOAD,
   opAt 3133 (.Swap ⟨1, by decide⟩),
   opAt 3134 (.Dup ⟨2, by decide⟩),
   opAt 3135 .ADD,
   opAt 3136 (.Swap ⟨1, by decide⟩),
   opAt 3137 (.Dup ⟨2, by decide⟩),
   opAt 3138 .LT,
   opAt 3139 .ADD,
   opAt 3140 (.Swap ⟨0, by decide⟩),
   opAt 3141 (.Dup ⟨4, by decide⟩),
   opAt 3142 .ADD,
   opAt 3143 (.Swap ⟨3, by decide⟩),
   opAt 3144 (.Dup ⟨4, by decide⟩),
   opAt 3145 .LT,
   opAt 3146 .ADD,
   opAt 3147 (.Swap ⟨2, by decide⟩),
   opAt 3148 (.Dup ⟨2, by decide⟩),
   opAt 3149 .MSTORE,
   pushAt 3150 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3151 .ADD,
   opAt 3152 (.Swap ⟨0, by decide⟩),
   pushAt 3153 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3154 .ADD,
   opAt 3155 (.Swap ⟨0, by decide⟩)
  ]

def h2L1Core4_1 : H2Path :=
  [
   opAt 3156 (.Dup ⟨3, by decide⟩),
   opAt 3157 (.Dup ⟨1, by decide⟩),
   opAt 3158 .MLOAD,
   opAt 3159 (.Dup ⟨1, by decide⟩),
   opAt 3160 (.Dup ⟨1, by decide⟩),
   opAt 3161 .MUL,
   opAt 3162 (.Swap ⟨1, by decide⟩),
   pushAt 3163 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 3164 (.Swap ⟨1, by decide⟩),
   opAt 3165 .MULMOD,
   opAt 3166 (.Dup ⟨1, by decide⟩),
   opAt 3167 (.Dup ⟨1, by decide⟩),
   opAt 3168 .LT,
   opAt 3169 (.Dup ⟨2, by decide⟩),
   opAt 3170 .ADD,
   opAt 3171 (.Swap ⟨0, by decide⟩),
   opAt 3172 .SUB,
   opAt 3173 (.Dup ⟨3, by decide⟩),
   opAt 3174 .MLOAD,
   opAt 3175 (.Swap ⟨1, by decide⟩),
   opAt 3176 (.Dup ⟨2, by decide⟩),
   opAt 3177 .ADD,
   opAt 3178 (.Swap ⟨1, by decide⟩),
   opAt 3179 (.Dup ⟨2, by decide⟩),
   opAt 3180 .LT,
   opAt 3181 .ADD,
   opAt 3182 (.Swap ⟨0, by decide⟩),
   opAt 3183 (.Dup ⟨4, by decide⟩),
   opAt 3184 .ADD,
   opAt 3185 (.Swap ⟨3, by decide⟩),
   opAt 3186 (.Dup ⟨4, by decide⟩),
   opAt 3187 .LT,
   opAt 3188 .ADD,
   opAt 3189 (.Swap ⟨2, by decide⟩),
   opAt 3190 (.Dup ⟨2, by decide⟩),
   opAt 3191 .MSTORE,
   pushAt 3192 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3193 .ADD,
   opAt 3194 (.Swap ⟨0, by decide⟩),
   pushAt 3195 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3196 .ADD,
   opAt 3197 (.Swap ⟨0, by decide⟩)
  ]

def h2L1Core4_2 : H2Path :=
  [
   opAt 3198 (.Dup ⟨3, by decide⟩),
   opAt 3199 (.Dup ⟨1, by decide⟩),
   opAt 3200 .MLOAD,
   opAt 3201 (.Dup ⟨1, by decide⟩),
   opAt 3202 (.Dup ⟨1, by decide⟩),
   opAt 3203 .MUL,
   opAt 3204 (.Swap ⟨1, by decide⟩),
   pushAt 3205 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 3206 (.Swap ⟨1, by decide⟩),
   opAt 3207 .MULMOD,
   opAt 3208 (.Dup ⟨1, by decide⟩),
   opAt 3209 (.Dup ⟨1, by decide⟩),
   opAt 3210 .LT,
   opAt 3211 (.Dup ⟨2, by decide⟩),
   opAt 3212 .ADD,
   opAt 3213 (.Swap ⟨0, by decide⟩),
   opAt 3214 .SUB,
   opAt 3215 (.Dup ⟨3, by decide⟩),
   opAt 3216 .MLOAD,
   opAt 3217 (.Swap ⟨1, by decide⟩),
   opAt 3218 (.Dup ⟨2, by decide⟩),
   opAt 3219 .ADD,
   opAt 3220 (.Swap ⟨1, by decide⟩),
   opAt 3221 (.Dup ⟨2, by decide⟩),
   opAt 3222 .LT,
   opAt 3223 .ADD,
   opAt 3224 (.Swap ⟨0, by decide⟩),
   opAt 3225 (.Dup ⟨4, by decide⟩),
   opAt 3226 .ADD,
   opAt 3227 (.Swap ⟨3, by decide⟩),
   opAt 3228 (.Dup ⟨4, by decide⟩),
   opAt 3229 .LT,
   opAt 3230 .ADD,
   opAt 3231 (.Swap ⟨2, by decide⟩),
   opAt 3232 (.Dup ⟨2, by decide⟩),
   opAt 3233 .MSTORE,
   pushAt 3234 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3235 .ADD,
   opAt 3236 (.Swap ⟨0, by decide⟩),
   pushAt 3237 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3238 .ADD,
   opAt 3239 (.Swap ⟨0, by decide⟩)
  ]

def h2L1Core4_3 : H2Path :=
  [
   opAt 3240 (.Dup ⟨3, by decide⟩),
   opAt 3241 (.Dup ⟨1, by decide⟩),
   opAt 3242 .MLOAD,
   opAt 3243 (.Dup ⟨1, by decide⟩),
   opAt 3244 (.Dup ⟨1, by decide⟩),
   opAt 3245 .MUL,
   opAt 3246 (.Swap ⟨1, by decide⟩),
   pushAt 3247 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 3248 (.Swap ⟨1, by decide⟩),
   opAt 3249 .MULMOD,
   opAt 3250 (.Dup ⟨1, by decide⟩),
   opAt 3251 (.Dup ⟨1, by decide⟩),
   opAt 3252 .LT,
   opAt 3253 (.Dup ⟨2, by decide⟩),
   opAt 3254 .ADD,
   opAt 3255 (.Swap ⟨0, by decide⟩),
   opAt 3256 .SUB,
   opAt 3257 (.Dup ⟨3, by decide⟩),
   opAt 3258 .MLOAD,
   opAt 3259 (.Swap ⟨1, by decide⟩),
   opAt 3260 (.Dup ⟨2, by decide⟩),
   opAt 3261 .ADD,
   opAt 3262 (.Swap ⟨1, by decide⟩),
   opAt 3263 (.Dup ⟨2, by decide⟩),
   opAt 3264 .LT,
   opAt 3265 .ADD,
   opAt 3266 (.Swap ⟨0, by decide⟩),
   opAt 3267 (.Dup ⟨4, by decide⟩),
   opAt 3268 .ADD,
   opAt 3269 (.Swap ⟨3, by decide⟩),
   opAt 3270 (.Dup ⟨4, by decide⟩),
   opAt 3271 .LT,
   opAt 3272 .ADD,
   opAt 3273 (.Swap ⟨2, by decide⟩),
   opAt 3274 (.Dup ⟨2, by decide⟩),
   opAt 3275 .MSTORE,
   pushAt 3276 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3277 .ADD,
   opAt 3278 (.Swap ⟨0, by decide⟩),
   pushAt 3279 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3280 .ADD,
   opAt 3281 (.Swap ⟨0, by decide⟩)
  ]

def h2Mid4 : H2Path :=
  [
   opAt 3282 .POP,
   opAt 3283 .POP,
   opAt 3284 (.Dup ⟨0, by decide⟩),
   pushAt 3285 2 8224,
   opAt 3286 .MLOAD,
   opAt 3287 .ADD,
   opAt 3288 (.Dup ⟨0, by decide⟩),
   pushAt 3289 2 8224,
   opAt 3290 .MSTORE,
   opAt 3291 .LT,
   pushAt 3292 2 8192,
   opAt 3293 .MSTORE,
   opAt 3294 (.Dup ⟨6, by decide⟩),
   opAt 3295 .MLOAD,
   opAt 3296 (.Dup ⟨0, by decide⟩),
   pushAt 3297 2 9376,
   opAt 3298 .MLOAD,
   opAt 3299 .MUL,
   opAt 3300 (.Swap ⟨0, by decide⟩),
   opAt 3301 (.Dup ⟨1, by decide⟩),
   pushAt 3302 2 9408,
   opAt 3303 .MLOAD,
   opAt 3304 .MLOAD,
   pushAt 3305 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 3306 (.Swap ⟨1, by decide⟩),
   opAt 3307 .MULMOD,
   opAt 3308 (.Dup ⟨1, by decide⟩),
   opAt 3309 .ADD,
   opAt 3310 (.Dup ⟨0, by decide⟩),
   opAt 3311 (.Swap ⟨1, by decide⟩),
   opAt 3312 .GT,
   opAt 3313 .ADD,
   opAt 3314 (.Dup ⟨8, by decide⟩),
   pushAt 3315 1 32,
   opAt 3316 (.Swap ⟨0, by decide⟩),
   opAt 3317 .SUB,
   pushAt 3318 2 9408,
   opAt 3319 .MLOAD,
   pushAt 3320 1 32,
   opAt 3321 (.Swap ⟨0, by decide⟩),
   opAt 3322 .SUB
  ]

def h2L2Core4_0 : H2Path :=
  [
   opAt 3323 (.Dup ⟨3, by decide⟩),
   opAt 3324 (.Dup ⟨1, by decide⟩),
   opAt 3325 .MLOAD,
   opAt 3326 (.Dup ⟨1, by decide⟩),
   opAt 3327 (.Dup ⟨1, by decide⟩),
   opAt 3328 .MUL,
   opAt 3329 (.Swap ⟨1, by decide⟩),
   pushAt 3330 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 3331 (.Swap ⟨1, by decide⟩),
   opAt 3332 .MULMOD,
   opAt 3333 (.Dup ⟨1, by decide⟩),
   opAt 3334 (.Dup ⟨1, by decide⟩),
   opAt 3335 .LT,
   opAt 3336 (.Dup ⟨2, by decide⟩),
   opAt 3337 .ADD,
   opAt 3338 (.Swap ⟨0, by decide⟩),
   opAt 3339 .SUB,
   opAt 3340 (.Dup ⟨3, by decide⟩),
   opAt 3341 .MLOAD,
   opAt 3342 (.Swap ⟨1, by decide⟩),
   opAt 3343 (.Dup ⟨2, by decide⟩),
   opAt 3344 .ADD,
   opAt 3345 (.Swap ⟨1, by decide⟩),
   opAt 3346 (.Dup ⟨2, by decide⟩),
   opAt 3347 .LT,
   opAt 3348 .ADD,
   opAt 3349 (.Swap ⟨0, by decide⟩),
   opAt 3350 (.Dup ⟨4, by decide⟩),
   opAt 3351 .ADD,
   opAt 3352 (.Swap ⟨3, by decide⟩),
   opAt 3353 (.Dup ⟨4, by decide⟩),
   opAt 3354 .LT,
   opAt 3355 .ADD,
   opAt 3356 (.Swap ⟨2, by decide⟩),
   opAt 3357 (.Dup ⟨2, by decide⟩),
   pushAt 3358 1 32,
   opAt 3359 .ADD,
   opAt 3360 .MSTORE,
   pushAt 3361 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3362 .ADD,
   opAt 3363 (.Swap ⟨0, by decide⟩),
   pushAt 3364 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3365 .ADD,
   opAt 3366 (.Swap ⟨0, by decide⟩)
  ]

def h2L2Core4_1 : H2Path :=
  [
   opAt 3367 (.Dup ⟨3, by decide⟩),
   opAt 3368 (.Dup ⟨1, by decide⟩),
   opAt 3369 .MLOAD,
   opAt 3370 (.Dup ⟨1, by decide⟩),
   opAt 3371 (.Dup ⟨1, by decide⟩),
   opAt 3372 .MUL,
   opAt 3373 (.Swap ⟨1, by decide⟩),
   pushAt 3374 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 3375 (.Swap ⟨1, by decide⟩),
   opAt 3376 .MULMOD,
   opAt 3377 (.Dup ⟨1, by decide⟩),
   opAt 3378 (.Dup ⟨1, by decide⟩),
   opAt 3379 .LT,
   opAt 3380 (.Dup ⟨2, by decide⟩),
   opAt 3381 .ADD,
   opAt 3382 (.Swap ⟨0, by decide⟩),
   opAt 3383 .SUB,
   opAt 3384 (.Dup ⟨3, by decide⟩),
   opAt 3385 .MLOAD,
   opAt 3386 (.Swap ⟨1, by decide⟩),
   opAt 3387 (.Dup ⟨2, by decide⟩),
   opAt 3388 .ADD,
   opAt 3389 (.Swap ⟨1, by decide⟩),
   opAt 3390 (.Dup ⟨2, by decide⟩),
   opAt 3391 .LT,
   opAt 3392 .ADD,
   opAt 3393 (.Swap ⟨0, by decide⟩),
   opAt 3394 (.Dup ⟨4, by decide⟩),
   opAt 3395 .ADD,
   opAt 3396 (.Swap ⟨3, by decide⟩),
   opAt 3397 (.Dup ⟨4, by decide⟩),
   opAt 3398 .LT,
   opAt 3399 .ADD,
   opAt 3400 (.Swap ⟨2, by decide⟩),
   opAt 3401 (.Dup ⟨2, by decide⟩),
   pushAt 3402 1 32,
   opAt 3403 .ADD,
   opAt 3404 .MSTORE,
   pushAt 3405 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3406 .ADD,
   opAt 3407 (.Swap ⟨0, by decide⟩),
   pushAt 3408 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3409 .ADD,
   opAt 3410 (.Swap ⟨0, by decide⟩)
  ]

def h2L2Core4_2 : H2Path :=
  [
   opAt 3411 (.Dup ⟨3, by decide⟩),
   opAt 3412 (.Dup ⟨1, by decide⟩),
   opAt 3413 .MLOAD,
   opAt 3414 (.Dup ⟨1, by decide⟩),
   opAt 3415 (.Dup ⟨1, by decide⟩),
   opAt 3416 .MUL,
   opAt 3417 (.Swap ⟨1, by decide⟩),
   pushAt 3418 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 3419 (.Swap ⟨1, by decide⟩),
   opAt 3420 .MULMOD,
   opAt 3421 (.Dup ⟨1, by decide⟩),
   opAt 3422 (.Dup ⟨1, by decide⟩),
   opAt 3423 .LT,
   opAt 3424 (.Dup ⟨2, by decide⟩),
   opAt 3425 .ADD,
   opAt 3426 (.Swap ⟨0, by decide⟩),
   opAt 3427 .SUB,
   opAt 3428 (.Dup ⟨3, by decide⟩),
   opAt 3429 .MLOAD,
   opAt 3430 (.Swap ⟨1, by decide⟩),
   opAt 3431 (.Dup ⟨2, by decide⟩),
   opAt 3432 .ADD,
   opAt 3433 (.Swap ⟨1, by decide⟩),
   opAt 3434 (.Dup ⟨2, by decide⟩),
   opAt 3435 .LT,
   opAt 3436 .ADD,
   opAt 3437 (.Swap ⟨0, by decide⟩),
   opAt 3438 (.Dup ⟨4, by decide⟩),
   opAt 3439 .ADD,
   opAt 3440 (.Swap ⟨3, by decide⟩),
   opAt 3441 (.Dup ⟨4, by decide⟩),
   opAt 3442 .LT,
   opAt 3443 .ADD,
   opAt 3444 (.Swap ⟨2, by decide⟩),
   opAt 3445 (.Dup ⟨2, by decide⟩),
   pushAt 3446 1 32,
   opAt 3447 .ADD,
   opAt 3448 .MSTORE,
   pushAt 3449 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3450 .ADD,
   opAt 3451 (.Swap ⟨0, by decide⟩),
   pushAt 3452 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3453 .ADD,
   opAt 3454 (.Swap ⟨0, by decide⟩)
  ]

def h2Tail4 : H2Path :=
  [
   opAt 3455 .POP,
   opAt 3456 .POP,
   opAt 3457 (.Swap ⟨0, by decide⟩),
   opAt 3458 .POP,
   opAt 3459 (.Swap ⟨0, by decide⟩),
   opAt 3460 .POP,
   opAt 3461 (.Dup ⟨0, by decide⟩),
   pushAt 3462 2 8224,
   opAt 3463 .MLOAD,
   opAt 3464 .ADD,
   opAt 3465 (.Dup ⟨0, by decide⟩),
   pushAt 3466 2 8256,
   opAt 3467 .MSTORE,
   opAt 3468 .LT,
   pushAt 3469 2 8192,
   opAt 3470 .MLOAD,
   opAt 3471 .ADD,
   pushAt 3472 2 8224,
   opAt 3473 .MSTORE,
   pushAt 3474 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3475 .ADD,
   opAt 3476 (.Dup ⟨2, by decide⟩),
   opAt 3477 (.Dup ⟨1, by decide⟩),
   opAt 3478 .GT,
   pushAt 3479 2 5517,
   opAt 3480 .JUMPI
  ]

def h2Exit4 : H2Path :=
  [
   opAt 3481 .POP,
   opAt 3482 .POP,
   opAt 3483 .POP,
   opAt 3484 (.Swap ⟨1, by decide⟩),
   opAt 3485 .POP,
   opAt 3486 (.Swap ⟨0, by decide⟩),
   pushAt 3487 2 2686,
   opAt 3488 .JUMP
  ]

def h2Entry8 : H2Path :=
  [
   opAt 3489 .JUMPDEST,
   opAt 3490 .POP
  ]

def h2Out8 : H2Path :=
  [
   opAt 3491 .JUMPDEST,
   opAt 3492 (.Dup ⟨0, by decide⟩),
   opAt 3493 .MLOAD,
   pushAt 3494 0 0,
   opAt 3495 (.Dup ⟨7, by decide⟩),
   opAt 3496 (.Dup ⟨4, by decide⟩),
   pushAt 3497 2 9344,
   opAt 3498 .MLOAD,
   opAt 3499 .ADD
  ]

def h2L1Core8_0 : H2Path :=
  [
   opAt 3500 (.Dup ⟨3, by decide⟩),
   opAt 3501 (.Dup ⟨1, by decide⟩),
   opAt 3502 .MLOAD,
   opAt 3503 (.Dup ⟨1, by decide⟩),
   opAt 3504 (.Dup ⟨1, by decide⟩),
   opAt 3505 .MUL,
   opAt 3506 (.Swap ⟨1, by decide⟩),
   pushAt 3507 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 3508 (.Swap ⟨1, by decide⟩),
   opAt 3509 .MULMOD,
   opAt 3510 (.Dup ⟨1, by decide⟩),
   opAt 3511 (.Dup ⟨1, by decide⟩),
   opAt 3512 .LT,
   opAt 3513 (.Dup ⟨2, by decide⟩),
   opAt 3514 .ADD,
   opAt 3515 (.Swap ⟨0, by decide⟩),
   opAt 3516 .SUB,
   opAt 3517 (.Dup ⟨3, by decide⟩),
   opAt 3518 .MLOAD,
   opAt 3519 (.Swap ⟨1, by decide⟩),
   opAt 3520 (.Dup ⟨2, by decide⟩),
   opAt 3521 .ADD,
   opAt 3522 (.Swap ⟨1, by decide⟩),
   opAt 3523 (.Dup ⟨2, by decide⟩),
   opAt 3524 .LT,
   opAt 3525 .ADD,
   opAt 3526 (.Swap ⟨0, by decide⟩),
   opAt 3527 (.Dup ⟨4, by decide⟩),
   opAt 3528 .ADD,
   opAt 3529 (.Swap ⟨3, by decide⟩),
   opAt 3530 (.Dup ⟨4, by decide⟩),
   opAt 3531 .LT,
   opAt 3532 .ADD,
   opAt 3533 (.Swap ⟨2, by decide⟩),
   opAt 3534 (.Dup ⟨2, by decide⟩),
   opAt 3535 .MSTORE,
   pushAt 3536 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3537 .ADD,
   opAt 3538 (.Swap ⟨0, by decide⟩),
   pushAt 3539 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3540 .ADD,
   opAt 3541 (.Swap ⟨0, by decide⟩)
  ]

def h2L1Core8_1 : H2Path :=
  [
   opAt 3542 (.Dup ⟨3, by decide⟩),
   opAt 3543 (.Dup ⟨1, by decide⟩),
   opAt 3544 .MLOAD,
   opAt 3545 (.Dup ⟨1, by decide⟩),
   opAt 3546 (.Dup ⟨1, by decide⟩),
   opAt 3547 .MUL,
   opAt 3548 (.Swap ⟨1, by decide⟩),
   pushAt 3549 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 3550 (.Swap ⟨1, by decide⟩),
   opAt 3551 .MULMOD,
   opAt 3552 (.Dup ⟨1, by decide⟩),
   opAt 3553 (.Dup ⟨1, by decide⟩),
   opAt 3554 .LT,
   opAt 3555 (.Dup ⟨2, by decide⟩),
   opAt 3556 .ADD,
   opAt 3557 (.Swap ⟨0, by decide⟩),
   opAt 3558 .SUB,
   opAt 3559 (.Dup ⟨3, by decide⟩),
   opAt 3560 .MLOAD,
   opAt 3561 (.Swap ⟨1, by decide⟩),
   opAt 3562 (.Dup ⟨2, by decide⟩),
   opAt 3563 .ADD,
   opAt 3564 (.Swap ⟨1, by decide⟩),
   opAt 3565 (.Dup ⟨2, by decide⟩),
   opAt 3566 .LT,
   opAt 3567 .ADD,
   opAt 3568 (.Swap ⟨0, by decide⟩),
   opAt 3569 (.Dup ⟨4, by decide⟩),
   opAt 3570 .ADD,
   opAt 3571 (.Swap ⟨3, by decide⟩),
   opAt 3572 (.Dup ⟨4, by decide⟩),
   opAt 3573 .LT,
   opAt 3574 .ADD,
   opAt 3575 (.Swap ⟨2, by decide⟩),
   opAt 3576 (.Dup ⟨2, by decide⟩),
   opAt 3577 .MSTORE,
   pushAt 3578 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3579 .ADD,
   opAt 3580 (.Swap ⟨0, by decide⟩),
   pushAt 3581 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3582 .ADD,
   opAt 3583 (.Swap ⟨0, by decide⟩)
  ]

def h2L1Core8_2 : H2Path :=
  [
   opAt 3584 (.Dup ⟨3, by decide⟩),
   opAt 3585 (.Dup ⟨1, by decide⟩),
   opAt 3586 .MLOAD,
   opAt 3587 (.Dup ⟨1, by decide⟩),
   opAt 3588 (.Dup ⟨1, by decide⟩),
   opAt 3589 .MUL,
   opAt 3590 (.Swap ⟨1, by decide⟩),
   pushAt 3591 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 3592 (.Swap ⟨1, by decide⟩),
   opAt 3593 .MULMOD,
   opAt 3594 (.Dup ⟨1, by decide⟩),
   opAt 3595 (.Dup ⟨1, by decide⟩),
   opAt 3596 .LT,
   opAt 3597 (.Dup ⟨2, by decide⟩),
   opAt 3598 .ADD,
   opAt 3599 (.Swap ⟨0, by decide⟩),
   opAt 3600 .SUB,
   opAt 3601 (.Dup ⟨3, by decide⟩),
   opAt 3602 .MLOAD,
   opAt 3603 (.Swap ⟨1, by decide⟩),
   opAt 3604 (.Dup ⟨2, by decide⟩),
   opAt 3605 .ADD,
   opAt 3606 (.Swap ⟨1, by decide⟩),
   opAt 3607 (.Dup ⟨2, by decide⟩),
   opAt 3608 .LT,
   opAt 3609 .ADD,
   opAt 3610 (.Swap ⟨0, by decide⟩),
   opAt 3611 (.Dup ⟨4, by decide⟩),
   opAt 3612 .ADD,
   opAt 3613 (.Swap ⟨3, by decide⟩),
   opAt 3614 (.Dup ⟨4, by decide⟩),
   opAt 3615 .LT,
   opAt 3616 .ADD,
   opAt 3617 (.Swap ⟨2, by decide⟩),
   opAt 3618 (.Dup ⟨2, by decide⟩),
   opAt 3619 .MSTORE,
   pushAt 3620 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3621 .ADD,
   opAt 3622 (.Swap ⟨0, by decide⟩),
   pushAt 3623 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3624 .ADD,
   opAt 3625 (.Swap ⟨0, by decide⟩)
  ]

def h2L1Core8_3 : H2Path :=
  [
   opAt 3626 (.Dup ⟨3, by decide⟩),
   opAt 3627 (.Dup ⟨1, by decide⟩),
   opAt 3628 .MLOAD,
   opAt 3629 (.Dup ⟨1, by decide⟩),
   opAt 3630 (.Dup ⟨1, by decide⟩),
   opAt 3631 .MUL,
   opAt 3632 (.Swap ⟨1, by decide⟩),
   pushAt 3633 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 3634 (.Swap ⟨1, by decide⟩),
   opAt 3635 .MULMOD,
   opAt 3636 (.Dup ⟨1, by decide⟩),
   opAt 3637 (.Dup ⟨1, by decide⟩),
   opAt 3638 .LT,
   opAt 3639 (.Dup ⟨2, by decide⟩),
   opAt 3640 .ADD,
   opAt 3641 (.Swap ⟨0, by decide⟩),
   opAt 3642 .SUB,
   opAt 3643 (.Dup ⟨3, by decide⟩),
   opAt 3644 .MLOAD,
   opAt 3645 (.Swap ⟨1, by decide⟩),
   opAt 3646 (.Dup ⟨2, by decide⟩),
   opAt 3647 .ADD,
   opAt 3648 (.Swap ⟨1, by decide⟩),
   opAt 3649 (.Dup ⟨2, by decide⟩),
   opAt 3650 .LT,
   opAt 3651 .ADD,
   opAt 3652 (.Swap ⟨0, by decide⟩),
   opAt 3653 (.Dup ⟨4, by decide⟩),
   opAt 3654 .ADD,
   opAt 3655 (.Swap ⟨3, by decide⟩),
   opAt 3656 (.Dup ⟨4, by decide⟩),
   opAt 3657 .LT,
   opAt 3658 .ADD,
   opAt 3659 (.Swap ⟨2, by decide⟩),
   opAt 3660 (.Dup ⟨2, by decide⟩),
   opAt 3661 .MSTORE,
   pushAt 3662 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3663 .ADD,
   opAt 3664 (.Swap ⟨0, by decide⟩),
   pushAt 3665 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3666 .ADD,
   opAt 3667 (.Swap ⟨0, by decide⟩)
  ]

def h2L1Core8_4 : H2Path :=
  [
   opAt 3668 (.Dup ⟨3, by decide⟩),
   opAt 3669 (.Dup ⟨1, by decide⟩),
   opAt 3670 .MLOAD,
   opAt 3671 (.Dup ⟨1, by decide⟩),
   opAt 3672 (.Dup ⟨1, by decide⟩),
   opAt 3673 .MUL,
   opAt 3674 (.Swap ⟨1, by decide⟩),
   pushAt 3675 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 3676 (.Swap ⟨1, by decide⟩),
   opAt 3677 .MULMOD,
   opAt 3678 (.Dup ⟨1, by decide⟩),
   opAt 3679 (.Dup ⟨1, by decide⟩),
   opAt 3680 .LT,
   opAt 3681 (.Dup ⟨2, by decide⟩),
   opAt 3682 .ADD,
   opAt 3683 (.Swap ⟨0, by decide⟩),
   opAt 3684 .SUB,
   opAt 3685 (.Dup ⟨3, by decide⟩),
   opAt 3686 .MLOAD,
   opAt 3687 (.Swap ⟨1, by decide⟩),
   opAt 3688 (.Dup ⟨2, by decide⟩),
   opAt 3689 .ADD,
   opAt 3690 (.Swap ⟨1, by decide⟩),
   opAt 3691 (.Dup ⟨2, by decide⟩),
   opAt 3692 .LT,
   opAt 3693 .ADD,
   opAt 3694 (.Swap ⟨0, by decide⟩),
   opAt 3695 (.Dup ⟨4, by decide⟩),
   opAt 3696 .ADD,
   opAt 3697 (.Swap ⟨3, by decide⟩),
   opAt 3698 (.Dup ⟨4, by decide⟩),
   opAt 3699 .LT,
   opAt 3700 .ADD,
   opAt 3701 (.Swap ⟨2, by decide⟩),
   opAt 3702 (.Dup ⟨2, by decide⟩),
   opAt 3703 .MSTORE,
   pushAt 3704 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3705 .ADD,
   opAt 3706 (.Swap ⟨0, by decide⟩),
   pushAt 3707 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3708 .ADD,
   opAt 3709 (.Swap ⟨0, by decide⟩)
  ]

def h2L1Core8_5 : H2Path :=
  [
   opAt 3710 (.Dup ⟨3, by decide⟩),
   opAt 3711 (.Dup ⟨1, by decide⟩),
   opAt 3712 .MLOAD,
   opAt 3713 (.Dup ⟨1, by decide⟩),
   opAt 3714 (.Dup ⟨1, by decide⟩),
   opAt 3715 .MUL,
   opAt 3716 (.Swap ⟨1, by decide⟩),
   pushAt 3717 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 3718 (.Swap ⟨1, by decide⟩),
   opAt 3719 .MULMOD,
   opAt 3720 (.Dup ⟨1, by decide⟩),
   opAt 3721 (.Dup ⟨1, by decide⟩),
   opAt 3722 .LT,
   opAt 3723 (.Dup ⟨2, by decide⟩),
   opAt 3724 .ADD,
   opAt 3725 (.Swap ⟨0, by decide⟩),
   opAt 3726 .SUB,
   opAt 3727 (.Dup ⟨3, by decide⟩),
   opAt 3728 .MLOAD,
   opAt 3729 (.Swap ⟨1, by decide⟩),
   opAt 3730 (.Dup ⟨2, by decide⟩),
   opAt 3731 .ADD,
   opAt 3732 (.Swap ⟨1, by decide⟩),
   opAt 3733 (.Dup ⟨2, by decide⟩),
   opAt 3734 .LT,
   opAt 3735 .ADD,
   opAt 3736 (.Swap ⟨0, by decide⟩),
   opAt 3737 (.Dup ⟨4, by decide⟩),
   opAt 3738 .ADD,
   opAt 3739 (.Swap ⟨3, by decide⟩),
   opAt 3740 (.Dup ⟨4, by decide⟩),
   opAt 3741 .LT,
   opAt 3742 .ADD,
   opAt 3743 (.Swap ⟨2, by decide⟩),
   opAt 3744 (.Dup ⟨2, by decide⟩),
   opAt 3745 .MSTORE,
   pushAt 3746 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3747 .ADD,
   opAt 3748 (.Swap ⟨0, by decide⟩),
   pushAt 3749 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3750 .ADD,
   opAt 3751 (.Swap ⟨0, by decide⟩)
  ]

def h2L1Core8_6 : H2Path :=
  [
   opAt 3752 (.Dup ⟨3, by decide⟩),
   opAt 3753 (.Dup ⟨1, by decide⟩),
   opAt 3754 .MLOAD,
   opAt 3755 (.Dup ⟨1, by decide⟩),
   opAt 3756 (.Dup ⟨1, by decide⟩),
   opAt 3757 .MUL,
   opAt 3758 (.Swap ⟨1, by decide⟩),
   pushAt 3759 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 3760 (.Swap ⟨1, by decide⟩),
   opAt 3761 .MULMOD,
   opAt 3762 (.Dup ⟨1, by decide⟩),
   opAt 3763 (.Dup ⟨1, by decide⟩),
   opAt 3764 .LT,
   opAt 3765 (.Dup ⟨2, by decide⟩),
   opAt 3766 .ADD,
   opAt 3767 (.Swap ⟨0, by decide⟩),
   opAt 3768 .SUB,
   opAt 3769 (.Dup ⟨3, by decide⟩),
   opAt 3770 .MLOAD,
   opAt 3771 (.Swap ⟨1, by decide⟩),
   opAt 3772 (.Dup ⟨2, by decide⟩),
   opAt 3773 .ADD,
   opAt 3774 (.Swap ⟨1, by decide⟩),
   opAt 3775 (.Dup ⟨2, by decide⟩),
   opAt 3776 .LT,
   opAt 3777 .ADD,
   opAt 3778 (.Swap ⟨0, by decide⟩),
   opAt 3779 (.Dup ⟨4, by decide⟩),
   opAt 3780 .ADD,
   opAt 3781 (.Swap ⟨3, by decide⟩),
   opAt 3782 (.Dup ⟨4, by decide⟩),
   opAt 3783 .LT,
   opAt 3784 .ADD,
   opAt 3785 (.Swap ⟨2, by decide⟩),
   opAt 3786 (.Dup ⟨2, by decide⟩),
   opAt 3787 .MSTORE,
   pushAt 3788 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3789 .ADD,
   opAt 3790 (.Swap ⟨0, by decide⟩),
   pushAt 3791 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3792 .ADD,
   opAt 3793 (.Swap ⟨0, by decide⟩)
  ]

def h2L1Core8_7 : H2Path :=
  [
   opAt 3794 (.Dup ⟨3, by decide⟩),
   opAt 3795 (.Dup ⟨1, by decide⟩),
   opAt 3796 .MLOAD,
   opAt 3797 (.Dup ⟨1, by decide⟩),
   opAt 3798 (.Dup ⟨1, by decide⟩),
   opAt 3799 .MUL,
   opAt 3800 (.Swap ⟨1, by decide⟩),
   pushAt 3801 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 3802 (.Swap ⟨1, by decide⟩),
   opAt 3803 .MULMOD,
   opAt 3804 (.Dup ⟨1, by decide⟩),
   opAt 3805 (.Dup ⟨1, by decide⟩),
   opAt 3806 .LT,
   opAt 3807 (.Dup ⟨2, by decide⟩),
   opAt 3808 .ADD,
   opAt 3809 (.Swap ⟨0, by decide⟩),
   opAt 3810 .SUB,
   opAt 3811 (.Dup ⟨3, by decide⟩),
   opAt 3812 .MLOAD,
   opAt 3813 (.Swap ⟨1, by decide⟩),
   opAt 3814 (.Dup ⟨2, by decide⟩),
   opAt 3815 .ADD,
   opAt 3816 (.Swap ⟨1, by decide⟩),
   opAt 3817 (.Dup ⟨2, by decide⟩),
   opAt 3818 .LT,
   opAt 3819 .ADD,
   opAt 3820 (.Swap ⟨0, by decide⟩),
   opAt 3821 (.Dup ⟨4, by decide⟩),
   opAt 3822 .ADD,
   opAt 3823 (.Swap ⟨3, by decide⟩),
   opAt 3824 (.Dup ⟨4, by decide⟩),
   opAt 3825 .LT,
   opAt 3826 .ADD,
   opAt 3827 (.Swap ⟨2, by decide⟩),
   opAt 3828 (.Dup ⟨2, by decide⟩),
   opAt 3829 .MSTORE,
   pushAt 3830 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3831 .ADD,
   opAt 3832 (.Swap ⟨0, by decide⟩),
   pushAt 3833 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3834 .ADD,
   opAt 3835 (.Swap ⟨0, by decide⟩)
  ]

def h2Mid8 : H2Path :=
  [
   opAt 3836 .POP,
   opAt 3837 .POP,
   opAt 3838 (.Dup ⟨0, by decide⟩),
   pushAt 3839 2 8224,
   opAt 3840 .MLOAD,
   opAt 3841 .ADD,
   opAt 3842 (.Dup ⟨0, by decide⟩),
   pushAt 3843 2 8224,
   opAt 3844 .MSTORE,
   opAt 3845 .LT,
   pushAt 3846 2 8192,
   opAt 3847 .MSTORE,
   opAt 3848 (.Dup ⟨6, by decide⟩),
   opAt 3849 .MLOAD,
   opAt 3850 (.Dup ⟨0, by decide⟩),
   pushAt 3851 2 9376,
   opAt 3852 .MLOAD,
   opAt 3853 .MUL,
   opAt 3854 (.Swap ⟨0, by decide⟩),
   opAt 3855 (.Dup ⟨1, by decide⟩),
   pushAt 3856 2 9408,
   opAt 3857 .MLOAD,
   opAt 3858 .MLOAD,
   pushAt 3859 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 3860 (.Swap ⟨1, by decide⟩),
   opAt 3861 .MULMOD,
   opAt 3862 (.Dup ⟨1, by decide⟩),
   opAt 3863 .ADD,
   opAt 3864 (.Dup ⟨0, by decide⟩),
   opAt 3865 (.Swap ⟨1, by decide⟩),
   opAt 3866 .GT,
   opAt 3867 .ADD,
   opAt 3868 (.Dup ⟨8, by decide⟩),
   pushAt 3869 1 32,
   opAt 3870 (.Swap ⟨0, by decide⟩),
   opAt 3871 .SUB,
   pushAt 3872 2 9408,
   opAt 3873 .MLOAD,
   pushAt 3874 1 32,
   opAt 3875 (.Swap ⟨0, by decide⟩),
   opAt 3876 .SUB
  ]

def h2L2Core8_0 : H2Path :=
  [
   opAt 3877 (.Dup ⟨3, by decide⟩),
   opAt 3878 (.Dup ⟨1, by decide⟩),
   opAt 3879 .MLOAD,
   opAt 3880 (.Dup ⟨1, by decide⟩),
   opAt 3881 (.Dup ⟨1, by decide⟩),
   opAt 3882 .MUL,
   opAt 3883 (.Swap ⟨1, by decide⟩),
   pushAt 3884 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 3885 (.Swap ⟨1, by decide⟩),
   opAt 3886 .MULMOD,
   opAt 3887 (.Dup ⟨1, by decide⟩),
   opAt 3888 (.Dup ⟨1, by decide⟩),
   opAt 3889 .LT,
   opAt 3890 (.Dup ⟨2, by decide⟩),
   opAt 3891 .ADD,
   opAt 3892 (.Swap ⟨0, by decide⟩),
   opAt 3893 .SUB,
   opAt 3894 (.Dup ⟨3, by decide⟩),
   opAt 3895 .MLOAD,
   opAt 3896 (.Swap ⟨1, by decide⟩),
   opAt 3897 (.Dup ⟨2, by decide⟩),
   opAt 3898 .ADD,
   opAt 3899 (.Swap ⟨1, by decide⟩),
   opAt 3900 (.Dup ⟨2, by decide⟩),
   opAt 3901 .LT,
   opAt 3902 .ADD,
   opAt 3903 (.Swap ⟨0, by decide⟩),
   opAt 3904 (.Dup ⟨4, by decide⟩),
   opAt 3905 .ADD,
   opAt 3906 (.Swap ⟨3, by decide⟩),
   opAt 3907 (.Dup ⟨4, by decide⟩),
   opAt 3908 .LT,
   opAt 3909 .ADD,
   opAt 3910 (.Swap ⟨2, by decide⟩),
   opAt 3911 (.Dup ⟨2, by decide⟩),
   pushAt 3912 1 32,
   opAt 3913 .ADD,
   opAt 3914 .MSTORE,
   pushAt 3915 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3916 .ADD,
   opAt 3917 (.Swap ⟨0, by decide⟩),
   pushAt 3918 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3919 .ADD,
   opAt 3920 (.Swap ⟨0, by decide⟩)
  ]

def h2L2Core8_1 : H2Path :=
  [
   opAt 3921 (.Dup ⟨3, by decide⟩),
   opAt 3922 (.Dup ⟨1, by decide⟩),
   opAt 3923 .MLOAD,
   opAt 3924 (.Dup ⟨1, by decide⟩),
   opAt 3925 (.Dup ⟨1, by decide⟩),
   opAt 3926 .MUL,
   opAt 3927 (.Swap ⟨1, by decide⟩),
   pushAt 3928 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 3929 (.Swap ⟨1, by decide⟩),
   opAt 3930 .MULMOD,
   opAt 3931 (.Dup ⟨1, by decide⟩),
   opAt 3932 (.Dup ⟨1, by decide⟩),
   opAt 3933 .LT,
   opAt 3934 (.Dup ⟨2, by decide⟩),
   opAt 3935 .ADD,
   opAt 3936 (.Swap ⟨0, by decide⟩),
   opAt 3937 .SUB,
   opAt 3938 (.Dup ⟨3, by decide⟩),
   opAt 3939 .MLOAD,
   opAt 3940 (.Swap ⟨1, by decide⟩),
   opAt 3941 (.Dup ⟨2, by decide⟩),
   opAt 3942 .ADD,
   opAt 3943 (.Swap ⟨1, by decide⟩),
   opAt 3944 (.Dup ⟨2, by decide⟩),
   opAt 3945 .LT,
   opAt 3946 .ADD,
   opAt 3947 (.Swap ⟨0, by decide⟩),
   opAt 3948 (.Dup ⟨4, by decide⟩),
   opAt 3949 .ADD,
   opAt 3950 (.Swap ⟨3, by decide⟩),
   opAt 3951 (.Dup ⟨4, by decide⟩),
   opAt 3952 .LT,
   opAt 3953 .ADD,
   opAt 3954 (.Swap ⟨2, by decide⟩),
   opAt 3955 (.Dup ⟨2, by decide⟩),
   pushAt 3956 1 32,
   opAt 3957 .ADD,
   opAt 3958 .MSTORE,
   pushAt 3959 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3960 .ADD,
   opAt 3961 (.Swap ⟨0, by decide⟩),
   pushAt 3962 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3963 .ADD,
   opAt 3964 (.Swap ⟨0, by decide⟩)
  ]

def h2L2Core8_2 : H2Path :=
  [
   opAt 3965 (.Dup ⟨3, by decide⟩),
   opAt 3966 (.Dup ⟨1, by decide⟩),
   opAt 3967 .MLOAD,
   opAt 3968 (.Dup ⟨1, by decide⟩),
   opAt 3969 (.Dup ⟨1, by decide⟩),
   opAt 3970 .MUL,
   opAt 3971 (.Swap ⟨1, by decide⟩),
   pushAt 3972 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 3973 (.Swap ⟨1, by decide⟩),
   opAt 3974 .MULMOD,
   opAt 3975 (.Dup ⟨1, by decide⟩),
   opAt 3976 (.Dup ⟨1, by decide⟩),
   opAt 3977 .LT,
   opAt 3978 (.Dup ⟨2, by decide⟩),
   opAt 3979 .ADD,
   opAt 3980 (.Swap ⟨0, by decide⟩),
   opAt 3981 .SUB,
   opAt 3982 (.Dup ⟨3, by decide⟩),
   opAt 3983 .MLOAD,
   opAt 3984 (.Swap ⟨1, by decide⟩),
   opAt 3985 (.Dup ⟨2, by decide⟩),
   opAt 3986 .ADD,
   opAt 3987 (.Swap ⟨1, by decide⟩),
   opAt 3988 (.Dup ⟨2, by decide⟩),
   opAt 3989 .LT,
   opAt 3990 .ADD,
   opAt 3991 (.Swap ⟨0, by decide⟩),
   opAt 3992 (.Dup ⟨4, by decide⟩),
   opAt 3993 .ADD,
   opAt 3994 (.Swap ⟨3, by decide⟩),
   opAt 3995 (.Dup ⟨4, by decide⟩),
   opAt 3996 .LT,
   opAt 3997 .ADD,
   opAt 3998 (.Swap ⟨2, by decide⟩),
   opAt 3999 (.Dup ⟨2, by decide⟩),
   pushAt 4000 1 32,
   opAt 4001 .ADD,
   opAt 4002 .MSTORE,
   pushAt 4003 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 4004 .ADD,
   opAt 4005 (.Swap ⟨0, by decide⟩),
   pushAt 4006 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 4007 .ADD,
   opAt 4008 (.Swap ⟨0, by decide⟩)
  ]

def h2L2Core8_3 : H2Path :=
  [
   opAt 4009 (.Dup ⟨3, by decide⟩),
   opAt 4010 (.Dup ⟨1, by decide⟩),
   opAt 4011 .MLOAD,
   opAt 4012 (.Dup ⟨1, by decide⟩),
   opAt 4013 (.Dup ⟨1, by decide⟩),
   opAt 4014 .MUL,
   opAt 4015 (.Swap ⟨1, by decide⟩),
   pushAt 4016 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 4017 (.Swap ⟨1, by decide⟩),
   opAt 4018 .MULMOD,
   opAt 4019 (.Dup ⟨1, by decide⟩),
   opAt 4020 (.Dup ⟨1, by decide⟩),
   opAt 4021 .LT,
   opAt 4022 (.Dup ⟨2, by decide⟩),
   opAt 4023 .ADD,
   opAt 4024 (.Swap ⟨0, by decide⟩),
   opAt 4025 .SUB,
   opAt 4026 (.Dup ⟨3, by decide⟩),
   opAt 4027 .MLOAD,
   opAt 4028 (.Swap ⟨1, by decide⟩),
   opAt 4029 (.Dup ⟨2, by decide⟩),
   opAt 4030 .ADD,
   opAt 4031 (.Swap ⟨1, by decide⟩),
   opAt 4032 (.Dup ⟨2, by decide⟩),
   opAt 4033 .LT,
   opAt 4034 .ADD,
   opAt 4035 (.Swap ⟨0, by decide⟩),
   opAt 4036 (.Dup ⟨4, by decide⟩),
   opAt 4037 .ADD,
   opAt 4038 (.Swap ⟨3, by decide⟩),
   opAt 4039 (.Dup ⟨4, by decide⟩),
   opAt 4040 .LT,
   opAt 4041 .ADD,
   opAt 4042 (.Swap ⟨2, by decide⟩),
   opAt 4043 (.Dup ⟨2, by decide⟩),
   pushAt 4044 1 32,
   opAt 4045 .ADD,
   opAt 4046 .MSTORE,
   pushAt 4047 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 4048 .ADD,
   opAt 4049 (.Swap ⟨0, by decide⟩),
   pushAt 4050 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 4051 .ADD,
   opAt 4052 (.Swap ⟨0, by decide⟩)
  ]

def h2L2Core8_4 : H2Path :=
  [
   opAt 4053 (.Dup ⟨3, by decide⟩),
   opAt 4054 (.Dup ⟨1, by decide⟩),
   opAt 4055 .MLOAD,
   opAt 4056 (.Dup ⟨1, by decide⟩),
   opAt 4057 (.Dup ⟨1, by decide⟩),
   opAt 4058 .MUL,
   opAt 4059 (.Swap ⟨1, by decide⟩),
   pushAt 4060 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 4061 (.Swap ⟨1, by decide⟩),
   opAt 4062 .MULMOD,
   opAt 4063 (.Dup ⟨1, by decide⟩),
   opAt 4064 (.Dup ⟨1, by decide⟩),
   opAt 4065 .LT,
   opAt 4066 (.Dup ⟨2, by decide⟩),
   opAt 4067 .ADD,
   opAt 4068 (.Swap ⟨0, by decide⟩),
   opAt 4069 .SUB,
   opAt 4070 (.Dup ⟨3, by decide⟩),
   opAt 4071 .MLOAD,
   opAt 4072 (.Swap ⟨1, by decide⟩),
   opAt 4073 (.Dup ⟨2, by decide⟩),
   opAt 4074 .ADD,
   opAt 4075 (.Swap ⟨1, by decide⟩),
   opAt 4076 (.Dup ⟨2, by decide⟩),
   opAt 4077 .LT,
   opAt 4078 .ADD,
   opAt 4079 (.Swap ⟨0, by decide⟩),
   opAt 4080 (.Dup ⟨4, by decide⟩),
   opAt 4081 .ADD,
   opAt 4082 (.Swap ⟨3, by decide⟩),
   opAt 4083 (.Dup ⟨4, by decide⟩),
   opAt 4084 .LT,
   opAt 4085 .ADD,
   opAt 4086 (.Swap ⟨2, by decide⟩),
   opAt 4087 (.Dup ⟨2, by decide⟩),
   pushAt 4088 1 32,
   opAt 4089 .ADD,
   opAt 4090 .MSTORE,
   pushAt 4091 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 4092 .ADD,
   opAt 4093 (.Swap ⟨0, by decide⟩),
   pushAt 4094 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 4095 .ADD,
   opAt 4096 (.Swap ⟨0, by decide⟩)
  ]

def h2L2Core8_5 : H2Path :=
  [
   opAt 4097 (.Dup ⟨3, by decide⟩),
   opAt 4098 (.Dup ⟨1, by decide⟩),
   opAt 4099 .MLOAD,
   opAt 4100 (.Dup ⟨1, by decide⟩),
   opAt 4101 (.Dup ⟨1, by decide⟩),
   opAt 4102 .MUL,
   opAt 4103 (.Swap ⟨1, by decide⟩),
   pushAt 4104 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 4105 (.Swap ⟨1, by decide⟩),
   opAt 4106 .MULMOD,
   opAt 4107 (.Dup ⟨1, by decide⟩),
   opAt 4108 (.Dup ⟨1, by decide⟩),
   opAt 4109 .LT,
   opAt 4110 (.Dup ⟨2, by decide⟩),
   opAt 4111 .ADD,
   opAt 4112 (.Swap ⟨0, by decide⟩),
   opAt 4113 .SUB,
   opAt 4114 (.Dup ⟨3, by decide⟩),
   opAt 4115 .MLOAD,
   opAt 4116 (.Swap ⟨1, by decide⟩),
   opAt 4117 (.Dup ⟨2, by decide⟩),
   opAt 4118 .ADD,
   opAt 4119 (.Swap ⟨1, by decide⟩),
   opAt 4120 (.Dup ⟨2, by decide⟩),
   opAt 4121 .LT,
   opAt 4122 .ADD,
   opAt 4123 (.Swap ⟨0, by decide⟩),
   opAt 4124 (.Dup ⟨4, by decide⟩),
   opAt 4125 .ADD,
   opAt 4126 (.Swap ⟨3, by decide⟩),
   opAt 4127 (.Dup ⟨4, by decide⟩),
   opAt 4128 .LT,
   opAt 4129 .ADD,
   opAt 4130 (.Swap ⟨2, by decide⟩),
   opAt 4131 (.Dup ⟨2, by decide⟩),
   pushAt 4132 1 32,
   opAt 4133 .ADD,
   opAt 4134 .MSTORE,
   pushAt 4135 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 4136 .ADD,
   opAt 4137 (.Swap ⟨0, by decide⟩),
   pushAt 4138 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 4139 .ADD,
   opAt 4140 (.Swap ⟨0, by decide⟩)
  ]

def h2L2Core8_6 : H2Path :=
  [
   opAt 4141 (.Dup ⟨3, by decide⟩),
   opAt 4142 (.Dup ⟨1, by decide⟩),
   opAt 4143 .MLOAD,
   opAt 4144 (.Dup ⟨1, by decide⟩),
   opAt 4145 (.Dup ⟨1, by decide⟩),
   opAt 4146 .MUL,
   opAt 4147 (.Swap ⟨1, by decide⟩),
   pushAt 4148 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 4149 (.Swap ⟨1, by decide⟩),
   opAt 4150 .MULMOD,
   opAt 4151 (.Dup ⟨1, by decide⟩),
   opAt 4152 (.Dup ⟨1, by decide⟩),
   opAt 4153 .LT,
   opAt 4154 (.Dup ⟨2, by decide⟩),
   opAt 4155 .ADD,
   opAt 4156 (.Swap ⟨0, by decide⟩),
   opAt 4157 .SUB,
   opAt 4158 (.Dup ⟨3, by decide⟩),
   opAt 4159 .MLOAD,
   opAt 4160 (.Swap ⟨1, by decide⟩),
   opAt 4161 (.Dup ⟨2, by decide⟩),
   opAt 4162 .ADD,
   opAt 4163 (.Swap ⟨1, by decide⟩),
   opAt 4164 (.Dup ⟨2, by decide⟩),
   opAt 4165 .LT,
   opAt 4166 .ADD,
   opAt 4167 (.Swap ⟨0, by decide⟩),
   opAt 4168 (.Dup ⟨4, by decide⟩),
   opAt 4169 .ADD,
   opAt 4170 (.Swap ⟨3, by decide⟩),
   opAt 4171 (.Dup ⟨4, by decide⟩),
   opAt 4172 .LT,
   opAt 4173 .ADD,
   opAt 4174 (.Swap ⟨2, by decide⟩),
   opAt 4175 (.Dup ⟨2, by decide⟩),
   pushAt 4176 1 32,
   opAt 4177 .ADD,
   opAt 4178 .MSTORE,
   pushAt 4179 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 4180 .ADD,
   opAt 4181 (.Swap ⟨0, by decide⟩),
   pushAt 4182 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 4183 .ADD,
   opAt 4184 (.Swap ⟨0, by decide⟩)
  ]

def h2Tail8 : H2Path :=
  [
   opAt 4185 .POP,
   opAt 4186 .POP,
   opAt 4187 (.Swap ⟨0, by decide⟩),
   opAt 4188 .POP,
   opAt 4189 (.Swap ⟨0, by decide⟩),
   opAt 4190 .POP,
   opAt 4191 (.Dup ⟨0, by decide⟩),
   pushAt 4192 2 8224,
   opAt 4193 .MLOAD,
   opAt 4194 .ADD,
   opAt 4195 (.Dup ⟨0, by decide⟩),
   pushAt 4196 2 8256,
   opAt 4197 .MSTORE,
   opAt 4198 .LT,
   pushAt 4199 2 8192,
   opAt 4200 .MLOAD,
   opAt 4201 .ADD,
   pushAt 4202 2 8224,
   opAt 4203 .MSTORE,
   pushAt 4204 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 4205 .ADD,
   opAt 4206 (.Dup ⟨2, by decide⟩),
   opAt 4207 (.Dup ⟨1, by decide⟩),
   opAt 4208 .GT,
   pushAt 4209 2 6670,
   opAt 4210 .JUMPI
  ]

def h2Exit8 : H2Path :=
  [
   opAt 4211 .POP,
   opAt 4212 .POP,
   opAt 4213 .POP,
   opAt 4214 (.Swap ⟨1, by decide⟩),
   opAt 4215 .POP,
   opAt 4216 (.Swap ⟨0, by decide⟩),
   pushAt 4217 2 2686,
   opAt 4218 .JUMP
  ]

def h2L1Core4 (j : Nat) : H2Path :=
  match j with
  | 0 => h2L1Core4_0
  | 1 => h2L1Core4_1
  | 2 => h2L1Core4_2
  | 3 => h2L1Core4_3
  | _ => []

def h2L1Core8 (j : Nat) : H2Path :=
  match j with
  | 0 => h2L1Core8_0
  | 1 => h2L1Core8_1
  | 2 => h2L1Core8_2
  | 3 => h2L1Core8_3
  | 4 => h2L1Core8_4
  | 5 => h2L1Core8_5
  | 6 => h2L1Core8_6
  | 7 => h2L1Core8_7
  | _ => []

def h2L2Core4 (k : Nat) : H2Path :=
  match k with
  | 0 => h2L2Core4_0
  | 1 => h2L2Core4_1
  | 2 => h2L2Core4_2
  | _ => []

def h2L2Core8 (k : Nat) : H2Path :=
  match k with
  | 0 => h2L2Core8_0
  | 1 => h2L2Core8_1
  | 2 => h2L2Core8_2
  | 3 => h2L2Core8_3
  | 4 => h2L2Core8_4
  | 5 => h2L2Core8_5
  | 6 => h2L2Core8_6
  | _ => []

def h2Entry (n : Nat) : H2Path :=
  match n with
  | 4 => h2Entry4
  | 8 => h2Entry8
  | _ => []

def h2Out (n : Nat) : H2Path :=
  match n with
  | 4 => h2Out4
  | 8 => h2Out8
  | _ => []

def h2L1Core (n j : Nat) : H2Path :=
  match n with
  | 4 => h2L1Core4 j
  | 8 => h2L1Core8 j
  | _ => []

def h2Mid (n : Nat) : H2Path :=
  match n with
  | 4 => h2Mid4
  | 8 => h2Mid8
  | _ => []

def h2L2Core (n k : Nat) : H2Path :=
  match n with
  | 4 => h2L2Core4 k
  | 8 => h2L2Core8 k
  | _ => []

def h2Tail (n : Nat) : H2Path :=
  match n with
  | 4 => h2Tail4
  | 8 => h2Tail8
  | _ => []

def h2Exit (n : Nat) : H2Path :=
  match n with
  | 4 => h2Exit4
  | 8 => h2Exit8
  | _ => []

def h2EntryPC (n : Nat) : Nat :=
  match n with
  | 4 => 5515
  | 8 => 6668
  | _ => 0

def h2OutPC (n : Nat) : Nat :=
  match n with
  | 4 => 5517
  | 8 => 6670
  | _ => 0

def h2L1PC (n j : Nat) : Nat :=
  match n with
  | 4 => 5528 + 138 * j
  | 8 => 6681 + 138 * j
  | _ => 0

def h2MidPC (n : Nat) : Nat :=
  match n with
  | 4 => 6080
  | 8 => 7785
  | _ => 0

def h2L2PC (n k : Nat) : Nat :=
  match n with
  | 4 => 6167 + 141 * k
  | 8 => 7872 + 141 * k
  | _ => 0

def h2TailPC (n : Nat) : Nat :=
  match n with
  | 4 => 6590
  | 8 => 8859
  | _ => 0

def h2ExitPC (n : Nat) : Nat :=
  match n with
  | 4 => 6658
  | 8 => 8927
  | _ => 0

end Challenge.Modexp.Submission.Proofs.Fast

