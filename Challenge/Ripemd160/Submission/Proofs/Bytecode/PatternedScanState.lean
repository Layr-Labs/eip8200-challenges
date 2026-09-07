import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedSwar
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedGuardSpec
import Challenge.EvmProof.Stepper
import Challenge.Ripemd160.ProofSupport.InitialState
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Artifact

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000

/-!
# States and paths of the scalar-SWAR patterned-1000 guard

The guard carries the expected word forward instead of storing thirty-two of
them, so the scan is one loop: `wordPath` derives the word and routes the four
straddling offsets to `straddlePath`, and `comparePath` folds the difference
into the accumulator and advances the offset and the scalar.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open PatternedInputData PatternedDigest PatternedGuardSpec PatternedSwar

def wfOp {op : Operation}
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op)
    (hplain : YulEvmCompiler.plainOp op)
    (havailable : op.availableInFork .Osaka = true) :
    Challenge.EvmProof.Stepper.WellFormed .Osaka (.op op) :=
  ⟨hopcode, hplain, havailable⟩

abbrev Located := Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka

def opAt (index : Nat) (op : Operation)
    (hget : Artifact.submissionInstructions[index]? = some (.op op) := by rfl)
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op := by decide)
    (hplain : YulEvmCompiler.plainOp op := by trivial)
    (havailable : op.availableInFork .Osaka = true := by rfl) : Located :=
  ⟨index, .op op, hget, wfOp hopcode hplain havailable⟩

def pushAt (index : Nat) (width : Fin 33) (value : UInt256)
    (hget : Artifact.submissionInstructions[index]? = some (.push width value) := by rfl)
    (hwf : Challenge.EvmProof.Stepper.WellFormed .Osaka
      (.push width value) := by decide) : Located :=
  ⟨index, .push width value, hget, hwf⟩

abbrev run := Challenge.EvmProof.Stepper.runLocatedBlock
  (artifact := Artifact.submissionArtifact) (fork := .Osaka)

/-- Push the five constants and start the scan. -/
def setupPath : List Located :=
  [opAt 3273 .JUMPDEST,
   pushAt 3274 1 255,
   pushAt 3275 0 0,
   opAt 3276 .NOT,
   opAt 3277 .DIV,
   pushAt 3278 32 3244493450063667868678674439968361782956185527883176199882357678282131398018,
   opAt 3279 (.Dup ⟨1, by decide⟩),
   pushAt 3280 1 7,
   opAt 3281 .SHL,
   opAt 3282 (.Dup ⟨0, by decide⟩),
   opAt 3283 .NOT,
   opAt 3284 (.Swap ⟨0, by decide⟩),
   opAt 3285 (.Swap ⟨2, by decide⟩),
   opAt 3286 (.Dup ⟨2, by decide⟩),
   opAt 3287 (.Dup ⟨2, by decide⟩),
   opAt 3288 .AND,
   pushAt 3289 0 0,
   pushAt 3290 0 0,
   pushAt 3291 0 0]

/-- Derive the expected word and test for a straddler. -/
def wordPath : List Located :=
  [opAt 3292 .JUMPDEST, opAt 3293 (.Dup ⟨0, by decide⟩),
   opAt 3294 (.Dup ⟨5, by decide⟩), opAt 3295 .MUL,
   opAt 3296 (.Dup ⟨0, by decide⟩), opAt 3297 (.Dup ⟨7, by decide⟩),
   opAt 3298 .AND, opAt 3299 (.Dup ⟨5, by decide⟩), opAt 3300 .ADD,
   opAt 3301 (.Dup ⟨1, by decide⟩), opAt 3302 (.Dup ⟨9, by decide⟩),
   opAt 3303 .XOR, opAt 3304 (.Dup ⟨10, by decide⟩), opAt 3305 .AND,
   opAt 3306 .XOR, opAt 3307 (.Dup ⟨3, by decide⟩), pushAt 3308 1 255,
   opAt 3309 .AND, pushAt 3310 1 224, opAt 3311 .EQ, pushAt 3312 2 5257,
   opAt 3313 .JUMPI]

/-- Fold one word into the accumulator and advance. -/
def comparePath : List Located :=
  [opAt 3314 .JUMPDEST, opAt 3315 (.Dup ⟨3, by decide⟩),
   opAt 3316 .CALLDATALOAD, opAt 3317 .XOR, opAt 3318 (.Dup ⟨4, by decide⟩),
   opAt 3319 .OR, opAt 3320 (.Swap ⟨3, by decide⟩), opAt 3321 .POP,
   opAt 3322 .POP, opAt 3323 .JUMPDEST, pushAt 3324 1 160,
   opAt 3325 .ADD, pushAt 3326 1 255, opAt 3327 .AND,
   opAt 3328 .JUMPDEST, opAt 3329 .JUMPDEST,
   opAt 3330 (.Swap ⟨0, by decide⟩), pushAt 3331 1 32, opAt 3332 .ADD,
   opAt 3333 (.Swap ⟨0, by decide⟩), opAt 3334 .JUMPDEST,
   opAt 3335 (.Dup ⟨1, by decide⟩), pushAt 3336 2 992, opAt 3337 .GT,
   pushAt 3338 2 5137, opAt 3339 .JUMPI]

/-- The padded tail word, the cleanup and the miss test. -/
def tailPath : List Located :=
  [pushAt 3340 2 992, opAt 3341 .CALLDATALOAD,
   pushAt 3342 8 9848759918901945995, pushAt 3343 1 192, opAt 3344 .SHL,
   opAt 3345 .XOR, opAt 3346 (.Dup ⟨3, by decide⟩), opAt 3347 .OR,
   opAt 3348 (.Swap ⟨2, by decide⟩), opAt 3349 .POP,
   opAt 3350 (.Swap ⟨1, by decide⟩), opAt 3351 (.Swap ⟨6, by decide⟩),
   opAt 3352 .POP, opAt 3353 .POP, opAt 3354 .POP, opAt 3355 .POP,
   opAt 3356 .POP, opAt 3357 .POP, opAt 3358 .POP, pushAt 3359 2 1011,
   opAt 3360 .JUMPI]

/-- Store and return the stored digest. -/
def returnPath : List Located :=
  [pushAt 3361 20 766350606435067737561421097975693824639675460820,
   pushAt 3362 0 0, opAt 3363 .MSTORE, pushAt 3364 1 32, pushAt 3365 0 0,
   opAt 3366 .RETURN]

/-- Shift the correction constant out of `M`. -/
def straddleCorrPath : List Located :=
  [opAt 3367 .JUMPDEST, opAt 3368 (.Dup ⟨6, by decide⟩),
   opAt 3369 (.Dup ⟨4, by decide⟩), pushAt 3370 1 8, opAt 3371 .SHR,
   pushAt 3372 1 5, opAt 3373 .MUL, pushAt 3374 1 27, opAt 3375 .SUB,
   pushAt 3376 1 8, opAt 3377 .MUL, opAt 3378 .SHR, pushAt 3379 1 11,
   opAt 3380 .MUL]

/-- Apply the correction to the expected word. -/
def straddleAddPath : List Located :=
  [opAt 3381 (.Dup ⟨1, by decide⟩), opAt 3382 (.Dup ⟨9, by decide⟩),
   opAt 3383 .AND, opAt 3384 (.Dup ⟨1, by decide⟩), opAt 3385 .ADD,
   opAt 3386 (.Dup ⟨2, by decide⟩), opAt 3387 (.Dup ⟨12, by decide⟩),
   opAt 3388 .AND, opAt 3389 .XOR, opAt 3390 (.Swap ⟨1, by decide⟩),
   opAt 3391 .POP, opAt 3392 .POP]

/-- Bump the scalar and rejoin the scan. -/
def straddleBackPath : List Located :=
  [opAt 3393 (.Dup ⟨2, by decide⟩), pushAt 3394 1 11, opAt 3395 .ADD,
   opAt 3396 (.Swap ⟨2, by decide⟩), opAt 3397 .POP, pushAt 3398 2 5163,
   opAt 3399 .JUMP]


@[simp] theorem pc2903 : Artifact.submissionArtifact.instructionPC 3273 = 0x13dc := by rfl
@[simp] theorem pc2904 : Artifact.submissionArtifact.instructionPC 3274 = 0x13dd := by rfl
@[simp] theorem pc2905 : Artifact.submissionArtifact.instructionPC 3278 = 0x13e2 := by rfl
@[simp] theorem pc2906 : Artifact.submissionArtifact.instructionPC 3283 = 0x1408 := by rfl
@[simp] theorem pc2907 : Artifact.submissionArtifact.instructionPC 3285 = 0x140a := by rfl
@[simp] theorem pc2908 : Artifact.submissionArtifact.instructionPC 3286 = 0x140b := by rfl
@[simp] theorem pc2909 : Artifact.submissionArtifact.instructionPC 3287 = 0x140c := by rfl
@[simp] theorem pc2910 : Artifact.submissionArtifact.instructionPC 3288 = 0x140d := by rfl
@[simp] theorem pc2911 : Artifact.submissionArtifact.instructionPC 3289 = 0x140e := by rfl
@[simp] theorem pc2912 : Artifact.submissionArtifact.instructionPC 3290 = 0x140f := by rfl
@[simp] theorem pc2913 : Artifact.submissionArtifact.instructionPC 3291 = 0x1410 := by rfl
@[simp] theorem pc2914 : Artifact.submissionArtifact.instructionPC 3292 = 0x1411 := by rfl
@[simp] theorem pc2915 : Artifact.submissionArtifact.instructionPC 3293 = 0x1412 := by rfl
@[simp] theorem pc2916 : Artifact.submissionArtifact.instructionPC 3294 = 0x1413 := by rfl
@[simp] theorem pc2917 : Artifact.submissionArtifact.instructionPC 3295 = 0x1414 := by rfl
@[simp] theorem pc2918 : Artifact.submissionArtifact.instructionPC 3296 = 0x1415 := by rfl
@[simp] theorem pc2919 : Artifact.submissionArtifact.instructionPC 3297 = 0x1416 := by rfl
@[simp] theorem pc2920 : Artifact.submissionArtifact.instructionPC 3298 = 0x1417 := by rfl
@[simp] theorem pc2921 : Artifact.submissionArtifact.instructionPC 3299 = 0x1418 := by rfl
@[simp] theorem pc2922 : Artifact.submissionArtifact.instructionPC 3300 = 0x1419 := by rfl
@[simp] theorem pc2923 : Artifact.submissionArtifact.instructionPC 3301 = 0x141a := by rfl
@[simp] theorem pc2924 : Artifact.submissionArtifact.instructionPC 3302 = 0x141b := by rfl
@[simp] theorem pc2925 : Artifact.submissionArtifact.instructionPC 3303 = 0x141c := by rfl
@[simp] theorem pc2926 : Artifact.submissionArtifact.instructionPC 3304 = 0x141d := by rfl
@[simp] theorem pc2927 : Artifact.submissionArtifact.instructionPC 3305 = 0x141e := by rfl
@[simp] theorem pc2928 : Artifact.submissionArtifact.instructionPC 3306 = 0x141f := by rfl
@[simp] theorem pc2929 : Artifact.submissionArtifact.instructionPC 3307 = 0x1420 := by rfl
@[simp] theorem pc2930 : Artifact.submissionArtifact.instructionPC 3308 = 0x1421 := by rfl
@[simp] theorem pc2931 : Artifact.submissionArtifact.instructionPC 3309 = 0x1423 := by rfl
@[simp] theorem pc2932 : Artifact.submissionArtifact.instructionPC 3310 = 0x1424 := by rfl
@[simp] theorem pc2933 : Artifact.submissionArtifact.instructionPC 3311 = 0x1426 := by rfl
@[simp] theorem pc2934 : Artifact.submissionArtifact.instructionPC 3312 = 0x1427 := by rfl
@[simp] theorem pc2935 : Artifact.submissionArtifact.instructionPC 3313 = 0x142a := by rfl
@[simp] theorem pc2936 : Artifact.submissionArtifact.instructionPC 3314 = 0x142b := by rfl
@[simp] theorem pc2937 : Artifact.submissionArtifact.instructionPC 3315 = 0x142c := by rfl
@[simp] theorem pc2938 : Artifact.submissionArtifact.instructionPC 3316 = 0x142d := by rfl
@[simp] theorem pc2939 : Artifact.submissionArtifact.instructionPC 3317 = 0x142e := by rfl
@[simp] theorem pc2940 : Artifact.submissionArtifact.instructionPC 3318 = 0x142f := by rfl
@[simp] theorem pc2941 : Artifact.submissionArtifact.instructionPC 3319 = 0x1430 := by rfl
@[simp] theorem pc2942 : Artifact.submissionArtifact.instructionPC 3320 = 0x1431 := by rfl
@[simp] theorem pc2943 : Artifact.submissionArtifact.instructionPC 3321 = 0x1432 := by rfl
@[simp] theorem pc2944 : Artifact.submissionArtifact.instructionPC 3322 = 0x1433 := by rfl
@[simp] theorem pc2945 : Artifact.submissionArtifact.instructionPC 3323 = 0x1434 := by rfl
@[simp] theorem pc2946 : Artifact.submissionArtifact.instructionPC 3324 = 0x1435 := by rfl
@[simp] theorem pc2947 : Artifact.submissionArtifact.instructionPC 3325 = 0x1437 := by rfl
@[simp] theorem pc2948 : Artifact.submissionArtifact.instructionPC 3326 = 0x1438 := by rfl
@[simp] theorem pc2949 : Artifact.submissionArtifact.instructionPC 3327 = 0x143a := by rfl
@[simp] theorem pc2950 : Artifact.submissionArtifact.instructionPC 3328 = 0x143b := by rfl
@[simp] theorem pc2951 : Artifact.submissionArtifact.instructionPC 3329 = 0x143c := by rfl
@[simp] theorem pc2952 : Artifact.submissionArtifact.instructionPC 3330 = 0x143d := by rfl
@[simp] theorem pc2953 : Artifact.submissionArtifact.instructionPC 3331 = 0x143e := by rfl
@[simp] theorem pc2954 : Artifact.submissionArtifact.instructionPC 3332 = 0x1440 := by rfl
@[simp] theorem pc2955 : Artifact.submissionArtifact.instructionPC 3333 = 0x1441 := by rfl
@[simp] theorem pc2956 : Artifact.submissionArtifact.instructionPC 3334 = 0x1442 := by rfl
@[simp] theorem pc2957 : Artifact.submissionArtifact.instructionPC 3335 = 0x1443 := by rfl
@[simp] theorem pc2958 : Artifact.submissionArtifact.instructionPC 3336 = 0x1444 := by rfl
@[simp] theorem pc2959 : Artifact.submissionArtifact.instructionPC 3337 = 0x1447 := by rfl
@[simp] theorem pc2960 : Artifact.submissionArtifact.instructionPC 3338 = 0x1448 := by rfl
@[simp] theorem pc2961 : Artifact.submissionArtifact.instructionPC 3339 = 0x144b := by rfl
@[simp] theorem pc2962 : Artifact.submissionArtifact.instructionPC 3340 = 0x144c := by rfl
@[simp] theorem pc2963 : Artifact.submissionArtifact.instructionPC 3341 = 0x144f := by rfl
@[simp] theorem pc2964 : Artifact.submissionArtifact.instructionPC 3342 = 0x1450 := by rfl
@[simp] theorem pc2965 : Artifact.submissionArtifact.instructionPC 3343 = 0x1459 := by rfl
@[simp] theorem pc2966 : Artifact.submissionArtifact.instructionPC 3344 = 0x145b := by rfl
@[simp] theorem pc2967 : Artifact.submissionArtifact.instructionPC 3345 = 0x145c := by rfl
@[simp] theorem pc2968 : Artifact.submissionArtifact.instructionPC 3346 = 0x145d := by rfl
@[simp] theorem pc2969 : Artifact.submissionArtifact.instructionPC 3347 = 0x145e := by rfl
@[simp] theorem pc2970 : Artifact.submissionArtifact.instructionPC 3348 = 0x145f := by rfl
@[simp] theorem pc2971 : Artifact.submissionArtifact.instructionPC 3349 = 0x1460 := by rfl
@[simp] theorem pc2972 : Artifact.submissionArtifact.instructionPC 3350 = 0x1461 := by rfl
@[simp] theorem pc2973 : Artifact.submissionArtifact.instructionPC 3351 = 0x1462 := by rfl
@[simp] theorem pc2974 : Artifact.submissionArtifact.instructionPC 3352 = 0x1463 := by rfl
@[simp] theorem pc2975 : Artifact.submissionArtifact.instructionPC 3353 = 0x1464 := by rfl
@[simp] theorem pc2976 : Artifact.submissionArtifact.instructionPC 3354 = 0x1465 := by rfl
@[simp] theorem pc2977 : Artifact.submissionArtifact.instructionPC 3355 = 0x1466 := by rfl
@[simp] theorem pc2978 : Artifact.submissionArtifact.instructionPC 3356 = 0x1467 := by rfl
@[simp] theorem pc2979 : Artifact.submissionArtifact.instructionPC 3357 = 0x1468 := by rfl
@[simp] theorem pc2980 : Artifact.submissionArtifact.instructionPC 3358 = 0x1469 := by rfl
@[simp] theorem pc2981 : Artifact.submissionArtifact.instructionPC 3359 = 0x146a := by rfl
@[simp] theorem pc2982 : Artifact.submissionArtifact.instructionPC 3360 = 0x146d := by rfl
@[simp] theorem pc2983 : Artifact.submissionArtifact.instructionPC 3361 = 0x146e := by rfl
@[simp] theorem pc2984 : Artifact.submissionArtifact.instructionPC 3362 = 0x1483 := by rfl
@[simp] theorem pc2985 : Artifact.submissionArtifact.instructionPC 3363 = 0x1484 := by rfl
@[simp] theorem pc2986 : Artifact.submissionArtifact.instructionPC 3364 = 0x1485 := by rfl
@[simp] theorem pc2987 : Artifact.submissionArtifact.instructionPC 3365 = 0x1487 := by rfl
@[simp] theorem pc2988 : Artifact.submissionArtifact.instructionPC 3366 = 0x1488 := by rfl
@[simp] theorem pc2989 : Artifact.submissionArtifact.instructionPC 3367 = 0x1489 := by rfl
@[simp] theorem pc2990 : Artifact.submissionArtifact.instructionPC 3368 = 0x148a := by rfl
@[simp] theorem pc2991 : Artifact.submissionArtifact.instructionPC 3369 = 0x148b := by rfl
@[simp] theorem pc2992 : Artifact.submissionArtifact.instructionPC 3370 = 0x148c := by rfl
@[simp] theorem pc2993 : Artifact.submissionArtifact.instructionPC 3371 = 0x148e := by rfl
@[simp] theorem pc2994 : Artifact.submissionArtifact.instructionPC 3372 = 0x148f := by rfl
@[simp] theorem pc2995 : Artifact.submissionArtifact.instructionPC 3373 = 0x1491 := by rfl
@[simp] theorem pc2996 : Artifact.submissionArtifact.instructionPC 3374 = 0x1492 := by rfl
@[simp] theorem pc2997 : Artifact.submissionArtifact.instructionPC 3375 = 0x1494 := by rfl
@[simp] theorem pc2998 : Artifact.submissionArtifact.instructionPC 3376 = 0x1495 := by rfl
@[simp] theorem pc2999 : Artifact.submissionArtifact.instructionPC 3377 = 0x1497 := by rfl
@[simp] theorem pc3000 : Artifact.submissionArtifact.instructionPC 3378 = 0x1498 := by rfl
@[simp] theorem pc3001 : Artifact.submissionArtifact.instructionPC 3379 = 0x1499 := by rfl
@[simp] theorem pc3002 : Artifact.submissionArtifact.instructionPC 3380 = 0x149b := by rfl
@[simp] theorem pc3003 : Artifact.submissionArtifact.instructionPC 3381 = 0x149c := by rfl
@[simp] theorem pc3004 : Artifact.submissionArtifact.instructionPC 3382 = 0x149d := by rfl
@[simp] theorem pc3005 : Artifact.submissionArtifact.instructionPC 3383 = 0x149e := by rfl
@[simp] theorem pc3006 : Artifact.submissionArtifact.instructionPC 3384 = 0x149f := by rfl
@[simp] theorem pc3007 : Artifact.submissionArtifact.instructionPC 3385 = 0x14a0 := by rfl
@[simp] theorem pc3008 : Artifact.submissionArtifact.instructionPC 3386 = 0x14a1 := by rfl
@[simp] theorem pc3009 : Artifact.submissionArtifact.instructionPC 3387 = 0x14a2 := by rfl
@[simp] theorem pc3010 : Artifact.submissionArtifact.instructionPC 3388 = 0x14a3 := by rfl
@[simp] theorem pc3011 : Artifact.submissionArtifact.instructionPC 3389 = 0x14a4 := by rfl
@[simp] theorem pc3012 : Artifact.submissionArtifact.instructionPC 3390 = 0x14a5 := by rfl
@[simp] theorem pc3013 : Artifact.submissionArtifact.instructionPC 3391 = 0x14a6 := by rfl
@[simp] theorem pc3014 : Artifact.submissionArtifact.instructionPC 3392 = 0x14a7 := by rfl
@[simp] theorem pc3015 : Artifact.submissionArtifact.instructionPC 3393 = 0x14a8 := by rfl
@[simp] theorem pc3016 : Artifact.submissionArtifact.instructionPC 3394 = 0x14a9 := by rfl
@[simp] theorem pc3017 : Artifact.submissionArtifact.instructionPC 3395 = 0x14ab := by rfl
@[simp] theorem pc3018 : Artifact.submissionArtifact.instructionPC 3396 = 0x14ac := by rfl
@[simp] theorem pc3019 : Artifact.submissionArtifact.instructionPC 3397 = 0x14ad := by rfl
@[simp] theorem pc3020 : Artifact.submissionArtifact.instructionPC 3398 = 0x14ae := by rfl
@[simp] theorem pc3021 : Artifact.submissionArtifact.instructionPC 3399 = 0x14b1 := by rfl
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan
