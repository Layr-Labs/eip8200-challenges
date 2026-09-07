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
  [opAt 3227 .JUMPDEST,
   pushAt 3228 1 255,
   pushAt 3229 0 0,
   opAt 3230 .NOT,
   opAt 3231 .DIV,
   pushAt 3232 32 3244493450063667868678674439968361782956185527883176199882357678282131398018,
   opAt 3233 (.Dup ⟨1, by decide⟩),
   pushAt 3234 1 7,
   opAt 3235 .SHL,
   opAt 3236 (.Dup ⟨0, by decide⟩),
   opAt 3237 .NOT,
   opAt 3238 (.Swap ⟨0, by decide⟩),
   opAt 3239 (.Swap ⟨2, by decide⟩),
   opAt 3240 (.Dup ⟨2, by decide⟩),
   opAt 3241 (.Dup ⟨2, by decide⟩),
   opAt 3242 .AND,
   pushAt 3243 0 0,
   pushAt 3244 0 0,
   pushAt 3245 0 0]

/-- Derive the expected word and test for a straddler. -/
def wordPath : List Located :=
  [opAt 3246 .JUMPDEST, opAt 3247 (.Dup ⟨0, by decide⟩),
   opAt 3248 (.Dup ⟨5, by decide⟩), opAt 3249 .MUL,
   opAt 3250 (.Dup ⟨0, by decide⟩), opAt 3251 (.Dup ⟨7, by decide⟩),
   opAt 3252 .AND, opAt 3253 (.Dup ⟨5, by decide⟩), opAt 3254 .ADD,
   opAt 3255 (.Dup ⟨1, by decide⟩), opAt 3256 (.Dup ⟨9, by decide⟩),
   opAt 3257 .XOR, opAt 3258 (.Dup ⟨10, by decide⟩), opAt 3259 .AND,
   opAt 3260 .XOR, opAt 3261 (.Dup ⟨3, by decide⟩), pushAt 3262 1 255,
   opAt 3263 .AND, pushAt 3264 1 224, opAt 3265 .EQ, pushAt 3266 2 5299,
   opAt 3267 .JUMPI]

/-- Fold one word into the accumulator and advance. -/
def comparePath : List Located :=
  [opAt 3268 .JUMPDEST, opAt 3269 (.Dup ⟨3, by decide⟩),
   opAt 3270 .CALLDATALOAD, opAt 3271 .XOR, opAt 3272 (.Dup ⟨4, by decide⟩),
   opAt 3273 .OR, opAt 3274 (.Swap ⟨3, by decide⟩), opAt 3275 .POP,
   opAt 3276 .POP, opAt 3277 .JUMPDEST, pushAt 3278 1 160,
   opAt 3279 .ADD, pushAt 3280 1 255, opAt 3281 .AND,
   opAt 3282 .JUMPDEST, opAt 3283 .JUMPDEST,
   opAt 3284 (.Swap ⟨0, by decide⟩), pushAt 3285 1 32, opAt 3286 .ADD,
   opAt 3287 (.Swap ⟨0, by decide⟩), opAt 3288 .JUMPDEST,
   opAt 3289 (.Dup ⟨1, by decide⟩), pushAt 3290 2 992, opAt 3291 .GT,
   pushAt 3292 2 5179, opAt 3293 .JUMPI]

/-- The padded tail word, the cleanup and the miss test. -/
def tailPath : List Located :=
  [pushAt 3294 2 992, opAt 3295 .CALLDATALOAD,
   pushAt 3296 8 9848759918901945995, pushAt 3297 1 192, opAt 3298 .SHL,
   opAt 3299 .XOR, opAt 3300 (.Dup ⟨3, by decide⟩), opAt 3301 .OR,
   opAt 3302 (.Swap ⟨2, by decide⟩), opAt 3303 .POP,
   opAt 3304 (.Swap ⟨1, by decide⟩), opAt 3305 (.Swap ⟨6, by decide⟩),
   opAt 3306 .POP, opAt 3307 .POP, opAt 3308 .POP, opAt 3309 .POP,
   opAt 3310 .POP, opAt 3311 .POP, opAt 3312 .POP, pushAt 3313 2 1011,
   opAt 3314 .JUMPI]

/-- Store and return the stored digest. -/
def returnPath : List Located :=
  [pushAt 3315 20 766350606435067737561421097975693824639675460820,
   pushAt 3316 0 0, opAt 3317 .MSTORE, pushAt 3318 1 32, pushAt 3319 0 0,
   opAt 3320 .RETURN]

/-- Shift the correction constant out of `M`. -/
def straddleCorrPath : List Located :=
  [opAt 3321 .JUMPDEST, opAt 3322 (.Dup ⟨6, by decide⟩),
   opAt 3323 (.Dup ⟨4, by decide⟩), pushAt 3324 1 8, opAt 3325 .SHR,
   pushAt 3326 1 5, opAt 3327 .MUL, pushAt 3328 1 27, opAt 3329 .SUB,
   pushAt 3330 1 8, opAt 3331 .MUL, opAt 3332 .SHR, pushAt 3333 1 11,
   opAt 3334 .MUL]

/-- Apply the correction to the expected word. -/
def straddleAddPath : List Located :=
  [opAt 3335 (.Dup ⟨1, by decide⟩), opAt 3336 (.Dup ⟨9, by decide⟩),
   opAt 3337 .AND, opAt 3338 (.Dup ⟨1, by decide⟩), opAt 3339 .ADD,
   opAt 3340 (.Dup ⟨2, by decide⟩), opAt 3341 (.Dup ⟨12, by decide⟩),
   opAt 3342 .AND, opAt 3343 .XOR, opAt 3344 (.Swap ⟨1, by decide⟩),
   opAt 3345 .POP, opAt 3346 .POP]

/-- Bump the scalar and rejoin the scan. -/
def straddleBackPath : List Located :=
  [opAt 3347 (.Dup ⟨2, by decide⟩), pushAt 3348 1 11, opAt 3349 .ADD,
   opAt 3350 (.Swap ⟨2, by decide⟩), opAt 3351 .POP, pushAt 3352 2 5205,
   opAt 3353 .JUMP]


@[simp] theorem pc2903 : Artifact.submissionArtifact.instructionPC 3227 = 0x1406 := by rfl
@[simp] theorem pc2904 : Artifact.submissionArtifact.instructionPC 3228 = 0x1407 := by rfl
@[simp] theorem pc2905 : Artifact.submissionArtifact.instructionPC 3232 = 0x140c := by rfl
@[simp] theorem pc2906 : Artifact.submissionArtifact.instructionPC 3237 = 0x1432 := by rfl
@[simp] theorem pc2907 : Artifact.submissionArtifact.instructionPC 3239 = 0x1434 := by rfl
@[simp] theorem pc2908 : Artifact.submissionArtifact.instructionPC 3240 = 0x1435 := by rfl
@[simp] theorem pc2909 : Artifact.submissionArtifact.instructionPC 3241 = 0x1436 := by rfl
@[simp] theorem pc2910 : Artifact.submissionArtifact.instructionPC 3242 = 0x1437 := by rfl
@[simp] theorem pc2911 : Artifact.submissionArtifact.instructionPC 3243 = 0x1438 := by rfl
@[simp] theorem pc2912 : Artifact.submissionArtifact.instructionPC 3244 = 0x1439 := by rfl
@[simp] theorem pc2913 : Artifact.submissionArtifact.instructionPC 3245 = 0x143a := by rfl
@[simp] theorem pc2914 : Artifact.submissionArtifact.instructionPC 3246 = 0x143b := by rfl
@[simp] theorem pc2915 : Artifact.submissionArtifact.instructionPC 3247 = 0x143c := by rfl
@[simp] theorem pc2916 : Artifact.submissionArtifact.instructionPC 3248 = 0x143d := by rfl
@[simp] theorem pc2917 : Artifact.submissionArtifact.instructionPC 3249 = 0x143e := by rfl
@[simp] theorem pc2918 : Artifact.submissionArtifact.instructionPC 3250 = 0x143f := by rfl
@[simp] theorem pc2919 : Artifact.submissionArtifact.instructionPC 3251 = 0x1440 := by rfl
@[simp] theorem pc2920 : Artifact.submissionArtifact.instructionPC 3252 = 0x1441 := by rfl
@[simp] theorem pc2921 : Artifact.submissionArtifact.instructionPC 3253 = 0x1442 := by rfl
@[simp] theorem pc2922 : Artifact.submissionArtifact.instructionPC 3254 = 0x1443 := by rfl
@[simp] theorem pc2923 : Artifact.submissionArtifact.instructionPC 3255 = 0x1444 := by rfl
@[simp] theorem pc2924 : Artifact.submissionArtifact.instructionPC 3256 = 0x1445 := by rfl
@[simp] theorem pc2925 : Artifact.submissionArtifact.instructionPC 3257 = 0x1446 := by rfl
@[simp] theorem pc2926 : Artifact.submissionArtifact.instructionPC 3258 = 0x1447 := by rfl
@[simp] theorem pc2927 : Artifact.submissionArtifact.instructionPC 3259 = 0x1448 := by rfl
@[simp] theorem pc2928 : Artifact.submissionArtifact.instructionPC 3260 = 0x1449 := by rfl
@[simp] theorem pc2929 : Artifact.submissionArtifact.instructionPC 3261 = 0x144a := by rfl
@[simp] theorem pc2930 : Artifact.submissionArtifact.instructionPC 3262 = 0x144b := by rfl
@[simp] theorem pc2931 : Artifact.submissionArtifact.instructionPC 3263 = 0x144d := by rfl
@[simp] theorem pc2932 : Artifact.submissionArtifact.instructionPC 3264 = 0x144e := by rfl
@[simp] theorem pc2933 : Artifact.submissionArtifact.instructionPC 3265 = 0x1450 := by rfl
@[simp] theorem pc2934 : Artifact.submissionArtifact.instructionPC 3266 = 0x1451 := by rfl
@[simp] theorem pc2935 : Artifact.submissionArtifact.instructionPC 3267 = 0x1454 := by rfl
@[simp] theorem pc2936 : Artifact.submissionArtifact.instructionPC 3268 = 0x1455 := by rfl
@[simp] theorem pc2937 : Artifact.submissionArtifact.instructionPC 3269 = 0x1456 := by rfl
@[simp] theorem pc2938 : Artifact.submissionArtifact.instructionPC 3270 = 0x1457 := by rfl
@[simp] theorem pc2939 : Artifact.submissionArtifact.instructionPC 3271 = 0x1458 := by rfl
@[simp] theorem pc2940 : Artifact.submissionArtifact.instructionPC 3272 = 0x1459 := by rfl
@[simp] theorem pc2941 : Artifact.submissionArtifact.instructionPC 3273 = 0x145a := by rfl
@[simp] theorem pc2942 : Artifact.submissionArtifact.instructionPC 3274 = 0x145b := by rfl
@[simp] theorem pc2943 : Artifact.submissionArtifact.instructionPC 3275 = 0x145c := by rfl
@[simp] theorem pc2944 : Artifact.submissionArtifact.instructionPC 3276 = 0x145d := by rfl
@[simp] theorem pc2945 : Artifact.submissionArtifact.instructionPC 3277 = 0x145e := by rfl
@[simp] theorem pc2946 : Artifact.submissionArtifact.instructionPC 3278 = 0x145f := by rfl
@[simp] theorem pc2947 : Artifact.submissionArtifact.instructionPC 3279 = 0x1461 := by rfl
@[simp] theorem pc2948 : Artifact.submissionArtifact.instructionPC 3280 = 0x1462 := by rfl
@[simp] theorem pc2949 : Artifact.submissionArtifact.instructionPC 3281 = 0x1464 := by rfl
@[simp] theorem pc2950 : Artifact.submissionArtifact.instructionPC 3282 = 0x1465 := by rfl
@[simp] theorem pc2951 : Artifact.submissionArtifact.instructionPC 3283 = 0x1466 := by rfl
@[simp] theorem pc2952 : Artifact.submissionArtifact.instructionPC 3284 = 0x1467 := by rfl
@[simp] theorem pc2953 : Artifact.submissionArtifact.instructionPC 3285 = 0x1468 := by rfl
@[simp] theorem pc2954 : Artifact.submissionArtifact.instructionPC 3286 = 0x146a := by rfl
@[simp] theorem pc2955 : Artifact.submissionArtifact.instructionPC 3287 = 0x146b := by rfl
@[simp] theorem pc2956 : Artifact.submissionArtifact.instructionPC 3288 = 0x146c := by rfl
@[simp] theorem pc2957 : Artifact.submissionArtifact.instructionPC 3289 = 0x146d := by rfl
@[simp] theorem pc2958 : Artifact.submissionArtifact.instructionPC 3290 = 0x146e := by rfl
@[simp] theorem pc2959 : Artifact.submissionArtifact.instructionPC 3291 = 0x1471 := by rfl
@[simp] theorem pc2960 : Artifact.submissionArtifact.instructionPC 3292 = 0x1472 := by rfl
@[simp] theorem pc2961 : Artifact.submissionArtifact.instructionPC 3293 = 0x1475 := by rfl
@[simp] theorem pc2962 : Artifact.submissionArtifact.instructionPC 3294 = 0x1476 := by rfl
@[simp] theorem pc2963 : Artifact.submissionArtifact.instructionPC 3295 = 0x1479 := by rfl
@[simp] theorem pc2964 : Artifact.submissionArtifact.instructionPC 3296 = 0x147a := by rfl
@[simp] theorem pc2965 : Artifact.submissionArtifact.instructionPC 3297 = 0x1483 := by rfl
@[simp] theorem pc2966 : Artifact.submissionArtifact.instructionPC 3298 = 0x1485 := by rfl
@[simp] theorem pc2967 : Artifact.submissionArtifact.instructionPC 3299 = 0x1486 := by rfl
@[simp] theorem pc2968 : Artifact.submissionArtifact.instructionPC 3300 = 0x1487 := by rfl
@[simp] theorem pc2969 : Artifact.submissionArtifact.instructionPC 3301 = 0x1488 := by rfl
@[simp] theorem pc2970 : Artifact.submissionArtifact.instructionPC 3302 = 0x1489 := by rfl
@[simp] theorem pc2971 : Artifact.submissionArtifact.instructionPC 3303 = 0x148a := by rfl
@[simp] theorem pc2972 : Artifact.submissionArtifact.instructionPC 3304 = 0x148b := by rfl
@[simp] theorem pc2973 : Artifact.submissionArtifact.instructionPC 3305 = 0x148c := by rfl
@[simp] theorem pc2974 : Artifact.submissionArtifact.instructionPC 3306 = 0x148d := by rfl
@[simp] theorem pc2975 : Artifact.submissionArtifact.instructionPC 3307 = 0x148e := by rfl
@[simp] theorem pc2976 : Artifact.submissionArtifact.instructionPC 3308 = 0x148f := by rfl
@[simp] theorem pc2977 : Artifact.submissionArtifact.instructionPC 3309 = 0x1490 := by rfl
@[simp] theorem pc2978 : Artifact.submissionArtifact.instructionPC 3310 = 0x1491 := by rfl
@[simp] theorem pc2979 : Artifact.submissionArtifact.instructionPC 3311 = 0x1492 := by rfl
@[simp] theorem pc2980 : Artifact.submissionArtifact.instructionPC 3312 = 0x1493 := by rfl
@[simp] theorem pc2981 : Artifact.submissionArtifact.instructionPC 3313 = 0x1494 := by rfl
@[simp] theorem pc2982 : Artifact.submissionArtifact.instructionPC 3314 = 0x1497 := by rfl
@[simp] theorem pc2983 : Artifact.submissionArtifact.instructionPC 3315 = 0x1498 := by rfl
@[simp] theorem pc2984 : Artifact.submissionArtifact.instructionPC 3316 = 0x14ad := by rfl
@[simp] theorem pc2985 : Artifact.submissionArtifact.instructionPC 3317 = 0x14ae := by rfl
@[simp] theorem pc2986 : Artifact.submissionArtifact.instructionPC 3318 = 0x14af := by rfl
@[simp] theorem pc2987 : Artifact.submissionArtifact.instructionPC 3319 = 0x14b1 := by rfl
@[simp] theorem pc2988 : Artifact.submissionArtifact.instructionPC 3320 = 0x14b2 := by rfl
@[simp] theorem pc2989 : Artifact.submissionArtifact.instructionPC 3321 = 0x14b3 := by rfl
@[simp] theorem pc2990 : Artifact.submissionArtifact.instructionPC 3322 = 0x14b4 := by rfl
@[simp] theorem pc2991 : Artifact.submissionArtifact.instructionPC 3323 = 0x14b5 := by rfl
@[simp] theorem pc2992 : Artifact.submissionArtifact.instructionPC 3324 = 0x14b6 := by rfl
@[simp] theorem pc2993 : Artifact.submissionArtifact.instructionPC 3325 = 0x14b8 := by rfl
@[simp] theorem pc2994 : Artifact.submissionArtifact.instructionPC 3326 = 0x14b9 := by rfl
@[simp] theorem pc2995 : Artifact.submissionArtifact.instructionPC 3327 = 0x14bb := by rfl
@[simp] theorem pc2996 : Artifact.submissionArtifact.instructionPC 3328 = 0x14bc := by rfl
@[simp] theorem pc2997 : Artifact.submissionArtifact.instructionPC 3329 = 0x14be := by rfl
@[simp] theorem pc2998 : Artifact.submissionArtifact.instructionPC 3330 = 0x14bf := by rfl
@[simp] theorem pc2999 : Artifact.submissionArtifact.instructionPC 3331 = 0x14c1 := by rfl
@[simp] theorem pc3000 : Artifact.submissionArtifact.instructionPC 3332 = 0x14c2 := by rfl
@[simp] theorem pc3001 : Artifact.submissionArtifact.instructionPC 3333 = 0x14c3 := by rfl
@[simp] theorem pc3002 : Artifact.submissionArtifact.instructionPC 3334 = 0x14c5 := by rfl
@[simp] theorem pc3003 : Artifact.submissionArtifact.instructionPC 3335 = 0x14c6 := by rfl
@[simp] theorem pc3004 : Artifact.submissionArtifact.instructionPC 3336 = 0x14c7 := by rfl
@[simp] theorem pc3005 : Artifact.submissionArtifact.instructionPC 3337 = 0x14c8 := by rfl
@[simp] theorem pc3006 : Artifact.submissionArtifact.instructionPC 3338 = 0x14c9 := by rfl
@[simp] theorem pc3007 : Artifact.submissionArtifact.instructionPC 3339 = 0x14ca := by rfl
@[simp] theorem pc3008 : Artifact.submissionArtifact.instructionPC 3340 = 0x14cb := by rfl
@[simp] theorem pc3009 : Artifact.submissionArtifact.instructionPC 3341 = 0x14cc := by rfl
@[simp] theorem pc3010 : Artifact.submissionArtifact.instructionPC 3342 = 0x14cd := by rfl
@[simp] theorem pc3011 : Artifact.submissionArtifact.instructionPC 3343 = 0x14ce := by rfl
@[simp] theorem pc3012 : Artifact.submissionArtifact.instructionPC 3344 = 0x14cf := by rfl
@[simp] theorem pc3013 : Artifact.submissionArtifact.instructionPC 3345 = 0x14d0 := by rfl
@[simp] theorem pc3014 : Artifact.submissionArtifact.instructionPC 3346 = 0x14d1 := by rfl
@[simp] theorem pc3015 : Artifact.submissionArtifact.instructionPC 3347 = 0x14d2 := by rfl
@[simp] theorem pc3016 : Artifact.submissionArtifact.instructionPC 3348 = 0x14d3 := by rfl
@[simp] theorem pc3017 : Artifact.submissionArtifact.instructionPC 3349 = 0x14d5 := by rfl
@[simp] theorem pc3018 : Artifact.submissionArtifact.instructionPC 3350 = 0x14d6 := by rfl
@[simp] theorem pc3019 : Artifact.submissionArtifact.instructionPC 3351 = 0x14d7 := by rfl
@[simp] theorem pc3020 : Artifact.submissionArtifact.instructionPC 3352 = 0x14d8 := by rfl
@[simp] theorem pc3021 : Artifact.submissionArtifact.instructionPC 3353 = 0x14db := by rfl
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan
