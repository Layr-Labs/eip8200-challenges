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
  [opAt 3127 .JUMPDEST,
   pushAt 3128 32 58123087930888129467517984631811969432229639361576439988433610796128943505536,
   pushAt 3129 32 3244493450063667868678674439968361782956185527883176199882357678282131398018,
   pushAt 3130 32 57669001306428065956053000376875938421040345304064124051023973211784186134399,
   pushAt 3131 32 454086624460063511464984254936031011189294057512315937409637584344757371137,
   opAt 3132 (.Dup ⟨2, by decide⟩), opAt 3133 (.Dup ⟨2, by decide⟩),
   opAt 3134 .AND, pushAt 3135 0 0, pushAt 3136 0 0, pushAt 3137 0 0]

/-- Derive the expected word and test for a straddler. -/
def wordPath : List Located :=
  [opAt 3138 .JUMPDEST, opAt 3139 (.Dup ⟨0, by decide⟩),
   opAt 3140 (.Dup ⟨5, by decide⟩), opAt 3141 .MUL,
   opAt 3142 (.Dup ⟨0, by decide⟩), opAt 3143 (.Dup ⟨7, by decide⟩),
   opAt 3144 .AND, opAt 3145 (.Dup ⟨5, by decide⟩), opAt 3146 .ADD,
   opAt 3147 (.Dup ⟨1, by decide⟩), opAt 3148 (.Dup ⟨9, by decide⟩),
   opAt 3149 .XOR, opAt 3150 (.Dup ⟨10, by decide⟩), opAt 3151 .AND,
   opAt 3152 .XOR, opAt 3153 (.Dup ⟨3, by decide⟩), pushAt 3154 1 255,
   opAt 3155 .AND, pushAt 3156 1 224, opAt 3157 .EQ, pushAt 3158 2 5288,
   opAt 3159 .JUMPI]

/-- Fold one word into the accumulator and advance. -/
def comparePath : List Located :=
  [opAt 3160 .JUMPDEST, opAt 3161 (.Dup ⟨3, by decide⟩),
   opAt 3162 .CALLDATALOAD, opAt 3163 .XOR, opAt 3164 (.Dup ⟨4, by decide⟩),
   opAt 3165 .OR, opAt 3166 (.Swap ⟨3, by decide⟩), opAt 3167 .POP,
   opAt 3168 .POP, opAt 3169 .JUMPDEST, pushAt 3170 1 160,
   opAt 3171 .ADD, pushAt 3172 1 255, opAt 3173 .AND,
   opAt 3174 .JUMPDEST, opAt 3175 .JUMPDEST,
   opAt 3176 (.Swap ⟨0, by decide⟩), pushAt 3177 1 32, opAt 3178 .ADD,
   opAt 3179 (.Swap ⟨0, by decide⟩), opAt 3180 .JUMPDEST,
   opAt 3181 (.Dup ⟨1, by decide⟩), pushAt 3182 2 992, opAt 3183 .GT,
   pushAt 3184 2 5168, opAt 3185 .JUMPI]

/-- The padded tail word, the cleanup and the miss test. -/
def tailPath : List Located :=
  [pushAt 3186 2 992, opAt 3187 .CALLDATALOAD,
   pushAt 3188 8 9848759918901945995, pushAt 3189 1 192, opAt 3190 .SHL,
   opAt 3191 .XOR, opAt 3192 (.Dup ⟨3, by decide⟩), opAt 3193 .OR,
   opAt 3194 (.Swap ⟨2, by decide⟩), opAt 3195 .POP,
   opAt 3196 (.Swap ⟨1, by decide⟩), opAt 3197 (.Swap ⟨6, by decide⟩),
   opAt 3198 .POP, opAt 3199 .POP, opAt 3200 .POP, opAt 3201 .POP,
   opAt 3202 .POP, opAt 3203 .POP, opAt 3204 .POP, pushAt 3205 2 1011,
   opAt 3206 .JUMPI]

/-- Store and return the stored digest. -/
def returnPath : List Located :=
  [pushAt 3207 20 766350606435067737561421097975693824639675460820,
   pushAt 3208 0 0, opAt 3209 .MSTORE, pushAt 3210 1 32, pushAt 3211 0 0,
   opAt 3212 .RETURN]

/-- Shift the correction constant out of `M`. -/
def straddleCorrPath : List Located :=
  [opAt 3213 .JUMPDEST, opAt 3214 (.Dup ⟨6, by decide⟩),
   opAt 3215 (.Dup ⟨4, by decide⟩), pushAt 3216 1 8, opAt 3217 .SHR,
   pushAt 3218 1 5, opAt 3219 .MUL, pushAt 3220 1 27, opAt 3221 .SUB,
   pushAt 3222 1 8, opAt 3223 .MUL, opAt 3224 .SHR, pushAt 3225 1 11,
   opAt 3226 .MUL]

/-- Apply the correction to the expected word. -/
def straddleAddPath : List Located :=
  [opAt 3227 (.Dup ⟨1, by decide⟩), opAt 3228 (.Dup ⟨9, by decide⟩),
   opAt 3229 .AND, opAt 3230 (.Dup ⟨1, by decide⟩), opAt 3231 .ADD,
   opAt 3232 (.Dup ⟨2, by decide⟩), opAt 3233 (.Dup ⟨12, by decide⟩),
   opAt 3234 .AND, opAt 3235 .XOR, opAt 3236 (.Swap ⟨1, by decide⟩),
   opAt 3237 .POP, opAt 3238 .POP]

/-- Bump the scalar and rejoin the scan. -/
def straddleBackPath : List Located :=
  [opAt 3239 (.Dup ⟨2, by decide⟩), pushAt 3240 1 11, opAt 3241 .ADD,
   opAt 3242 (.Swap ⟨2, by decide⟩), opAt 3243 .POP, pushAt 3244 2 5194,
   opAt 3245 .JUMP]


@[simp] theorem pc2903 : Artifact.submissionArtifact.instructionPC 3127 = 0x13a5 := by rfl
@[simp] theorem pc2904 : Artifact.submissionArtifact.instructionPC 3128 = 0x13a6 := by rfl
@[simp] theorem pc2905 : Artifact.submissionArtifact.instructionPC 3129 = 0x13c7 := by rfl
@[simp] theorem pc2906 : Artifact.submissionArtifact.instructionPC 3130 = 0x13e8 := by rfl
@[simp] theorem pc2907 : Artifact.submissionArtifact.instructionPC 3131 = 0x1409 := by rfl
@[simp] theorem pc2908 : Artifact.submissionArtifact.instructionPC 3132 = 0x142a := by rfl
@[simp] theorem pc2909 : Artifact.submissionArtifact.instructionPC 3133 = 0x142b := by rfl
@[simp] theorem pc2910 : Artifact.submissionArtifact.instructionPC 3134 = 0x142c := by rfl
@[simp] theorem pc2911 : Artifact.submissionArtifact.instructionPC 3135 = 0x142d := by rfl
@[simp] theorem pc2912 : Artifact.submissionArtifact.instructionPC 3136 = 0x142e := by rfl
@[simp] theorem pc2913 : Artifact.submissionArtifact.instructionPC 3137 = 0x142f := by rfl
@[simp] theorem pc2914 : Artifact.submissionArtifact.instructionPC 3138 = 0x1430 := by rfl
@[simp] theorem pc2915 : Artifact.submissionArtifact.instructionPC 3139 = 0x1431 := by rfl
@[simp] theorem pc2916 : Artifact.submissionArtifact.instructionPC 3140 = 0x1432 := by rfl
@[simp] theorem pc2917 : Artifact.submissionArtifact.instructionPC 3141 = 0x1433 := by rfl
@[simp] theorem pc2918 : Artifact.submissionArtifact.instructionPC 3142 = 0x1434 := by rfl
@[simp] theorem pc2919 : Artifact.submissionArtifact.instructionPC 3143 = 0x1435 := by rfl
@[simp] theorem pc2920 : Artifact.submissionArtifact.instructionPC 3144 = 0x1436 := by rfl
@[simp] theorem pc2921 : Artifact.submissionArtifact.instructionPC 3145 = 0x1437 := by rfl
@[simp] theorem pc2922 : Artifact.submissionArtifact.instructionPC 3146 = 0x1438 := by rfl
@[simp] theorem pc2923 : Artifact.submissionArtifact.instructionPC 3147 = 0x1439 := by rfl
@[simp] theorem pc2924 : Artifact.submissionArtifact.instructionPC 3148 = 0x143a := by rfl
@[simp] theorem pc2925 : Artifact.submissionArtifact.instructionPC 3149 = 0x143b := by rfl
@[simp] theorem pc2926 : Artifact.submissionArtifact.instructionPC 3150 = 0x143c := by rfl
@[simp] theorem pc2927 : Artifact.submissionArtifact.instructionPC 3151 = 0x143d := by rfl
@[simp] theorem pc2928 : Artifact.submissionArtifact.instructionPC 3152 = 0x143e := by rfl
@[simp] theorem pc2929 : Artifact.submissionArtifact.instructionPC 3153 = 0x143f := by rfl
@[simp] theorem pc2930 : Artifact.submissionArtifact.instructionPC 3154 = 0x1440 := by rfl
@[simp] theorem pc2931 : Artifact.submissionArtifact.instructionPC 3155 = 0x1442 := by rfl
@[simp] theorem pc2932 : Artifact.submissionArtifact.instructionPC 3156 = 0x1443 := by rfl
@[simp] theorem pc2933 : Artifact.submissionArtifact.instructionPC 3157 = 0x1445 := by rfl
@[simp] theorem pc2934 : Artifact.submissionArtifact.instructionPC 3158 = 0x1446 := by rfl
@[simp] theorem pc2935 : Artifact.submissionArtifact.instructionPC 3159 = 0x1449 := by rfl
@[simp] theorem pc2936 : Artifact.submissionArtifact.instructionPC 3160 = 0x144a := by rfl
@[simp] theorem pc2937 : Artifact.submissionArtifact.instructionPC 3161 = 0x144b := by rfl
@[simp] theorem pc2938 : Artifact.submissionArtifact.instructionPC 3162 = 0x144c := by rfl
@[simp] theorem pc2939 : Artifact.submissionArtifact.instructionPC 3163 = 0x144d := by rfl
@[simp] theorem pc2940 : Artifact.submissionArtifact.instructionPC 3164 = 0x144e := by rfl
@[simp] theorem pc2941 : Artifact.submissionArtifact.instructionPC 3165 = 0x144f := by rfl
@[simp] theorem pc2942 : Artifact.submissionArtifact.instructionPC 3166 = 0x1450 := by rfl
@[simp] theorem pc2943 : Artifact.submissionArtifact.instructionPC 3167 = 0x1451 := by rfl
@[simp] theorem pc2944 : Artifact.submissionArtifact.instructionPC 3168 = 0x1452 := by rfl
@[simp] theorem pc2945 : Artifact.submissionArtifact.instructionPC 3169 = 0x1453 := by rfl
@[simp] theorem pc2946 : Artifact.submissionArtifact.instructionPC 3170 = 0x1454 := by rfl
@[simp] theorem pc2947 : Artifact.submissionArtifact.instructionPC 3171 = 0x1456 := by rfl
@[simp] theorem pc2948 : Artifact.submissionArtifact.instructionPC 3172 = 0x1457 := by rfl
@[simp] theorem pc2949 : Artifact.submissionArtifact.instructionPC 3173 = 0x1459 := by rfl
@[simp] theorem pc2950 : Artifact.submissionArtifact.instructionPC 3174 = 0x145a := by rfl
@[simp] theorem pc2951 : Artifact.submissionArtifact.instructionPC 3175 = 0x145b := by rfl
@[simp] theorem pc2952 : Artifact.submissionArtifact.instructionPC 3176 = 0x145c := by rfl
@[simp] theorem pc2953 : Artifact.submissionArtifact.instructionPC 3177 = 0x145d := by rfl
@[simp] theorem pc2954 : Artifact.submissionArtifact.instructionPC 3178 = 0x145f := by rfl
@[simp] theorem pc2955 : Artifact.submissionArtifact.instructionPC 3179 = 0x1460 := by rfl
@[simp] theorem pc2956 : Artifact.submissionArtifact.instructionPC 3180 = 0x1461 := by rfl
@[simp] theorem pc2957 : Artifact.submissionArtifact.instructionPC 3181 = 0x1462 := by rfl
@[simp] theorem pc2958 : Artifact.submissionArtifact.instructionPC 3182 = 0x1463 := by rfl
@[simp] theorem pc2959 : Artifact.submissionArtifact.instructionPC 3183 = 0x1466 := by rfl
@[simp] theorem pc2960 : Artifact.submissionArtifact.instructionPC 3184 = 0x1467 := by rfl
@[simp] theorem pc2961 : Artifact.submissionArtifact.instructionPC 3185 = 0x146a := by rfl
@[simp] theorem pc2962 : Artifact.submissionArtifact.instructionPC 3186 = 0x146b := by rfl
@[simp] theorem pc2963 : Artifact.submissionArtifact.instructionPC 3187 = 0x146e := by rfl
@[simp] theorem pc2964 : Artifact.submissionArtifact.instructionPC 3188 = 0x146f := by rfl
@[simp] theorem pc2965 : Artifact.submissionArtifact.instructionPC 3189 = 0x1478 := by rfl
@[simp] theorem pc2966 : Artifact.submissionArtifact.instructionPC 3190 = 0x147a := by rfl
@[simp] theorem pc2967 : Artifact.submissionArtifact.instructionPC 3191 = 0x147b := by rfl
@[simp] theorem pc2968 : Artifact.submissionArtifact.instructionPC 3192 = 0x147c := by rfl
@[simp] theorem pc2969 : Artifact.submissionArtifact.instructionPC 3193 = 0x147d := by rfl
@[simp] theorem pc2970 : Artifact.submissionArtifact.instructionPC 3194 = 0x147e := by rfl
@[simp] theorem pc2971 : Artifact.submissionArtifact.instructionPC 3195 = 0x147f := by rfl
@[simp] theorem pc2972 : Artifact.submissionArtifact.instructionPC 3196 = 0x1480 := by rfl
@[simp] theorem pc2973 : Artifact.submissionArtifact.instructionPC 3197 = 0x1481 := by rfl
@[simp] theorem pc2974 : Artifact.submissionArtifact.instructionPC 3198 = 0x1482 := by rfl
@[simp] theorem pc2975 : Artifact.submissionArtifact.instructionPC 3199 = 0x1483 := by rfl
@[simp] theorem pc2976 : Artifact.submissionArtifact.instructionPC 3200 = 0x1484 := by rfl
@[simp] theorem pc2977 : Artifact.submissionArtifact.instructionPC 3201 = 0x1485 := by rfl
@[simp] theorem pc2978 : Artifact.submissionArtifact.instructionPC 3202 = 0x1486 := by rfl
@[simp] theorem pc2979 : Artifact.submissionArtifact.instructionPC 3203 = 0x1487 := by rfl
@[simp] theorem pc2980 : Artifact.submissionArtifact.instructionPC 3204 = 0x1488 := by rfl
@[simp] theorem pc2981 : Artifact.submissionArtifact.instructionPC 3205 = 0x1489 := by rfl
@[simp] theorem pc2982 : Artifact.submissionArtifact.instructionPC 3206 = 0x148c := by rfl
@[simp] theorem pc2983 : Artifact.submissionArtifact.instructionPC 3207 = 0x148d := by rfl
@[simp] theorem pc2984 : Artifact.submissionArtifact.instructionPC 3208 = 0x14a2 := by rfl
@[simp] theorem pc2985 : Artifact.submissionArtifact.instructionPC 3209 = 0x14a3 := by rfl
@[simp] theorem pc2986 : Artifact.submissionArtifact.instructionPC 3210 = 0x14a4 := by rfl
@[simp] theorem pc2987 : Artifact.submissionArtifact.instructionPC 3211 = 0x14a6 := by rfl
@[simp] theorem pc2988 : Artifact.submissionArtifact.instructionPC 3212 = 0x14a7 := by rfl
@[simp] theorem pc2989 : Artifact.submissionArtifact.instructionPC 3213 = 0x14a8 := by rfl
@[simp] theorem pc2990 : Artifact.submissionArtifact.instructionPC 3214 = 0x14a9 := by rfl
@[simp] theorem pc2991 : Artifact.submissionArtifact.instructionPC 3215 = 0x14aa := by rfl
@[simp] theorem pc2992 : Artifact.submissionArtifact.instructionPC 3216 = 0x14ab := by rfl
@[simp] theorem pc2993 : Artifact.submissionArtifact.instructionPC 3217 = 0x14ad := by rfl
@[simp] theorem pc2994 : Artifact.submissionArtifact.instructionPC 3218 = 0x14ae := by rfl
@[simp] theorem pc2995 : Artifact.submissionArtifact.instructionPC 3219 = 0x14b0 := by rfl
@[simp] theorem pc2996 : Artifact.submissionArtifact.instructionPC 3220 = 0x14b1 := by rfl
@[simp] theorem pc2997 : Artifact.submissionArtifact.instructionPC 3221 = 0x14b3 := by rfl
@[simp] theorem pc2998 : Artifact.submissionArtifact.instructionPC 3222 = 0x14b4 := by rfl
@[simp] theorem pc2999 : Artifact.submissionArtifact.instructionPC 3223 = 0x14b6 := by rfl
@[simp] theorem pc3000 : Artifact.submissionArtifact.instructionPC 3224 = 0x14b7 := by rfl
@[simp] theorem pc3001 : Artifact.submissionArtifact.instructionPC 3225 = 0x14b8 := by rfl
@[simp] theorem pc3002 : Artifact.submissionArtifact.instructionPC 3226 = 0x14ba := by rfl
@[simp] theorem pc3003 : Artifact.submissionArtifact.instructionPC 3227 = 0x14bb := by rfl
@[simp] theorem pc3004 : Artifact.submissionArtifact.instructionPC 3228 = 0x14bc := by rfl
@[simp] theorem pc3005 : Artifact.submissionArtifact.instructionPC 3229 = 0x14bd := by rfl
@[simp] theorem pc3006 : Artifact.submissionArtifact.instructionPC 3230 = 0x14be := by rfl
@[simp] theorem pc3007 : Artifact.submissionArtifact.instructionPC 3231 = 0x14bf := by rfl
@[simp] theorem pc3008 : Artifact.submissionArtifact.instructionPC 3232 = 0x14c0 := by rfl
@[simp] theorem pc3009 : Artifact.submissionArtifact.instructionPC 3233 = 0x14c1 := by rfl
@[simp] theorem pc3010 : Artifact.submissionArtifact.instructionPC 3234 = 0x14c2 := by rfl
@[simp] theorem pc3011 : Artifact.submissionArtifact.instructionPC 3235 = 0x14c3 := by rfl
@[simp] theorem pc3012 : Artifact.submissionArtifact.instructionPC 3236 = 0x14c4 := by rfl
@[simp] theorem pc3013 : Artifact.submissionArtifact.instructionPC 3237 = 0x14c5 := by rfl
@[simp] theorem pc3014 : Artifact.submissionArtifact.instructionPC 3238 = 0x14c6 := by rfl
@[simp] theorem pc3015 : Artifact.submissionArtifact.instructionPC 3239 = 0x14c7 := by rfl
@[simp] theorem pc3016 : Artifact.submissionArtifact.instructionPC 3240 = 0x14c8 := by rfl
@[simp] theorem pc3017 : Artifact.submissionArtifact.instructionPC 3241 = 0x14ca := by rfl
@[simp] theorem pc3018 : Artifact.submissionArtifact.instructionPC 3242 = 0x14cb := by rfl
@[simp] theorem pc3019 : Artifact.submissionArtifact.instructionPC 3243 = 0x14cc := by rfl
@[simp] theorem pc3020 : Artifact.submissionArtifact.instructionPC 3244 = 0x14cd := by rfl
@[simp] theorem pc3021 : Artifact.submissionArtifact.instructionPC 3245 = 0x14d0 := by rfl
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan
