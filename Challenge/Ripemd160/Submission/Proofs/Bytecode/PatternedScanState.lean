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
  [opAt 3027 .JUMPDEST,
   pushAt 3028 32 58123087930888129467517984631811969432229639361576439988433610796128943505536,
   pushAt 3029 32 3244493450063667868678674439968361782956185527883176199882357678282131398018,
   pushAt 3030 32 57669001306428065956053000376875938421040345304064124051023973211784186134399,
   pushAt 3031 32 454086624460063511464984254936031011189294057512315937409637584344757371137,
   opAt 3032 (.Dup ⟨2, by decide⟩), opAt 3033 (.Dup ⟨2, by decide⟩),
   opAt 3034 .AND, pushAt 3035 0 0, pushAt 3036 0 0, pushAt 3037 0 0]

/-- Derive the expected word and test for a straddler. -/
def wordPath : List Located :=
  [opAt 3038 .JUMPDEST, opAt 3039 (.Dup ⟨0, by decide⟩),
   opAt 3040 (.Dup ⟨5, by decide⟩), opAt 3041 .MUL,
   opAt 3042 (.Dup ⟨0, by decide⟩), opAt 3043 (.Dup ⟨7, by decide⟩),
   opAt 3044 .AND, opAt 3045 (.Dup ⟨5, by decide⟩), opAt 3046 .ADD,
   opAt 3047 (.Dup ⟨1, by decide⟩), opAt 3048 (.Dup ⟨9, by decide⟩),
   opAt 3049 .XOR, opAt 3050 (.Dup ⟨10, by decide⟩), opAt 3051 .AND,
   opAt 3052 .XOR, opAt 3053 (.Dup ⟨3, by decide⟩), pushAt 3054 1 255,
   opAt 3055 .AND, pushAt 3056 1 224, opAt 3057 .EQ, pushAt 3058 2 5192,
   opAt 3059 .JUMPI]

/-- Fold one word into the accumulator and advance. -/
def comparePath : List Located :=
  [opAt 3060 .JUMPDEST, opAt 3061 (.Dup ⟨3, by decide⟩),
   opAt 3062 .CALLDATALOAD, opAt 3063 .XOR, opAt 3064 (.Dup ⟨4, by decide⟩),
   opAt 3065 .OR, opAt 3066 (.Swap ⟨3, by decide⟩), opAt 3067 .POP,
   opAt 3068 .POP, opAt 3069 .JUMPDEST, pushAt 3070 1 160,
   opAt 3071 .ADD, pushAt 3072 1 255, opAt 3073 .AND,
   opAt 3074 .JUMPDEST, opAt 3075 .JUMPDEST,
   opAt 3076 (.Swap ⟨0, by decide⟩), pushAt 3077 1 32, opAt 3078 .ADD,
   opAt 3079 (.Swap ⟨0, by decide⟩), opAt 3080 .JUMPDEST,
   opAt 3081 (.Dup ⟨1, by decide⟩), pushAt 3082 2 992, opAt 3083 .GT,
   pushAt 3084 2 5072, opAt 3085 .JUMPI]

/-- The padded tail word, the cleanup and the miss test. -/
def tailPath : List Located :=
  [pushAt 3086 2 992, opAt 3087 .CALLDATALOAD,
   pushAt 3088 8 9848759918901945995, pushAt 3089 1 192, opAt 3090 .SHL,
   opAt 3091 .XOR, opAt 3092 (.Dup ⟨3, by decide⟩), opAt 3093 .OR,
   opAt 3094 (.Swap ⟨2, by decide⟩), opAt 3095 .POP,
   opAt 3096 (.Swap ⟨1, by decide⟩), opAt 3097 (.Swap ⟨6, by decide⟩),
   opAt 3098 .POP, opAt 3099 .POP, opAt 3100 .POP, opAt 3101 .POP,
   opAt 3102 .POP, opAt 3103 .POP, opAt 3104 .POP, pushAt 3105 2 1011,
   opAt 3106 .JUMPI]

/-- Store and return the stored digest. -/
def returnPath : List Located :=
  [pushAt 3107 20 766350606435067737561421097975693824639675460820,
   pushAt 3108 0 0, opAt 3109 .MSTORE, pushAt 3110 1 32, pushAt 3111 0 0,
   opAt 3112 .RETURN]

/-- Shift the correction constant out of `M`. -/
def straddleCorrPath : List Located :=
  [opAt 3113 .JUMPDEST, opAt 3114 (.Dup ⟨6, by decide⟩),
   opAt 3115 (.Dup ⟨4, by decide⟩), pushAt 3116 1 8, opAt 3117 .SHR,
   pushAt 3118 1 5, opAt 3119 .MUL, pushAt 3120 1 27, opAt 3121 .SUB,
   pushAt 3122 1 8, opAt 3123 .MUL, opAt 3124 .SHR, pushAt 3125 1 11,
   opAt 3126 .MUL]

/-- Apply the correction to the expected word. -/
def straddleAddPath : List Located :=
  [opAt 3127 (.Dup ⟨1, by decide⟩), opAt 3128 (.Dup ⟨9, by decide⟩),
   opAt 3129 .AND, opAt 3130 (.Dup ⟨1, by decide⟩), opAt 3131 .ADD,
   opAt 3132 (.Dup ⟨2, by decide⟩), opAt 3133 (.Dup ⟨12, by decide⟩),
   opAt 3134 .AND, opAt 3135 .XOR, opAt 3136 (.Swap ⟨1, by decide⟩),
   opAt 3137 .POP, opAt 3138 .POP]

/-- Bump the scalar and rejoin the scan. -/
def straddleBackPath : List Located :=
  [opAt 3139 (.Dup ⟨2, by decide⟩), pushAt 3140 1 11, opAt 3141 .ADD,
   opAt 3142 (.Swap ⟨2, by decide⟩), opAt 3143 .POP, pushAt 3144 2 5098,
   opAt 3145 .JUMP]


@[simp] theorem pc2903 : Artifact.submissionArtifact.instructionPC 3027 = 0x1345 := by rfl
@[simp] theorem pc2904 : Artifact.submissionArtifact.instructionPC 3028 = 0x1346 := by rfl
@[simp] theorem pc2905 : Artifact.submissionArtifact.instructionPC 3029 = 0x1367 := by rfl
@[simp] theorem pc2906 : Artifact.submissionArtifact.instructionPC 3030 = 0x1388 := by rfl
@[simp] theorem pc2907 : Artifact.submissionArtifact.instructionPC 3031 = 0x13a9 := by rfl
@[simp] theorem pc2908 : Artifact.submissionArtifact.instructionPC 3032 = 0x13ca := by rfl
@[simp] theorem pc2909 : Artifact.submissionArtifact.instructionPC 3033 = 0x13cb := by rfl
@[simp] theorem pc2910 : Artifact.submissionArtifact.instructionPC 3034 = 0x13cc := by rfl
@[simp] theorem pc2911 : Artifact.submissionArtifact.instructionPC 3035 = 0x13cd := by rfl
@[simp] theorem pc2912 : Artifact.submissionArtifact.instructionPC 3036 = 0x13ce := by rfl
@[simp] theorem pc2913 : Artifact.submissionArtifact.instructionPC 3037 = 0x13cf := by rfl
@[simp] theorem pc2914 : Artifact.submissionArtifact.instructionPC 3038 = 0x13d0 := by rfl
@[simp] theorem pc2915 : Artifact.submissionArtifact.instructionPC 3039 = 0x13d1 := by rfl
@[simp] theorem pc2916 : Artifact.submissionArtifact.instructionPC 3040 = 0x13d2 := by rfl
@[simp] theorem pc2917 : Artifact.submissionArtifact.instructionPC 3041 = 0x13d3 := by rfl
@[simp] theorem pc2918 : Artifact.submissionArtifact.instructionPC 3042 = 0x13d4 := by rfl
@[simp] theorem pc2919 : Artifact.submissionArtifact.instructionPC 3043 = 0x13d5 := by rfl
@[simp] theorem pc2920 : Artifact.submissionArtifact.instructionPC 3044 = 0x13d6 := by rfl
@[simp] theorem pc2921 : Artifact.submissionArtifact.instructionPC 3045 = 0x13d7 := by rfl
@[simp] theorem pc2922 : Artifact.submissionArtifact.instructionPC 3046 = 0x13d8 := by rfl
@[simp] theorem pc2923 : Artifact.submissionArtifact.instructionPC 3047 = 0x13d9 := by rfl
@[simp] theorem pc2924 : Artifact.submissionArtifact.instructionPC 3048 = 0x13da := by rfl
@[simp] theorem pc2925 : Artifact.submissionArtifact.instructionPC 3049 = 0x13db := by rfl
@[simp] theorem pc2926 : Artifact.submissionArtifact.instructionPC 3050 = 0x13dc := by rfl
@[simp] theorem pc2927 : Artifact.submissionArtifact.instructionPC 3051 = 0x13dd := by rfl
@[simp] theorem pc2928 : Artifact.submissionArtifact.instructionPC 3052 = 0x13de := by rfl
@[simp] theorem pc2929 : Artifact.submissionArtifact.instructionPC 3053 = 0x13df := by rfl
@[simp] theorem pc2930 : Artifact.submissionArtifact.instructionPC 3054 = 0x13e0 := by rfl
@[simp] theorem pc2931 : Artifact.submissionArtifact.instructionPC 3055 = 0x13e2 := by rfl
@[simp] theorem pc2932 : Artifact.submissionArtifact.instructionPC 3056 = 0x13e3 := by rfl
@[simp] theorem pc2933 : Artifact.submissionArtifact.instructionPC 3057 = 0x13e5 := by rfl
@[simp] theorem pc2934 : Artifact.submissionArtifact.instructionPC 3058 = 0x13e6 := by rfl
@[simp] theorem pc2935 : Artifact.submissionArtifact.instructionPC 3059 = 0x13e9 := by rfl
@[simp] theorem pc2936 : Artifact.submissionArtifact.instructionPC 3060 = 0x13ea := by rfl
@[simp] theorem pc2937 : Artifact.submissionArtifact.instructionPC 3061 = 0x13eb := by rfl
@[simp] theorem pc2938 : Artifact.submissionArtifact.instructionPC 3062 = 0x13ec := by rfl
@[simp] theorem pc2939 : Artifact.submissionArtifact.instructionPC 3063 = 0x13ed := by rfl
@[simp] theorem pc2940 : Artifact.submissionArtifact.instructionPC 3064 = 0x13ee := by rfl
@[simp] theorem pc2941 : Artifact.submissionArtifact.instructionPC 3065 = 0x13ef := by rfl
@[simp] theorem pc2942 : Artifact.submissionArtifact.instructionPC 3066 = 0x13f0 := by rfl
@[simp] theorem pc2943 : Artifact.submissionArtifact.instructionPC 3067 = 0x13f1 := by rfl
@[simp] theorem pc2944 : Artifact.submissionArtifact.instructionPC 3068 = 0x13f2 := by rfl
@[simp] theorem pc2945 : Artifact.submissionArtifact.instructionPC 3069 = 0x13f3 := by rfl
@[simp] theorem pc2946 : Artifact.submissionArtifact.instructionPC 3070 = 0x13f4 := by rfl
@[simp] theorem pc2947 : Artifact.submissionArtifact.instructionPC 3071 = 0x13f6 := by rfl
@[simp] theorem pc2948 : Artifact.submissionArtifact.instructionPC 3072 = 0x13f7 := by rfl
@[simp] theorem pc2949 : Artifact.submissionArtifact.instructionPC 3073 = 0x13f9 := by rfl
@[simp] theorem pc2950 : Artifact.submissionArtifact.instructionPC 3074 = 0x13fa := by rfl
@[simp] theorem pc2951 : Artifact.submissionArtifact.instructionPC 3075 = 0x13fb := by rfl
@[simp] theorem pc2952 : Artifact.submissionArtifact.instructionPC 3076 = 0x13fc := by rfl
@[simp] theorem pc2953 : Artifact.submissionArtifact.instructionPC 3077 = 0x13fd := by rfl
@[simp] theorem pc2954 : Artifact.submissionArtifact.instructionPC 3078 = 0x13ff := by rfl
@[simp] theorem pc2955 : Artifact.submissionArtifact.instructionPC 3079 = 0x1400 := by rfl
@[simp] theorem pc2956 : Artifact.submissionArtifact.instructionPC 3080 = 0x1401 := by rfl
@[simp] theorem pc2957 : Artifact.submissionArtifact.instructionPC 3081 = 0x1402 := by rfl
@[simp] theorem pc2958 : Artifact.submissionArtifact.instructionPC 3082 = 0x1403 := by rfl
@[simp] theorem pc2959 : Artifact.submissionArtifact.instructionPC 3083 = 0x1406 := by rfl
@[simp] theorem pc2960 : Artifact.submissionArtifact.instructionPC 3084 = 0x1407 := by rfl
@[simp] theorem pc2961 : Artifact.submissionArtifact.instructionPC 3085 = 0x140a := by rfl
@[simp] theorem pc2962 : Artifact.submissionArtifact.instructionPC 3086 = 0x140b := by rfl
@[simp] theorem pc2963 : Artifact.submissionArtifact.instructionPC 3087 = 0x140e := by rfl
@[simp] theorem pc2964 : Artifact.submissionArtifact.instructionPC 3088 = 0x140f := by rfl
@[simp] theorem pc2965 : Artifact.submissionArtifact.instructionPC 3089 = 0x1418 := by rfl
@[simp] theorem pc2966 : Artifact.submissionArtifact.instructionPC 3090 = 0x141a := by rfl
@[simp] theorem pc2967 : Artifact.submissionArtifact.instructionPC 3091 = 0x141b := by rfl
@[simp] theorem pc2968 : Artifact.submissionArtifact.instructionPC 3092 = 0x141c := by rfl
@[simp] theorem pc2969 : Artifact.submissionArtifact.instructionPC 3093 = 0x141d := by rfl
@[simp] theorem pc2970 : Artifact.submissionArtifact.instructionPC 3094 = 0x141e := by rfl
@[simp] theorem pc2971 : Artifact.submissionArtifact.instructionPC 3095 = 0x141f := by rfl
@[simp] theorem pc2972 : Artifact.submissionArtifact.instructionPC 3096 = 0x1420 := by rfl
@[simp] theorem pc2973 : Artifact.submissionArtifact.instructionPC 3097 = 0x1421 := by rfl
@[simp] theorem pc2974 : Artifact.submissionArtifact.instructionPC 3098 = 0x1422 := by rfl
@[simp] theorem pc2975 : Artifact.submissionArtifact.instructionPC 3099 = 0x1423 := by rfl
@[simp] theorem pc2976 : Artifact.submissionArtifact.instructionPC 3100 = 0x1424 := by rfl
@[simp] theorem pc2977 : Artifact.submissionArtifact.instructionPC 3101 = 0x1425 := by rfl
@[simp] theorem pc2978 : Artifact.submissionArtifact.instructionPC 3102 = 0x1426 := by rfl
@[simp] theorem pc2979 : Artifact.submissionArtifact.instructionPC 3103 = 0x1427 := by rfl
@[simp] theorem pc2980 : Artifact.submissionArtifact.instructionPC 3104 = 0x1428 := by rfl
@[simp] theorem pc2981 : Artifact.submissionArtifact.instructionPC 3105 = 0x1429 := by rfl
@[simp] theorem pc2982 : Artifact.submissionArtifact.instructionPC 3106 = 0x142c := by rfl
@[simp] theorem pc2983 : Artifact.submissionArtifact.instructionPC 3107 = 0x142d := by rfl
@[simp] theorem pc2984 : Artifact.submissionArtifact.instructionPC 3108 = 0x1442 := by rfl
@[simp] theorem pc2985 : Artifact.submissionArtifact.instructionPC 3109 = 0x1443 := by rfl
@[simp] theorem pc2986 : Artifact.submissionArtifact.instructionPC 3110 = 0x1444 := by rfl
@[simp] theorem pc2987 : Artifact.submissionArtifact.instructionPC 3111 = 0x1446 := by rfl
@[simp] theorem pc2988 : Artifact.submissionArtifact.instructionPC 3112 = 0x1447 := by rfl
@[simp] theorem pc2989 : Artifact.submissionArtifact.instructionPC 3113 = 0x1448 := by rfl
@[simp] theorem pc2990 : Artifact.submissionArtifact.instructionPC 3114 = 0x1449 := by rfl
@[simp] theorem pc2991 : Artifact.submissionArtifact.instructionPC 3115 = 0x144a := by rfl
@[simp] theorem pc2992 : Artifact.submissionArtifact.instructionPC 3116 = 0x144b := by rfl
@[simp] theorem pc2993 : Artifact.submissionArtifact.instructionPC 3117 = 0x144d := by rfl
@[simp] theorem pc2994 : Artifact.submissionArtifact.instructionPC 3118 = 0x144e := by rfl
@[simp] theorem pc2995 : Artifact.submissionArtifact.instructionPC 3119 = 0x1450 := by rfl
@[simp] theorem pc2996 : Artifact.submissionArtifact.instructionPC 3120 = 0x1451 := by rfl
@[simp] theorem pc2997 : Artifact.submissionArtifact.instructionPC 3121 = 0x1453 := by rfl
@[simp] theorem pc2998 : Artifact.submissionArtifact.instructionPC 3122 = 0x1454 := by rfl
@[simp] theorem pc2999 : Artifact.submissionArtifact.instructionPC 3123 = 0x1456 := by rfl
@[simp] theorem pc3000 : Artifact.submissionArtifact.instructionPC 3124 = 0x1457 := by rfl
@[simp] theorem pc3001 : Artifact.submissionArtifact.instructionPC 3125 = 0x1458 := by rfl
@[simp] theorem pc3002 : Artifact.submissionArtifact.instructionPC 3126 = 0x145a := by rfl
@[simp] theorem pc3003 : Artifact.submissionArtifact.instructionPC 3127 = 0x145b := by rfl
@[simp] theorem pc3004 : Artifact.submissionArtifact.instructionPC 3128 = 0x145c := by rfl
@[simp] theorem pc3005 : Artifact.submissionArtifact.instructionPC 3129 = 0x145d := by rfl
@[simp] theorem pc3006 : Artifact.submissionArtifact.instructionPC 3130 = 0x145e := by rfl
@[simp] theorem pc3007 : Artifact.submissionArtifact.instructionPC 3131 = 0x145f := by rfl
@[simp] theorem pc3008 : Artifact.submissionArtifact.instructionPC 3132 = 0x1460 := by rfl
@[simp] theorem pc3009 : Artifact.submissionArtifact.instructionPC 3133 = 0x1461 := by rfl
@[simp] theorem pc3010 : Artifact.submissionArtifact.instructionPC 3134 = 0x1462 := by rfl
@[simp] theorem pc3011 : Artifact.submissionArtifact.instructionPC 3135 = 0x1463 := by rfl
@[simp] theorem pc3012 : Artifact.submissionArtifact.instructionPC 3136 = 0x1464 := by rfl
@[simp] theorem pc3013 : Artifact.submissionArtifact.instructionPC 3137 = 0x1465 := by rfl
@[simp] theorem pc3014 : Artifact.submissionArtifact.instructionPC 3138 = 0x1466 := by rfl
@[simp] theorem pc3015 : Artifact.submissionArtifact.instructionPC 3139 = 0x1467 := by rfl
@[simp] theorem pc3016 : Artifact.submissionArtifact.instructionPC 3140 = 0x1468 := by rfl
@[simp] theorem pc3017 : Artifact.submissionArtifact.instructionPC 3141 = 0x146a := by rfl
@[simp] theorem pc3018 : Artifact.submissionArtifact.instructionPC 3142 = 0x146b := by rfl
@[simp] theorem pc3019 : Artifact.submissionArtifact.instructionPC 3143 = 0x146c := by rfl
@[simp] theorem pc3020 : Artifact.submissionArtifact.instructionPC 3144 = 0x146d := by rfl
@[simp] theorem pc3021 : Artifact.submissionArtifact.instructionPC 3145 = 0x1470 := by rfl
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan
