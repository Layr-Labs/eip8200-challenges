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
  [opAt 3009 .JUMPDEST,
   pushAt 3010 32 0x8080808080808080808080808080808080808080808080808080808080808080,
   pushAt 3011 32 0x072c51769bc0e50a2f54799ec3e80d32577ca1c6eb10355a7fa4c9ee13385d82,
   pushAt 3012 32 0x7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f,
   pushAt 3013 32 0x0101010101010101010101010101010101010101010101010101010101010101,
   opAt 3014 (.Dup ⟨2, by decide⟩), opAt 3015 (.Dup ⟨2, by decide⟩),
   opAt 3016 .AND, pushAt 3017 0 0, pushAt 3018 0 0, pushAt 3019 0 0]

/-- Derive the expected word and test for a straddler. -/
def wordPath : List Located :=
  [opAt 3020 .JUMPDEST, opAt 3021 (.Dup ⟨0, by decide⟩),
   opAt 3022 (.Dup ⟨5, by decide⟩), opAt 3023 .MUL,
   opAt 3024 (.Dup ⟨0, by decide⟩), opAt 3025 (.Dup ⟨7, by decide⟩),
   opAt 3026 .AND, opAt 3027 (.Dup ⟨5, by decide⟩), opAt 3028 .ADD,
   opAt 3029 (.Dup ⟨1, by decide⟩), opAt 3030 (.Dup ⟨9, by decide⟩),
   opAt 3031 .XOR, opAt 3032 (.Dup ⟨10, by decide⟩), opAt 3033 .AND,
   opAt 3034 .XOR, opAt 3035 (.Dup ⟨3, by decide⟩), pushAt 3036 1 0xff,
   opAt 3037 .AND, pushAt 3038 1 0xe0, opAt 3039 .EQ, pushAt 3040 2 0x14a7,
   opAt 3041 .JUMPI]

/-- Fold one word into the accumulator and advance. -/
def comparePath : List Located :=
  [opAt 3042 .JUMPDEST, opAt 3043 (.Dup ⟨3, by decide⟩),
   opAt 3044 .CALLDATALOAD, opAt 3045 .XOR, opAt 3046 (.Dup ⟨4, by decide⟩),
   opAt 3047 .OR, opAt 3048 (.Swap ⟨3, by decide⟩), opAt 3049 .POP,
   opAt 3050 .POP, opAt 3051 .JUMPDEST, pushAt 3052 1 0xa0,
   opAt 3053 .ADD, pushAt 3054 1 0xff, opAt 3055 .AND,
   opAt 3056 .JUMPDEST, opAt 3057 .JUMPDEST,
   opAt 3058 (.Dup ⟨1, by decide⟩), pushAt 3059 1 0x20, opAt 3060 .ADD,
   opAt 3061 (.Swap ⟨1, by decide⟩), opAt 3062 .POP,
   opAt 3063 (.Dup ⟨1, by decide⟩), pushAt 3064 2 0x03e0, opAt 3065 .GT,
   pushAt 3066 2 0x142f, opAt 3067 .JUMPI]

/-- The padded tail word, the cleanup and the miss test. -/
def tailPath : List Located :=
  [pushAt 3068 2 0x03e0, opAt 3069 .CALLDATALOAD,
   pushAt 3070 8 0x88add2f71c41668b, pushAt 3071 1 0xc0, opAt 3072 .SHL,
   opAt 3073 .XOR, opAt 3074 (.Dup ⟨3, by decide⟩), opAt 3075 .OR,
   opAt 3076 (.Swap ⟨2, by decide⟩), opAt 3077 .POP,
   opAt 3078 (.Swap ⟨1, by decide⟩), opAt 3079 (.Swap ⟨6, by decide⟩),
   opAt 3080 .POP, opAt 3081 .POP, opAt 3082 .POP, opAt 3083 .POP,
   opAt 3084 .POP, opAt 3085 .POP, opAt 3086 .POP, pushAt 3087 2 0x03ee,
   opAt 3088 .JUMPI]

/-- Store and return the stored digest. -/
def returnPath : List Located :=
  [pushAt 3089 20 0x863c598588bd72a4babf36c6bb01f27bbdc0ecd4,
   pushAt 3090 0 0, opAt 3091 .MSTORE, pushAt 3092 1 0x20, pushAt 3093 0 0,
   opAt 3094 .RETURN]

/-- Shift the correction constant out of `M`. -/
def straddleCorrPath : List Located :=
  [opAt 3095 .JUMPDEST, opAt 3096 (.Dup ⟨6, by decide⟩),
   opAt 3097 (.Dup ⟨4, by decide⟩), pushAt 3098 1 0x08, opAt 3099 .SHR,
   pushAt 3100 1 0x05, opAt 3101 .MUL, pushAt 3102 1 0x1b, opAt 3103 .SUB,
   pushAt 3104 1 0x03, opAt 3105 .SHL, opAt 3106 .SHR, pushAt 3107 1 0x0b,
   opAt 3108 .MUL]

/-- Apply the correction to the expected word. -/
def straddleAddPath : List Located :=
  [opAt 3109 (.Dup ⟨1, by decide⟩), opAt 3110 (.Dup ⟨9, by decide⟩),
   opAt 3111 .AND, opAt 3112 (.Dup ⟨1, by decide⟩), opAt 3113 .ADD,
   opAt 3114 (.Dup ⟨2, by decide⟩), opAt 3115 (.Dup ⟨12, by decide⟩),
   opAt 3116 .AND, opAt 3117 .XOR, opAt 3118 (.Swap ⟨1, by decide⟩),
   opAt 3119 .POP, opAt 3120 .POP]

/-- Bump the scalar and rejoin the scan. -/
def straddleBackPath : List Located :=
  [opAt 3121 (.Dup ⟨2, by decide⟩), pushAt 3122 1 0x0b, opAt 3123 .ADD,
   opAt 3124 (.Swap ⟨2, by decide⟩), opAt 3125 .POP, pushAt 3126 2 0x1449,
   opAt 3127 .JUMP]


@[simp] theorem pc2903 : Artifact.submissionArtifact.instructionPC 3009 = 5028 := by rfl
@[simp] theorem pc2904 : Artifact.submissionArtifact.instructionPC 3010 = 5029 := by rfl
@[simp] theorem pc2905 : Artifact.submissionArtifact.instructionPC 3011 = 5062 := by rfl
@[simp] theorem pc2906 : Artifact.submissionArtifact.instructionPC 3012 = 5095 := by rfl
@[simp] theorem pc2907 : Artifact.submissionArtifact.instructionPC 3013 = 5128 := by rfl
@[simp] theorem pc2908 : Artifact.submissionArtifact.instructionPC 3014 = 5161 := by rfl
@[simp] theorem pc2909 : Artifact.submissionArtifact.instructionPC 3015 = 5162 := by rfl
@[simp] theorem pc2910 : Artifact.submissionArtifact.instructionPC 3016 = 5163 := by rfl
@[simp] theorem pc2911 : Artifact.submissionArtifact.instructionPC 3017 = 5164 := by rfl
@[simp] theorem pc2912 : Artifact.submissionArtifact.instructionPC 3018 = 5165 := by rfl
@[simp] theorem pc2913 : Artifact.submissionArtifact.instructionPC 3019 = 5166 := by rfl
@[simp] theorem pc2914 : Artifact.submissionArtifact.instructionPC 3020 = 5167 := by rfl
@[simp] theorem pc2915 : Artifact.submissionArtifact.instructionPC 3021 = 5168 := by rfl
@[simp] theorem pc2916 : Artifact.submissionArtifact.instructionPC 3022 = 5169 := by rfl
@[simp] theorem pc2917 : Artifact.submissionArtifact.instructionPC 3023 = 5170 := by rfl
@[simp] theorem pc2918 : Artifact.submissionArtifact.instructionPC 3024 = 5171 := by rfl
@[simp] theorem pc2919 : Artifact.submissionArtifact.instructionPC 3025 = 5172 := by rfl
@[simp] theorem pc2920 : Artifact.submissionArtifact.instructionPC 3026 = 5173 := by rfl
@[simp] theorem pc2921 : Artifact.submissionArtifact.instructionPC 3027 = 5174 := by rfl
@[simp] theorem pc2922 : Artifact.submissionArtifact.instructionPC 3028 = 5175 := by rfl
@[simp] theorem pc2923 : Artifact.submissionArtifact.instructionPC 3029 = 5176 := by rfl
@[simp] theorem pc2924 : Artifact.submissionArtifact.instructionPC 3030 = 5177 := by rfl
@[simp] theorem pc2925 : Artifact.submissionArtifact.instructionPC 3031 = 5178 := by rfl
@[simp] theorem pc2926 : Artifact.submissionArtifact.instructionPC 3032 = 5179 := by rfl
@[simp] theorem pc2927 : Artifact.submissionArtifact.instructionPC 3033 = 5180 := by rfl
@[simp] theorem pc2928 : Artifact.submissionArtifact.instructionPC 3034 = 5181 := by rfl
@[simp] theorem pc2929 : Artifact.submissionArtifact.instructionPC 3035 = 5182 := by rfl
@[simp] theorem pc2930 : Artifact.submissionArtifact.instructionPC 3036 = 5183 := by rfl
@[simp] theorem pc2931 : Artifact.submissionArtifact.instructionPC 3037 = 5185 := by rfl
@[simp] theorem pc2932 : Artifact.submissionArtifact.instructionPC 3038 = 5186 := by rfl
@[simp] theorem pc2933 : Artifact.submissionArtifact.instructionPC 3039 = 5188 := by rfl
@[simp] theorem pc2934 : Artifact.submissionArtifact.instructionPC 3040 = 5189 := by rfl
@[simp] theorem pc2935 : Artifact.submissionArtifact.instructionPC 3041 = 5192 := by rfl
@[simp] theorem pc2936 : Artifact.submissionArtifact.instructionPC 3042 = 5193 := by rfl
@[simp] theorem pc2937 : Artifact.submissionArtifact.instructionPC 3043 = 5194 := by rfl
@[simp] theorem pc2938 : Artifact.submissionArtifact.instructionPC 3044 = 5195 := by rfl
@[simp] theorem pc2939 : Artifact.submissionArtifact.instructionPC 3045 = 5196 := by rfl
@[simp] theorem pc2940 : Artifact.submissionArtifact.instructionPC 3046 = 5197 := by rfl
@[simp] theorem pc2941 : Artifact.submissionArtifact.instructionPC 3047 = 5198 := by rfl
@[simp] theorem pc2942 : Artifact.submissionArtifact.instructionPC 3048 = 5199 := by rfl
@[simp] theorem pc2943 : Artifact.submissionArtifact.instructionPC 3049 = 5200 := by rfl
@[simp] theorem pc2944 : Artifact.submissionArtifact.instructionPC 3050 = 5201 := by rfl
@[simp] theorem pc2945 : Artifact.submissionArtifact.instructionPC 3051 = 5202 := by rfl
@[simp] theorem pc2946 : Artifact.submissionArtifact.instructionPC 3052 = 5203 := by rfl
@[simp] theorem pc2947 : Artifact.submissionArtifact.instructionPC 3053 = 5205 := by rfl
@[simp] theorem pc2948 : Artifact.submissionArtifact.instructionPC 3054 = 5206 := by rfl
@[simp] theorem pc2949 : Artifact.submissionArtifact.instructionPC 3055 = 5208 := by rfl
@[simp] theorem pc2950 : Artifact.submissionArtifact.instructionPC 3056 = 5209 := by rfl
@[simp] theorem pc2951 : Artifact.submissionArtifact.instructionPC 3057 = 5210 := by rfl
@[simp] theorem pc2952 : Artifact.submissionArtifact.instructionPC 3058 = 5211 := by rfl
@[simp] theorem pc2953 : Artifact.submissionArtifact.instructionPC 3059 = 5212 := by rfl
@[simp] theorem pc2954 : Artifact.submissionArtifact.instructionPC 3060 = 5214 := by rfl
@[simp] theorem pc2955 : Artifact.submissionArtifact.instructionPC 3061 = 5215 := by rfl
@[simp] theorem pc2956 : Artifact.submissionArtifact.instructionPC 3062 = 5216 := by rfl
@[simp] theorem pc2957 : Artifact.submissionArtifact.instructionPC 3063 = 5217 := by rfl
@[simp] theorem pc2958 : Artifact.submissionArtifact.instructionPC 3064 = 5218 := by rfl
@[simp] theorem pc2959 : Artifact.submissionArtifact.instructionPC 3065 = 5221 := by rfl
@[simp] theorem pc2960 : Artifact.submissionArtifact.instructionPC 3066 = 5222 := by rfl
@[simp] theorem pc2961 : Artifact.submissionArtifact.instructionPC 3067 = 5225 := by rfl
@[simp] theorem pc2962 : Artifact.submissionArtifact.instructionPC 3068 = 5226 := by rfl
@[simp] theorem pc2963 : Artifact.submissionArtifact.instructionPC 3069 = 5229 := by rfl
@[simp] theorem pc2964 : Artifact.submissionArtifact.instructionPC 3070 = 5230 := by rfl
@[simp] theorem pc2965 : Artifact.submissionArtifact.instructionPC 3071 = 5239 := by rfl
@[simp] theorem pc2966 : Artifact.submissionArtifact.instructionPC 3072 = 5241 := by rfl
@[simp] theorem pc2967 : Artifact.submissionArtifact.instructionPC 3073 = 5242 := by rfl
@[simp] theorem pc2968 : Artifact.submissionArtifact.instructionPC 3074 = 5243 := by rfl
@[simp] theorem pc2969 : Artifact.submissionArtifact.instructionPC 3075 = 5244 := by rfl
@[simp] theorem pc2970 : Artifact.submissionArtifact.instructionPC 3076 = 5245 := by rfl
@[simp] theorem pc2971 : Artifact.submissionArtifact.instructionPC 3077 = 5246 := by rfl
@[simp] theorem pc2972 : Artifact.submissionArtifact.instructionPC 3078 = 5247 := by rfl
@[simp] theorem pc2973 : Artifact.submissionArtifact.instructionPC 3079 = 5248 := by rfl
@[simp] theorem pc2974 : Artifact.submissionArtifact.instructionPC 3080 = 5249 := by rfl
@[simp] theorem pc2975 : Artifact.submissionArtifact.instructionPC 3081 = 5250 := by rfl
@[simp] theorem pc2976 : Artifact.submissionArtifact.instructionPC 3082 = 5251 := by rfl
@[simp] theorem pc2977 : Artifact.submissionArtifact.instructionPC 3083 = 5252 := by rfl
@[simp] theorem pc2978 : Artifact.submissionArtifact.instructionPC 3084 = 5253 := by rfl
@[simp] theorem pc2979 : Artifact.submissionArtifact.instructionPC 3085 = 5254 := by rfl
@[simp] theorem pc2980 : Artifact.submissionArtifact.instructionPC 3086 = 5255 := by rfl
@[simp] theorem pc2981 : Artifact.submissionArtifact.instructionPC 3087 = 5256 := by rfl
@[simp] theorem pc2982 : Artifact.submissionArtifact.instructionPC 3088 = 5259 := by rfl
@[simp] theorem pc2983 : Artifact.submissionArtifact.instructionPC 3089 = 5260 := by rfl
@[simp] theorem pc2984 : Artifact.submissionArtifact.instructionPC 3090 = 5281 := by rfl
@[simp] theorem pc2985 : Artifact.submissionArtifact.instructionPC 3091 = 5282 := by rfl
@[simp] theorem pc2986 : Artifact.submissionArtifact.instructionPC 3092 = 5283 := by rfl
@[simp] theorem pc2987 : Artifact.submissionArtifact.instructionPC 3093 = 5285 := by rfl
@[simp] theorem pc2988 : Artifact.submissionArtifact.instructionPC 3094 = 5286 := by rfl
@[simp] theorem pc2989 : Artifact.submissionArtifact.instructionPC 3095 = 5287 := by rfl
@[simp] theorem pc2990 : Artifact.submissionArtifact.instructionPC 3096 = 5288 := by rfl
@[simp] theorem pc2991 : Artifact.submissionArtifact.instructionPC 3097 = 5289 := by rfl
@[simp] theorem pc2992 : Artifact.submissionArtifact.instructionPC 3098 = 5290 := by rfl
@[simp] theorem pc2993 : Artifact.submissionArtifact.instructionPC 3099 = 5292 := by rfl
@[simp] theorem pc2994 : Artifact.submissionArtifact.instructionPC 3100 = 5293 := by rfl
@[simp] theorem pc2995 : Artifact.submissionArtifact.instructionPC 3101 = 5295 := by rfl
@[simp] theorem pc2996 : Artifact.submissionArtifact.instructionPC 3102 = 5296 := by rfl
@[simp] theorem pc2997 : Artifact.submissionArtifact.instructionPC 3103 = 5298 := by rfl
@[simp] theorem pc2998 : Artifact.submissionArtifact.instructionPC 3104 = 5299 := by rfl
@[simp] theorem pc2999 : Artifact.submissionArtifact.instructionPC 3105 = 5301 := by rfl
@[simp] theorem pc3000 : Artifact.submissionArtifact.instructionPC 3106 = 5302 := by rfl
@[simp] theorem pc3001 : Artifact.submissionArtifact.instructionPC 3107 = 5303 := by rfl
@[simp] theorem pc3002 : Artifact.submissionArtifact.instructionPC 3108 = 5305 := by rfl
@[simp] theorem pc3003 : Artifact.submissionArtifact.instructionPC 3109 = 5306 := by rfl
@[simp] theorem pc3004 : Artifact.submissionArtifact.instructionPC 3110 = 5307 := by rfl
@[simp] theorem pc3005 : Artifact.submissionArtifact.instructionPC 3111 = 5308 := by rfl
@[simp] theorem pc3006 : Artifact.submissionArtifact.instructionPC 3112 = 5309 := by rfl
@[simp] theorem pc3007 : Artifact.submissionArtifact.instructionPC 3113 = 5310 := by rfl
@[simp] theorem pc3008 : Artifact.submissionArtifact.instructionPC 3114 = 5311 := by rfl
@[simp] theorem pc3009 : Artifact.submissionArtifact.instructionPC 3115 = 5312 := by rfl
@[simp] theorem pc3010 : Artifact.submissionArtifact.instructionPC 3116 = 5313 := by rfl
@[simp] theorem pc3011 : Artifact.submissionArtifact.instructionPC 3117 = 5314 := by rfl
@[simp] theorem pc3012 : Artifact.submissionArtifact.instructionPC 3118 = 5315 := by rfl
@[simp] theorem pc3013 : Artifact.submissionArtifact.instructionPC 3119 = 5316 := by rfl
@[simp] theorem pc3014 : Artifact.submissionArtifact.instructionPC 3120 = 5317 := by rfl
@[simp] theorem pc3015 : Artifact.submissionArtifact.instructionPC 3121 = 5318 := by rfl
@[simp] theorem pc3016 : Artifact.submissionArtifact.instructionPC 3122 = 5319 := by rfl
@[simp] theorem pc3017 : Artifact.submissionArtifact.instructionPC 3123 = 5321 := by rfl
@[simp] theorem pc3018 : Artifact.submissionArtifact.instructionPC 3124 = 5322 := by rfl
@[simp] theorem pc3019 : Artifact.submissionArtifact.instructionPC 3125 = 5323 := by rfl
@[simp] theorem pc3020 : Artifact.submissionArtifact.instructionPC 3126 = 5324 := by rfl
@[simp] theorem pc3021 : Artifact.submissionArtifact.instructionPC 3127 = 5327 := by rfl
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan
