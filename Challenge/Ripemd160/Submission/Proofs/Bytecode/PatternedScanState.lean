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
  [opAt 3016 .JUMPDEST,
   pushAt 3017 32 0x8080808080808080808080808080808080808080808080808080808080808080,
   pushAt 3018 32 0x072c51769bc0e50a2f54799ec3e80d32577ca1c6eb10355a7fa4c9ee13385d82,
   pushAt 3019 32 0x7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f,
   pushAt 3020 32 0x0101010101010101010101010101010101010101010101010101010101010101,
   opAt 3021 (.Dup ⟨2, by decide⟩), opAt 3022 (.Dup ⟨2, by decide⟩),
   opAt 3023 .AND, pushAt 3024 0 0, pushAt 3025 0 0, pushAt 3026 0 0]

/-- Derive the expected word and test for a straddler. -/
def wordPath : List Located :=
  [opAt 3027 .JUMPDEST, opAt 3028 (.Dup ⟨0, by decide⟩),
   opAt 3029 (.Dup ⟨5, by decide⟩), opAt 3030 .MUL,
   opAt 3031 (.Dup ⟨0, by decide⟩), opAt 3032 (.Dup ⟨7, by decide⟩),
   opAt 3033 .AND, opAt 3034 (.Dup ⟨5, by decide⟩), opAt 3035 .ADD,
   opAt 3036 (.Dup ⟨1, by decide⟩), opAt 3037 (.Dup ⟨9, by decide⟩),
   opAt 3038 .XOR, opAt 3039 (.Dup ⟨10, by decide⟩), opAt 3040 .AND,
   opAt 3041 .XOR, opAt 3042 (.Dup ⟨3, by decide⟩), pushAt 3043 1 0xff,
   opAt 3044 .AND, pushAt 3045 1 0xe0, opAt 3046 .EQ, pushAt 3047 2 0x149e,
   opAt 3048 .JUMPI]

/-- Fold one word into the accumulator and advance. -/
def comparePath : List Located :=
  [opAt 3049 .JUMPDEST, opAt 3050 (.Dup ⟨3, by decide⟩),
   opAt 3051 .CALLDATALOAD, opAt 3052 .XOR, opAt 3053 (.Dup ⟨4, by decide⟩),
   opAt 3054 .OR, opAt 3055 (.Swap ⟨3, by decide⟩), opAt 3056 .POP,
   opAt 3057 .POP, opAt 3058 .JUMPDEST, pushAt 3059 1 0xa0,
   opAt 3060 .ADD, pushAt 3061 1 0xff, opAt 3062 .AND,
   opAt 3063 .JUMPDEST, opAt 3064 .JUMPDEST,
   opAt 3065 (.Dup ⟨1, by decide⟩), pushAt 3066 1 0x20, opAt 3067 .ADD,
   opAt 3068 (.Swap ⟨1, by decide⟩), opAt 3069 .POP,
   opAt 3070 (.Dup ⟨1, by decide⟩), pushAt 3071 2 0x03e0, opAt 3072 .GT,
   pushAt 3073 2 0x1426, opAt 3074 .JUMPI]

/-- The padded tail word, the cleanup and the miss test. -/
def tailPath : List Located :=
  [pushAt 3075 2 0x03e0, opAt 3076 .CALLDATALOAD,
   pushAt 3077 8 0x88add2f71c41668b, pushAt 3078 1 0xc0, opAt 3079 .SHL,
   opAt 3080 .XOR, opAt 3081 (.Dup ⟨3, by decide⟩), opAt 3082 .OR,
   opAt 3083 (.Swap ⟨2, by decide⟩), opAt 3084 .POP,
   opAt 3085 (.Swap ⟨1, by decide⟩), opAt 3086 (.Swap ⟨6, by decide⟩),
   opAt 3087 .POP, opAt 3088 .POP, opAt 3089 .POP, opAt 3090 .POP,
   opAt 3091 .POP, opAt 3092 .POP, opAt 3093 .POP, pushAt 3094 2 0x03ee,
   opAt 3095 .JUMPI]

/-- Store and return the stored digest. -/
def returnPath : List Located :=
  [pushAt 3096 20 0x863c598588bd72a4babf36c6bb01f27bbdc0ecd4,
   pushAt 3097 0 0, opAt 3098 .MSTORE, pushAt 3099 1 0x20, pushAt 3100 0 0,
   opAt 3101 .RETURN]

/-- Shift the correction constant out of `M`. -/
def straddleCorrPath : List Located :=
  [opAt 3102 .JUMPDEST, opAt 3103 (.Dup ⟨6, by decide⟩),
   opAt 3104 (.Dup ⟨4, by decide⟩), pushAt 3105 1 0x08, opAt 3106 .SHR,
   pushAt 3107 1 0x05, opAt 3108 .MUL, pushAt 3109 1 0x1b, opAt 3110 .SUB,
   pushAt 3111 1 0x08, opAt 3112 .MUL, opAt 3113 .SHR, pushAt 3114 1 0x0b,
   opAt 3115 .MUL]

/-- Apply the correction to the expected word. -/
def straddleAddPath : List Located :=
  [opAt 3116 (.Dup ⟨1, by decide⟩), opAt 3117 (.Dup ⟨9, by decide⟩),
   opAt 3118 .AND, opAt 3119 (.Dup ⟨1, by decide⟩), opAt 3120 .ADD,
   opAt 3121 (.Dup ⟨2, by decide⟩), opAt 3122 (.Dup ⟨12, by decide⟩),
   opAt 3123 .AND, opAt 3124 .XOR, opAt 3125 (.Swap ⟨1, by decide⟩),
   opAt 3126 .POP, opAt 3127 .POP]

/-- Bump the scalar and rejoin the scan. -/
def straddleBackPath : List Located :=
  [opAt 3128 (.Dup ⟨2, by decide⟩), pushAt 3129 1 0x0b, opAt 3130 .ADD,
   opAt 3131 (.Swap ⟨2, by decide⟩), opAt 3132 .POP, pushAt 3133 2 0x1440,
   opAt 3134 .JUMP]


@[simp] theorem pc2903 : Artifact.submissionArtifact.instructionPC 3016 = 5019 := by rfl
@[simp] theorem pc2904 : Artifact.submissionArtifact.instructionPC 3017 = 5020 := by rfl
@[simp] theorem pc2905 : Artifact.submissionArtifact.instructionPC 3018 = 5053 := by rfl
@[simp] theorem pc2906 : Artifact.submissionArtifact.instructionPC 3019 = 5086 := by rfl
@[simp] theorem pc2907 : Artifact.submissionArtifact.instructionPC 3020 = 5119 := by rfl
@[simp] theorem pc2908 : Artifact.submissionArtifact.instructionPC 3021 = 5152 := by rfl
@[simp] theorem pc2909 : Artifact.submissionArtifact.instructionPC 3022 = 5153 := by rfl
@[simp] theorem pc2910 : Artifact.submissionArtifact.instructionPC 3023 = 5154 := by rfl
@[simp] theorem pc2911 : Artifact.submissionArtifact.instructionPC 3024 = 5155 := by rfl
@[simp] theorem pc2912 : Artifact.submissionArtifact.instructionPC 3025 = 5156 := by rfl
@[simp] theorem pc2913 : Artifact.submissionArtifact.instructionPC 3026 = 5157 := by rfl
@[simp] theorem pc2914 : Artifact.submissionArtifact.instructionPC 3027 = 5158 := by rfl
@[simp] theorem pc2915 : Artifact.submissionArtifact.instructionPC 3028 = 5159 := by rfl
@[simp] theorem pc2916 : Artifact.submissionArtifact.instructionPC 3029 = 5160 := by rfl
@[simp] theorem pc2917 : Artifact.submissionArtifact.instructionPC 3030 = 5161 := by rfl
@[simp] theorem pc2918 : Artifact.submissionArtifact.instructionPC 3031 = 5162 := by rfl
@[simp] theorem pc2919 : Artifact.submissionArtifact.instructionPC 3032 = 5163 := by rfl
@[simp] theorem pc2920 : Artifact.submissionArtifact.instructionPC 3033 = 5164 := by rfl
@[simp] theorem pc2921 : Artifact.submissionArtifact.instructionPC 3034 = 5165 := by rfl
@[simp] theorem pc2922 : Artifact.submissionArtifact.instructionPC 3035 = 5166 := by rfl
@[simp] theorem pc2923 : Artifact.submissionArtifact.instructionPC 3036 = 5167 := by rfl
@[simp] theorem pc2924 : Artifact.submissionArtifact.instructionPC 3037 = 5168 := by rfl
@[simp] theorem pc2925 : Artifact.submissionArtifact.instructionPC 3038 = 5169 := by rfl
@[simp] theorem pc2926 : Artifact.submissionArtifact.instructionPC 3039 = 5170 := by rfl
@[simp] theorem pc2927 : Artifact.submissionArtifact.instructionPC 3040 = 5171 := by rfl
@[simp] theorem pc2928 : Artifact.submissionArtifact.instructionPC 3041 = 5172 := by rfl
@[simp] theorem pc2929 : Artifact.submissionArtifact.instructionPC 3042 = 5173 := by rfl
@[simp] theorem pc2930 : Artifact.submissionArtifact.instructionPC 3043 = 5174 := by rfl
@[simp] theorem pc2931 : Artifact.submissionArtifact.instructionPC 3044 = 5176 := by rfl
@[simp] theorem pc2932 : Artifact.submissionArtifact.instructionPC 3045 = 5177 := by rfl
@[simp] theorem pc2933 : Artifact.submissionArtifact.instructionPC 3046 = 5179 := by rfl
@[simp] theorem pc2934 : Artifact.submissionArtifact.instructionPC 3047 = 5180 := by rfl
@[simp] theorem pc2935 : Artifact.submissionArtifact.instructionPC 3048 = 5183 := by rfl
@[simp] theorem pc2936 : Artifact.submissionArtifact.instructionPC 3049 = 5184 := by rfl
@[simp] theorem pc2937 : Artifact.submissionArtifact.instructionPC 3050 = 5185 := by rfl
@[simp] theorem pc2938 : Artifact.submissionArtifact.instructionPC 3051 = 5186 := by rfl
@[simp] theorem pc2939 : Artifact.submissionArtifact.instructionPC 3052 = 5187 := by rfl
@[simp] theorem pc2940 : Artifact.submissionArtifact.instructionPC 3053 = 5188 := by rfl
@[simp] theorem pc2941 : Artifact.submissionArtifact.instructionPC 3054 = 5189 := by rfl
@[simp] theorem pc2942 : Artifact.submissionArtifact.instructionPC 3055 = 5190 := by rfl
@[simp] theorem pc2943 : Artifact.submissionArtifact.instructionPC 3056 = 5191 := by rfl
@[simp] theorem pc2944 : Artifact.submissionArtifact.instructionPC 3057 = 5192 := by rfl
@[simp] theorem pc2945 : Artifact.submissionArtifact.instructionPC 3058 = 5193 := by rfl
@[simp] theorem pc2946 : Artifact.submissionArtifact.instructionPC 3059 = 5194 := by rfl
@[simp] theorem pc2947 : Artifact.submissionArtifact.instructionPC 3060 = 5196 := by rfl
@[simp] theorem pc2948 : Artifact.submissionArtifact.instructionPC 3061 = 5197 := by rfl
@[simp] theorem pc2949 : Artifact.submissionArtifact.instructionPC 3062 = 5199 := by rfl
@[simp] theorem pc2950 : Artifact.submissionArtifact.instructionPC 3063 = 5200 := by rfl
@[simp] theorem pc2951 : Artifact.submissionArtifact.instructionPC 3064 = 5201 := by rfl
@[simp] theorem pc2952 : Artifact.submissionArtifact.instructionPC 3065 = 5202 := by rfl
@[simp] theorem pc2953 : Artifact.submissionArtifact.instructionPC 3066 = 5203 := by rfl
@[simp] theorem pc2954 : Artifact.submissionArtifact.instructionPC 3067 = 5205 := by rfl
@[simp] theorem pc2955 : Artifact.submissionArtifact.instructionPC 3068 = 5206 := by rfl
@[simp] theorem pc2956 : Artifact.submissionArtifact.instructionPC 3069 = 5207 := by rfl
@[simp] theorem pc2957 : Artifact.submissionArtifact.instructionPC 3070 = 5208 := by rfl
@[simp] theorem pc2958 : Artifact.submissionArtifact.instructionPC 3071 = 5209 := by rfl
@[simp] theorem pc2959 : Artifact.submissionArtifact.instructionPC 3072 = 5212 := by rfl
@[simp] theorem pc2960 : Artifact.submissionArtifact.instructionPC 3073 = 5213 := by rfl
@[simp] theorem pc2961 : Artifact.submissionArtifact.instructionPC 3074 = 5216 := by rfl
@[simp] theorem pc2962 : Artifact.submissionArtifact.instructionPC 3075 = 5217 := by rfl
@[simp] theorem pc2963 : Artifact.submissionArtifact.instructionPC 3076 = 5220 := by rfl
@[simp] theorem pc2964 : Artifact.submissionArtifact.instructionPC 3077 = 5221 := by rfl
@[simp] theorem pc2965 : Artifact.submissionArtifact.instructionPC 3078 = 5230 := by rfl
@[simp] theorem pc2966 : Artifact.submissionArtifact.instructionPC 3079 = 5232 := by rfl
@[simp] theorem pc2967 : Artifact.submissionArtifact.instructionPC 3080 = 5233 := by rfl
@[simp] theorem pc2968 : Artifact.submissionArtifact.instructionPC 3081 = 5234 := by rfl
@[simp] theorem pc2969 : Artifact.submissionArtifact.instructionPC 3082 = 5235 := by rfl
@[simp] theorem pc2970 : Artifact.submissionArtifact.instructionPC 3083 = 5236 := by rfl
@[simp] theorem pc2971 : Artifact.submissionArtifact.instructionPC 3084 = 5237 := by rfl
@[simp] theorem pc2972 : Artifact.submissionArtifact.instructionPC 3085 = 5238 := by rfl
@[simp] theorem pc2973 : Artifact.submissionArtifact.instructionPC 3086 = 5239 := by rfl
@[simp] theorem pc2974 : Artifact.submissionArtifact.instructionPC 3087 = 5240 := by rfl
@[simp] theorem pc2975 : Artifact.submissionArtifact.instructionPC 3088 = 5241 := by rfl
@[simp] theorem pc2976 : Artifact.submissionArtifact.instructionPC 3089 = 5242 := by rfl
@[simp] theorem pc2977 : Artifact.submissionArtifact.instructionPC 3090 = 5243 := by rfl
@[simp] theorem pc2978 : Artifact.submissionArtifact.instructionPC 3091 = 5244 := by rfl
@[simp] theorem pc2979 : Artifact.submissionArtifact.instructionPC 3092 = 5245 := by rfl
@[simp] theorem pc2980 : Artifact.submissionArtifact.instructionPC 3093 = 5246 := by rfl
@[simp] theorem pc2981 : Artifact.submissionArtifact.instructionPC 3094 = 5247 := by rfl
@[simp] theorem pc2982 : Artifact.submissionArtifact.instructionPC 3095 = 5250 := by rfl
@[simp] theorem pc2983 : Artifact.submissionArtifact.instructionPC 3096 = 5251 := by rfl
@[simp] theorem pc2984 : Artifact.submissionArtifact.instructionPC 3097 = 5272 := by rfl
@[simp] theorem pc2985 : Artifact.submissionArtifact.instructionPC 3098 = 5273 := by rfl
@[simp] theorem pc2986 : Artifact.submissionArtifact.instructionPC 3099 = 5274 := by rfl
@[simp] theorem pc2987 : Artifact.submissionArtifact.instructionPC 3100 = 5276 := by rfl
@[simp] theorem pc2988 : Artifact.submissionArtifact.instructionPC 3101 = 5277 := by rfl
@[simp] theorem pc2989 : Artifact.submissionArtifact.instructionPC 3102 = 5278 := by rfl
@[simp] theorem pc2990 : Artifact.submissionArtifact.instructionPC 3103 = 5279 := by rfl
@[simp] theorem pc2991 : Artifact.submissionArtifact.instructionPC 3104 = 5280 := by rfl
@[simp] theorem pc2992 : Artifact.submissionArtifact.instructionPC 3105 = 5281 := by rfl
@[simp] theorem pc2993 : Artifact.submissionArtifact.instructionPC 3106 = 5283 := by rfl
@[simp] theorem pc2994 : Artifact.submissionArtifact.instructionPC 3107 = 5284 := by rfl
@[simp] theorem pc2995 : Artifact.submissionArtifact.instructionPC 3108 = 5286 := by rfl
@[simp] theorem pc2996 : Artifact.submissionArtifact.instructionPC 3109 = 5287 := by rfl
@[simp] theorem pc2997 : Artifact.submissionArtifact.instructionPC 3110 = 5289 := by rfl
@[simp] theorem pc2998 : Artifact.submissionArtifact.instructionPC 3111 = 5290 := by rfl
@[simp] theorem pc2999 : Artifact.submissionArtifact.instructionPC 3112 = 5292 := by rfl
@[simp] theorem pc3000 : Artifact.submissionArtifact.instructionPC 3113 = 5293 := by rfl
@[simp] theorem pc3001 : Artifact.submissionArtifact.instructionPC 3114 = 5294 := by rfl
@[simp] theorem pc3002 : Artifact.submissionArtifact.instructionPC 3115 = 5296 := by rfl
@[simp] theorem pc3003 : Artifact.submissionArtifact.instructionPC 3116 = 5297 := by rfl
@[simp] theorem pc3004 : Artifact.submissionArtifact.instructionPC 3117 = 5298 := by rfl
@[simp] theorem pc3005 : Artifact.submissionArtifact.instructionPC 3118 = 5299 := by rfl
@[simp] theorem pc3006 : Artifact.submissionArtifact.instructionPC 3119 = 5300 := by rfl
@[simp] theorem pc3007 : Artifact.submissionArtifact.instructionPC 3120 = 5301 := by rfl
@[simp] theorem pc3008 : Artifact.submissionArtifact.instructionPC 3121 = 5302 := by rfl
@[simp] theorem pc3009 : Artifact.submissionArtifact.instructionPC 3122 = 5303 := by rfl
@[simp] theorem pc3010 : Artifact.submissionArtifact.instructionPC 3123 = 5304 := by rfl
@[simp] theorem pc3011 : Artifact.submissionArtifact.instructionPC 3124 = 5305 := by rfl
@[simp] theorem pc3012 : Artifact.submissionArtifact.instructionPC 3125 = 5306 := by rfl
@[simp] theorem pc3013 : Artifact.submissionArtifact.instructionPC 3126 = 5307 := by rfl
@[simp] theorem pc3014 : Artifact.submissionArtifact.instructionPC 3127 = 5308 := by rfl
@[simp] theorem pc3015 : Artifact.submissionArtifact.instructionPC 3128 = 5309 := by rfl
@[simp] theorem pc3016 : Artifact.submissionArtifact.instructionPC 3129 = 5310 := by rfl
@[simp] theorem pc3017 : Artifact.submissionArtifact.instructionPC 3130 = 5312 := by rfl
@[simp] theorem pc3018 : Artifact.submissionArtifact.instructionPC 3131 = 5313 := by rfl
@[simp] theorem pc3019 : Artifact.submissionArtifact.instructionPC 3132 = 5314 := by rfl
@[simp] theorem pc3020 : Artifact.submissionArtifact.instructionPC 3133 = 5315 := by rfl
@[simp] theorem pc3021 : Artifact.submissionArtifact.instructionPC 3134 = 5318 := by rfl
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan
