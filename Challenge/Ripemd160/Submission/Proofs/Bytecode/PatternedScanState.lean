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
  [opAt 3036 .JUMPDEST,
   pushAt 3037 32 0x8080808080808080808080808080808080808080808080808080808080808080,
   pushAt 3038 32 0x72c51769bc0e50a2f54799ec3e80d32577ca1c6eb10355a7fa4c9ee13385d82,
   pushAt 3039 32 0x7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f,
   pushAt 3040 32 0x101010101010101010101010101010101010101010101010101010101010101,
   opAt 3041 (.Dup ⟨2, by decide⟩), opAt 3042 (.Dup ⟨2, by decide⟩),
   opAt 3043 .AND, pushAt 3044 0 0, pushAt 3045 0 0, pushAt 3046 0 0]

/-- Derive the expected word and test for a straddler. -/
def wordPath : List Located :=
  [opAt 3047 .JUMPDEST, opAt 3048 (.Dup ⟨0, by decide⟩),
   opAt 3049 (.Dup ⟨5, by decide⟩), opAt 3050 .MUL,
   opAt 3051 (.Dup ⟨0, by decide⟩), opAt 3052 (.Dup ⟨7, by decide⟩),
   opAt 3053 .AND, opAt 3054 (.Dup ⟨5, by decide⟩), opAt 3055 .ADD,
   opAt 3056 (.Dup ⟨1, by decide⟩), opAt 3057 (.Dup ⟨9, by decide⟩),
   opAt 3058 .XOR, opAt 3059 (.Dup ⟨10, by decide⟩), opAt 3060 .AND,
   opAt 3061 .XOR, opAt 3062 (.Dup ⟨3, by decide⟩), pushAt 3063 1 0xff,
   opAt 3064 .AND, pushAt 3065 1 0xe0, opAt 3066 .EQ, pushAt 3067 2 0x145f,
   opAt 3068 .JUMPI]

/-- Fold one word into the accumulator and advance. -/
def comparePath : List Located :=
  [opAt 3069 .JUMPDEST, opAt 3070 (.Dup ⟨3, by decide⟩),
   opAt 3071 .CALLDATALOAD, opAt 3072 .XOR, opAt 3073 (.Dup ⟨4, by decide⟩),
   opAt 3074 .OR, opAt 3075 (.Swap ⟨3, by decide⟩), opAt 3076 .POP,
   opAt 3077 .POP, opAt 3078 .JUMPDEST, pushAt 3079 1 0xa0,
   opAt 3080 .ADD, pushAt 3081 1 0xff, opAt 3082 .AND,
   opAt 3083 .JUMPDEST, opAt 3084 .JUMPDEST,
   opAt 3085 (.Dup ⟨1, by decide⟩), pushAt 3086 1 0x20, opAt 3087 .ADD,
   opAt 3088 (.Swap ⟨1, by decide⟩), opAt 3089 .POP,
   opAt 3090 (.Dup ⟨1, by decide⟩), pushAt 3091 2 0x3e0, opAt 3092 .GT,
   pushAt 3093 2 0x13e7, opAt 3094 .JUMPI]

/-- The padded tail word, the cleanup and the miss test. -/
def tailPath : List Located :=
  [pushAt 3095 2 0x3e0, opAt 3096 .CALLDATALOAD,
   pushAt 3097 8 0x88add2f71c41668b, pushAt 3098 1 0xc0, opAt 3099 .SHL,
   opAt 3100 .XOR, opAt 3101 (.Dup ⟨3, by decide⟩), opAt 3102 .OR,
   opAt 3103 (.Swap ⟨2, by decide⟩), opAt 3104 .POP,
   opAt 3105 (.Swap ⟨1, by decide⟩), opAt 3106 (.Swap ⟨6, by decide⟩),
   opAt 3107 .POP, opAt 3108 .POP, opAt 3109 .POP, opAt 3110 .POP,
   opAt 3111 .POP, opAt 3112 .POP, opAt 3113 .POP, pushAt 3114 2 0x3d3,
   opAt 3115 .JUMPI]

/-- Store and return the stored digest. -/
def returnPath : List Located :=
  [pushAt 3116 20 0x863c598588bd72a4babf36c6bb01f27bbdc0ecd4,
   pushAt 3117 0 0, opAt 3118 .MSTORE, pushAt 3119 1 0x20, pushAt 3120 0 0,
   opAt 3121 .RETURN]

/-- Shift the correction constant out of `M`. -/
def straddleCorrPath : List Located :=
  [opAt 3122 .JUMPDEST, opAt 3123 (.Dup ⟨6, by decide⟩),
   opAt 3124 (.Dup ⟨4, by decide⟩), pushAt 3125 1 0x8, opAt 3126 .SHR,
   pushAt 3127 1 0x5, opAt 3128 .MUL, pushAt 3129 1 0x1b, opAt 3130 .SUB,
   pushAt 3131 1 0x8, opAt 3132 .MUL, opAt 3133 .SHR, pushAt 3134 1 0xb,
   opAt 3135 .MUL]

/-- Apply the correction to the expected word. -/
def straddleAddPath : List Located :=
  [opAt 3136 (.Dup ⟨1, by decide⟩), opAt 3137 (.Dup ⟨9, by decide⟩),
   opAt 3138 .AND, opAt 3139 (.Dup ⟨1, by decide⟩), opAt 3140 .ADD,
   opAt 3141 (.Dup ⟨2, by decide⟩), opAt 3142 (.Dup ⟨12, by decide⟩),
   opAt 3143 .AND, opAt 3144 .XOR, opAt 3145 (.Swap ⟨1, by decide⟩),
   opAt 3146 .POP, opAt 3147 .POP]

/-- Bump the scalar and rejoin the scan. -/
def straddleBackPath : List Located :=
  [opAt 3148 (.Dup ⟨2, by decide⟩), pushAt 3149 1 0xb, opAt 3150 .ADD,
   opAt 3151 (.Swap ⟨2, by decide⟩), opAt 3152 .POP, pushAt 3153 2 0x1401,
   opAt 3154 .JUMP]


@[simp] theorem pc2903 : Artifact.submissionArtifact.instructionPC 3036 = 4956 := by rfl
@[simp] theorem pc2904 : Artifact.submissionArtifact.instructionPC 3037 = 4957 := by rfl
@[simp] theorem pc2905 : Artifact.submissionArtifact.instructionPC 3038 = 4990 := by rfl
@[simp] theorem pc2906 : Artifact.submissionArtifact.instructionPC 3039 = 5023 := by rfl
@[simp] theorem pc2907 : Artifact.submissionArtifact.instructionPC 3040 = 5056 := by rfl
@[simp] theorem pc2908 : Artifact.submissionArtifact.instructionPC 3041 = 5089 := by rfl
@[simp] theorem pc2909 : Artifact.submissionArtifact.instructionPC 3042 = 5090 := by rfl
@[simp] theorem pc2910 : Artifact.submissionArtifact.instructionPC 3043 = 5091 := by rfl
@[simp] theorem pc2911 : Artifact.submissionArtifact.instructionPC 3044 = 5092 := by rfl
@[simp] theorem pc2912 : Artifact.submissionArtifact.instructionPC 3045 = 5093 := by rfl
@[simp] theorem pc2913 : Artifact.submissionArtifact.instructionPC 3046 = 5094 := by rfl
@[simp] theorem pc2914 : Artifact.submissionArtifact.instructionPC 3047 = 5095 := by rfl
@[simp] theorem pc2915 : Artifact.submissionArtifact.instructionPC 3048 = 5096 := by rfl
@[simp] theorem pc2916 : Artifact.submissionArtifact.instructionPC 3049 = 5097 := by rfl
@[simp] theorem pc2917 : Artifact.submissionArtifact.instructionPC 3050 = 5098 := by rfl
@[simp] theorem pc2918 : Artifact.submissionArtifact.instructionPC 3051 = 5099 := by rfl
@[simp] theorem pc2919 : Artifact.submissionArtifact.instructionPC 3052 = 5100 := by rfl
@[simp] theorem pc2920 : Artifact.submissionArtifact.instructionPC 3053 = 5101 := by rfl
@[simp] theorem pc2921 : Artifact.submissionArtifact.instructionPC 3054 = 5102 := by rfl
@[simp] theorem pc2922 : Artifact.submissionArtifact.instructionPC 3055 = 5103 := by rfl
@[simp] theorem pc2923 : Artifact.submissionArtifact.instructionPC 3056 = 5104 := by rfl
@[simp] theorem pc2924 : Artifact.submissionArtifact.instructionPC 3057 = 5105 := by rfl
@[simp] theorem pc2925 : Artifact.submissionArtifact.instructionPC 3058 = 5106 := by rfl
@[simp] theorem pc2926 : Artifact.submissionArtifact.instructionPC 3059 = 5107 := by rfl
@[simp] theorem pc2927 : Artifact.submissionArtifact.instructionPC 3060 = 5108 := by rfl
@[simp] theorem pc2928 : Artifact.submissionArtifact.instructionPC 3061 = 5109 := by rfl
@[simp] theorem pc2929 : Artifact.submissionArtifact.instructionPC 3062 = 5110 := by rfl
@[simp] theorem pc2930 : Artifact.submissionArtifact.instructionPC 3063 = 5111 := by rfl
@[simp] theorem pc2931 : Artifact.submissionArtifact.instructionPC 3064 = 5113 := by rfl
@[simp] theorem pc2932 : Artifact.submissionArtifact.instructionPC 3065 = 5114 := by rfl
@[simp] theorem pc2933 : Artifact.submissionArtifact.instructionPC 3066 = 5116 := by rfl
@[simp] theorem pc2934 : Artifact.submissionArtifact.instructionPC 3067 = 5117 := by rfl
@[simp] theorem pc2935 : Artifact.submissionArtifact.instructionPC 3068 = 5120 := by rfl
@[simp] theorem pc2936 : Artifact.submissionArtifact.instructionPC 3069 = 5121 := by rfl
@[simp] theorem pc2937 : Artifact.submissionArtifact.instructionPC 3070 = 5122 := by rfl
@[simp] theorem pc2938 : Artifact.submissionArtifact.instructionPC 3071 = 5123 := by rfl
@[simp] theorem pc2939 : Artifact.submissionArtifact.instructionPC 3072 = 5124 := by rfl
@[simp] theorem pc2940 : Artifact.submissionArtifact.instructionPC 3073 = 5125 := by rfl
@[simp] theorem pc2941 : Artifact.submissionArtifact.instructionPC 3074 = 5126 := by rfl
@[simp] theorem pc2942 : Artifact.submissionArtifact.instructionPC 3075 = 5127 := by rfl
@[simp] theorem pc2943 : Artifact.submissionArtifact.instructionPC 3076 = 5128 := by rfl
@[simp] theorem pc2944 : Artifact.submissionArtifact.instructionPC 3077 = 5129 := by rfl
@[simp] theorem pc2945 : Artifact.submissionArtifact.instructionPC 3078 = 5130 := by rfl
@[simp] theorem pc2946 : Artifact.submissionArtifact.instructionPC 3079 = 5131 := by rfl
@[simp] theorem pc2947 : Artifact.submissionArtifact.instructionPC 3080 = 5133 := by rfl
@[simp] theorem pc2948 : Artifact.submissionArtifact.instructionPC 3081 = 5134 := by rfl
@[simp] theorem pc2949 : Artifact.submissionArtifact.instructionPC 3082 = 5136 := by rfl
@[simp] theorem pc2950 : Artifact.submissionArtifact.instructionPC 3083 = 5137 := by rfl
@[simp] theorem pc2951 : Artifact.submissionArtifact.instructionPC 3084 = 5138 := by rfl
@[simp] theorem pc2952 : Artifact.submissionArtifact.instructionPC 3085 = 5139 := by rfl
@[simp] theorem pc2953 : Artifact.submissionArtifact.instructionPC 3086 = 5140 := by rfl
@[simp] theorem pc2954 : Artifact.submissionArtifact.instructionPC 3087 = 5142 := by rfl
@[simp] theorem pc2955 : Artifact.submissionArtifact.instructionPC 3088 = 5143 := by rfl
@[simp] theorem pc2956 : Artifact.submissionArtifact.instructionPC 3089 = 5144 := by rfl
@[simp] theorem pc2957 : Artifact.submissionArtifact.instructionPC 3090 = 5145 := by rfl
@[simp] theorem pc2958 : Artifact.submissionArtifact.instructionPC 3091 = 5146 := by rfl
@[simp] theorem pc2959 : Artifact.submissionArtifact.instructionPC 3092 = 5149 := by rfl
@[simp] theorem pc2960 : Artifact.submissionArtifact.instructionPC 3093 = 5150 := by rfl
@[simp] theorem pc2961 : Artifact.submissionArtifact.instructionPC 3094 = 5153 := by rfl
@[simp] theorem pc2962 : Artifact.submissionArtifact.instructionPC 3095 = 5154 := by rfl
@[simp] theorem pc2963 : Artifact.submissionArtifact.instructionPC 3096 = 5157 := by rfl
@[simp] theorem pc2964 : Artifact.submissionArtifact.instructionPC 3097 = 5158 := by rfl
@[simp] theorem pc2965 : Artifact.submissionArtifact.instructionPC 3098 = 5167 := by rfl
@[simp] theorem pc2966 : Artifact.submissionArtifact.instructionPC 3099 = 5169 := by rfl
@[simp] theorem pc2967 : Artifact.submissionArtifact.instructionPC 3100 = 5170 := by rfl
@[simp] theorem pc2968 : Artifact.submissionArtifact.instructionPC 3101 = 5171 := by rfl
@[simp] theorem pc2969 : Artifact.submissionArtifact.instructionPC 3102 = 5172 := by rfl
@[simp] theorem pc2970 : Artifact.submissionArtifact.instructionPC 3103 = 5173 := by rfl
@[simp] theorem pc2971 : Artifact.submissionArtifact.instructionPC 3104 = 5174 := by rfl
@[simp] theorem pc2972 : Artifact.submissionArtifact.instructionPC 3105 = 5175 := by rfl
@[simp] theorem pc2973 : Artifact.submissionArtifact.instructionPC 3106 = 5176 := by rfl
@[simp] theorem pc2974 : Artifact.submissionArtifact.instructionPC 3107 = 5177 := by rfl
@[simp] theorem pc2975 : Artifact.submissionArtifact.instructionPC 3108 = 5178 := by rfl
@[simp] theorem pc2976 : Artifact.submissionArtifact.instructionPC 3109 = 5179 := by rfl
@[simp] theorem pc2977 : Artifact.submissionArtifact.instructionPC 3110 = 5180 := by rfl
@[simp] theorem pc2978 : Artifact.submissionArtifact.instructionPC 3111 = 5181 := by rfl
@[simp] theorem pc2979 : Artifact.submissionArtifact.instructionPC 3112 = 5182 := by rfl
@[simp] theorem pc2980 : Artifact.submissionArtifact.instructionPC 3113 = 5183 := by rfl
@[simp] theorem pc2981 : Artifact.submissionArtifact.instructionPC 3114 = 5184 := by rfl
@[simp] theorem pc2982 : Artifact.submissionArtifact.instructionPC 3115 = 5187 := by rfl
@[simp] theorem pc2983 : Artifact.submissionArtifact.instructionPC 3116 = 5188 := by rfl
@[simp] theorem pc2984 : Artifact.submissionArtifact.instructionPC 3117 = 5209 := by rfl
@[simp] theorem pc2985 : Artifact.submissionArtifact.instructionPC 3118 = 5210 := by rfl
@[simp] theorem pc2986 : Artifact.submissionArtifact.instructionPC 3119 = 5211 := by rfl
@[simp] theorem pc2987 : Artifact.submissionArtifact.instructionPC 3120 = 5213 := by rfl
@[simp] theorem pc2988 : Artifact.submissionArtifact.instructionPC 3121 = 5214 := by rfl
@[simp] theorem pc2989 : Artifact.submissionArtifact.instructionPC 3122 = 5215 := by rfl
@[simp] theorem pc2990 : Artifact.submissionArtifact.instructionPC 3123 = 5216 := by rfl
@[simp] theorem pc2991 : Artifact.submissionArtifact.instructionPC 3124 = 5217 := by rfl
@[simp] theorem pc2992 : Artifact.submissionArtifact.instructionPC 3125 = 5218 := by rfl
@[simp] theorem pc2993 : Artifact.submissionArtifact.instructionPC 3126 = 5220 := by rfl
@[simp] theorem pc2994 : Artifact.submissionArtifact.instructionPC 3127 = 5221 := by rfl
@[simp] theorem pc2995 : Artifact.submissionArtifact.instructionPC 3128 = 5223 := by rfl
@[simp] theorem pc2996 : Artifact.submissionArtifact.instructionPC 3129 = 5224 := by rfl
@[simp] theorem pc2997 : Artifact.submissionArtifact.instructionPC 3130 = 5226 := by rfl
@[simp] theorem pc2998 : Artifact.submissionArtifact.instructionPC 3131 = 5227 := by rfl
@[simp] theorem pc2999 : Artifact.submissionArtifact.instructionPC 3132 = 5229 := by rfl
@[simp] theorem pc3000 : Artifact.submissionArtifact.instructionPC 3133 = 5230 := by rfl
@[simp] theorem pc3001 : Artifact.submissionArtifact.instructionPC 3134 = 5231 := by rfl
@[simp] theorem pc3002 : Artifact.submissionArtifact.instructionPC 3135 = 5233 := by rfl
@[simp] theorem pc3003 : Artifact.submissionArtifact.instructionPC 3136 = 5234 := by rfl
@[simp] theorem pc3004 : Artifact.submissionArtifact.instructionPC 3137 = 5235 := by rfl
@[simp] theorem pc3005 : Artifact.submissionArtifact.instructionPC 3138 = 5236 := by rfl
@[simp] theorem pc3006 : Artifact.submissionArtifact.instructionPC 3139 = 5237 := by rfl
@[simp] theorem pc3007 : Artifact.submissionArtifact.instructionPC 3140 = 5238 := by rfl
@[simp] theorem pc3008 : Artifact.submissionArtifact.instructionPC 3141 = 5239 := by rfl
@[simp] theorem pc3009 : Artifact.submissionArtifact.instructionPC 3142 = 5240 := by rfl
@[simp] theorem pc3010 : Artifact.submissionArtifact.instructionPC 3143 = 5241 := by rfl
@[simp] theorem pc3011 : Artifact.submissionArtifact.instructionPC 3144 = 5242 := by rfl
@[simp] theorem pc3012 : Artifact.submissionArtifact.instructionPC 3145 = 5243 := by rfl
@[simp] theorem pc3013 : Artifact.submissionArtifact.instructionPC 3146 = 5244 := by rfl
@[simp] theorem pc3014 : Artifact.submissionArtifact.instructionPC 3147 = 5245 := by rfl
@[simp] theorem pc3015 : Artifact.submissionArtifact.instructionPC 3148 = 5246 := by rfl
@[simp] theorem pc3016 : Artifact.submissionArtifact.instructionPC 3149 = 5247 := by rfl
@[simp] theorem pc3017 : Artifact.submissionArtifact.instructionPC 3150 = 5249 := by rfl
@[simp] theorem pc3018 : Artifact.submissionArtifact.instructionPC 3151 = 5250 := by rfl
@[simp] theorem pc3019 : Artifact.submissionArtifact.instructionPC 3152 = 5251 := by rfl
@[simp] theorem pc3020 : Artifact.submissionArtifact.instructionPC 3153 = 5252 := by rfl
@[simp] theorem pc3021 : Artifact.submissionArtifact.instructionPC 3154 = 5255 := by rfl
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan
