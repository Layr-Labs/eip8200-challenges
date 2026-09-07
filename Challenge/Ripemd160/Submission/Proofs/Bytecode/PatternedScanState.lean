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
  [opAt 2995 .JUMPDEST,
   pushAt 2996 32 0x8080808080808080808080808080808080808080808080808080808080808080,
   pushAt 2997 32 0x072c51769bc0e50a2f54799ec3e80d32577ca1c6eb10355a7fa4c9ee13385d82,
   pushAt 2998 32 0x7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f,
   pushAt 2999 32 0x0101010101010101010101010101010101010101010101010101010101010101,
   opAt 3000 (.Dup ⟨2, by decide⟩), opAt 3001 (.Dup ⟨2, by decide⟩),
   opAt 3002 .AND, pushAt 3003 0 0, pushAt 3004 0 0, pushAt 3005 0 0]

/-- Derive the expected word and test for a straddler. -/
def wordPath : List Located :=
  [opAt 3006 .JUMPDEST, opAt 3007 (.Dup ⟨0, by decide⟩),
   opAt 3008 (.Dup ⟨5, by decide⟩), opAt 3009 .MUL,
   opAt 3010 (.Dup ⟨0, by decide⟩), opAt 3011 (.Dup ⟨7, by decide⟩),
   opAt 3012 .AND, opAt 3013 (.Dup ⟨5, by decide⟩), opAt 3014 .ADD,
   opAt 3015 (.Dup ⟨1, by decide⟩), opAt 3016 (.Dup ⟨9, by decide⟩),
   opAt 3017 .XOR, opAt 3018 (.Dup ⟨10, by decide⟩), opAt 3019 .AND,
   opAt 3020 .XOR, opAt 3021 (.Dup ⟨3, by decide⟩), pushAt 3022 1 0xff,
   opAt 3023 .AND, pushAt 3024 1 0xe0, opAt 3025 .EQ, pushAt 3026 2 0x1499,
   opAt 3027 .JUMPI]

/-- Fold one word into the accumulator and advance. -/
def comparePath : List Located :=
  [opAt 3028 .JUMPDEST, opAt 3029 (.Dup ⟨3, by decide⟩),
   opAt 3030 .CALLDATALOAD, opAt 3031 .XOR, opAt 3032 (.Dup ⟨4, by decide⟩),
   opAt 3033 .OR, opAt 3034 (.Swap ⟨3, by decide⟩), opAt 3035 .POP,
   opAt 3036 .POP, opAt 3037 .JUMPDEST, pushAt 3038 1 0xa0,
   opAt 3039 .ADD, pushAt 3040 1 0xff, opAt 3041 .AND,
   opAt 3042 .JUMPDEST, opAt 3043 .JUMPDEST,
   opAt 3044 (.Dup ⟨1, by decide⟩), pushAt 3045 1 0x20, opAt 3046 .ADD,
   opAt 3047 (.Swap ⟨1, by decide⟩), opAt 3048 .POP,
   opAt 3049 (.Dup ⟨1, by decide⟩), pushAt 3050 2 0x03e0, opAt 3051 .GT,
   pushAt 3052 2 0x1421, opAt 3053 .JUMPI]

/-- The padded tail word, the cleanup and the miss test. -/
def tailPath : List Located :=
  [pushAt 3054 2 0x03e0, opAt 3055 .CALLDATALOAD,
   pushAt 3056 8 0x88add2f71c41668b, pushAt 3057 1 0xc0, opAt 3058 .SHL,
   opAt 3059 .XOR, opAt 3060 (.Dup ⟨3, by decide⟩), opAt 3061 .OR,
   opAt 3062 (.Swap ⟨2, by decide⟩), opAt 3063 .POP,
   opAt 3064 (.Swap ⟨1, by decide⟩), opAt 3065 (.Swap ⟨6, by decide⟩),
   opAt 3066 .POP, opAt 3067 .POP, opAt 3068 .POP, opAt 3069 .POP,
   opAt 3070 .POP, opAt 3071 .POP, opAt 3072 .POP, pushAt 3073 2 0x03ee,
   opAt 3074 .JUMPI]

/-- Store and return the stored digest. -/
def returnPath : List Located :=
  [pushAt 3075 20 0x863c598588bd72a4babf36c6bb01f27bbdc0ecd4,
   pushAt 3076 0 0, opAt 3077 .MSTORE, pushAt 3078 1 0x20, pushAt 3079 0 0,
   opAt 3080 .RETURN]

/-- Shift the correction constant out of `M`. -/
def straddleCorrPath : List Located :=
  [opAt 3081 .JUMPDEST, opAt 3082 (.Dup ⟨6, by decide⟩),
   opAt 3083 (.Dup ⟨4, by decide⟩), pushAt 3084 1 0x08, opAt 3085 .SHR,
   pushAt 3086 1 0x05, opAt 3087 .MUL, pushAt 3088 1 0x1b, opAt 3089 .SUB,
   pushAt 3090 1 0x08, opAt 3091 .MUL, opAt 3092 .SHR, pushAt 3093 1 0x0b,
   opAt 3094 .MUL]

/-- Apply the correction to the expected word. -/
def straddleAddPath : List Located :=
  [opAt 3095 (.Dup ⟨1, by decide⟩), opAt 3096 (.Dup ⟨9, by decide⟩),
   opAt 3097 .AND, opAt 3098 (.Dup ⟨1, by decide⟩), opAt 3099 .ADD,
   opAt 3100 (.Dup ⟨2, by decide⟩), opAt 3101 (.Dup ⟨12, by decide⟩),
   opAt 3102 .AND, opAt 3103 .XOR, opAt 3104 (.Swap ⟨1, by decide⟩),
   opAt 3105 .POP, opAt 3106 .POP]

/-- Bump the scalar and rejoin the scan. -/
def straddleBackPath : List Located :=
  [opAt 3107 (.Dup ⟨2, by decide⟩), pushAt 3108 1 0x0b, opAt 3109 .ADD,
   opAt 3110 (.Swap ⟨2, by decide⟩), opAt 3111 .POP, pushAt 3112 2 0x143b,
   opAt 3113 .JUMP]


@[simp] theorem pc2903 : Artifact.submissionArtifact.instructionPC 2995 = 5014 := by rfl
@[simp] theorem pc2904 : Artifact.submissionArtifact.instructionPC 2996 = 5015 := by rfl
@[simp] theorem pc2905 : Artifact.submissionArtifact.instructionPC 2997 = 5048 := by rfl
@[simp] theorem pc2906 : Artifact.submissionArtifact.instructionPC 2998 = 5081 := by rfl
@[simp] theorem pc2907 : Artifact.submissionArtifact.instructionPC 2999 = 5114 := by rfl
@[simp] theorem pc2908 : Artifact.submissionArtifact.instructionPC 3000 = 5147 := by rfl
@[simp] theorem pc2909 : Artifact.submissionArtifact.instructionPC 3001 = 5148 := by rfl
@[simp] theorem pc2910 : Artifact.submissionArtifact.instructionPC 3002 = 5149 := by rfl
@[simp] theorem pc2911 : Artifact.submissionArtifact.instructionPC 3003 = 5150 := by rfl
@[simp] theorem pc2912 : Artifact.submissionArtifact.instructionPC 3004 = 5151 := by rfl
@[simp] theorem pc2913 : Artifact.submissionArtifact.instructionPC 3005 = 5152 := by rfl
@[simp] theorem pc2914 : Artifact.submissionArtifact.instructionPC 3006 = 5153 := by rfl
@[simp] theorem pc2915 : Artifact.submissionArtifact.instructionPC 3007 = 5154 := by rfl
@[simp] theorem pc2916 : Artifact.submissionArtifact.instructionPC 3008 = 5155 := by rfl
@[simp] theorem pc2917 : Artifact.submissionArtifact.instructionPC 3009 = 5156 := by rfl
@[simp] theorem pc2918 : Artifact.submissionArtifact.instructionPC 3010 = 5157 := by rfl
@[simp] theorem pc2919 : Artifact.submissionArtifact.instructionPC 3011 = 5158 := by rfl
@[simp] theorem pc2920 : Artifact.submissionArtifact.instructionPC 3012 = 5159 := by rfl
@[simp] theorem pc2921 : Artifact.submissionArtifact.instructionPC 3013 = 5160 := by rfl
@[simp] theorem pc2922 : Artifact.submissionArtifact.instructionPC 3014 = 5161 := by rfl
@[simp] theorem pc2923 : Artifact.submissionArtifact.instructionPC 3015 = 5162 := by rfl
@[simp] theorem pc2924 : Artifact.submissionArtifact.instructionPC 3016 = 5163 := by rfl
@[simp] theorem pc2925 : Artifact.submissionArtifact.instructionPC 3017 = 5164 := by rfl
@[simp] theorem pc2926 : Artifact.submissionArtifact.instructionPC 3018 = 5165 := by rfl
@[simp] theorem pc2927 : Artifact.submissionArtifact.instructionPC 3019 = 5166 := by rfl
@[simp] theorem pc2928 : Artifact.submissionArtifact.instructionPC 3020 = 5167 := by rfl
@[simp] theorem pc2929 : Artifact.submissionArtifact.instructionPC 3021 = 5168 := by rfl
@[simp] theorem pc2930 : Artifact.submissionArtifact.instructionPC 3022 = 5169 := by rfl
@[simp] theorem pc2931 : Artifact.submissionArtifact.instructionPC 3023 = 5171 := by rfl
@[simp] theorem pc2932 : Artifact.submissionArtifact.instructionPC 3024 = 5172 := by rfl
@[simp] theorem pc2933 : Artifact.submissionArtifact.instructionPC 3025 = 5174 := by rfl
@[simp] theorem pc2934 : Artifact.submissionArtifact.instructionPC 3026 = 5175 := by rfl
@[simp] theorem pc2935 : Artifact.submissionArtifact.instructionPC 3027 = 5178 := by rfl
@[simp] theorem pc2936 : Artifact.submissionArtifact.instructionPC 3028 = 5179 := by rfl
@[simp] theorem pc2937 : Artifact.submissionArtifact.instructionPC 3029 = 5180 := by rfl
@[simp] theorem pc2938 : Artifact.submissionArtifact.instructionPC 3030 = 5181 := by rfl
@[simp] theorem pc2939 : Artifact.submissionArtifact.instructionPC 3031 = 5182 := by rfl
@[simp] theorem pc2940 : Artifact.submissionArtifact.instructionPC 3032 = 5183 := by rfl
@[simp] theorem pc2941 : Artifact.submissionArtifact.instructionPC 3033 = 5184 := by rfl
@[simp] theorem pc2942 : Artifact.submissionArtifact.instructionPC 3034 = 5185 := by rfl
@[simp] theorem pc2943 : Artifact.submissionArtifact.instructionPC 3035 = 5186 := by rfl
@[simp] theorem pc2944 : Artifact.submissionArtifact.instructionPC 3036 = 5187 := by rfl
@[simp] theorem pc2945 : Artifact.submissionArtifact.instructionPC 3037 = 5188 := by rfl
@[simp] theorem pc2946 : Artifact.submissionArtifact.instructionPC 3038 = 5189 := by rfl
@[simp] theorem pc2947 : Artifact.submissionArtifact.instructionPC 3039 = 5191 := by rfl
@[simp] theorem pc2948 : Artifact.submissionArtifact.instructionPC 3040 = 5192 := by rfl
@[simp] theorem pc2949 : Artifact.submissionArtifact.instructionPC 3041 = 5194 := by rfl
@[simp] theorem pc2950 : Artifact.submissionArtifact.instructionPC 3042 = 5195 := by rfl
@[simp] theorem pc2951 : Artifact.submissionArtifact.instructionPC 3043 = 5196 := by rfl
@[simp] theorem pc2952 : Artifact.submissionArtifact.instructionPC 3044 = 5197 := by rfl
@[simp] theorem pc2953 : Artifact.submissionArtifact.instructionPC 3045 = 5198 := by rfl
@[simp] theorem pc2954 : Artifact.submissionArtifact.instructionPC 3046 = 5200 := by rfl
@[simp] theorem pc2955 : Artifact.submissionArtifact.instructionPC 3047 = 5201 := by rfl
@[simp] theorem pc2956 : Artifact.submissionArtifact.instructionPC 3048 = 5202 := by rfl
@[simp] theorem pc2957 : Artifact.submissionArtifact.instructionPC 3049 = 5203 := by rfl
@[simp] theorem pc2958 : Artifact.submissionArtifact.instructionPC 3050 = 5204 := by rfl
@[simp] theorem pc2959 : Artifact.submissionArtifact.instructionPC 3051 = 5207 := by rfl
@[simp] theorem pc2960 : Artifact.submissionArtifact.instructionPC 3052 = 5208 := by rfl
@[simp] theorem pc2961 : Artifact.submissionArtifact.instructionPC 3053 = 5211 := by rfl
@[simp] theorem pc2962 : Artifact.submissionArtifact.instructionPC 3054 = 5212 := by rfl
@[simp] theorem pc2963 : Artifact.submissionArtifact.instructionPC 3055 = 5215 := by rfl
@[simp] theorem pc2964 : Artifact.submissionArtifact.instructionPC 3056 = 5216 := by rfl
@[simp] theorem pc2965 : Artifact.submissionArtifact.instructionPC 3057 = 5225 := by rfl
@[simp] theorem pc2966 : Artifact.submissionArtifact.instructionPC 3058 = 5227 := by rfl
@[simp] theorem pc2967 : Artifact.submissionArtifact.instructionPC 3059 = 5228 := by rfl
@[simp] theorem pc2968 : Artifact.submissionArtifact.instructionPC 3060 = 5229 := by rfl
@[simp] theorem pc2969 : Artifact.submissionArtifact.instructionPC 3061 = 5230 := by rfl
@[simp] theorem pc2970 : Artifact.submissionArtifact.instructionPC 3062 = 5231 := by rfl
@[simp] theorem pc2971 : Artifact.submissionArtifact.instructionPC 3063 = 5232 := by rfl
@[simp] theorem pc2972 : Artifact.submissionArtifact.instructionPC 3064 = 5233 := by rfl
@[simp] theorem pc2973 : Artifact.submissionArtifact.instructionPC 3065 = 5234 := by rfl
@[simp] theorem pc2974 : Artifact.submissionArtifact.instructionPC 3066 = 5235 := by rfl
@[simp] theorem pc2975 : Artifact.submissionArtifact.instructionPC 3067 = 5236 := by rfl
@[simp] theorem pc2976 : Artifact.submissionArtifact.instructionPC 3068 = 5237 := by rfl
@[simp] theorem pc2977 : Artifact.submissionArtifact.instructionPC 3069 = 5238 := by rfl
@[simp] theorem pc2978 : Artifact.submissionArtifact.instructionPC 3070 = 5239 := by rfl
@[simp] theorem pc2979 : Artifact.submissionArtifact.instructionPC 3071 = 5240 := by rfl
@[simp] theorem pc2980 : Artifact.submissionArtifact.instructionPC 3072 = 5241 := by rfl
@[simp] theorem pc2981 : Artifact.submissionArtifact.instructionPC 3073 = 5242 := by rfl
@[simp] theorem pc2982 : Artifact.submissionArtifact.instructionPC 3074 = 5245 := by rfl
@[simp] theorem pc2983 : Artifact.submissionArtifact.instructionPC 3075 = 5246 := by rfl
@[simp] theorem pc2984 : Artifact.submissionArtifact.instructionPC 3076 = 5267 := by rfl
@[simp] theorem pc2985 : Artifact.submissionArtifact.instructionPC 3077 = 5268 := by rfl
@[simp] theorem pc2986 : Artifact.submissionArtifact.instructionPC 3078 = 5269 := by rfl
@[simp] theorem pc2987 : Artifact.submissionArtifact.instructionPC 3079 = 5271 := by rfl
@[simp] theorem pc2988 : Artifact.submissionArtifact.instructionPC 3080 = 5272 := by rfl
@[simp] theorem pc2989 : Artifact.submissionArtifact.instructionPC 3081 = 5273 := by rfl
@[simp] theorem pc2990 : Artifact.submissionArtifact.instructionPC 3082 = 5274 := by rfl
@[simp] theorem pc2991 : Artifact.submissionArtifact.instructionPC 3083 = 5275 := by rfl
@[simp] theorem pc2992 : Artifact.submissionArtifact.instructionPC 3084 = 5276 := by rfl
@[simp] theorem pc2993 : Artifact.submissionArtifact.instructionPC 3085 = 5278 := by rfl
@[simp] theorem pc2994 : Artifact.submissionArtifact.instructionPC 3086 = 5279 := by rfl
@[simp] theorem pc2995 : Artifact.submissionArtifact.instructionPC 3087 = 5281 := by rfl
@[simp] theorem pc2996 : Artifact.submissionArtifact.instructionPC 3088 = 5282 := by rfl
@[simp] theorem pc2997 : Artifact.submissionArtifact.instructionPC 3089 = 5284 := by rfl
@[simp] theorem pc2998 : Artifact.submissionArtifact.instructionPC 3090 = 5285 := by rfl
@[simp] theorem pc2999 : Artifact.submissionArtifact.instructionPC 3091 = 5287 := by rfl
@[simp] theorem pc3000 : Artifact.submissionArtifact.instructionPC 3092 = 5288 := by rfl
@[simp] theorem pc3001 : Artifact.submissionArtifact.instructionPC 3093 = 5289 := by rfl
@[simp] theorem pc3002 : Artifact.submissionArtifact.instructionPC 3094 = 5291 := by rfl
@[simp] theorem pc3003 : Artifact.submissionArtifact.instructionPC 3095 = 5292 := by rfl
@[simp] theorem pc3004 : Artifact.submissionArtifact.instructionPC 3096 = 5293 := by rfl
@[simp] theorem pc3005 : Artifact.submissionArtifact.instructionPC 3097 = 5294 := by rfl
@[simp] theorem pc3006 : Artifact.submissionArtifact.instructionPC 3098 = 5295 := by rfl
@[simp] theorem pc3007 : Artifact.submissionArtifact.instructionPC 3099 = 5296 := by rfl
@[simp] theorem pc3008 : Artifact.submissionArtifact.instructionPC 3100 = 5297 := by rfl
@[simp] theorem pc3009 : Artifact.submissionArtifact.instructionPC 3101 = 5298 := by rfl
@[simp] theorem pc3010 : Artifact.submissionArtifact.instructionPC 3102 = 5299 := by rfl
@[simp] theorem pc3011 : Artifact.submissionArtifact.instructionPC 3103 = 5300 := by rfl
@[simp] theorem pc3012 : Artifact.submissionArtifact.instructionPC 3104 = 5301 := by rfl
@[simp] theorem pc3013 : Artifact.submissionArtifact.instructionPC 3105 = 5302 := by rfl
@[simp] theorem pc3014 : Artifact.submissionArtifact.instructionPC 3106 = 5303 := by rfl
@[simp] theorem pc3015 : Artifact.submissionArtifact.instructionPC 3107 = 5304 := by rfl
@[simp] theorem pc3016 : Artifact.submissionArtifact.instructionPC 3108 = 5305 := by rfl
@[simp] theorem pc3017 : Artifact.submissionArtifact.instructionPC 3109 = 5307 := by rfl
@[simp] theorem pc3018 : Artifact.submissionArtifact.instructionPC 3110 = 5308 := by rfl
@[simp] theorem pc3019 : Artifact.submissionArtifact.instructionPC 3111 = 5309 := by rfl
@[simp] theorem pc3020 : Artifact.submissionArtifact.instructionPC 3112 = 5310 := by rfl
@[simp] theorem pc3021 : Artifact.submissionArtifact.instructionPC 3113 = 5313 := by rfl
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan
