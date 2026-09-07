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
  [opAt 3115 .JUMPDEST,
   pushAt 3116 32 0x8080808080808080808080808080808080808080808080808080808080808080,
   pushAt 3117 32 0x072c51769bc0e50a2f54799ec3e80d32577ca1c6eb10355a7fa4c9ee13385d82,
   pushAt 3118 32 0x7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f,
   pushAt 3119 32 0x0101010101010101010101010101010101010101010101010101010101010101,
   opAt 3120 (.Dup ⟨2, by decide⟩), opAt 3121 (.Dup ⟨2, by decide⟩),
   opAt 3122 .AND, pushAt 3123 0 0, pushAt 3124 0 0, pushAt 3125 0 0]

/-- Derive the expected word and test for a straddler. -/
def wordPath : List Located :=
  [opAt 3126 .JUMPDEST, opAt 3127 (.Dup ⟨0, by decide⟩),
   opAt 3128 (.Dup ⟨5, by decide⟩), opAt 3129 .MUL,
   opAt 3130 (.Dup ⟨0, by decide⟩), opAt 3131 (.Dup ⟨7, by decide⟩),
   opAt 3132 .AND, opAt 3133 (.Dup ⟨5, by decide⟩), opAt 3134 .ADD,
   opAt 3135 (.Dup ⟨1, by decide⟩), opAt 3136 (.Dup ⟨9, by decide⟩),
   opAt 3137 .XOR, opAt 3138 (.Dup ⟨10, by decide⟩), opAt 3139 .AND,
   opAt 3140 .XOR, opAt 3141 (.Dup ⟨3, by decide⟩), pushAt 3142 1 0xff,
   opAt 3143 .AND, pushAt 3144 1 0xe0, opAt 3145 .EQ, pushAt 3146 2 0x1490,
   opAt 3147 .JUMPI]

/-- Fold one word into the accumulator and advance. -/
def comparePath : List Located :=
  [opAt 3148 .JUMPDEST, opAt 3149 (.Dup ⟨3, by decide⟩),
   opAt 3150 .CALLDATALOAD, opAt 3151 .XOR, opAt 3152 (.Dup ⟨4, by decide⟩),
   opAt 3153 .OR, opAt 3154 (.Swap ⟨3, by decide⟩), opAt 3155 .POP,
   opAt 3156 .POP, opAt 3157 .JUMPDEST, pushAt 3158 1 0xa0,
   opAt 3159 .ADD, pushAt 3160 1 0xff, opAt 3161 .AND,
   opAt 3162 .JUMPDEST, opAt 3163 .JUMPDEST,
   opAt 3164 (.Dup ⟨1, by decide⟩), pushAt 3165 1 0x20, opAt 3166 .ADD,
   opAt 3167 (.Swap ⟨1, by decide⟩), opAt 3168 .POP,
   opAt 3169 (.Dup ⟨1, by decide⟩), pushAt 3170 2 0x03e0, opAt 3171 .GT,
   pushAt 3172 2 0x1418, opAt 3173 .JUMPI]

/-- The padded tail word, the cleanup and the miss test. -/
def tailPath : List Located :=
  [pushAt 3174 2 0x03e0, opAt 3175 .CALLDATALOAD,
   pushAt 3176 8 0x88add2f71c41668b, pushAt 3177 1 0xc0, opAt 3178 .SHL,
   opAt 3179 .XOR, opAt 3180 (.Dup ⟨3, by decide⟩), opAt 3181 .OR,
   opAt 3182 (.Swap ⟨2, by decide⟩), opAt 3183 .POP,
   opAt 3184 (.Swap ⟨1, by decide⟩), opAt 3185 (.Swap ⟨6, by decide⟩),
   opAt 3186 .POP, opAt 3187 .POP, opAt 3188 .POP, opAt 3189 .POP,
   opAt 3190 .POP, opAt 3191 .POP, opAt 3192 .POP, pushAt 3193 2 0x03ee,
   opAt 3194 .JUMPI]

/-- Store and return the stored digest. -/
def returnPath : List Located :=
  [pushAt 3195 20 0x863c598588bd72a4babf36c6bb01f27bbdc0ecd4,
   pushAt 3196 0 0, opAt 3197 .MSTORE, pushAt 3198 1 0x20, pushAt 3199 0 0,
   opAt 3200 .RETURN]

/-- Shift the correction constant out of `M`. -/
def straddleCorrPath : List Located :=
  [opAt 3201 .JUMPDEST, opAt 3202 (.Dup ⟨6, by decide⟩),
   opAt 3203 (.Dup ⟨4, by decide⟩), pushAt 3204 1 0x08, opAt 3205 .SHR,
   pushAt 3206 1 0x05, opAt 3207 .MUL, pushAt 3208 1 0x1b, opAt 3209 .SUB,
   pushAt 3210 1 0x08, opAt 3211 .MUL, opAt 3212 .SHR, pushAt 3213 1 0x0b,
   opAt 3214 .MUL]

/-- Apply the correction to the expected word. -/
def straddleAddPath : List Located :=
  [opAt 3215 (.Dup ⟨1, by decide⟩), opAt 3216 (.Dup ⟨9, by decide⟩),
   opAt 3217 .AND, opAt 3218 (.Dup ⟨1, by decide⟩), opAt 3219 .ADD,
   opAt 3220 (.Dup ⟨2, by decide⟩), opAt 3221 (.Dup ⟨12, by decide⟩),
   opAt 3222 .AND, opAt 3223 .XOR, opAt 3224 (.Swap ⟨1, by decide⟩),
   opAt 3225 .POP, opAt 3226 .POP]

/-- Bump the scalar and rejoin the scan. -/
def straddleBackPath : List Located :=
  [opAt 3227 (.Dup ⟨2, by decide⟩), pushAt 3228 1 0x0b, opAt 3229 .ADD,
   opAt 3230 (.Swap ⟨2, by decide⟩), opAt 3231 .POP, pushAt 3232 2 0x1432,
   opAt 3233 .JUMP]


@[simp] theorem pc2903 : Artifact.submissionArtifact.instructionPC 3115 = 5005 := by rfl
@[simp] theorem pc2904 : Artifact.submissionArtifact.instructionPC 3116 = 5006 := by rfl
@[simp] theorem pc2905 : Artifact.submissionArtifact.instructionPC 3117 = 5039 := by rfl
@[simp] theorem pc2906 : Artifact.submissionArtifact.instructionPC 3118 = 5072 := by rfl
@[simp] theorem pc2907 : Artifact.submissionArtifact.instructionPC 3119 = 5105 := by rfl
@[simp] theorem pc2908 : Artifact.submissionArtifact.instructionPC 3120 = 5138 := by rfl
@[simp] theorem pc2909 : Artifact.submissionArtifact.instructionPC 3121 = 5139 := by rfl
@[simp] theorem pc2910 : Artifact.submissionArtifact.instructionPC 3122 = 5140 := by rfl
@[simp] theorem pc2911 : Artifact.submissionArtifact.instructionPC 3123 = 5141 := by rfl
@[simp] theorem pc2912 : Artifact.submissionArtifact.instructionPC 3124 = 5142 := by rfl
@[simp] theorem pc2913 : Artifact.submissionArtifact.instructionPC 3125 = 5143 := by rfl
@[simp] theorem pc2914 : Artifact.submissionArtifact.instructionPC 3126 = 5144 := by rfl
@[simp] theorem pc2915 : Artifact.submissionArtifact.instructionPC 3127 = 5145 := by rfl
@[simp] theorem pc2916 : Artifact.submissionArtifact.instructionPC 3128 = 5146 := by rfl
@[simp] theorem pc2917 : Artifact.submissionArtifact.instructionPC 3129 = 5147 := by rfl
@[simp] theorem pc2918 : Artifact.submissionArtifact.instructionPC 3130 = 5148 := by rfl
@[simp] theorem pc2919 : Artifact.submissionArtifact.instructionPC 3131 = 5149 := by rfl
@[simp] theorem pc2920 : Artifact.submissionArtifact.instructionPC 3132 = 5150 := by rfl
@[simp] theorem pc2921 : Artifact.submissionArtifact.instructionPC 3133 = 5151 := by rfl
@[simp] theorem pc2922 : Artifact.submissionArtifact.instructionPC 3134 = 5152 := by rfl
@[simp] theorem pc2923 : Artifact.submissionArtifact.instructionPC 3135 = 5153 := by rfl
@[simp] theorem pc2924 : Artifact.submissionArtifact.instructionPC 3136 = 5154 := by rfl
@[simp] theorem pc2925 : Artifact.submissionArtifact.instructionPC 3137 = 5155 := by rfl
@[simp] theorem pc2926 : Artifact.submissionArtifact.instructionPC 3138 = 5156 := by rfl
@[simp] theorem pc2927 : Artifact.submissionArtifact.instructionPC 3139 = 5157 := by rfl
@[simp] theorem pc2928 : Artifact.submissionArtifact.instructionPC 3140 = 5158 := by rfl
@[simp] theorem pc2929 : Artifact.submissionArtifact.instructionPC 3141 = 5159 := by rfl
@[simp] theorem pc2930 : Artifact.submissionArtifact.instructionPC 3142 = 5160 := by rfl
@[simp] theorem pc2931 : Artifact.submissionArtifact.instructionPC 3143 = 5162 := by rfl
@[simp] theorem pc2932 : Artifact.submissionArtifact.instructionPC 3144 = 5163 := by rfl
@[simp] theorem pc2933 : Artifact.submissionArtifact.instructionPC 3145 = 5165 := by rfl
@[simp] theorem pc2934 : Artifact.submissionArtifact.instructionPC 3146 = 5166 := by rfl
@[simp] theorem pc2935 : Artifact.submissionArtifact.instructionPC 3147 = 5169 := by rfl
@[simp] theorem pc2936 : Artifact.submissionArtifact.instructionPC 3148 = 5170 := by rfl
@[simp] theorem pc2937 : Artifact.submissionArtifact.instructionPC 3149 = 5171 := by rfl
@[simp] theorem pc2938 : Artifact.submissionArtifact.instructionPC 3150 = 5172 := by rfl
@[simp] theorem pc2939 : Artifact.submissionArtifact.instructionPC 3151 = 5173 := by rfl
@[simp] theorem pc2940 : Artifact.submissionArtifact.instructionPC 3152 = 5174 := by rfl
@[simp] theorem pc2941 : Artifact.submissionArtifact.instructionPC 3153 = 5175 := by rfl
@[simp] theorem pc2942 : Artifact.submissionArtifact.instructionPC 3154 = 5176 := by rfl
@[simp] theorem pc2943 : Artifact.submissionArtifact.instructionPC 3155 = 5177 := by rfl
@[simp] theorem pc2944 : Artifact.submissionArtifact.instructionPC 3156 = 5178 := by rfl
@[simp] theorem pc2945 : Artifact.submissionArtifact.instructionPC 3157 = 5179 := by rfl
@[simp] theorem pc2946 : Artifact.submissionArtifact.instructionPC 3158 = 5180 := by rfl
@[simp] theorem pc2947 : Artifact.submissionArtifact.instructionPC 3159 = 5182 := by rfl
@[simp] theorem pc2948 : Artifact.submissionArtifact.instructionPC 3160 = 5183 := by rfl
@[simp] theorem pc2949 : Artifact.submissionArtifact.instructionPC 3161 = 5185 := by rfl
@[simp] theorem pc2950 : Artifact.submissionArtifact.instructionPC 3162 = 5186 := by rfl
@[simp] theorem pc2951 : Artifact.submissionArtifact.instructionPC 3163 = 5187 := by rfl
@[simp] theorem pc2952 : Artifact.submissionArtifact.instructionPC 3164 = 5188 := by rfl
@[simp] theorem pc2953 : Artifact.submissionArtifact.instructionPC 3165 = 5189 := by rfl
@[simp] theorem pc2954 : Artifact.submissionArtifact.instructionPC 3166 = 5191 := by rfl
@[simp] theorem pc2955 : Artifact.submissionArtifact.instructionPC 3167 = 5192 := by rfl
@[simp] theorem pc2956 : Artifact.submissionArtifact.instructionPC 3168 = 5193 := by rfl
@[simp] theorem pc2957 : Artifact.submissionArtifact.instructionPC 3169 = 5194 := by rfl
@[simp] theorem pc2958 : Artifact.submissionArtifact.instructionPC 3170 = 5195 := by rfl
@[simp] theorem pc2959 : Artifact.submissionArtifact.instructionPC 3171 = 5198 := by rfl
@[simp] theorem pc2960 : Artifact.submissionArtifact.instructionPC 3172 = 5199 := by rfl
@[simp] theorem pc2961 : Artifact.submissionArtifact.instructionPC 3173 = 5202 := by rfl
@[simp] theorem pc2962 : Artifact.submissionArtifact.instructionPC 3174 = 5203 := by rfl
@[simp] theorem pc2963 : Artifact.submissionArtifact.instructionPC 3175 = 5206 := by rfl
@[simp] theorem pc2964 : Artifact.submissionArtifact.instructionPC 3176 = 5207 := by rfl
@[simp] theorem pc2965 : Artifact.submissionArtifact.instructionPC 3177 = 5216 := by rfl
@[simp] theorem pc2966 : Artifact.submissionArtifact.instructionPC 3178 = 5218 := by rfl
@[simp] theorem pc2967 : Artifact.submissionArtifact.instructionPC 3179 = 5219 := by rfl
@[simp] theorem pc2968 : Artifact.submissionArtifact.instructionPC 3180 = 5220 := by rfl
@[simp] theorem pc2969 : Artifact.submissionArtifact.instructionPC 3181 = 5221 := by rfl
@[simp] theorem pc2970 : Artifact.submissionArtifact.instructionPC 3182 = 5222 := by rfl
@[simp] theorem pc2971 : Artifact.submissionArtifact.instructionPC 3183 = 5223 := by rfl
@[simp] theorem pc2972 : Artifact.submissionArtifact.instructionPC 3184 = 5224 := by rfl
@[simp] theorem pc2973 : Artifact.submissionArtifact.instructionPC 3185 = 5225 := by rfl
@[simp] theorem pc2974 : Artifact.submissionArtifact.instructionPC 3186 = 5226 := by rfl
@[simp] theorem pc2975 : Artifact.submissionArtifact.instructionPC 3187 = 5227 := by rfl
@[simp] theorem pc2976 : Artifact.submissionArtifact.instructionPC 3188 = 5228 := by rfl
@[simp] theorem pc2977 : Artifact.submissionArtifact.instructionPC 3189 = 5229 := by rfl
@[simp] theorem pc2978 : Artifact.submissionArtifact.instructionPC 3190 = 5230 := by rfl
@[simp] theorem pc2979 : Artifact.submissionArtifact.instructionPC 3191 = 5231 := by rfl
@[simp] theorem pc2980 : Artifact.submissionArtifact.instructionPC 3192 = 5232 := by rfl
@[simp] theorem pc2981 : Artifact.submissionArtifact.instructionPC 3193 = 5233 := by rfl
@[simp] theorem pc2982 : Artifact.submissionArtifact.instructionPC 3194 = 5236 := by rfl
@[simp] theorem pc2983 : Artifact.submissionArtifact.instructionPC 3195 = 5237 := by rfl
@[simp] theorem pc2984 : Artifact.submissionArtifact.instructionPC 3196 = 5258 := by rfl
@[simp] theorem pc2985 : Artifact.submissionArtifact.instructionPC 3197 = 5259 := by rfl
@[simp] theorem pc2986 : Artifact.submissionArtifact.instructionPC 3198 = 5260 := by rfl
@[simp] theorem pc2987 : Artifact.submissionArtifact.instructionPC 3199 = 5262 := by rfl
@[simp] theorem pc2988 : Artifact.submissionArtifact.instructionPC 3200 = 5263 := by rfl
@[simp] theorem pc2989 : Artifact.submissionArtifact.instructionPC 3201 = 5264 := by rfl
@[simp] theorem pc2990 : Artifact.submissionArtifact.instructionPC 3202 = 5265 := by rfl
@[simp] theorem pc2991 : Artifact.submissionArtifact.instructionPC 3203 = 5266 := by rfl
@[simp] theorem pc2992 : Artifact.submissionArtifact.instructionPC 3204 = 5267 := by rfl
@[simp] theorem pc2993 : Artifact.submissionArtifact.instructionPC 3205 = 5269 := by rfl
@[simp] theorem pc2994 : Artifact.submissionArtifact.instructionPC 3206 = 5270 := by rfl
@[simp] theorem pc2995 : Artifact.submissionArtifact.instructionPC 3207 = 5272 := by rfl
@[simp] theorem pc2996 : Artifact.submissionArtifact.instructionPC 3208 = 5273 := by rfl
@[simp] theorem pc2997 : Artifact.submissionArtifact.instructionPC 3209 = 5275 := by rfl
@[simp] theorem pc2998 : Artifact.submissionArtifact.instructionPC 3210 = 5276 := by rfl
@[simp] theorem pc2999 : Artifact.submissionArtifact.instructionPC 3211 = 5278 := by rfl
@[simp] theorem pc3000 : Artifact.submissionArtifact.instructionPC 3212 = 5279 := by rfl
@[simp] theorem pc3001 : Artifact.submissionArtifact.instructionPC 3213 = 5280 := by rfl
@[simp] theorem pc3002 : Artifact.submissionArtifact.instructionPC 3214 = 5282 := by rfl
@[simp] theorem pc3003 : Artifact.submissionArtifact.instructionPC 3215 = 5283 := by rfl
@[simp] theorem pc3004 : Artifact.submissionArtifact.instructionPC 3216 = 5284 := by rfl
@[simp] theorem pc3005 : Artifact.submissionArtifact.instructionPC 3217 = 5285 := by rfl
@[simp] theorem pc3006 : Artifact.submissionArtifact.instructionPC 3218 = 5286 := by rfl
@[simp] theorem pc3007 : Artifact.submissionArtifact.instructionPC 3219 = 5287 := by rfl
@[simp] theorem pc3008 : Artifact.submissionArtifact.instructionPC 3220 = 5288 := by rfl
@[simp] theorem pc3009 : Artifact.submissionArtifact.instructionPC 3221 = 5289 := by rfl
@[simp] theorem pc3010 : Artifact.submissionArtifact.instructionPC 3222 = 5290 := by rfl
@[simp] theorem pc3011 : Artifact.submissionArtifact.instructionPC 3223 = 5291 := by rfl
@[simp] theorem pc3012 : Artifact.submissionArtifact.instructionPC 3224 = 5292 := by rfl
@[simp] theorem pc3013 : Artifact.submissionArtifact.instructionPC 3225 = 5293 := by rfl
@[simp] theorem pc3014 : Artifact.submissionArtifact.instructionPC 3226 = 5294 := by rfl
@[simp] theorem pc3015 : Artifact.submissionArtifact.instructionPC 3227 = 5295 := by rfl
@[simp] theorem pc3016 : Artifact.submissionArtifact.instructionPC 3228 = 5296 := by rfl
@[simp] theorem pc3017 : Artifact.submissionArtifact.instructionPC 3229 = 5298 := by rfl
@[simp] theorem pc3018 : Artifact.submissionArtifact.instructionPC 3230 = 5299 := by rfl
@[simp] theorem pc3019 : Artifact.submissionArtifact.instructionPC 3231 = 5300 := by rfl
@[simp] theorem pc3020 : Artifact.submissionArtifact.instructionPC 3232 = 5301 := by rfl
@[simp] theorem pc3021 : Artifact.submissionArtifact.instructionPC 3233 = 5304 := by rfl
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan
