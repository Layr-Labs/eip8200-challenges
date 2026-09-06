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
  [opAt 2890 .JUMPDEST,
   pushAt 2891 32 0x8080808080808080808080808080808080808080808080808080808080808080,
   pushAt 2892 32 0x072c51769bc0e50a2f54799ec3e80d32577ca1c6eb10355a7fa4c9ee13385d82,
   pushAt 2893 32 0x7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f,
   pushAt 2894 32 0x0101010101010101010101010101010101010101010101010101010101010101,
   opAt 2895 (.Dup ⟨2, by decide⟩), opAt 2896 (.Dup ⟨2, by decide⟩),
   opAt 2897 .AND, pushAt 2898 0 0, pushAt 2899 0 0, pushAt 2900 0 0]

/-- Derive the expected word and test for a straddler. -/
def wordPath : List Located :=
  [opAt 2901 .JUMPDEST, opAt 2902 (.Dup ⟨0, by decide⟩),
   opAt 2903 (.Dup ⟨5, by decide⟩), opAt 2904 .MUL,
   opAt 2905 (.Dup ⟨0, by decide⟩), opAt 2906 (.Dup ⟨7, by decide⟩),
   opAt 2907 .AND, opAt 2908 (.Dup ⟨5, by decide⟩), opAt 2909 .ADD,
   opAt 2910 (.Dup ⟨1, by decide⟩), opAt 2911 (.Dup ⟨9, by decide⟩),
   opAt 2912 .XOR, opAt 2913 (.Dup ⟨10, by decide⟩), opAt 2914 .AND,
   opAt 2915 .XOR, opAt 2916 (.Dup ⟨3, by decide⟩), pushAt 2917 1 0xff,
   opAt 2918 .AND, pushAt 2919 1 0xe0, opAt 2920 .EQ, pushAt 2921 2 0x14d3,
   opAt 2922 .JUMPI]

/-- Fold one word into the accumulator and advance. -/
def comparePath : List Located :=
  [opAt 2923 .JUMPDEST, opAt 2924 (.Dup ⟨3, by decide⟩),
   opAt 2925 .CALLDATALOAD, opAt 2926 .XOR, opAt 2927 (.Dup ⟨4, by decide⟩),
   opAt 2928 .OR, opAt 2929 (.Swap ⟨3, by decide⟩), opAt 2930 .POP,
   opAt 2931 .POP, opAt 2932 .JUMPDEST, pushAt 2933 1 0xa0,
   opAt 2934 .ADD, pushAt 2935 1 0xff, opAt 2936 .AND,
   opAt 2937 .JUMPDEST, opAt 2938 .JUMPDEST,
   opAt 2939 (.Swap ⟨0, by decide⟩), pushAt 2940 1 0x20, opAt 2941 .ADD,
   opAt 2942 (.Swap ⟨0, by decide⟩), opAt 2943 .JUMPDEST,
   opAt 2944 (.Dup ⟨1, by decide⟩), pushAt 2945 2 0x03e0, opAt 2946 .GT,
   pushAt 2947 2 0x145b, opAt 2948 .JUMPI]

/-- The padded tail word, the cleanup and the miss test. -/
def tailPath : List Located :=
  [pushAt 2949 2 0x03e0, opAt 2950 .CALLDATALOAD,
   pushAt 2951 8 0x88add2f71c41668b, pushAt 2952 1 0xc0, opAt 2953 .SHL,
   opAt 2954 .XOR, opAt 2955 (.Dup ⟨3, by decide⟩), opAt 2956 .OR,
   opAt 2957 (.Swap ⟨2, by decide⟩), opAt 2958 .POP,
   opAt 2959 (.Swap ⟨1, by decide⟩), opAt 2960 (.Swap ⟨6, by decide⟩),
   opAt 2961 .POP, opAt 2962 .POP, opAt 2963 .POP, opAt 2964 .POP,
   opAt 2965 .POP, opAt 2966 .POP, opAt 2967 .POP, pushAt 2968 2 0x03ee,
   opAt 2969 .JUMPI]

/-- Store and return the stored digest. -/
def returnPath : List Located :=
  [pushAt 2970 20 0x863c598588bd72a4babf36c6bb01f27bbdc0ecd4,
   pushAt 2971 0 0, opAt 2972 .MSTORE, pushAt 2973 1 0x20, pushAt 2974 0 0,
   opAt 2975 .RETURN]

/-- Shift the correction constant out of `M`. -/
def straddleCorrPath : List Located :=
  [opAt 2976 .JUMPDEST, opAt 2977 (.Dup ⟨6, by decide⟩),
   opAt 2978 (.Dup ⟨4, by decide⟩), pushAt 2979 1 0x08, opAt 2980 .SHR,
   pushAt 2981 1 0x05, opAt 2982 .MUL, pushAt 2983 1 0x1b, opAt 2984 .SUB,
   pushAt 2985 1 0x08, opAt 2986 .MUL, opAt 2987 .SHR, pushAt 2988 1 0x0b,
   opAt 2989 .MUL]

/-- Apply the correction to the expected word. -/
def straddleAddPath : List Located :=
  [opAt 2990 (.Dup ⟨1, by decide⟩), opAt 2991 (.Dup ⟨9, by decide⟩),
   opAt 2992 .AND, opAt 2993 (.Dup ⟨1, by decide⟩), opAt 2994 .ADD,
   opAt 2995 (.Dup ⟨2, by decide⟩), opAt 2996 (.Dup ⟨12, by decide⟩),
   opAt 2997 .AND, opAt 2998 .XOR, opAt 2999 (.Swap ⟨1, by decide⟩),
   opAt 3000 .POP, opAt 3001 .POP]

/-- Bump the scalar and rejoin the scan. -/
def straddleBackPath : List Located :=
  [opAt 3002 (.Dup ⟨2, by decide⟩), pushAt 3003 1 0x0b, opAt 3004 .ADD,
   opAt 3005 (.Swap ⟨2, by decide⟩), opAt 3006 .POP, pushAt 3007 2 0x1475,
   opAt 3008 .JUMP]


@[simp] theorem pc2903 : Artifact.submissionArtifact.instructionPC 2890 = 5072 := by rfl
@[simp] theorem pc2904 : Artifact.submissionArtifact.instructionPC 2891 = 5073 := by rfl
@[simp] theorem pc2905 : Artifact.submissionArtifact.instructionPC 2892 = 5106 := by rfl
@[simp] theorem pc2906 : Artifact.submissionArtifact.instructionPC 2893 = 5139 := by rfl
@[simp] theorem pc2907 : Artifact.submissionArtifact.instructionPC 2894 = 5172 := by rfl
@[simp] theorem pc2908 : Artifact.submissionArtifact.instructionPC 2895 = 5205 := by rfl
@[simp] theorem pc2909 : Artifact.submissionArtifact.instructionPC 2896 = 5206 := by rfl
@[simp] theorem pc2910 : Artifact.submissionArtifact.instructionPC 2897 = 5207 := by rfl
@[simp] theorem pc2911 : Artifact.submissionArtifact.instructionPC 2898 = 5208 := by rfl
@[simp] theorem pc2912 : Artifact.submissionArtifact.instructionPC 2899 = 5209 := by rfl
@[simp] theorem pc2913 : Artifact.submissionArtifact.instructionPC 2900 = 5210 := by rfl
@[simp] theorem pc2914 : Artifact.submissionArtifact.instructionPC 2901 = 5211 := by rfl
@[simp] theorem pc2915 : Artifact.submissionArtifact.instructionPC 2902 = 5212 := by rfl
@[simp] theorem pc2916 : Artifact.submissionArtifact.instructionPC 2903 = 5213 := by rfl
@[simp] theorem pc2917 : Artifact.submissionArtifact.instructionPC 2904 = 5214 := by rfl
@[simp] theorem pc2918 : Artifact.submissionArtifact.instructionPC 2905 = 5215 := by rfl
@[simp] theorem pc2919 : Artifact.submissionArtifact.instructionPC 2906 = 5216 := by rfl
@[simp] theorem pc2920 : Artifact.submissionArtifact.instructionPC 2907 = 5217 := by rfl
@[simp] theorem pc2921 : Artifact.submissionArtifact.instructionPC 2908 = 5218 := by rfl
@[simp] theorem pc2922 : Artifact.submissionArtifact.instructionPC 2909 = 5219 := by rfl
@[simp] theorem pc2923 : Artifact.submissionArtifact.instructionPC 2910 = 5220 := by rfl
@[simp] theorem pc2924 : Artifact.submissionArtifact.instructionPC 2911 = 5221 := by rfl
@[simp] theorem pc2925 : Artifact.submissionArtifact.instructionPC 2912 = 5222 := by rfl
@[simp] theorem pc2926 : Artifact.submissionArtifact.instructionPC 2913 = 5223 := by rfl
@[simp] theorem pc2927 : Artifact.submissionArtifact.instructionPC 2914 = 5224 := by rfl
@[simp] theorem pc2928 : Artifact.submissionArtifact.instructionPC 2915 = 5225 := by rfl
@[simp] theorem pc2929 : Artifact.submissionArtifact.instructionPC 2916 = 5226 := by rfl
@[simp] theorem pc2930 : Artifact.submissionArtifact.instructionPC 2917 = 5227 := by rfl
@[simp] theorem pc2931 : Artifact.submissionArtifact.instructionPC 2918 = 5229 := by rfl
@[simp] theorem pc2932 : Artifact.submissionArtifact.instructionPC 2919 = 5230 := by rfl
@[simp] theorem pc2933 : Artifact.submissionArtifact.instructionPC 2920 = 5232 := by rfl
@[simp] theorem pc2934 : Artifact.submissionArtifact.instructionPC 2921 = 5233 := by rfl
@[simp] theorem pc2935 : Artifact.submissionArtifact.instructionPC 2922 = 5236 := by rfl
@[simp] theorem pc2936 : Artifact.submissionArtifact.instructionPC 2923 = 5237 := by rfl
@[simp] theorem pc2937 : Artifact.submissionArtifact.instructionPC 2924 = 5238 := by rfl
@[simp] theorem pc2938 : Artifact.submissionArtifact.instructionPC 2925 = 5239 := by rfl
@[simp] theorem pc2939 : Artifact.submissionArtifact.instructionPC 2926 = 5240 := by rfl
@[simp] theorem pc2940 : Artifact.submissionArtifact.instructionPC 2927 = 5241 := by rfl
@[simp] theorem pc2941 : Artifact.submissionArtifact.instructionPC 2928 = 5242 := by rfl
@[simp] theorem pc2942 : Artifact.submissionArtifact.instructionPC 2929 = 5243 := by rfl
@[simp] theorem pc2943 : Artifact.submissionArtifact.instructionPC 2930 = 5244 := by rfl
@[simp] theorem pc2944 : Artifact.submissionArtifact.instructionPC 2931 = 5245 := by rfl
@[simp] theorem pc2945 : Artifact.submissionArtifact.instructionPC 2932 = 5246 := by rfl
@[simp] theorem pc2946 : Artifact.submissionArtifact.instructionPC 2933 = 5247 := by rfl
@[simp] theorem pc2947 : Artifact.submissionArtifact.instructionPC 2934 = 5249 := by rfl
@[simp] theorem pc2948 : Artifact.submissionArtifact.instructionPC 2935 = 5250 := by rfl
@[simp] theorem pc2949 : Artifact.submissionArtifact.instructionPC 2936 = 5252 := by rfl
@[simp] theorem pc2950 : Artifact.submissionArtifact.instructionPC 2937 = 5253 := by rfl
@[simp] theorem pc2951 : Artifact.submissionArtifact.instructionPC 2938 = 5254 := by rfl
@[simp] theorem pc2952 : Artifact.submissionArtifact.instructionPC 2939 = 5255 := by rfl
@[simp] theorem pc2953 : Artifact.submissionArtifact.instructionPC 2940 = 5256 := by rfl
@[simp] theorem pc2954 : Artifact.submissionArtifact.instructionPC 2941 = 5258 := by rfl
@[simp] theorem pc2955 : Artifact.submissionArtifact.instructionPC 2942 = 5259 := by rfl
@[simp] theorem pc2956 : Artifact.submissionArtifact.instructionPC 2943 = 5260 := by rfl
@[simp] theorem pc2957 : Artifact.submissionArtifact.instructionPC 2944 = 5261 := by rfl
@[simp] theorem pc2958 : Artifact.submissionArtifact.instructionPC 2945 = 5262 := by rfl
@[simp] theorem pc2959 : Artifact.submissionArtifact.instructionPC 2946 = 5265 := by rfl
@[simp] theorem pc2960 : Artifact.submissionArtifact.instructionPC 2947 = 5266 := by rfl
@[simp] theorem pc2961 : Artifact.submissionArtifact.instructionPC 2948 = 5269 := by rfl
@[simp] theorem pc2962 : Artifact.submissionArtifact.instructionPC 2949 = 5270 := by rfl
@[simp] theorem pc2963 : Artifact.submissionArtifact.instructionPC 2950 = 5273 := by rfl
@[simp] theorem pc2964 : Artifact.submissionArtifact.instructionPC 2951 = 5274 := by rfl
@[simp] theorem pc2965 : Artifact.submissionArtifact.instructionPC 2952 = 5283 := by rfl
@[simp] theorem pc2966 : Artifact.submissionArtifact.instructionPC 2953 = 5285 := by rfl
@[simp] theorem pc2967 : Artifact.submissionArtifact.instructionPC 2954 = 5286 := by rfl
@[simp] theorem pc2968 : Artifact.submissionArtifact.instructionPC 2955 = 5287 := by rfl
@[simp] theorem pc2969 : Artifact.submissionArtifact.instructionPC 2956 = 5288 := by rfl
@[simp] theorem pc2970 : Artifact.submissionArtifact.instructionPC 2957 = 5289 := by rfl
@[simp] theorem pc2971 : Artifact.submissionArtifact.instructionPC 2958 = 5290 := by rfl
@[simp] theorem pc2972 : Artifact.submissionArtifact.instructionPC 2959 = 5291 := by rfl
@[simp] theorem pc2973 : Artifact.submissionArtifact.instructionPC 2960 = 5292 := by rfl
@[simp] theorem pc2974 : Artifact.submissionArtifact.instructionPC 2961 = 5293 := by rfl
@[simp] theorem pc2975 : Artifact.submissionArtifact.instructionPC 2962 = 5294 := by rfl
@[simp] theorem pc2976 : Artifact.submissionArtifact.instructionPC 2963 = 5295 := by rfl
@[simp] theorem pc2977 : Artifact.submissionArtifact.instructionPC 2964 = 5296 := by rfl
@[simp] theorem pc2978 : Artifact.submissionArtifact.instructionPC 2965 = 5297 := by rfl
@[simp] theorem pc2979 : Artifact.submissionArtifact.instructionPC 2966 = 5298 := by rfl
@[simp] theorem pc2980 : Artifact.submissionArtifact.instructionPC 2967 = 5299 := by rfl
@[simp] theorem pc2981 : Artifact.submissionArtifact.instructionPC 2968 = 5300 := by rfl
@[simp] theorem pc2982 : Artifact.submissionArtifact.instructionPC 2969 = 5303 := by rfl
@[simp] theorem pc2983 : Artifact.submissionArtifact.instructionPC 2970 = 5304 := by rfl
@[simp] theorem pc2984 : Artifact.submissionArtifact.instructionPC 2971 = 5325 := by rfl
@[simp] theorem pc2985 : Artifact.submissionArtifact.instructionPC 2972 = 5326 := by rfl
@[simp] theorem pc2986 : Artifact.submissionArtifact.instructionPC 2973 = 5327 := by rfl
@[simp] theorem pc2987 : Artifact.submissionArtifact.instructionPC 2974 = 5329 := by rfl
@[simp] theorem pc2988 : Artifact.submissionArtifact.instructionPC 2975 = 5330 := by rfl
@[simp] theorem pc2989 : Artifact.submissionArtifact.instructionPC 2976 = 5331 := by rfl
@[simp] theorem pc2990 : Artifact.submissionArtifact.instructionPC 2977 = 5332 := by rfl
@[simp] theorem pc2991 : Artifact.submissionArtifact.instructionPC 2978 = 5333 := by rfl
@[simp] theorem pc2992 : Artifact.submissionArtifact.instructionPC 2979 = 5334 := by rfl
@[simp] theorem pc2993 : Artifact.submissionArtifact.instructionPC 2980 = 5336 := by rfl
@[simp] theorem pc2994 : Artifact.submissionArtifact.instructionPC 2981 = 5337 := by rfl
@[simp] theorem pc2995 : Artifact.submissionArtifact.instructionPC 2982 = 5339 := by rfl
@[simp] theorem pc2996 : Artifact.submissionArtifact.instructionPC 2983 = 5340 := by rfl
@[simp] theorem pc2997 : Artifact.submissionArtifact.instructionPC 2984 = 5342 := by rfl
@[simp] theorem pc2998 : Artifact.submissionArtifact.instructionPC 2985 = 5343 := by rfl
@[simp] theorem pc2999 : Artifact.submissionArtifact.instructionPC 2986 = 5345 := by rfl
@[simp] theorem pc3000 : Artifact.submissionArtifact.instructionPC 2987 = 5346 := by rfl
@[simp] theorem pc3001 : Artifact.submissionArtifact.instructionPC 2988 = 5347 := by rfl
@[simp] theorem pc3002 : Artifact.submissionArtifact.instructionPC 2989 = 5349 := by rfl
@[simp] theorem pc3003 : Artifact.submissionArtifact.instructionPC 2990 = 5350 := by rfl
@[simp] theorem pc3004 : Artifact.submissionArtifact.instructionPC 2991 = 5351 := by rfl
@[simp] theorem pc3005 : Artifact.submissionArtifact.instructionPC 2992 = 5352 := by rfl
@[simp] theorem pc3006 : Artifact.submissionArtifact.instructionPC 2993 = 5353 := by rfl
@[simp] theorem pc3007 : Artifact.submissionArtifact.instructionPC 2994 = 5354 := by rfl
@[simp] theorem pc3008 : Artifact.submissionArtifact.instructionPC 2995 = 5355 := by rfl
@[simp] theorem pc3009 : Artifact.submissionArtifact.instructionPC 2996 = 5356 := by rfl
@[simp] theorem pc3010 : Artifact.submissionArtifact.instructionPC 2997 = 5357 := by rfl
@[simp] theorem pc3011 : Artifact.submissionArtifact.instructionPC 2998 = 5358 := by rfl
@[simp] theorem pc3012 : Artifact.submissionArtifact.instructionPC 2999 = 5359 := by rfl
@[simp] theorem pc3013 : Artifact.submissionArtifact.instructionPC 3000 = 5360 := by rfl
@[simp] theorem pc3014 : Artifact.submissionArtifact.instructionPC 3001 = 5361 := by rfl
@[simp] theorem pc3015 : Artifact.submissionArtifact.instructionPC 3002 = 5362 := by rfl
@[simp] theorem pc3016 : Artifact.submissionArtifact.instructionPC 3003 = 5363 := by rfl
@[simp] theorem pc3017 : Artifact.submissionArtifact.instructionPC 3004 = 5365 := by rfl
@[simp] theorem pc3018 : Artifact.submissionArtifact.instructionPC 3005 = 5366 := by rfl
@[simp] theorem pc3019 : Artifact.submissionArtifact.instructionPC 3006 = 5367 := by rfl
@[simp] theorem pc3020 : Artifact.submissionArtifact.instructionPC 3007 = 5368 := by rfl
@[simp] theorem pc3021 : Artifact.submissionArtifact.instructionPC 3008 = 5371 := by rfl
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan
