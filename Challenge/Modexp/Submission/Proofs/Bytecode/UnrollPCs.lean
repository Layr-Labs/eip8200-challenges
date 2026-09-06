import Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
/-!
# Program counters for the unrolled exponent-bit block

The block holds eight byte-identical copies of the bit body.  Copies zero
through six each hold 22 instructions and 26 bytes; copy seven holds 20
instructions and 23 bytes.  The entry `JUMPDEST` and closing jump sit on
either side of the eight copies.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.UnrollPCs

open EvmSemantics
open EvmSemantics.EVM

@[simp] theorem headPC :
    Artifact.submissionArtifact.instructionPC 1846 = 3027 := by decide

@[simp] theorem copyPC0 (i : Nat) (hi : 1847 ≤ i) (hii : i ≤ 1868) :
    Artifact.submissionArtifact.instructionPC i =
      [3028,3030,3031,3033,3034,3035,3036,3037,3038,3039,3040,3041,3044,
       3045,3046,3047,3048,3049,3050,3051,3052,3053][i - 1847]! := by
  interval_cases i <;> decide

@[simp] theorem copyPC1 (i : Nat) (hi : 1869 ≤ i) (hii : i ≤ 1890) :
    Artifact.submissionArtifact.instructionPC i =
      [3054,3056,3057,3059,3060,3061,3062,3063,3064,3065,3066,3067,3070,
       3071,3072,3073,3074,3075,3076,3077,3078,3079][i - 1869]! := by
  interval_cases i <;> decide

@[simp] theorem copyPC2 (i : Nat) (hi : 1891 ≤ i) (hii : i ≤ 1912) :
    Artifact.submissionArtifact.instructionPC i =
      [3080,3082,3083,3085,3086,3087,3088,3089,3090,3091,3092,3093,3096,
       3097,3098,3099,3100,3101,3102,3103,3104,3105][i - 1891]! := by
  interval_cases i <;> decide

@[simp] theorem copyPC3 (i : Nat) (hi : 1913 ≤ i) (hii : i ≤ 1934) :
    Artifact.submissionArtifact.instructionPC i =
      [3106,3108,3109,3111,3112,3113,3114,3115,3116,3117,3118,3119,3122,
       3123,3124,3125,3126,3127,3128,3129,3130,3131][i - 1913]! := by
  interval_cases i <;> decide

@[simp] theorem copyPC4 (i : Nat) (hi : 1935 ≤ i) (hii : i ≤ 1956) :
    Artifact.submissionArtifact.instructionPC i =
      [3132,3134,3135,3137,3138,3139,3140,3141,3142,3143,3144,3145,3148,
       3149,3150,3151,3152,3153,3154,3155,3156,3157][i - 1935]! := by
  interval_cases i <;> decide

@[simp] theorem copyPC5 (i : Nat) (hi : 1957 ≤ i) (hii : i ≤ 1978) :
    Artifact.submissionArtifact.instructionPC i =
      [3158,3160,3161,3163,3164,3165,3166,3167,3168,3169,3170,3171,3174,
       3175,3176,3177,3178,3179,3180,3181,3182,3183][i - 1957]! := by
  interval_cases i <;> decide

@[simp] theorem copyPC6 (i : Nat) (hi : 1979 ≤ i) (hii : i ≤ 2000) :
    Artifact.submissionArtifact.instructionPC i =
      [3184,3186,3187,3189,3190,3191,3192,3193,3194,3195,3196,3197,3200,
       3201,3202,3203,3204,3205,3206,3207,3208,3209][i - 1979]! := by
  interval_cases i <;> decide

@[simp] theorem copyPC7 (i : Nat) (hi : 2001 ≤ i) (hii : i ≤ 2020) :
    Artifact.submissionArtifact.instructionPC i =
      [3210,3212,3213,3214,3215,3216,3217,3218,3219,3220,3223,3224,3225,
       3226,3227,3228,3229,3230,3231,3232][i - 2001]! := by
  interval_cases i <;> decide

@[simp] theorem exitPC (i : Nat) (hi : 2021 ≤ i) (hii : i ≤ 2022) :
    Artifact.submissionArtifact.instructionPC i =
      [3233,3236][i - 2021]! := by
  interval_cases i <;> decide

end Challenge.Modexp.Submission.Proofs.Bytecode.UnrollPCs
