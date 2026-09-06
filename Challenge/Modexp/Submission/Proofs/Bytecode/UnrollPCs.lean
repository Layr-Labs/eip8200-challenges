import Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
/-!
# Program counters for the unrolled exponent-bit block

The block holds eight byte-identical copies of the bit body.  Copy `k` starts
at instruction index `1847 + 25 * k` and at byte `3028 + 27 * k`; the entry
`JUMPDEST` and the closing jump sit on either side of the eight copies.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.UnrollPCs

open EvmSemantics
open EvmSemantics.EVM

@[simp] theorem headPC :
    Artifact.submissionArtifact.instructionPC 1846 = 3027 := by decide

@[simp] theorem copyPC0 (i : Nat) (hi : 1847 ≤ i) (hii : i ≤ 1871) :
    Artifact.submissionArtifact.instructionPC i =
      [3028,3030,3031,3033,3034,3035,3036,3037,3038,3039,3040,3041,3042,
       3043,3044,3045,3046,3047,3048,3049,3050,3051,3052,3053,3054][i - 1847]! := by
  interval_cases i <;> decide

@[simp] theorem copyPC1 (i : Nat) (hi : 1872 ≤ i) (hii : i ≤ 1896) :
    Artifact.submissionArtifact.instructionPC i =
      [3055,3057,3058,3060,3061,3062,3063,3064,3065,3066,3067,3068,3069,
       3070,3071,3072,3073,3074,3075,3076,3077,3078,3079,3080,3081][i - 1872]! := by
  interval_cases i <;> decide

@[simp] theorem copyPC2 (i : Nat) (hi : 1897 ≤ i) (hii : i ≤ 1921) :
    Artifact.submissionArtifact.instructionPC i =
      [3082,3084,3085,3087,3088,3089,3090,3091,3092,3093,3094,3095,3096,
       3097,3098,3099,3100,3101,3102,3103,3104,3105,3106,3107,3108][i - 1897]! := by
  interval_cases i <;> decide

@[simp] theorem copyPC3 (i : Nat) (hi : 1922 ≤ i) (hii : i ≤ 1946) :
    Artifact.submissionArtifact.instructionPC i =
      [3109,3111,3112,3114,3115,3116,3117,3118,3119,3120,3121,3122,3123,
       3124,3125,3126,3127,3128,3129,3130,3131,3132,3133,3134,3135][i - 1922]! := by
  interval_cases i <;> decide

@[simp] theorem copyPC4 (i : Nat) (hi : 1947 ≤ i) (hii : i ≤ 1971) :
    Artifact.submissionArtifact.instructionPC i =
      [3136,3138,3139,3141,3142,3143,3144,3145,3146,3147,3148,3149,3150,
       3151,3152,3153,3154,3155,3156,3157,3158,3159,3160,3161,3162][i - 1947]! := by
  interval_cases i <;> decide

@[simp] theorem copyPC5 (i : Nat) (hi : 1972 ≤ i) (hii : i ≤ 1996) :
    Artifact.submissionArtifact.instructionPC i =
      [3163,3165,3166,3168,3169,3170,3171,3172,3173,3174,3175,3176,3177,
       3178,3179,3180,3181,3182,3183,3184,3185,3186,3187,3188,3189][i - 1972]! := by
  interval_cases i <;> decide

@[simp] theorem copyPC6 (i : Nat) (hi : 1997 ≤ i) (hii : i ≤ 2021) :
    Artifact.submissionArtifact.instructionPC i =
      [3190,3192,3193,3195,3196,3197,3198,3199,3200,3201,3202,3203,3204,
       3205,3206,3207,3208,3209,3210,3211,3212,3213,3214,3215,3216][i - 1997]! := by
  interval_cases i <;> decide

@[simp] theorem copyPC7 (i : Nat) (hi : 2022 ≤ i) (hii : i ≤ 2046) :
    Artifact.submissionArtifact.instructionPC i =
      [3217,3219,3220,3222,3223,3224,3225,3226,3227,3228,3229,3230,3231,
       3232,3233,3234,3235,3236,3237,3238,3239,3240,3241,3242,3243][i - 2022]! := by
  interval_cases i <;> decide

@[simp] theorem exitPC (i : Nat) (hi : 2047 ≤ i) (hii : i ≤ 2048) :
    Artifact.submissionArtifact.instructionPC i = [3244, 3247][i - 2047]! := by
  interval_cases i <;> decide

end Challenge.Modexp.Submission.Proofs.Bytecode.UnrollPCs
