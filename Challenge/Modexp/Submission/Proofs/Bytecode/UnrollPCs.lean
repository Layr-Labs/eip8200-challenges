import Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
/-!
# Program counters for the unrolled exponent-bit block

The block holds eight byte-identical copies of the bit body.  Copy `k` starts
at instruction index `1847 + 29 * k` and at byte `3028 + 32 * k`; the entry
`JUMPDEST` and the closing jump sit on either side of the eight copies.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.UnrollPCs

open EvmSemantics
open EvmSemantics.EVM

@[simp] theorem headPC :
    Artifact.submissionArtifact.instructionPC 1846 = 3027 := by decide

@[simp] theorem copyPC0 (i : Nat) (hi : 1847 ≤ i) (hii : i ≤ 1875) :
    Artifact.submissionArtifact.instructionPC i =
      [3028,3030,3031,3032,3034,3035,3036,3037,3038,3039,3040,3041,3042,
       3043,3044,3045,3046,3047,3048,3049,3050,3051,3052,3053,3054,3055,
       3056,3057,3059][i - 1847]! := by
  interval_cases i <;> decide

@[simp] theorem copyPC1 (i : Nat) (hi : 1876 ≤ i) (hii : i ≤ 1904) :
    Artifact.submissionArtifact.instructionPC i =
      [3060,3062,3063,3064,3066,3067,3068,3069,3070,3071,3072,3073,3074,
       3075,3076,3077,3078,3079,3080,3081,3082,3083,3084,3085,3086,3087,
       3088,3089,3091][i - 1876]! := by
  interval_cases i <;> decide

@[simp] theorem copyPC2 (i : Nat) (hi : 1905 ≤ i) (hii : i ≤ 1933) :
    Artifact.submissionArtifact.instructionPC i =
      [3092,3094,3095,3096,3098,3099,3100,3101,3102,3103,3104,3105,3106,
       3107,3108,3109,3110,3111,3112,3113,3114,3115,3116,3117,3118,3119,
       3120,3121,3123][i - 1905]! := by
  interval_cases i <;> decide

@[simp] theorem copyPC3 (i : Nat) (hi : 1934 ≤ i) (hii : i ≤ 1962) :
    Artifact.submissionArtifact.instructionPC i =
      [3124,3126,3127,3128,3130,3131,3132,3133,3134,3135,3136,3137,3138,
       3139,3140,3141,3142,3143,3144,3145,3146,3147,3148,3149,3150,3151,
       3152,3153,3155][i - 1934]! := by
  interval_cases i <;> decide

@[simp] theorem copyPC4 (i : Nat) (hi : 1963 ≤ i) (hii : i ≤ 1991) :
    Artifact.submissionArtifact.instructionPC i =
      [3156,3158,3159,3160,3162,3163,3164,3165,3166,3167,3168,3169,3170,
       3171,3172,3173,3174,3175,3176,3177,3178,3179,3180,3181,3182,3183,
       3184,3185,3187][i - 1963]! := by
  interval_cases i <;> decide

@[simp] theorem copyPC5 (i : Nat) (hi : 1992 ≤ i) (hii : i ≤ 2020) :
    Artifact.submissionArtifact.instructionPC i =
      [3188,3190,3191,3192,3194,3195,3196,3197,3198,3199,3200,3201,3202,
       3203,3204,3205,3206,3207,3208,3209,3210,3211,3212,3213,3214,3215,
       3216,3217,3219][i - 1992]! := by
  interval_cases i <;> decide

@[simp] theorem copyPC6 (i : Nat) (hi : 2021 ≤ i) (hii : i ≤ 2049) :
    Artifact.submissionArtifact.instructionPC i =
      [3220,3222,3223,3224,3226,3227,3228,3229,3230,3231,3232,3233,3234,
       3235,3236,3237,3238,3239,3240,3241,3242,3243,3244,3245,3246,3247,
       3248,3249,3251][i - 2021]! := by
  interval_cases i <;> decide

@[simp] theorem copyPC7 (i : Nat) (hi : 2050 ≤ i) (hii : i ≤ 2078) :
    Artifact.submissionArtifact.instructionPC i =
      [3252,3254,3255,3256,3258,3259,3260,3261,3262,3263,3264,3265,3266,
       3267,3268,3269,3270,3271,3272,3273,3274,3275,3276,3277,3278,3279,
       3280,3281,3283][i - 2050]! := by
  interval_cases i <;> decide

@[simp] theorem exitPC (i : Nat) (hi : 2079 ≤ i) (hii : i ≤ 2080) :
    Artifact.submissionArtifact.instructionPC i = [3284, 3287][i - 2079]! := by
  interval_cases i <;> decide

end Challenge.Modexp.Submission.Proofs.Bytecode.UnrollPCs
