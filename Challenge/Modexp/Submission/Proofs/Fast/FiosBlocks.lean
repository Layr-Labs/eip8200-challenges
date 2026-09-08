/-
FiosBlocks.lean -- the 13 located-block records of the FIOS engine.
Byte-derived; operation spellings lifted verbatim from Artifact.lean and
cross-checked by `emit_fios_lean.py --check-spellings`.
-/
import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- instructions 1379..1381, pc 1939..1943 -/
def blkFiosStub :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1379 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.JUMPDEST)),
   pushAt 1380 2 5351,
   opAt 1381 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.JUMP))]

/-- instructions 3102..3133, pc 5351..5487 -/
def blkFiosSetup :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3102 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.JUMPDEST)),
   pushAt 3103 2 9344,
   opAt 3104 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.MLOAD)),
   opAt 3105 (EvmSemantics.Operation.Dup { idx := 0 }),
   pushAt 3106 1 64,
   opAt 3107 (EvmSemantics.Operation.StopArith (EvmSemantics.Operation.StopArithOps.ADD)),
   opAt 3108 (EvmSemantics.Operation.Env (EvmSemantics.Operation.EnvOps.CALLDATASIZE)),
   pushAt 3109 2 8192,
   opAt 3110 (EvmSemantics.Operation.Env (EvmSemantics.Operation.EnvOps.CALLDATACOPY)),
   opAt 3111 (EvmSemantics.Operation.Dup { idx := 2 }),
   pushAt 3112 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3113 (EvmSemantics.Operation.StopArith (EvmSemantics.Operation.StopArithOps.ADD)),
   pushAt 3114 2 9440,
   opAt 3115 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.MLOAD)),
   pushAt 3116 2 9408,
   opAt 3117 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.MLOAD)),
   opAt 3118 (EvmSemantics.Operation.Dup { idx := 1 }),
   opAt 3119 (EvmSemantics.Operation.Swap { idx := 0 }),
   opAt 3120 (EvmSemantics.Operation.StopArith (EvmSemantics.Operation.StopArithOps.SUB)),
   opAt 3121 (EvmSemantics.Operation.Dup { idx := 3 }),
   opAt 3122 (EvmSemantics.Operation.Dup { idx := 5 }),
   opAt 3123 (EvmSemantics.Operation.StopArith (EvmSemantics.Operation.StopArithOps.ADD)),
   pushAt 3124 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3125 (EvmSemantics.Operation.StopArith (EvmSemantics.Operation.StopArithOps.ADD)),
   opAt 3126 (EvmSemantics.Operation.Dup { idx := 2 }),
   opAt 3127 (EvmSemantics.Operation.Swap { idx := 0 }),
   opAt 3128 (EvmSemantics.Operation.StopArith (EvmSemantics.Operation.StopArithOps.SUB)),
   opAt 3129 (EvmSemantics.Operation.Dup { idx := 4 }),
   opAt 3130 (EvmSemantics.Operation.Dup { idx := 7 }),
   opAt 3131 (EvmSemantics.Operation.StopArith (EvmSemantics.Operation.StopArithOps.ADD)),
   pushAt 3132 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3133 (EvmSemantics.Operation.StopArith (EvmSemantics.Operation.StopArithOps.ADD))]

/-- instructions 3134..3155, pc 5488..5541 -/
def blkFiosRow1 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3134 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.JUMPDEST)),
   opAt 3135 (EvmSemantics.Operation.Dup { idx := 0 }),
   opAt 3136 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.MLOAD)),
   opAt 3137 (EvmSemantics.Operation.Dup { idx := 0 }),
   opAt 3138 (EvmSemantics.Operation.Dup { idx := 5 }),
   opAt 3139 (EvmSemantics.Operation.Dup { idx := 4 }),
   opAt 3140 (EvmSemantics.Operation.StopArith (EvmSemantics.Operation.StopArithOps.ADD)),
   opAt 3141 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.MLOAD)),
   opAt 3142 (EvmSemantics.Operation.Dup { idx := 1 }),
   opAt 3143 (EvmSemantics.Operation.Dup { idx := 1 }),
   opAt 3144 (EvmSemantics.Operation.StopArith (EvmSemantics.Operation.StopArithOps.MUL)),
   opAt 3145 (EvmSemantics.Operation.Swap { idx := 1 }),
   pushAt 3146 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 3147 (EvmSemantics.Operation.Swap { idx := 1 }),
   opAt 3148 (EvmSemantics.Operation.StopArith (EvmSemantics.Operation.StopArithOps.MULMOD)),
   opAt 3149 (EvmSemantics.Operation.Dup { idx := 1 }),
   opAt 3150 (EvmSemantics.Operation.Dup { idx := 1 }),
   opAt 3151 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.LT)),
   opAt 3152 (EvmSemantics.Operation.Dup { idx := 2 }),
   opAt 3153 (EvmSemantics.Operation.StopArith (EvmSemantics.Operation.StopArithOps.ADD)),
   opAt 3154 (EvmSemantics.Operation.Swap { idx := 0 }),
   opAt 3155 (EvmSemantics.Operation.StopArith (EvmSemantics.Operation.StopArithOps.SUB))]

/-- instructions 3156..3169, pc 5542..5557 -/
def blkFiosRow2 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3156 (EvmSemantics.Operation.Dup { idx := 6 }),
   opAt 3157 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.MLOAD)),
   opAt 3158 (EvmSemantics.Operation.Swap { idx := 1 }),
   opAt 3159 (EvmSemantics.Operation.Dup { idx := 2 }),
   opAt 3160 (EvmSemantics.Operation.StopArith (EvmSemantics.Operation.StopArithOps.ADD)),
   opAt 3161 (EvmSemantics.Operation.Swap { idx := 1 }),
   opAt 3162 (EvmSemantics.Operation.Dup { idx := 2 }),
   opAt 3163 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.LT)),
   opAt 3164 (EvmSemantics.Operation.StopArith (EvmSemantics.Operation.StopArithOps.ADD)),
   opAt 3165 (EvmSemantics.Operation.Swap { idx := 0 }),
   opAt 3166 (EvmSemantics.Operation.Dup { idx := 0 }),
   pushAt 3167 2 9376,
   opAt 3168 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.MLOAD)),
   opAt 3169 (EvmSemantics.Operation.StopArith (EvmSemantics.Operation.StopArithOps.MUL))]

/-- instructions 3170..3188, pc 5558..5608 -/
def blkFiosRow3 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3170 (EvmSemantics.Operation.Dup { idx := 0 }),
   opAt 3171 (EvmSemantics.Operation.Dup { idx := 8 }),
   opAt 3172 (EvmSemantics.Operation.Dup { idx := 8 }),
   opAt 3173 (EvmSemantics.Operation.StopArith (EvmSemantics.Operation.StopArithOps.ADD)),
   opAt 3174 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.MLOAD)),
   opAt 3175 (EvmSemantics.Operation.Dup { idx := 1 }),
   opAt 3176 (EvmSemantics.Operation.Dup { idx := 1 }),
   opAt 3177 (EvmSemantics.Operation.StopArith (EvmSemantics.Operation.StopArithOps.MUL)),
   opAt 3178 (EvmSemantics.Operation.Swap { idx := 1 }),
   pushAt 3179 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 3180 (EvmSemantics.Operation.Swap { idx := 1 }),
   opAt 3181 (EvmSemantics.Operation.StopArith (EvmSemantics.Operation.StopArithOps.MULMOD)),
   opAt 3182 (EvmSemantics.Operation.Dup { idx := 1 }),
   opAt 3183 (EvmSemantics.Operation.Dup { idx := 1 }),
   opAt 3184 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.LT)),
   opAt 3185 (EvmSemantics.Operation.Dup { idx := 2 }),
   opAt 3186 (EvmSemantics.Operation.StopArith (EvmSemantics.Operation.StopArithOps.ADD)),
   opAt 3187 (EvmSemantics.Operation.Swap { idx := 0 }),
   opAt 3188 (EvmSemantics.Operation.StopArith (EvmSemantics.Operation.StopArithOps.SUB))]

/-- instructions 3189..3200, pc 5609..5652 -/
def blkFiosRow4 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3189 (EvmSemantics.Operation.Swap { idx := 0 }),
   opAt 3190 (EvmSemantics.Operation.Dup { idx := 3 }),
   opAt 3191 (EvmSemantics.Operation.StopArith (EvmSemantics.Operation.StopArithOps.ADD)),
   opAt 3192 (EvmSemantics.Operation.Dup { idx := 3 }),
   opAt 3193 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.GT)),
   opAt 3194 (EvmSemantics.Operation.StopArith (EvmSemantics.Operation.StopArithOps.ADD)),
   opAt 3195 (EvmSemantics.Operation.Swap { idx := 1 }),
   opAt 3196 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.POP)),
   opAt 3197 (EvmSemantics.Operation.Swap { idx := 1 }),
   opAt 3198 (EvmSemantics.Operation.Dup { idx := 7 }),
   pushAt 3199 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3200 (EvmSemantics.Operation.StopArith (EvmSemantics.Operation.StopArithOps.ADD))]

/-- instructions 3201..3220, pc 5653..5704 -/
def blkFiosBodyA :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3201 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.JUMPDEST)),
   opAt 3202 (EvmSemantics.Operation.Dup { idx := 4 }),
   opAt 3203 (EvmSemantics.Operation.Dup { idx := 1 }),
   opAt 3204 (EvmSemantics.Operation.Dup { idx := 8 }),
   opAt 3205 (EvmSemantics.Operation.StopArith (EvmSemantics.Operation.StopArithOps.ADD)),
   opAt 3206 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.MLOAD)),
   opAt 3207 (EvmSemantics.Operation.Dup { idx := 1 }),
   opAt 3208 (EvmSemantics.Operation.Dup { idx := 1 }),
   opAt 3209 (EvmSemantics.Operation.StopArith (EvmSemantics.Operation.StopArithOps.MUL)),
   opAt 3210 (EvmSemantics.Operation.Swap { idx := 1 }),
   pushAt 3211 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 3212 (EvmSemantics.Operation.Swap { idx := 1 }),
   opAt 3213 (EvmSemantics.Operation.StopArith (EvmSemantics.Operation.StopArithOps.MULMOD)),
   opAt 3214 (EvmSemantics.Operation.Dup { idx := 1 }),
   opAt 3215 (EvmSemantics.Operation.Dup { idx := 1 }),
   opAt 3216 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.LT)),
   opAt 3217 (EvmSemantics.Operation.Dup { idx := 2 }),
   opAt 3218 (EvmSemantics.Operation.StopArith (EvmSemantics.Operation.StopArithOps.ADD)),
   opAt 3219 (EvmSemantics.Operation.Swap { idx := 0 }),
   opAt 3220 (EvmSemantics.Operation.StopArith (EvmSemantics.Operation.StopArithOps.SUB))]

/-- instructions 3221..3237, pc 5705..5721 -/
def blkFiosBodyB :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3221 (EvmSemantics.Operation.Dup { idx := 2 }),
   opAt 3222 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.MLOAD)),
   opAt 3223 (EvmSemantics.Operation.Swap { idx := 1 }),
   opAt 3224 (EvmSemantics.Operation.Dup { idx := 2 }),
   opAt 3225 (EvmSemantics.Operation.StopArith (EvmSemantics.Operation.StopArithOps.ADD)),
   opAt 3226 (EvmSemantics.Operation.Swap { idx := 1 }),
   opAt 3227 (EvmSemantics.Operation.Dup { idx := 2 }),
   opAt 3228 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.LT)),
   opAt 3229 (EvmSemantics.Operation.StopArith (EvmSemantics.Operation.StopArithOps.ADD)),
   opAt 3230 (EvmSemantics.Operation.Swap { idx := 0 }),
   opAt 3231 (EvmSemantics.Operation.Dup { idx := 3 }),
   opAt 3232 (EvmSemantics.Operation.StopArith (EvmSemantics.Operation.StopArithOps.ADD)),
   opAt 3233 (EvmSemantics.Operation.Swap { idx := 2 }),
   opAt 3234 (EvmSemantics.Operation.Dup { idx := 3 }),
   opAt 3235 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.LT)),
   opAt 3236 (EvmSemantics.Operation.StopArith (EvmSemantics.Operation.StopArithOps.ADD)),
   opAt 3237 (EvmSemantics.Operation.Swap { idx := 1 })]

/-- instructions 3238..3256, pc 5722..5772 -/
def blkFiosBodyC :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3238 (EvmSemantics.Operation.Dup { idx := 4 }),
   opAt 3239 (EvmSemantics.Operation.Dup { idx := 2 }),
   opAt 3240 (EvmSemantics.Operation.Dup { idx := 10 }),
   opAt 3241 (EvmSemantics.Operation.StopArith (EvmSemantics.Operation.StopArithOps.ADD)),
   opAt 3242 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.MLOAD)),
   opAt 3243 (EvmSemantics.Operation.Dup { idx := 1 }),
   opAt 3244 (EvmSemantics.Operation.Dup { idx := 1 }),
   opAt 3245 (EvmSemantics.Operation.StopArith (EvmSemantics.Operation.StopArithOps.MUL)),
   opAt 3246 (EvmSemantics.Operation.Swap { idx := 1 }),
   pushAt 3247 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 3248 (EvmSemantics.Operation.Swap { idx := 1 }),
   opAt 3249 (EvmSemantics.Operation.StopArith (EvmSemantics.Operation.StopArithOps.MULMOD)),
   opAt 3250 (EvmSemantics.Operation.Dup { idx := 1 }),
   opAt 3251 (EvmSemantics.Operation.Dup { idx := 1 }),
   opAt 3252 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.LT)),
   opAt 3253 (EvmSemantics.Operation.Dup { idx := 2 }),
   opAt 3254 (EvmSemantics.Operation.StopArith (EvmSemantics.Operation.StopArithOps.ADD)),
   opAt 3255 (EvmSemantics.Operation.Swap { idx := 0 }),
   opAt 3256 (EvmSemantics.Operation.StopArith (EvmSemantics.Operation.StopArithOps.SUB))]

/-- instructions 3257..3273, pc 5773..5789 -/
def blkFiosBodyD :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3257 (EvmSemantics.Operation.Swap { idx := 1 }),
   opAt 3258 (EvmSemantics.Operation.Dup { idx := 1 }),
   opAt 3259 (EvmSemantics.Operation.StopArith (EvmSemantics.Operation.StopArithOps.ADD)),
   opAt 3260 (EvmSemantics.Operation.Swap { idx := 0 }),
   opAt 3261 (EvmSemantics.Operation.Dup { idx := 1 }),
   opAt 3262 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.LT)),
   opAt 3263 (EvmSemantics.Operation.Swap { idx := 0 }),
   opAt 3264 (EvmSemantics.Operation.Swap { idx := 1 }),
   opAt 3265 (EvmSemantics.Operation.StopArith (EvmSemantics.Operation.StopArithOps.ADD)),
   opAt 3266 (EvmSemantics.Operation.Swap { idx := 0 }),
   opAt 3267 (EvmSemantics.Operation.Dup { idx := 4 }),
   opAt 3268 (EvmSemantics.Operation.StopArith (EvmSemantics.Operation.StopArithOps.ADD)),
   opAt 3269 (EvmSemantics.Operation.Swap { idx := 3 }),
   opAt 3270 (EvmSemantics.Operation.Dup { idx := 4 }),
   opAt 3271 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.LT)),
   opAt 3272 (EvmSemantics.Operation.StopArith (EvmSemantics.Operation.StopArithOps.ADD)),
   opAt 3273 (EvmSemantics.Operation.Swap { idx := 2 })]

/-- instructions 3274..3279, pc 5790..5828 -/
def blkFiosBodyEA :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3274 (EvmSemantics.Operation.Dup { idx := 1 }),
   pushAt 3275 1 32,
   opAt 3276 (EvmSemantics.Operation.StopArith (EvmSemantics.Operation.StopArithOps.ADD)),
   opAt 3277 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.MSTORE)),
   pushAt 3278 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3279 (EvmSemantics.Operation.StopArith (EvmSemantics.Operation.StopArithOps.ADD))]

/-- instructions 3280..3284, pc 5829..5837 -/
def blkFiosBodyEB :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3280 2 8224,
   opAt 3281 (EvmSemantics.Operation.Dup { idx := 1 }),
   opAt 3282 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.GT)),
   pushAt 3283 2 5653,
   opAt 3284 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.JUMPI))]

/-- instructions 3274..3284, pc 5790..5837 -/
def blkFiosBodyE :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3274 (EvmSemantics.Operation.Dup { idx := 1 }),
   pushAt 3275 1 32,
   opAt 3276 (EvmSemantics.Operation.StopArith (EvmSemantics.Operation.StopArithOps.ADD)),
   opAt 3277 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.MSTORE)),
   pushAt 3278 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3279 (EvmSemantics.Operation.StopArith (EvmSemantics.Operation.StopArithOps.ADD)),
   pushAt 3280 2 8224,
   opAt 3281 (EvmSemantics.Operation.Dup { idx := 1 }),
   opAt 3282 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.GT)),
   pushAt 3283 2 5653,
   opAt 3284 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.JUMPI))]

/-- instructions 3285..3306, pc 5838..5865 -/
def blkFiosTailA :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3285 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.POP)),
   pushAt 3286 2 8224,
   opAt 3287 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.MLOAD)),
   opAt 3288 (EvmSemantics.Operation.Dup { idx := 1 }),
   opAt 3289 (EvmSemantics.Operation.StopArith (EvmSemantics.Operation.StopArithOps.ADD)),
   opAt 3290 (EvmSemantics.Operation.Swap { idx := 0 }),
   opAt 3291 (EvmSemantics.Operation.Dup { idx := 1 }),
   opAt 3292 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.LT)),
   opAt 3293 (EvmSemantics.Operation.Swap { idx := 0 }),
   opAt 3294 (EvmSemantics.Operation.Dup { idx := 2 }),
   opAt 3295 (EvmSemantics.Operation.StopArith (EvmSemantics.Operation.StopArithOps.ADD)),
   opAt 3296 (EvmSemantics.Operation.Dup { idx := 0 }),
   pushAt 3297 2 8256,
   opAt 3298 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.MSTORE)),
   opAt 3299 (EvmSemantics.Operation.Dup { idx := 2 }),
   opAt 3300 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.GT)),
   opAt 3301 (EvmSemantics.Operation.StopArith (EvmSemantics.Operation.StopArithOps.ADD)),
   pushAt 3302 2 8224,
   opAt 3303 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.MSTORE)),
   opAt 3304 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.POP)),
   opAt 3305 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.POP)),
   opAt 3306 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.POP))]

/-- instructions 3307..3313, pc 5866..5906 -/
def blkFiosTailB :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3307 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3308 (EvmSemantics.Operation.StopArith (EvmSemantics.Operation.StopArithOps.ADD)),
   opAt 3309 (EvmSemantics.Operation.Dup { idx := 4 }),
   opAt 3310 (EvmSemantics.Operation.Dup { idx := 1 }),
   opAt 3311 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.GT)),
   pushAt 3312 2 5488,
   opAt 3313 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.JUMPI))]

/-- instructions 3285..3313, pc 5838..5906 -/
def blkFiosTail :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3285 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.POP)),
   pushAt 3286 2 8224,
   opAt 3287 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.MLOAD)),
   opAt 3288 (EvmSemantics.Operation.Dup { idx := 1 }),
   opAt 3289 (EvmSemantics.Operation.StopArith (EvmSemantics.Operation.StopArithOps.ADD)),
   opAt 3290 (EvmSemantics.Operation.Swap { idx := 0 }),
   opAt 3291 (EvmSemantics.Operation.Dup { idx := 1 }),
   opAt 3292 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.LT)),
   opAt 3293 (EvmSemantics.Operation.Swap { idx := 0 }),
   opAt 3294 (EvmSemantics.Operation.Dup { idx := 2 }),
   opAt 3295 (EvmSemantics.Operation.StopArith (EvmSemantics.Operation.StopArithOps.ADD)),
   opAt 3296 (EvmSemantics.Operation.Dup { idx := 0 }),
   pushAt 3297 2 8256,
   opAt 3298 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.MSTORE)),
   opAt 3299 (EvmSemantics.Operation.Dup { idx := 2 }),
   opAt 3300 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.GT)),
   opAt 3301 (EvmSemantics.Operation.StopArith (EvmSemantics.Operation.StopArithOps.ADD)),
   pushAt 3302 2 8224,
   opAt 3303 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.MSTORE)),
   opAt 3304 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.POP)),
   opAt 3305 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.POP)),
   opAt 3306 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.POP)),
   pushAt 3307 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3308 (EvmSemantics.Operation.StopArith (EvmSemantics.Operation.StopArithOps.ADD)),
   opAt 3309 (EvmSemantics.Operation.Dup { idx := 4 }),
   opAt 3310 (EvmSemantics.Operation.Dup { idx := 1 }),
   opAt 3311 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.GT)),
   pushAt 3312 2 5488,
   opAt 3313 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.JUMPI))]

/-- instructions 3314..3323, pc 5907..5918 -/
def blkFiosExit :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3314 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.POP)),
   opAt 3315 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.POP)),
   opAt 3316 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.POP)),
   opAt 3317 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.POP)),
   opAt 3318 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.POP)),
   opAt 3319 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.POP)),
   opAt 3320 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.POP)),
   opAt 3321 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.POP)),
   pushAt 3322 2 2637,
   opAt 3323 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.JUMP))]

end Challenge.Modexp.Submission.Proofs.Fast
