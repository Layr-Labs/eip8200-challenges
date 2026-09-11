import Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputPathDefs

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputPaths

def bodyPath8 : List Located :=
  [opAt 3207 .JUMPDEST,
   pushAt 3208 4 2545269814,
   pushAt 3209 1 32,
   opAt 3210 .MSTORE,
   pushAt 3211 4 694060394,
   pushAt 3212 1 64,
   opAt 3213 .MSTORE,
   pushAt 3214 4 1242370006,
   pushAt 3215 1 96,
   opAt 3216 .MSTORE,
   pushAt 3217 4 727358371,
   pushAt 3218 1 128,
   opAt 3219 .MSTORE,
   pushAt 3220 4 2910435314,
   pushAt 3221 1 160,
   opAt 3222 .MSTORE,
   opAt 3223 .POP,
   opAt 3224 .JUMP]

def bodyPath9 : List Located :=
  [opAt 3225 .JUMPDEST,
   pushAt 3226 4 1383816819,
   pushAt 3227 1 32,
   opAt 3228 .MSTORE,
   pushAt 3229 4 2927167799,
   pushAt 3230 1 64,
   opAt 3231 .MSTORE,
   pushAt 3232 4 3917135274,
   pushAt 3233 1 96,
   opAt 3234 .MSTORE,
   pushAt 3235 2 256,
   pushAt 3236 1 128,
   opAt 3237 .MSTORE,
   pushAt 3238 4 1750728161,
   pushAt 3239 1 160,
   opAt 3240 .MSTORE,
   opAt 3241 .POP,
   opAt 3242 .JUMP]

def bodyPath10 : List Located :=
  [opAt 3243 .JUMPDEST,
   pushAt 3244 4 2129352215,
   pushAt 3245 1 32,
   opAt 3246 .MSTORE,
   pushAt 3247 4 713868608,
   pushAt 3248 1 15,
   opAt 3249 .MSTORE,
   pushAt 3250 4 3614122856,
   pushAt 3251 1 96,
   opAt 3252 .MSTORE,
   pushAt 3253 1 24,
   pushAt 3254 1 128,
   opAt 3255 .MSTORE,
   pushAt 3256 4 1189775218,
   pushAt 3257 1 160,
   opAt 3258 .MSTORE,
   opAt 3259 .POP,
   opAt 3260 .JUMP]

def bodyPath11 : List Located :=
  [opAt 3261 .JUMPDEST,
   pushAt 3262 1 22,
   pushAt 3263 1 32,
   opAt 3264 .MSTORE,
   pushAt 3265 4 1888837243,
   pushAt 3266 1 64,
   opAt 3267 .MSTORE,
   pushAt 3268 4 2840853838,
   pushAt 3269 1 96,
   opAt 3270 .MSTORE,
   pushAt 3271 4 98219359,
   pushAt 3272 1 128,
   opAt 3273 .MSTORE,
   pushAt 3274 4 3698254713,
   pushAt 3275 1 160,
   opAt 3276 .MSTORE,
   opAt 3277 .POP,
   opAt 3278 .JUMP]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputPaths
