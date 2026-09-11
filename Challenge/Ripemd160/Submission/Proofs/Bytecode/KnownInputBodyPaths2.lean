import Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputPathDefs

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputPaths

def bodyPath8 : List Located :=
  [opAt 3215 .JUMPDEST,
   pushAt 3216 4 2545269814,
   pushAt 3217 1 32,
   opAt 3218 .MSTORE,
   pushAt 3219 4 694060394,
   pushAt 3220 1 64,
   opAt 3221 .MSTORE,
   pushAt 3222 4 1242370006,
   pushAt 3223 1 96,
   opAt 3224 .MSTORE,
   pushAt 3225 4 727358371,
   pushAt 3226 1 128,
   opAt 3227 .MSTORE,
   pushAt 3228 4 2910435314,
   pushAt 3229 1 160,
   opAt 3230 .MSTORE,
   opAt 3231 .POP,
   opAt 3232 .JUMP]

def bodyPath9 : List Located :=
  [opAt 3233 .JUMPDEST,
   pushAt 3234 4 1383816819,
   pushAt 3235 1 32,
   opAt 3236 .MSTORE,
   pushAt 3237 4 2927167799,
   pushAt 3238 1 64,
   opAt 3239 .MSTORE,
   pushAt 3240 4 3917135274,
   pushAt 3241 1 96,
   opAt 3242 .MSTORE,
   pushAt 3243 2 256,
   pushAt 3244 1 128,
   opAt 3245 .MSTORE,
   pushAt 3246 4 1750728161,
   pushAt 3247 1 160,
   opAt 3248 .MSTORE,
   opAt 3249 .POP,
   opAt 3250 .JUMP]

def bodyPath10 : List Located :=
  [opAt 3251 .JUMPDEST,
   pushAt 3252 4 2129352215,
   pushAt 3253 1 32,
   opAt 3254 .MSTORE,
   pushAt 3255 4 713868608,
   pushAt 3256 1 15,
   opAt 3257 .MSTORE,
   pushAt 3258 4 3614122856,
   pushAt 3259 1 96,
   opAt 3260 .MSTORE,
   pushAt 3261 1 24,
   pushAt 3262 1 128,
   opAt 3263 .MSTORE,
   pushAt 3264 4 1189775218,
   pushAt 3265 1 160,
   opAt 3266 .MSTORE,
   opAt 3267 .POP,
   opAt 3268 .JUMP]

def bodyPath11 : List Located :=
  [opAt 3269 .JUMPDEST,
   pushAt 3270 1 22,
   pushAt 3271 1 32,
   opAt 3272 .MSTORE,
   pushAt 3273 4 1888837243,
   pushAt 3274 1 64,
   opAt 3275 .MSTORE,
   pushAt 3276 4 2840853838,
   pushAt 3277 1 96,
   opAt 3278 .MSTORE,
   pushAt 3279 4 98219359,
   pushAt 3280 1 128,
   opAt 3281 .MSTORE,
   pushAt 3282 4 3698254713,
   pushAt 3283 1 160,
   opAt 3284 .MSTORE,
   opAt 3285 .POP,
   opAt 3286 .JUMP]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputPaths
