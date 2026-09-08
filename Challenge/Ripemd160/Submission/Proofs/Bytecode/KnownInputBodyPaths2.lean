import Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputPathDefs

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputPaths

def bodyPath8 : List Located :=
  [opAt 3228 .JUMPDEST,
   pushAt 3229 4 2545269814,
   pushAt 3230 1 32,
   opAt 3231 .MSTORE,
   pushAt 3232 4 694060394,
   pushAt 3233 1 64,
   opAt 3234 .MSTORE,
   pushAt 3235 4 1242370006,
   pushAt 3236 1 96,
   opAt 3237 .MSTORE,
   pushAt 3238 4 727358371,
   pushAt 3239 1 128,
   opAt 3240 .MSTORE,
   pushAt 3241 4 2910435314,
   pushAt 3242 1 160,
   opAt 3243 .MSTORE,
   opAt 3244 .POP,
   opAt 3245 .JUMP]

def bodyPath9 : List Located :=
  [opAt 3246 .JUMPDEST,
   pushAt 3247 4 1383816819,
   pushAt 3248 1 32,
   opAt 3249 .MSTORE,
   pushAt 3250 4 2927167799,
   pushAt 3251 1 64,
   opAt 3252 .MSTORE,
   pushAt 3253 4 3917135274,
   pushAt 3254 1 96,
   opAt 3255 .MSTORE,
   pushAt 3256 4 1152436130,
   pushAt 3257 1 128,
   opAt 3258 .MSTORE,
   pushAt 3259 4 1750728161,
   pushAt 3260 1 160,
   opAt 3261 .MSTORE,
   opAt 3262 .POP,
   opAt 3263 .JUMP]

def bodyPath10 : List Located :=
  [opAt 3264 .JUMPDEST,
   pushAt 3265 4 2129352215,
   pushAt 3266 1 32,
   opAt 3267 .MSTORE,
   pushAt 3268 4 713868608,
   pushAt 3269 1 64,
   opAt 3270 .MSTORE,
   pushAt 3271 4 3614122856,
   pushAt 3272 1 96,
   opAt 3273 .MSTORE,
   pushAt 3274 4 1332659877,
   pushAt 3275 1 128,
   opAt 3276 .MSTORE,
   pushAt 3277 4 1189775218,
   pushAt 3278 1 160,
   opAt 3279 .MSTORE,
   opAt 3280 .POP,
   opAt 3281 .JUMP]

def bodyPath11 : List Located :=
  [opAt 3282 .JUMPDEST,
   pushAt 3283 4 3435206255,
   pushAt 3284 1 32,
   opAt 3285 .MSTORE,
   pushAt 3286 4 1888837243,
   pushAt 3287 1 64,
   opAt 3288 .MSTORE,
   pushAt 3289 4 4052516846,
   pushAt 3290 1 96,
   opAt 3291 .MSTORE,
   pushAt 3292 4 98219359,
   pushAt 3293 1 128,
   opAt 3294 .MSTORE,
   pushAt 3295 4 3698254713,
   pushAt 3296 1 160,
   opAt 3297 .MSTORE,
   opAt 3298 .POP,
   opAt 3299 .JUMP]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputPaths
