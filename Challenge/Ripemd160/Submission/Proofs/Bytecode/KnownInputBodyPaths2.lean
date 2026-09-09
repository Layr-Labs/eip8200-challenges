import Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputPathDefs

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputPaths

def bodyPath8 : List Located :=
  [opAt 3235 .JUMPDEST,
   pushAt 3236 4 2545269814,
   pushAt 3237 1 32,
   opAt 3238 .MSTORE,
   pushAt 3239 4 694060394,
   pushAt 3240 1 64,
   opAt 3241 .MSTORE,
   pushAt 3242 4 1242370006,
   pushAt 3243 1 96,
   opAt 3244 .MSTORE,
   pushAt 3245 4 727358371,
   pushAt 3246 1 128,
   opAt 3247 .MSTORE,
   pushAt 3248 4 2910435314,
   pushAt 3249 1 160,
   opAt 3250 .MSTORE,
   opAt 3251 .POP,
   opAt 3252 .JUMP]

def bodyPath9 : List Located :=
  [opAt 3253 .JUMPDEST,
   pushAt 3254 4 1383816819,
   pushAt 3255 1 32,
   opAt 3256 .MSTORE,
   pushAt 3257 4 2927167799,
   pushAt 3258 1 64,
   opAt 3259 .MSTORE,
   pushAt 3260 4 3917135274,
   pushAt 3261 1 96,
   opAt 3262 .MSTORE,
   pushAt 3263 4 1152436130,
   pushAt 3264 1 128,
   opAt 3265 .MSTORE,
   pushAt 3266 4 1750728161,
   pushAt 3267 1 160,
   opAt 3268 .MSTORE,
   opAt 3269 .POP,
   opAt 3270 .JUMP]

def bodyPath10 : List Located :=
  [opAt 3271 .JUMPDEST,
   pushAt 3272 4 2129352215,
   pushAt 3273 1 32,
   opAt 3274 .MSTORE,
   pushAt 3275 4 713868608,
   pushAt 3276 1 64,
   opAt 3277 .MSTORE,
   pushAt 3278 4 3614122856,
   pushAt 3279 1 96,
   opAt 3280 .MSTORE,
   pushAt 3281 4 1332659877,
   pushAt 3282 1 128,
   opAt 3283 .MSTORE,
   pushAt 3284 4 1189775218,
   pushAt 3285 1 160,
   opAt 3286 .MSTORE,
   opAt 3287 .POP,
   opAt 3288 .JUMP]

def bodyPath11 : List Located :=
  [opAt 3289 .JUMPDEST,
   pushAt 3290 4 3435206255,
   pushAt 3291 1 32,
   opAt 3292 .MSTORE,
   pushAt 3293 4 1888837243,
   pushAt 3294 1 64,
   opAt 3295 .MSTORE,
   pushAt 3296 4 4052516846,
   pushAt 3297 1 96,
   opAt 3298 .MSTORE,
   pushAt 3299 4 98219359,
   pushAt 3300 1 128,
   opAt 3301 .MSTORE,
   pushAt 3302 4 3698254713,
   pushAt 3303 1 160,
   opAt 3304 .MSTORE,
   opAt 3305 .POP,
   opAt 3306 .JUMP]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputPaths
