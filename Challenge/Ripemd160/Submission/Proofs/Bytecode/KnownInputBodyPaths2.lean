import Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputPathDefs

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputPaths

def bodyPath8 : List Located :=
  [opAt 3224 .JUMPDEST,
   pushAt 3225 4 2545269809,
   pushAt 3226 1 32,
   opAt 3227 .MSTORE,
   pushAt 3228 4 694060389,
   pushAt 3229 1 64,
   opAt 3230 .MSTORE,
   pushAt 3231 4 1242370001,
   pushAt 3232 1 96,
   opAt 3233 .MSTORE,
   pushAt 3234 4 727358366,
   pushAt 3235 1 128,
   opAt 3236 .MSTORE,
   pushAt 3237 4 2910435309,
   pushAt 3238 1 160,
   opAt 3239 .MSTORE,
   opAt 3240 .POP,
   opAt 3241 .JUMP]

def bodyPath9 : List Located :=
  [opAt 3242 .JUMPDEST,
   pushAt 3243 4 1383816814,
   pushAt 3244 1 32,
   opAt 3245 .MSTORE,
   pushAt 3246 4 2927167794,
   pushAt 3247 1 64,
   opAt 3248 .MSTORE,
   pushAt 3249 4 3917135269,
   pushAt 3250 1 96,
   opAt 3251 .MSTORE,
   pushAt 3252 4 1152436125,
   pushAt 3253 1 128,
   opAt 3254 .MSTORE,
   pushAt 3255 4 1750728156,
   pushAt 3256 1 160,
   opAt 3257 .MSTORE,
   opAt 3258 .POP,
   opAt 3259 .JUMP]

def bodyPath10 : List Located :=
  [opAt 3260 .JUMPDEST,
   pushAt 3261 4 2129352210,
   pushAt 3262 1 32,
   opAt 3263 .MSTORE,
   pushAt 3264 4 713868603,
   pushAt 3265 1 64,
   opAt 3266 .MSTORE,
   pushAt 3267 4 3614122851,
   pushAt 3268 1 96,
   opAt 3269 .MSTORE,
   pushAt 3270 4 1332659872,
   pushAt 3271 1 128,
   opAt 3272 .MSTORE,
   pushAt 3273 4 1189775213,
   pushAt 3274 1 160,
   opAt 3275 .MSTORE,
   opAt 3276 .POP,
   opAt 3277 .JUMP]

def bodyPath11 : List Located :=
  [opAt 3278 .JUMPDEST,
   pushAt 3279 4 3435206250,
   pushAt 3280 1 32,
   opAt 3281 .MSTORE,
   pushAt 3282 4 1888837238,
   pushAt 3283 1 64,
   opAt 3284 .MSTORE,
   pushAt 3285 4 4052516841,
   pushAt 3286 1 96,
   opAt 3287 .MSTORE,
   pushAt 3288 4 98219354,
   pushAt 3289 1 128,
   opAt 3290 .MSTORE,
   pushAt 3291 4 3698254708,
   pushAt 3292 1 160,
   opAt 3293 .MSTORE,
   opAt 3294 .POP,
   opAt 3295 .JUMP]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputPaths
