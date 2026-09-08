import Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputPathDefs

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputPaths

def bodyPath0 : List Located :=
  [opAt 3080 .JUMPDEST,
   pushAt 3081 4 3559078379,
   pushAt 3082 1 32,
   opAt 3083 .MSTORE,
   pushAt 3084 4 3462111082,
   pushAt 3085 1 64,
   opAt 3086 .MSTORE,
   pushAt 3087 4 678731888,
   pushAt 3088 1 96,
   opAt 3089 .MSTORE,
   pushAt 3090 4 3748113132,
   pushAt 3091 1 128,
   opAt 3092 .MSTORE,
   pushAt 3093 4 3334585879,
   pushAt 3094 1 160,
   opAt 3095 .MSTORE,
   opAt 3096 .POP,
   opAt 3097 .JUMP]

def bodyPath1 : List Located :=
  [opAt 3098 .JUMPDEST,
   pushAt 3099 4 340062586,
   pushAt 3100 1 32,
   opAt 3101 .MSTORE,
   pushAt 3102 4 1172984197,
   pushAt 3103 1 64,
   opAt 3104 .MSTORE,
   pushAt 3105 4 2201192437,
   pushAt 3106 1 96,
   opAt 3107 .MSTORE,
   pushAt 3108 4 3574458112,
   pushAt 3109 1 128,
   opAt 3110 .MSTORE,
   pushAt 3111 4 2363114419,
   pushAt 3112 1 160,
   opAt 3113 .MSTORE,
   opAt 3114 .POP,
   opAt 3115 .JUMP]

def bodyPath2 : List Located :=
  [opAt 3116 .JUMPDEST,
   pushAt 3117 4 252128907,
   pushAt 3118 1 32,
   opAt 3119 .MSTORE,
   pushAt 3120 4 1375323404,
   pushAt 3121 1 64,
   opAt 3122 .MSTORE,
   pushAt 3123 4 388551888,
   pushAt 3124 1 96,
   opAt 3125 .MSTORE,
   pushAt 3126 4 2965778244,
   pushAt 3127 1 128,
   opAt 3128 .MSTORE,
   pushAt 3129 4 2859683440,
   pushAt 3130 1 160,
   opAt 3131 .MSTORE,
   opAt 3132 .POP,
   opAt 3133 .JUMP]

def bodyPath3 : List Located :=
  [opAt 3134 .JUMPDEST,
   pushAt 3135 4 574200439,
   pushAt 3136 1 32,
   opAt 3137 .MSTORE,
   pushAt 3138 4 4203611128,
   pushAt 3139 1 64,
   opAt 3140 .MSTORE,
   pushAt 3141 4 2300602174,
   pushAt 3142 1 96,
   opAt 3143 .MSTORE,
   pushAt 3144 4 140662177,
   pushAt 3145 1 128,
   opAt 3146 .MSTORE,
   pushAt 3147 4 1945316577,
   pushAt 3148 1 160,
   opAt 3149 .MSTORE,
   opAt 3150 .POP,
   opAt 3151 .JUMP]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputPaths
