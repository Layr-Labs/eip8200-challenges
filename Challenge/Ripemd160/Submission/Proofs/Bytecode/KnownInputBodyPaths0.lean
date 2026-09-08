import Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputPathDefs

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputPaths

def bodyPath0 : List Located :=
  [opAt 3084 .JUMPDEST,
   pushAt 3085 4 3559078384,
   pushAt 3086 1 32,
   opAt 3087 .MSTORE,
   pushAt 3088 4 3462111087,
   pushAt 3089 1 64,
   opAt 3090 .MSTORE,
   pushAt 3091 4 678731893,
   pushAt 3092 1 96,
   opAt 3093 .MSTORE,
   pushAt 3094 4 3748113137,
   pushAt 3095 1 128,
   opAt 3096 .MSTORE,
   pushAt 3097 4 3334585884,
   pushAt 3098 1 160,
   opAt 3099 .MSTORE,
   opAt 3100 .POP,
   opAt 3101 .JUMP]

def bodyPath1 : List Located :=
  [opAt 3102 .JUMPDEST,
   pushAt 3103 4 340062591,
   pushAt 3104 1 32,
   opAt 3105 .MSTORE,
   pushAt 3106 4 1172984202,
   pushAt 3107 1 64,
   opAt 3108 .MSTORE,
   pushAt 3109 4 2201192442,
   pushAt 3110 1 96,
   opAt 3111 .MSTORE,
   pushAt 3112 4 3574458117,
   pushAt 3113 1 128,
   opAt 3114 .MSTORE,
   pushAt 3115 4 2363114424,
   pushAt 3116 1 160,
   opAt 3117 .MSTORE,
   opAt 3118 .POP,
   opAt 3119 .JUMP]

def bodyPath2 : List Located :=
  [opAt 3120 .JUMPDEST,
   pushAt 3121 4 252128912,
   pushAt 3122 1 32,
   opAt 3123 .MSTORE,
   pushAt 3124 4 1375323409,
   pushAt 3125 1 64,
   opAt 3126 .MSTORE,
   pushAt 3127 4 388551893,
   pushAt 3128 1 96,
   opAt 3129 .MSTORE,
   pushAt 3130 4 2965778249,
   pushAt 3131 1 128,
   opAt 3132 .MSTORE,
   pushAt 3133 4 2859683445,
   pushAt 3134 1 160,
   opAt 3135 .MSTORE,
   opAt 3136 .POP,
   opAt 3137 .JUMP]

def bodyPath3 : List Located :=
  [opAt 3138 .JUMPDEST,
   pushAt 3139 4 574200444,
   pushAt 3140 1 32,
   opAt 3141 .MSTORE,
   pushAt 3142 4 4203611133,
   pushAt 3143 1 64,
   opAt 3144 .MSTORE,
   pushAt 3145 4 2300602179,
   pushAt 3146 1 96,
   opAt 3147 .MSTORE,
   pushAt 3148 4 140662182,
   pushAt 3149 1 128,
   opAt 3150 .MSTORE,
   pushAt 3151 4 1945316582,
   pushAt 3152 1 160,
   opAt 3153 .MSTORE,
   opAt 3154 .POP,
   opAt 3155 .JUMP]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputPaths
