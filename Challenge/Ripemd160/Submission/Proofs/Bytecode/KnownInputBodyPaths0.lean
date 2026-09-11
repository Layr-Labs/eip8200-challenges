import Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputPathDefs

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputPaths

def bodyPath0 : List Located :=
  [opAt 3071 .JUMPDEST,
   pushAt 3072 4 3559078384,
   pushAt 3073 1 32,
   opAt 3074 .MSTORE,
   pushAt 3075 4 3462111087,
   pushAt 3076 1 64,
   opAt 3077 .MSTORE,
   pushAt 3078 4 678731893,
   pushAt 3079 1 26,
   opAt 3080 .MSTORE,
   pushAt 3081 4 3748113137,
   pushAt 3082 1 128,
   opAt 3083 .MSTORE,
   pushAt 3084 4 3334585884,
   pushAt 3085 1 160,
   opAt 3086 .MSTORE,
   opAt 3087 .POP,
   opAt 3088 .JUMP]

def bodyPath1 : List Located :=
  [opAt 3089 .JUMPDEST,
   pushAt 3090 4 340062591,
   pushAt 3091 1 32,
   opAt 3092 .MSTORE,
   pushAt 3093 4 1172984202,
   pushAt 3094 1 64,
   opAt 3095 .MSTORE,
   pushAt 3096 4 2201192442,
   pushAt 3097 1 96,
   opAt 3098 .MSTORE,
   pushAt 3099 4 3574458117,
   pushAt 3100 1 128,
   opAt 3101 .MSTORE,
   pushAt 3102 4 2363114424,
   pushAt 3103 1 160,
   opAt 3104 .MSTORE,
   opAt 3105 .POP,
   opAt 3106 .JUMP]

def bodyPath2 : List Located :=
  [opAt 3107 .JUMPDEST,
   pushAt 3108 4 252128912,
   pushAt 3109 2 496,
   opAt 3110 .MSTORE,
   pushAt 3111 4 1375323409,
   pushAt 3112 1 64,
   opAt 3113 .MSTORE,
   pushAt 3114 4 388551893,
   pushAt 3115 1 96,
   opAt 3116 .MSTORE,
   pushAt 3117 4 2965778249,
   pushAt 3118 1 128,
   opAt 3119 .MSTORE,
   pushAt 3120 1 15,
   pushAt 3121 1 160,
   opAt 3122 .MSTORE,
   opAt 3123 .POP,
   opAt 3124 .JUMP]

def bodyPath3 : List Located :=
  [opAt 3125 .JUMPDEST,
   pushAt 3126 4 574200444,
   pushAt 3127 1 32,
   opAt 3128 .MSTORE,
   pushAt 3129 4 4203611133,
   pushAt 3130 1 64,
   opAt 3131 .MSTORE,
   pushAt 3132 4 2300602179,
   pushAt 3133 1 96,
   opAt 3134 .MSTORE,
   pushAt 3135 4 140662182,
   pushAt 3136 1 128,
   opAt 3137 .MSTORE,
   pushAt 3138 4 1945316582,
   pushAt 3139 1 160,
   opAt 3140 .MSTORE,
   opAt 3141 .POP,
   opAt 3142 .JUMP]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputPaths
