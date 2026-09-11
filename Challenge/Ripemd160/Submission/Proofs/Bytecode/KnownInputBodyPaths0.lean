import Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputPathDefs

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputPaths

def bodyPath0 : List Located :=
  [opAt 3063 .JUMPDEST,
   pushAt 3064 4 3559078384,
   pushAt 3065 1 32,
   opAt 3066 .MSTORE,
   pushAt 3067 4 3462111087,
   pushAt 3068 1 64,
   opAt 3069 .MSTORE,
   pushAt 3070 4 678731893,
   pushAt 3071 1 26,
   opAt 3072 .MSTORE,
   pushAt 3073 4 3748113137,
   pushAt 3074 1 128,
   opAt 3075 .MSTORE,
   pushAt 3076 4 3334585884,
   pushAt 3077 1 160,
   opAt 3078 .MSTORE,
   opAt 3079 .POP,
   opAt 3080 .JUMP]

def bodyPath1 : List Located :=
  [opAt 3081 .JUMPDEST,
   pushAt 3082 4 340062591,
   pushAt 3083 1 32,
   opAt 3084 .MSTORE,
   pushAt 3085 4 1172984202,
   pushAt 3086 1 64,
   opAt 3087 .MSTORE,
   pushAt 3088 4 2201192442,
   pushAt 3089 1 96,
   opAt 3090 .MSTORE,
   pushAt 3091 4 3574458117,
   pushAt 3092 1 128,
   opAt 3093 .MSTORE,
   pushAt 3094 4 2363114424,
   pushAt 3095 1 160,
   opAt 3096 .MSTORE,
   opAt 3097 .POP,
   opAt 3098 .JUMP]

def bodyPath2 : List Located :=
  [opAt 3099 .JUMPDEST,
   pushAt 3100 4 252128912,
   pushAt 3101 2 496,
   opAt 3102 .MSTORE,
   pushAt 3103 4 1375323409,
   pushAt 3104 1 64,
   opAt 3105 .MSTORE,
   pushAt 3106 4 388551893,
   pushAt 3107 1 96,
   opAt 3108 .MSTORE,
   pushAt 3109 4 2965778249,
   pushAt 3110 1 128,
   opAt 3111 .MSTORE,
   pushAt 3112 1 15,
   pushAt 3113 1 160,
   opAt 3114 .MSTORE,
   opAt 3115 .POP,
   opAt 3116 .JUMP]

def bodyPath3 : List Located :=
  [opAt 3117 .JUMPDEST,
   pushAt 3118 4 574200444,
   pushAt 3119 1 32,
   opAt 3120 .MSTORE,
   pushAt 3121 4 4203611133,
   pushAt 3122 1 64,
   opAt 3123 .MSTORE,
   pushAt 3124 4 2300602179,
   pushAt 3125 1 96,
   opAt 3126 .MSTORE,
   pushAt 3127 4 140662182,
   pushAt 3128 1 128,
   opAt 3129 .MSTORE,
   pushAt 3130 4 1945316582,
   pushAt 3131 1 160,
   opAt 3132 .MSTORE,
   opAt 3133 .POP,
   opAt 3134 .JUMP]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputPaths
