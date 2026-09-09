import Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputPathDefs

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputPaths

def bodyPath0 : List Located :=
  [opAt 3091 .JUMPDEST,
   pushAt 3092 4 3559078384,
   pushAt 3093 1 32,
   opAt 3094 .MSTORE,
   pushAt 3095 4 3462111087,
   pushAt 3096 1 64,
   opAt 3097 .MSTORE,
   pushAt 3098 4 678731893,
   pushAt 3099 1 96,
   opAt 3100 .MSTORE,
   pushAt 3101 4 3748113137,
   pushAt 3102 1 128,
   opAt 3103 .MSTORE,
   pushAt 3104 4 3334585884,
   pushAt 3105 1 160,
   opAt 3106 .MSTORE,
   opAt 3107 .POP,
   opAt 3108 .JUMP]

def bodyPath1 : List Located :=
  [opAt 3109 .JUMPDEST,
   pushAt 3110 4 340062591,
   pushAt 3111 1 32,
   opAt 3112 .MSTORE,
   pushAt 3113 4 1172984202,
   pushAt 3114 1 64,
   opAt 3115 .MSTORE,
   pushAt 3116 4 2201192442,
   pushAt 3117 1 96,
   opAt 3118 .MSTORE,
   pushAt 3119 4 3574458117,
   pushAt 3120 1 128,
   opAt 3121 .MSTORE,
   pushAt 3122 4 2363114424,
   pushAt 3123 1 160,
   opAt 3124 .MSTORE,
   opAt 3125 .POP,
   opAt 3126 .JUMP]

def bodyPath2 : List Located :=
  [opAt 3127 .JUMPDEST,
   pushAt 3128 4 252128912,
   pushAt 3129 1 32,
   opAt 3130 .MSTORE,
   pushAt 3131 4 1375323409,
   pushAt 3132 1 64,
   opAt 3133 .MSTORE,
   pushAt 3134 4 388551893,
   pushAt 3135 1 96,
   opAt 3136 .MSTORE,
   pushAt 3137 4 2965778249,
   pushAt 3138 1 128,
   opAt 3139 .MSTORE,
   pushAt 3140 4 2859683445,
   pushAt 3141 1 160,
   opAt 3142 .MSTORE,
   opAt 3143 .POP,
   opAt 3144 .JUMP]

def bodyPath3 : List Located :=
  [opAt 3145 .JUMPDEST,
   pushAt 3146 4 574200444,
   pushAt 3147 1 32,
   opAt 3148 .MSTORE,
   pushAt 3149 4 4203611133,
   pushAt 3150 1 64,
   opAt 3151 .MSTORE,
   pushAt 3152 4 2300602179,
   pushAt 3153 1 96,
   opAt 3154 .MSTORE,
   pushAt 3155 4 140662182,
   pushAt 3156 1 128,
   opAt 3157 .MSTORE,
   pushAt 3158 4 1945316582,
   pushAt 3159 1 160,
   opAt 3160 .MSTORE,
   opAt 3161 .POP,
   opAt 3162 .JUMP]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputPaths
