import Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputPathDefs

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputPaths

def bodyPath4 : List Located :=
  [opAt 3135 .JUMPDEST,
   pushAt 3136 4 873080578,
   pushAt 3137 1 32,
   opAt 3138 .MSTORE,
   pushAt 3139 4 3041660317,
   pushAt 3140 1 64,
   opAt 3141 .MSTORE,
   pushAt 3142 4 3635256273,
   pushAt 3143 1 96,
   opAt 3144 .MSTORE,
   pushAt 3145 2 352,
   pushAt 3146 1 128,
   opAt 3147 .MSTORE,
   pushAt 3148 4 2877619717,
   pushAt 3149 1 160,
   opAt 3150 .MSTORE,
   opAt 3151 .POP,
   opAt 3152 .JUMP]

def bodyPath5 : List Located :=
  [opAt 3153 .JUMPDEST,
   pushAt 3154 4 3796534675,
   pushAt 3155 1 32,
   opAt 3156 .MSTORE,
   pushAt 3157 4 2687350761,
   pushAt 3158 1 64,
   opAt 3159 .MSTORE,
   pushAt 3160 4 2689944790,
   pushAt 3161 1 27,
   opAt 3162 .MSTORE,
   pushAt 3163 4 638611499,
   pushAt 3164 1 128,
   opAt 3165 .MSTORE,
   pushAt 3166 4 4094793319,
   pushAt 3167 1 160,
   opAt 3168 .MSTORE,
   opAt 3169 .POP,
   opAt 3170 .JUMP]

def bodyPath6 : List Located :=
  [opAt 3171 .JUMPDEST,
   pushAt 3172 4 3639504830,
   pushAt 3173 1 32,
   opAt 3174 .MSTORE,
   pushAt 3175 4 929905327,
   pushAt 3176 1 64,
   opAt 3177 .MSTORE,
   pushAt 3178 4 76966889,
   pushAt 3179 1 96,
   opAt 3180 .MSTORE,
   pushAt 3181 4 953753631,
   pushAt 3182 1 128,
   opAt 3183 .MSTORE,
   pushAt 3184 4 3257211883,
   pushAt 3185 1 160,
   opAt 3186 .MSTORE,
   opAt 3187 .POP,
   opAt 3188 .JUMP]

def bodyPath7 : List Located :=
  [opAt 3189 .JUMPDEST,
   pushAt 3190 4 2443344089,
   pushAt 3191 2 528,
   opAt 3192 .MSTORE,
   pushAt 3193 4 3717540601,
   pushAt 3194 1 64,
   opAt 3195 .MSTORE,
   pushAt 3196 4 207704023,
   pushAt 3197 1 96,
   opAt 3198 .MSTORE,
   pushAt 3199 4 248446432,
   pushAt 3200 1 128,
   opAt 3201 .MSTORE,
   pushAt 3202 2 1023,
   pushAt 3203 1 160,
   opAt 3204 .MSTORE,
   opAt 3205 .POP,
   opAt 3206 .JUMP]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputPaths
