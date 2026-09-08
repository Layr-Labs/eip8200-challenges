import Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputPathDefs

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputPaths

def bodyPath4 : List Located :=
  [opAt 3156 .JUMPDEST,
   pushAt 3157 4 873080578,
   pushAt 3158 1 32,
   opAt 3159 .MSTORE,
   pushAt 3160 4 3041660317,
   pushAt 3161 1 64,
   opAt 3162 .MSTORE,
   pushAt 3163 4 3635256273,
   pushAt 3164 1 96,
   opAt 3165 .MSTORE,
   pushAt 3166 4 3366369317,
   pushAt 3167 1 128,
   opAt 3168 .MSTORE,
   pushAt 3169 4 2877619717,
   pushAt 3170 1 160,
   opAt 3171 .MSTORE,
   opAt 3172 .POP,
   opAt 3173 .JUMP]

def bodyPath5 : List Located :=
  [opAt 3174 .JUMPDEST,
   pushAt 3175 4 3796534675,
   pushAt 3176 1 32,
   opAt 3177 .MSTORE,
   pushAt 3178 4 2687350761,
   pushAt 3179 1 64,
   opAt 3180 .MSTORE,
   pushAt 3181 4 2689944790,
   pushAt 3182 1 96,
   opAt 3183 .MSTORE,
   pushAt 3184 4 638611499,
   pushAt 3185 1 128,
   opAt 3186 .MSTORE,
   pushAt 3187 4 4094793319,
   pushAt 3188 1 160,
   opAt 3189 .MSTORE,
   opAt 3190 .POP,
   opAt 3191 .JUMP]

def bodyPath6 : List Located :=
  [opAt 3192 .JUMPDEST,
   pushAt 3193 4 3639504830,
   pushAt 3194 1 32,
   opAt 3195 .MSTORE,
   pushAt 3196 4 929905327,
   pushAt 3197 1 64,
   opAt 3198 .MSTORE,
   pushAt 3199 4 76966889,
   pushAt 3200 1 96,
   opAt 3201 .MSTORE,
   pushAt 3202 4 953753631,
   pushAt 3203 1 128,
   opAt 3204 .MSTORE,
   pushAt 3205 4 3257211883,
   pushAt 3206 1 160,
   opAt 3207 .MSTORE,
   opAt 3208 .POP,
   opAt 3209 .JUMP]

def bodyPath7 : List Located :=
  [opAt 3210 .JUMPDEST,
   pushAt 3211 4 2443344089,
   pushAt 3212 1 32,
   opAt 3213 .MSTORE,
   pushAt 3214 4 3717540601,
   pushAt 3215 1 64,
   opAt 3216 .MSTORE,
   pushAt 3217 4 207704023,
   pushAt 3218 1 96,
   opAt 3219 .MSTORE,
   pushAt 3220 4 248446432,
   pushAt 3221 1 128,
   opAt 3222 .MSTORE,
   pushAt 3223 4 3649743890,
   pushAt 3224 1 160,
   opAt 3225 .MSTORE,
   opAt 3226 .POP,
   opAt 3227 .JUMP]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputPaths
