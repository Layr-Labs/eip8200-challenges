import Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputPathDefs

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputPaths

def bodyPath4 : List Located :=
  [opAt 3163 .JUMPDEST,
   pushAt 3164 4 873080578,
   pushAt 3165 1 32,
   opAt 3166 .MSTORE,
   pushAt 3167 4 3041660317,
   pushAt 3168 1 64,
   opAt 3169 .MSTORE,
   pushAt 3170 4 3635256273,
   pushAt 3171 1 96,
   opAt 3172 .MSTORE,
   pushAt 3173 4 3366369317,
   pushAt 3174 1 128,
   opAt 3175 .MSTORE,
   pushAt 3176 4 2877619717,
   pushAt 3177 1 160,
   opAt 3178 .MSTORE,
   opAt 3179 .POP,
   opAt 3180 .JUMP]

def bodyPath5 : List Located :=
  [opAt 3181 .JUMPDEST,
   pushAt 3182 4 3796534675,
   pushAt 3183 1 32,
   opAt 3184 .MSTORE,
   pushAt 3185 4 2687350761,
   pushAt 3186 1 64,
   opAt 3187 .MSTORE,
   pushAt 3188 4 2689944790,
   pushAt 3189 1 96,
   opAt 3190 .MSTORE,
   pushAt 3191 4 638611499,
   pushAt 3192 1 128,
   opAt 3193 .MSTORE,
   pushAt 3194 4 4094793319,
   pushAt 3195 1 160,
   opAt 3196 .MSTORE,
   opAt 3197 .POP,
   opAt 3198 .JUMP]

def bodyPath6 : List Located :=
  [opAt 3199 .JUMPDEST,
   pushAt 3200 4 3639504830,
   pushAt 3201 1 32,
   opAt 3202 .MSTORE,
   pushAt 3203 4 929905327,
   pushAt 3204 1 64,
   opAt 3205 .MSTORE,
   pushAt 3206 4 76966889,
   pushAt 3207 1 96,
   opAt 3208 .MSTORE,
   pushAt 3209 4 953753631,
   pushAt 3210 1 128,
   opAt 3211 .MSTORE,
   pushAt 3212 4 3257211883,
   pushAt 3213 1 160,
   opAt 3214 .MSTORE,
   opAt 3215 .POP,
   opAt 3216 .JUMP]

def bodyPath7 : List Located :=
  [opAt 3217 .JUMPDEST,
   pushAt 3218 4 2443344089,
   pushAt 3219 1 32,
   opAt 3220 .MSTORE,
   pushAt 3221 4 3717540601,
   pushAt 3222 1 64,
   opAt 3223 .MSTORE,
   pushAt 3224 4 207704023,
   pushAt 3225 1 96,
   opAt 3226 .MSTORE,
   pushAt 3227 4 248446432,
   pushAt 3228 1 128,
   opAt 3229 .MSTORE,
   pushAt 3230 4 3649743890,
   pushAt 3231 1 160,
   opAt 3232 .MSTORE,
   opAt 3233 .POP,
   opAt 3234 .JUMP]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputPaths
