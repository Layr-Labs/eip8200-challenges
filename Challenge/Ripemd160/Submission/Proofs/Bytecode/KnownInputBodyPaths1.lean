import Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputPathDefs

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputPaths

def bodyPath4 : List Located :=
  [opAt 3152 .JUMPDEST,
   pushAt 3153 4 873080573,
   pushAt 3154 1 32,
   opAt 3155 .MSTORE,
   pushAt 3156 4 3041660312,
   pushAt 3157 1 64,
   opAt 3158 .MSTORE,
   pushAt 3159 4 3635256268,
   pushAt 3160 1 96,
   opAt 3161 .MSTORE,
   pushAt 3162 4 3366369312,
   pushAt 3163 1 128,
   opAt 3164 .MSTORE,
   pushAt 3165 4 2877619712,
   pushAt 3166 1 160,
   opAt 3167 .MSTORE,
   opAt 3168 .POP,
   opAt 3169 .JUMP]

def bodyPath5 : List Located :=
  [opAt 3170 .JUMPDEST,
   pushAt 3171 4 3796534670,
   pushAt 3172 1 32,
   opAt 3173 .MSTORE,
   pushAt 3174 4 2687350756,
   pushAt 3175 1 64,
   opAt 3176 .MSTORE,
   pushAt 3177 4 2689944785,
   pushAt 3178 1 96,
   opAt 3179 .MSTORE,
   pushAt 3180 4 638611494,
   pushAt 3181 1 128,
   opAt 3182 .MSTORE,
   pushAt 3183 4 4094793314,
   pushAt 3184 1 160,
   opAt 3185 .MSTORE,
   opAt 3186 .POP,
   opAt 3187 .JUMP]

def bodyPath6 : List Located :=
  [opAt 3188 .JUMPDEST,
   pushAt 3189 4 3639504825,
   pushAt 3190 1 32,
   opAt 3191 .MSTORE,
   pushAt 3192 4 929905322,
   pushAt 3193 1 64,
   opAt 3194 .MSTORE,
   pushAt 3195 4 76966884,
   pushAt 3196 1 96,
   opAt 3197 .MSTORE,
   pushAt 3198 4 953753626,
   pushAt 3199 1 128,
   opAt 3200 .MSTORE,
   pushAt 3201 4 3257211878,
   pushAt 3202 1 160,
   opAt 3203 .MSTORE,
   opAt 3204 .POP,
   opAt 3205 .JUMP]

def bodyPath7 : List Located :=
  [opAt 3206 .JUMPDEST,
   pushAt 3207 4 2443344084,
   pushAt 3208 1 32,
   opAt 3209 .MSTORE,
   pushAt 3210 4 3717540596,
   pushAt 3211 1 64,
   opAt 3212 .MSTORE,
   pushAt 3213 4 207704018,
   pushAt 3214 1 96,
   opAt 3215 .MSTORE,
   pushAt 3216 4 248446427,
   pushAt 3217 1 128,
   opAt 3218 .MSTORE,
   pushAt 3219 4 3649743885,
   pushAt 3220 1 160,
   opAt 3221 .MSTORE,
   opAt 3222 .POP,
   opAt 3223 .JUMP]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputPaths
