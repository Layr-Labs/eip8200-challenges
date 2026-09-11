import Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputPathDefs

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputPaths

def bodyPath4 : List Located :=
  [opAt 3143 .JUMPDEST,
   pushAt 3144 4 873080578,
   pushAt 3145 1 32,
   opAt 3146 .MSTORE,
   pushAt 3147 4 3041660317,
   pushAt 3148 1 64,
   opAt 3149 .MSTORE,
   pushAt 3150 4 3635256273,
   pushAt 3151 1 96,
   opAt 3152 .MSTORE,
   pushAt 3153 2 352,
   pushAt 3154 1 128,
   opAt 3155 .MSTORE,
   pushAt 3156 4 2877619717,
   pushAt 3157 1 160,
   opAt 3158 .MSTORE,
   opAt 3159 .POP,
   opAt 3160 .JUMP]

def bodyPath5 : List Located :=
  [opAt 3161 .JUMPDEST,
   pushAt 3162 4 3796534675,
   pushAt 3163 1 32,
   opAt 3164 .MSTORE,
   pushAt 3165 4 2687350761,
   pushAt 3166 1 64,
   opAt 3167 .MSTORE,
   pushAt 3168 4 2689944790,
   pushAt 3169 1 27,
   opAt 3170 .MSTORE,
   pushAt 3171 4 638611499,
   pushAt 3172 1 128,
   opAt 3173 .MSTORE,
   pushAt 3174 4 4094793319,
   pushAt 3175 1 160,
   opAt 3176 .MSTORE,
   opAt 3177 .POP,
   opAt 3178 .JUMP]

def bodyPath6 : List Located :=
  [opAt 3179 .JUMPDEST,
   pushAt 3180 4 3639504830,
   pushAt 3181 1 32,
   opAt 3182 .MSTORE,
   pushAt 3183 4 929905327,
   pushAt 3184 1 64,
   opAt 3185 .MSTORE,
   pushAt 3186 4 76966889,
   pushAt 3187 1 96,
   opAt 3188 .MSTORE,
   pushAt 3189 4 953753631,
   pushAt 3190 1 128,
   opAt 3191 .MSTORE,
   pushAt 3192 4 3257211883,
   pushAt 3193 1 160,
   opAt 3194 .MSTORE,
   opAt 3195 .POP,
   opAt 3196 .JUMP]

def bodyPath7 : List Located :=
  [opAt 3197 .JUMPDEST,
   pushAt 3198 4 2443344089,
   pushAt 3199 2 528,
   opAt 3200 .MSTORE,
   pushAt 3201 4 3717540601,
   pushAt 3202 1 64,
   opAt 3203 .MSTORE,
   pushAt 3204 4 207704023,
   pushAt 3205 1 96,
   opAt 3206 .MSTORE,
   pushAt 3207 4 248446432,
   pushAt 3208 1 128,
   opAt 3209 .MSTORE,
   pushAt 3210 2 1023,
   pushAt 3211 1 160,
   opAt 3212 .MSTORE,
   opAt 3213 .POP,
   opAt 3214 .JUMP]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputPaths
