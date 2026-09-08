import Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputPathDefs

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputPaths

def selectorGroup0 : List Located :=
  [opAt 2998 (.Dup ⟨2, by decide⟩),
   pushAt 2999 0 0,
   opAt 3000 .EQ,
   pushAt 3001 2 6211,
   opAt 3002 .JUMPI]

def selectorGroup1 : List Located :=
  [opAt 3003 (.Dup ⟨2, by decide⟩),
   pushAt 3004 1 64,
   opAt 3005 .EQ,
   pushAt 3006 2 6254,
   opAt 3007 .JUMPI]

def selectorGroup2 : List Located :=
  [opAt 3008 (.Dup ⟨2, by decide⟩),
   pushAt 3009 1 128,
   opAt 3010 .EQ,
   pushAt 3011 2 6297,
   opAt 3012 .JUMPI]

def selectorGroup3 : List Located :=
  [opAt 3013 (.Dup ⟨2, by decide⟩),
   pushAt 3014 1 192,
   opAt 3015 .EQ,
   pushAt 3016 2 6340,
   opAt 3017 .JUMPI]

def selectorGroup4 : List Located :=
  [opAt 3018 (.Dup ⟨2, by decide⟩),
   pushAt 3019 2 256,
   opAt 3020 .EQ,
   pushAt 3021 2 6383,
   opAt 3022 .JUMPI]

def selectorGroup5 : List Located :=
  [opAt 3023 (.Dup ⟨2, by decide⟩),
   pushAt 3024 2 320,
   opAt 3025 .EQ,
   pushAt 3026 2 6426,
   opAt 3027 .JUMPI]

def selectorGroup6 : List Located :=
  [opAt 3028 (.Dup ⟨2, by decide⟩),
   pushAt 3029 2 384,
   opAt 3030 .EQ,
   pushAt 3031 2 6469,
   opAt 3032 .JUMPI]

def selectorGroup7 : List Located :=
  [opAt 3033 (.Dup ⟨2, by decide⟩),
   pushAt 3034 2 448,
   opAt 3035 .EQ,
   pushAt 3036 2 6512,
   opAt 3037 .JUMPI]

def selectorGroup8 : List Located :=
  [opAt 3038 (.Dup ⟨2, by decide⟩),
   pushAt 3039 2 512,
   opAt 3040 .EQ,
   pushAt 3041 2 6555,
   opAt 3042 .JUMPI]

def selectorGroup9 : List Located :=
  [opAt 3043 (.Dup ⟨2, by decide⟩),
   pushAt 3044 2 576,
   opAt 3045 .EQ,
   pushAt 3046 2 6598,
   opAt 3047 .JUMPI]

def selectorGroup10 : List Located :=
  [opAt 3048 (.Dup ⟨2, by decide⟩),
   pushAt 3049 2 640,
   opAt 3050 .EQ,
   pushAt 3051 2 6641,
   opAt 3052 .JUMPI]

def selectorGroup11 : List Located :=
  [opAt 3053 (.Dup ⟨2, by decide⟩),
   pushAt 3054 2 704,
   opAt 3055 .EQ,
   pushAt 3056 2 6684,
   opAt 3057 .JUMPI]

def selectorGroup12 : List Located :=
  [opAt 3058 (.Dup ⟨2, by decide⟩),
   pushAt 3059 2 768,
   opAt 3060 .EQ,
   pushAt 3061 2 6727,
   opAt 3062 .JUMPI]

def selectorGroup13 : List Located :=
  [opAt 3063 (.Dup ⟨2, by decide⟩),
   pushAt 3064 2 832,
   opAt 3065 .EQ,
   pushAt 3066 2 6770,
   opAt 3067 .JUMPI]

def selectorGroup14 : List Located :=
  [opAt 3068 (.Dup ⟨2, by decide⟩),
   pushAt 3069 2 896,
   opAt 3070 .EQ,
   pushAt 3071 2 6813,
   opAt 3072 .JUMPI]

def selectorGroup15 : List Located :=
  [opAt 3073 (.Dup ⟨2, by decide⟩),
   pushAt 3074 2 960,
   opAt 3075 .EQ,
   pushAt 3076 2 6856,
   opAt 3077 .JUMPI]

def selectorPath0 : List Located := selectorGroup0
def selectorPath1 : List Located := selectorGroup0 ++ selectorGroup1
def selectorPath2 : List Located := selectorGroup0 ++ selectorGroup1 ++ selectorGroup2
def selectorPath3 : List Located := selectorGroup0 ++ selectorGroup1 ++ selectorGroup2 ++ selectorGroup3
def selectorPath4 : List Located := selectorGroup0 ++ selectorGroup1 ++ selectorGroup2 ++ selectorGroup3 ++ selectorGroup4
def selectorPath5 : List Located := selectorGroup0 ++ selectorGroup1 ++ selectorGroup2 ++ selectorGroup3 ++ selectorGroup4 ++ selectorGroup5
def selectorPath6 : List Located := selectorGroup0 ++ selectorGroup1 ++ selectorGroup2 ++ selectorGroup3 ++ selectorGroup4 ++ selectorGroup5 ++ selectorGroup6
def selectorPath7 : List Located := selectorGroup0 ++ selectorGroup1 ++ selectorGroup2 ++ selectorGroup3 ++ selectorGroup4 ++ selectorGroup5 ++ selectorGroup6 ++ selectorGroup7
def selectorPath8 : List Located := selectorGroup0 ++ selectorGroup1 ++ selectorGroup2 ++ selectorGroup3 ++ selectorGroup4 ++ selectorGroup5 ++ selectorGroup6 ++ selectorGroup7 ++ selectorGroup8
def selectorPath9 : List Located := selectorGroup0 ++ selectorGroup1 ++ selectorGroup2 ++ selectorGroup3 ++ selectorGroup4 ++ selectorGroup5 ++ selectorGroup6 ++ selectorGroup7 ++ selectorGroup8 ++ selectorGroup9
def selectorPath10 : List Located := selectorGroup0 ++ selectorGroup1 ++ selectorGroup2 ++ selectorGroup3 ++ selectorGroup4 ++ selectorGroup5 ++ selectorGroup6 ++ selectorGroup7 ++ selectorGroup8 ++ selectorGroup9 ++ selectorGroup10
def selectorPath11 : List Located := selectorGroup0 ++ selectorGroup1 ++ selectorGroup2 ++ selectorGroup3 ++ selectorGroup4 ++ selectorGroup5 ++ selectorGroup6 ++ selectorGroup7 ++ selectorGroup8 ++ selectorGroup9 ++ selectorGroup10 ++ selectorGroup11
def selectorPath12 : List Located := selectorGroup0 ++ selectorGroup1 ++ selectorGroup2 ++ selectorGroup3 ++ selectorGroup4 ++ selectorGroup5 ++ selectorGroup6 ++ selectorGroup7 ++ selectorGroup8 ++ selectorGroup9 ++ selectorGroup10 ++ selectorGroup11 ++ selectorGroup12
def selectorPath13 : List Located := selectorGroup0 ++ selectorGroup1 ++ selectorGroup2 ++ selectorGroup3 ++ selectorGroup4 ++ selectorGroup5 ++ selectorGroup6 ++ selectorGroup7 ++ selectorGroup8 ++ selectorGroup9 ++ selectorGroup10 ++ selectorGroup11 ++ selectorGroup12 ++ selectorGroup13
def selectorPath14 : List Located := selectorGroup0 ++ selectorGroup1 ++ selectorGroup2 ++ selectorGroup3 ++ selectorGroup4 ++ selectorGroup5 ++ selectorGroup6 ++ selectorGroup7 ++ selectorGroup8 ++ selectorGroup9 ++ selectorGroup10 ++ selectorGroup11 ++ selectorGroup12 ++ selectorGroup13 ++ selectorGroup14
def selectorPath15 : List Located := selectorGroup0 ++ selectorGroup1 ++ selectorGroup2 ++ selectorGroup3 ++ selectorGroup4 ++ selectorGroup5 ++ selectorGroup6 ++ selectorGroup7 ++ selectorGroup8 ++ selectorGroup9 ++ selectorGroup10 ++ selectorGroup11 ++ selectorGroup12 ++ selectorGroup13 ++ selectorGroup14 ++ selectorGroup15

def selectorPath (i : Nat) : List Located :=
  match i with
  | 0 => selectorPath0
  | 1 => selectorPath1
  | 2 => selectorPath2
  | 3 => selectorPath3
  | 4 => selectorPath4
  | 5 => selectorPath5
  | 6 => selectorPath6
  | 7 => selectorPath7
  | 8 => selectorPath8
  | 9 => selectorPath9
  | 10 => selectorPath10
  | 11 => selectorPath11
  | 12 => selectorPath12
  | 13 => selectorPath13
  | 14 => selectorPath14
  | _ => selectorPath15

end Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputPaths
