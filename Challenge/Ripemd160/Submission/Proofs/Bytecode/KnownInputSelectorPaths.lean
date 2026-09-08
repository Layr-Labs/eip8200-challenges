import Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputPathDefs

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputPaths

def selectorGroup0 : List Located :=
  [opAt 3002 (.Dup ⟨2, by decide⟩),
   pushAt 3003 0 0,
   opAt 3004 .EQ,
   pushAt 3005 2 6216,
   opAt 3006 .JUMPI]

def selectorGroup1 : List Located :=
  [opAt 3007 (.Dup ⟨2, by decide⟩),
   pushAt 3008 1 64,
   opAt 3009 .EQ,
   pushAt 3010 2 6259,
   opAt 3011 .JUMPI]

def selectorGroup2 : List Located :=
  [opAt 3012 (.Dup ⟨2, by decide⟩),
   pushAt 3013 1 128,
   opAt 3014 .EQ,
   pushAt 3015 2 6302,
   opAt 3016 .JUMPI]

def selectorGroup3 : List Located :=
  [opAt 3017 (.Dup ⟨2, by decide⟩),
   pushAt 3018 1 192,
   opAt 3019 .EQ,
   pushAt 3020 2 6345,
   opAt 3021 .JUMPI]

def selectorGroup4 : List Located :=
  [opAt 3022 (.Dup ⟨2, by decide⟩),
   pushAt 3023 2 256,
   opAt 3024 .EQ,
   pushAt 3025 2 6388,
   opAt 3026 .JUMPI]

def selectorGroup5 : List Located :=
  [opAt 3027 (.Dup ⟨2, by decide⟩),
   pushAt 3028 2 320,
   opAt 3029 .EQ,
   pushAt 3030 2 6431,
   opAt 3031 .JUMPI]

def selectorGroup6 : List Located :=
  [opAt 3032 (.Dup ⟨2, by decide⟩),
   pushAt 3033 2 384,
   opAt 3034 .EQ,
   pushAt 3035 2 6474,
   opAt 3036 .JUMPI]

def selectorGroup7 : List Located :=
  [opAt 3037 (.Dup ⟨2, by decide⟩),
   pushAt 3038 2 448,
   opAt 3039 .EQ,
   pushAt 3040 2 6517,
   opAt 3041 .JUMPI]

def selectorGroup8 : List Located :=
  [opAt 3042 (.Dup ⟨2, by decide⟩),
   pushAt 3043 2 512,
   opAt 3044 .EQ,
   pushAt 3045 2 6560,
   opAt 3046 .JUMPI]

def selectorGroup9 : List Located :=
  [opAt 3047 (.Dup ⟨2, by decide⟩),
   pushAt 3048 2 576,
   opAt 3049 .EQ,
   pushAt 3050 2 6603,
   opAt 3051 .JUMPI]

def selectorGroup10 : List Located :=
  [opAt 3052 (.Dup ⟨2, by decide⟩),
   pushAt 3053 2 640,
   opAt 3054 .EQ,
   pushAt 3055 2 6646,
   opAt 3056 .JUMPI]

def selectorGroup11 : List Located :=
  [opAt 3057 (.Dup ⟨2, by decide⟩),
   pushAt 3058 2 704,
   opAt 3059 .EQ,
   pushAt 3060 2 6689,
   opAt 3061 .JUMPI]

def selectorGroup12 : List Located :=
  [opAt 3062 (.Dup ⟨2, by decide⟩),
   pushAt 3063 2 768,
   opAt 3064 .EQ,
   pushAt 3065 2 6732,
   opAt 3066 .JUMPI]

def selectorGroup13 : List Located :=
  [opAt 3067 (.Dup ⟨2, by decide⟩),
   pushAt 3068 2 832,
   opAt 3069 .EQ,
   pushAt 3070 2 6775,
   opAt 3071 .JUMPI]

def selectorGroup14 : List Located :=
  [opAt 3072 (.Dup ⟨2, by decide⟩),
   pushAt 3073 2 896,
   opAt 3074 .EQ,
   pushAt 3075 2 6818,
   opAt 3076 .JUMPI]

def selectorGroup15 : List Located :=
  [opAt 3077 (.Dup ⟨2, by decide⟩),
   pushAt 3078 2 960,
   opAt 3079 .EQ,
   pushAt 3080 2 6861,
   opAt 3081 .JUMPI]

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
