import Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputPathDefs

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputPaths

def selectorGroup0 : List Located :=
  [opAt 2989 (.Dup ⟨2, by decide⟩),
   pushAt 2990 0 0,
   opAt 2991 .EQ,
   pushAt 2992 2 6216,
   opAt 2993 .JUMPI]

def selectorGroup1 : List Located :=
  [opAt 2994 (.Dup ⟨2, by decide⟩),
   pushAt 2995 1 64,
   opAt 2996 .EQ,
   pushAt 2997 2 6259,
   opAt 2998 .JUMPI]

def selectorGroup2 : List Located :=
  [opAt 2999 (.Dup ⟨2, by decide⟩),
   pushAt 3000 1 128,
   opAt 3001 .EQ,
   pushAt 3002 2 6302,
   opAt 3003 .JUMPI]

def selectorGroup3 : List Located :=
  [opAt 3004 (.Dup ⟨2, by decide⟩),
   pushAt 3005 1 192,
   opAt 3006 .EQ,
   pushAt 3007 2 6345,
   opAt 3008 .JUMPI]

def selectorGroup4 : List Located :=
  [opAt 3009 (.Dup ⟨2, by decide⟩),
   pushAt 3010 2 256,
   opAt 3011 .EQ,
   pushAt 3012 2 6388,
   opAt 3013 .JUMPI]

def selectorGroup5 : List Located :=
  [opAt 3014 (.Dup ⟨2, by decide⟩),
   pushAt 3015 2 416,
   opAt 3016 .EQ,
   pushAt 3017 2 272,
   opAt 3018 .JUMPI]

def selectorGroup6 : List Located :=
  [opAt 3019 (.Dup ⟨2, by decide⟩),
   pushAt 3020 2 384,
   opAt 3021 .EQ,
   pushAt 3022 2 6474,
   opAt 3023 .JUMPI]

def selectorGroup7 : List Located :=
  [opAt 3024 (.Dup ⟨2, by decide⟩),
   pushAt 3025 2 448,
   opAt 3026 .EQ,
   pushAt 3027 2 6517,
   opAt 3028 .JUMPI]

def selectorGroup8 : List Located :=
  [opAt 3029 (.Dup ⟨2, by decide⟩),
   pushAt 3030 2 512,
   opAt 3031 .EQ,
   pushAt 3032 2 6560,
   opAt 3033 .JUMPI]

def selectorGroup9 : List Located :=
  [opAt 3034 (.Dup ⟨2, by decide⟩),
   pushAt 3035 2 576,
   opAt 3036 .EQ,
   pushAt 3037 2 6603,
   opAt 3038 .JUMPI]

def selectorGroup10 : List Located :=
  [opAt 3039 (.Dup ⟨2, by decide⟩),
   pushAt 3040 2 640,
   opAt 3041 .EQ,
   pushAt 3042 1 22,
   opAt 3043 .JUMPI]

def selectorGroup11 : List Located :=
  [opAt 3044 (.Dup ⟨2, by decide⟩),
   pushAt 3045 2 704,
   opAt 3046 .EQ,
   pushAt 3047 2 6689,
   opAt 3048 .JUMPI]

def selectorGroup12 : List Located :=
  [opAt 3049 (.Dup ⟨2, by decide⟩),
   pushAt 3050 2 768,
   opAt 3051 .EQ,
   pushAt 3052 2 6732,
   opAt 3053 .JUMPI]

def selectorGroup13 : List Located :=
  [opAt 3054 (.Dup ⟨2, by decide⟩),
   pushAt 3055 2 832,
   opAt 3056 .EQ,
   pushAt 3057 2 6775,
   opAt 3058 .JUMPI]

def selectorGroup14 : List Located :=
  [opAt 3059 (.Dup ⟨2, by decide⟩),
   pushAt 3060 2 896,
   opAt 3061 .EQ,
   pushAt 3062 2 6818,
   opAt 3063 .JUMPI]

def selectorGroup15 : List Located :=
  [opAt 3064 (.Dup ⟨2, by decide⟩),
   pushAt 3065 2 960,
   opAt 3066 .EQ,
   pushAt 3067 2 6861,
   opAt 3068 .JUMPI]

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
