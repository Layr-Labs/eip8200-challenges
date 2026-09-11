import Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputPathDefs

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputPaths

def selectorGroup0 : List Located :=
  [opAt 2981 (.Dup ⟨2, by decide⟩),
   pushAt 2982 0 0,
   opAt 2983 .EQ,
   pushAt 2984 2 6222,
   opAt 2985 .JUMPI]

def selectorGroup1 : List Located :=
  [opAt 2986 (.Dup ⟨2, by decide⟩),
   pushAt 2987 1 64,
   opAt 2988 .EQ,
   pushAt 2989 2 6265,
   opAt 2990 .JUMPI]

def selectorGroup2 : List Located :=
  [opAt 2991 (.Dup ⟨2, by decide⟩),
   pushAt 2992 1 128,
   opAt 2993 .EQ,
   pushAt 2994 2 6308,
   opAt 2995 .JUMPI]

def selectorGroup3 : List Located :=
  [opAt 2996 (.Dup ⟨2, by decide⟩),
   pushAt 2997 1 192,
   opAt 2998 .EQ,
   pushAt 2999 2 6351,
   opAt 3000 .JUMPI]

def selectorGroup4 : List Located :=
  [opAt 3001 (.Dup ⟨2, by decide⟩),
   pushAt 3002 2 256,
   opAt 3003 .EQ,
   pushAt 3004 2 6394,
   opAt 3005 .JUMPI]

def selectorGroup5 : List Located :=
  [opAt 3006 (.Dup ⟨2, by decide⟩),
   pushAt 3007 2 416,
   opAt 3008 .EQ,
   pushAt 3009 2 272,
   opAt 3010 .JUMPI]

def selectorGroup6 : List Located :=
  [opAt 3011 (.Dup ⟨2, by decide⟩),
   pushAt 3012 2 384,
   opAt 3013 .EQ,
   pushAt 3014 2 6480,
   opAt 3015 .JUMPI]

def selectorGroup7 : List Located :=
  [opAt 3016 (.Dup ⟨2, by decide⟩),
   pushAt 3017 2 448,
   opAt 3018 .EQ,
   pushAt 3019 2 6523,
   opAt 3020 .JUMPI]

def selectorGroup8 : List Located :=
  [opAt 3021 (.Dup ⟨2, by decide⟩),
   pushAt 3022 2 512,
   opAt 3023 .EQ,
   pushAt 3024 2 6566,
   opAt 3025 .JUMPI]

def selectorGroup9 : List Located :=
  [opAt 3026 (.Dup ⟨2, by decide⟩),
   pushAt 3027 2 576,
   opAt 3028 .EQ,
   pushAt 3029 2 6609,
   opAt 3030 .JUMPI]

def selectorGroup10 : List Located :=
  [opAt 3031 (.Dup ⟨2, by decide⟩),
   pushAt 3032 2 640,
   opAt 3033 .EQ,
   pushAt 3034 1 22,
   opAt 3035 .JUMPI]

def selectorGroup11 : List Located :=
  [opAt 3036 (.Dup ⟨2, by decide⟩),
   pushAt 3037 2 704,
   opAt 3038 .EQ,
   pushAt 3039 2 6695,
   opAt 3040 .JUMPI]

def selectorGroup12 : List Located :=
  [opAt 3041 (.Dup ⟨2, by decide⟩),
   pushAt 3042 2 768,
   opAt 3043 .EQ,
   pushAt 3044 2 6738,
   opAt 3045 .JUMPI]

def selectorGroup13 : List Located :=
  [opAt 3046 (.Dup ⟨2, by decide⟩),
   pushAt 3047 2 832,
   opAt 3048 .EQ,
   pushAt 3049 2 6781,
   opAt 3050 .JUMPI]

def selectorGroup14 : List Located :=
  [opAt 3051 (.Dup ⟨2, by decide⟩),
   pushAt 3052 2 896,
   opAt 3053 .EQ,
   pushAt 3054 2 6824,
   opAt 3055 .JUMPI]

def selectorGroup15 : List Located :=
  [opAt 3056 (.Dup ⟨2, by decide⟩),
   pushAt 3057 2 960,
   opAt 3058 .EQ,
   pushAt 3059 2 6867,
   opAt 3060 .JUMPI]

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
