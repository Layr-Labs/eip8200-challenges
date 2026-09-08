import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedSwar
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedGuardSpec
import Challenge.EvmProof.Stepper
import Challenge.Ripemd160.ProofSupport.InitialState
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Artifact

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000

/-!
# States and paths of the scalar-SWAR patterned-1000 guard

The guard carries the expected word forward instead of storing thirty-two of
them, so the scan is one loop: `wordPath` derives the word and routes the four
straddling offsets to `straddlePath`, and `comparePath` folds the difference
into the accumulator and advances the offset and the scalar.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open PatternedInputData PatternedDigest PatternedGuardSpec PatternedSwar

def wfOp {op : Operation}
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op)
    (hplain : YulEvmCompiler.plainOp op)
    (havailable : op.availableInFork .Osaka = true) :
    Challenge.EvmProof.Stepper.WellFormed .Osaka (.op op) :=
  ⟨hopcode, hplain, havailable⟩

abbrev Located := Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka

def opAt (index : Nat) (op : Operation)
    (hget : Artifact.submissionInstructions[index]? = some (.op op) := by rfl)
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op := by decide)
    (hplain : YulEvmCompiler.plainOp op := by trivial)
    (havailable : op.availableInFork .Osaka = true := by rfl) : Located :=
  ⟨index, .op op, hget, wfOp hopcode hplain havailable⟩

def pushAt (index : Nat) (width : Fin 33) (value : UInt256)
    (hget : Artifact.submissionInstructions[index]? = some (.push width value) := by rfl)
    (hwf : Challenge.EvmProof.Stepper.WellFormed .Osaka
      (.push width value) := by decide) : Located :=
  ⟨index, .push width value, hget, hwf⟩

abbrev run := Challenge.EvmProof.Stepper.runLocatedBlock
  (artifact := Artifact.submissionArtifact) (fork := .Osaka)

/-- Push the five constants and start the scan. -/
def setupPath : List Located :=
  [opAt 64 .JUMPDEST,
   pushAt 65 1 255,
   pushAt 66 0 0,
   opAt 67 .NOT,
   opAt 68 .DIV,
   pushAt 69 32 3244493450063667868678674439968361782956185527883176199882357678282131398018,
   opAt 70 (.Dup ⟨1, by decide⟩),
   pushAt 71 1 7,
   opAt 72 .SHL,
   opAt 73 (.Dup ⟨0, by decide⟩),
   opAt 74 .NOT,
   opAt 75 (.Swap ⟨0, by decide⟩),
   opAt 76 (.Swap ⟨2, by decide⟩),
   opAt 77 (.Dup ⟨2, by decide⟩),
   opAt 78 (.Dup ⟨2, by decide⟩),
   opAt 79 .AND,
   pushAt 80 0 0,
   pushAt 81 0 0,
   pushAt 82 0 0]

/-- Derive the expected word and test for a straddler. -/
def wordPath : List Located :=
  [opAt 83 .JUMPDEST, opAt 84 (.Dup ⟨0, by decide⟩),
   opAt 85 (.Dup ⟨5, by decide⟩), opAt 86 .MUL,
   opAt 87 (.Dup ⟨0, by decide⟩), opAt 88 (.Dup ⟨7, by decide⟩),
   opAt 89 .AND, opAt 90 (.Dup ⟨5, by decide⟩), opAt 91 .ADD,
   opAt 92 (.Dup ⟨1, by decide⟩), opAt 93 (.Dup ⟨9, by decide⟩),
   opAt 94 .XOR, opAt 95 (.Dup ⟨10, by decide⟩), opAt 96 .AND,
   opAt 97 .XOR, opAt 98 (.Dup ⟨3, by decide⟩), pushAt 99 1 255,
   opAt 100 .AND, pushAt 101 1 224, opAt 102 .EQ, pushAt 103 2 312,
   opAt 104 .JUMPI]

/-- Fold one word into the accumulator and advance. -/
def comparePath : List Located :=
  [opAt 105 .JUMPDEST, opAt 106 (.Dup ⟨3, by decide⟩),
   opAt 107 .CALLDATALOAD, opAt 108 .XOR, opAt 109 (.Dup ⟨4, by decide⟩),
   opAt 110 .OR, opAt 111 (.Swap ⟨3, by decide⟩), opAt 112 .POP,
   opAt 113 .POP, pushAt 114 1 160,
   opAt 115 .ADD, pushAt 116 1 255, opAt 117 .AND,
   opAt 118 (.Swap ⟨0, by decide⟩), pushAt 119 1 32, opAt 120 .ADD,
   opAt 121 (.Swap ⟨0, by decide⟩), opAt 122 .JUMPDEST,
   opAt 128 (.Dup ⟨1, by decide⟩), pushAt 129 2 992, opAt 130 .GT,
   pushAt 131 1 189, opAt 132 .JUMPI]

/-- The padded tail word, the cleanup and the miss test. -/
def tailPath : List Located :=
  [pushAt 133 2 992, opAt 134 .CALLDATALOAD,
   pushAt 135 8 9848759918901945995, pushAt 136 1 192, opAt 137 .SHL,
   opAt 138 .XOR, opAt 139 (.Dup ⟨3, by decide⟩), opAt 140 .OR,
   opAt 141 (.Swap ⟨2, by decide⟩), opAt 142 .POP,
   opAt 143 (.Swap ⟨1, by decide⟩), opAt 144 (.Swap ⟨6, by decide⟩),
   opAt 145 .POP, opAt 146 .POP, opAt 147 .POP, opAt 148 .POP,
   opAt 149 .POP, opAt 150 .POP, opAt 151 .POP, pushAt 152 2 352,
   opAt 153 .JUMPI]

/-- Store and return the stored digest. -/
def returnPath : List Located :=
  [pushAt 154 20 766350606435067737561421097975693824639675460820,
   pushAt 155 0 0, opAt 156 .MSTORE, pushAt 157 1 32, pushAt 158 0 0,
   opAt 159 .RETURN]

/-- Shift the correction constant out of `M`. -/
def straddleCorrPath : List Located :=
  [opAt 160 .JUMPDEST, opAt 161 (.Dup ⟨6, by decide⟩),
   opAt 162 (.Dup ⟨4, by decide⟩), pushAt 163 1 8, opAt 164 .SHR,
   pushAt 165 1 5, opAt 166 .MUL, pushAt 167 1 27, opAt 168 .SUB,
   pushAt 169 1 8, opAt 170 .MUL, opAt 171 .SHR, pushAt 172 1 11,
   opAt 173 .MUL]

/-- Apply the correction to the expected word. -/
def straddleAddPath : List Located :=
  [opAt 174 (.Dup ⟨1, by decide⟩), opAt 175 (.Dup ⟨9, by decide⟩),
   opAt 176 .AND, opAt 177 (.Dup ⟨1, by decide⟩), opAt 178 .ADD,
   opAt 179 (.Dup ⟨2, by decide⟩), opAt 180 (.Dup ⟨12, by decide⟩),
   opAt 181 .AND, opAt 182 .XOR, opAt 183 (.Swap ⟨1, by decide⟩),
   opAt 184 .POP, opAt 185 .POP]

/-- Bump the scalar and rejoin the scan. -/
def straddleBackPath : List Located :=
  [opAt 186 (.Dup ⟨2, by decide⟩), pushAt 187 1 11, opAt 188 .ADD,
   opAt 189 (.Swap ⟨2, by decide⟩), opAt 190 .POP, pushAt 191 1 215,
   opAt 192 .JUMP]


@[simp] theorem pc2903 : Artifact.submissionArtifact.instructionPC 64 = 0x88 := by rfl
@[simp] theorem pc2904 : Artifact.submissionArtifact.instructionPC 65 = 0x89 := by rfl
@[simp] theorem pc2905 : Artifact.submissionArtifact.instructionPC 69 = 0x8e := by rfl
@[simp] theorem pc2906 : Artifact.submissionArtifact.instructionPC 74 = 0xb4 := by rfl
@[simp] theorem pc2907 : Artifact.submissionArtifact.instructionPC 76 = 0xb6 := by rfl
@[simp] theorem pc2908 : Artifact.submissionArtifact.instructionPC 77 = 0xb7 := by rfl
@[simp] theorem pc2909 : Artifact.submissionArtifact.instructionPC 78 = 0xb8 := by rfl
@[simp] theorem pc2910 : Artifact.submissionArtifact.instructionPC 79 = 0xb9 := by rfl
@[simp] theorem pc2911 : Artifact.submissionArtifact.instructionPC 80 = 0xba := by rfl
@[simp] theorem pc2912 : Artifact.submissionArtifact.instructionPC 81 = 0xbb := by rfl
@[simp] theorem pc2913 : Artifact.submissionArtifact.instructionPC 82 = 0xbc := by rfl
@[simp] theorem pc2914 : Artifact.submissionArtifact.instructionPC 83 = 0xbd := by rfl
@[simp] theorem pc2915 : Artifact.submissionArtifact.instructionPC 84 = 0xbe := by rfl
@[simp] theorem pc2916 : Artifact.submissionArtifact.instructionPC 85 = 0xbf := by rfl
@[simp] theorem pc2917 : Artifact.submissionArtifact.instructionPC 86 = 0xc0 := by rfl
@[simp] theorem pc2918 : Artifact.submissionArtifact.instructionPC 87 = 0xc1 := by rfl
@[simp] theorem pc2919 : Artifact.submissionArtifact.instructionPC 88 = 0xc2 := by rfl
@[simp] theorem pc2920 : Artifact.submissionArtifact.instructionPC 89 = 0xc3 := by rfl
@[simp] theorem pc2921 : Artifact.submissionArtifact.instructionPC 90 = 0xc4 := by rfl
@[simp] theorem pc2922 : Artifact.submissionArtifact.instructionPC 91 = 0xc5 := by rfl
@[simp] theorem pc2923 : Artifact.submissionArtifact.instructionPC 92 = 0xc6 := by rfl
@[simp] theorem pc2924 : Artifact.submissionArtifact.instructionPC 93 = 0xc7 := by rfl
@[simp] theorem pc2925 : Artifact.submissionArtifact.instructionPC 94 = 0xc8 := by rfl
@[simp] theorem pc2926 : Artifact.submissionArtifact.instructionPC 95 = 0xc9 := by rfl
@[simp] theorem pc2927 : Artifact.submissionArtifact.instructionPC 96 = 0xca := by rfl
@[simp] theorem pc2928 : Artifact.submissionArtifact.instructionPC 97 = 0xcb := by rfl
@[simp] theorem pc2929 : Artifact.submissionArtifact.instructionPC 98 = 0xcc := by rfl
@[simp] theorem pc2930 : Artifact.submissionArtifact.instructionPC 99 = 0xcd := by rfl
@[simp] theorem pc2931 : Artifact.submissionArtifact.instructionPC 100 = 0xcf := by rfl
@[simp] theorem pc2932 : Artifact.submissionArtifact.instructionPC 101 = 0xd0 := by rfl
@[simp] theorem pc2933 : Artifact.submissionArtifact.instructionPC 102 = 0xd2 := by rfl
@[simp] theorem pc2934 : Artifact.submissionArtifact.instructionPC 103 = 0xd3 := by rfl
@[simp] theorem pc2935 : Artifact.submissionArtifact.instructionPC 104 = 0xd6 := by rfl
@[simp] theorem pc2936 : Artifact.submissionArtifact.instructionPC 105 = 0xd7 := by rfl
@[simp] theorem pc2937 : Artifact.submissionArtifact.instructionPC 106 = 0xd8 := by rfl
@[simp] theorem pc2938 : Artifact.submissionArtifact.instructionPC 107 = 0xd9 := by rfl
@[simp] theorem pc2939 : Artifact.submissionArtifact.instructionPC 108 = 0xda := by rfl
@[simp] theorem pc2940 : Artifact.submissionArtifact.instructionPC 109 = 0xdb := by rfl
@[simp] theorem pc2941 : Artifact.submissionArtifact.instructionPC 110 = 0xdc := by rfl
@[simp] theorem pc2942 : Artifact.submissionArtifact.instructionPC 111 = 0xdd := by rfl
@[simp] theorem pc2943 : Artifact.submissionArtifact.instructionPC 112 = 0xde := by rfl
@[simp] theorem pc2944 : Artifact.submissionArtifact.instructionPC 113 = 0xdf := by rfl
@[simp] theorem pc2946 : Artifact.submissionArtifact.instructionPC 114 = 0xe0 := by rfl
@[simp] theorem pc2947 : Artifact.submissionArtifact.instructionPC 115 = 0xe2 := by rfl
@[simp] theorem pc2948 : Artifact.submissionArtifact.instructionPC 116 = 0xe3 := by rfl
@[simp] theorem pc2949 : Artifact.submissionArtifact.instructionPC 117 = 0xe5 := by rfl
@[simp] theorem pc2952 : Artifact.submissionArtifact.instructionPC 118 = 0xe6 := by rfl
@[simp] theorem pc2953 : Artifact.submissionArtifact.instructionPC 119 = 0xe7 := by rfl
@[simp] theorem pc2954 : Artifact.submissionArtifact.instructionPC 120 = 0xe9 := by rfl
@[simp] theorem pc2955 : Artifact.submissionArtifact.instructionPC 121 = 0xea := by rfl
@[simp] theorem pc2956 : Artifact.submissionArtifact.instructionPC 122 = 0xeb := by rfl
@[simp] theorem pc2957 : Artifact.submissionArtifact.instructionPC 128 = 0xf3 := by rfl
@[simp] theorem pc2958 : Artifact.submissionArtifact.instructionPC 129 = 0xf4 := by rfl
@[simp] theorem pc2959 : Artifact.submissionArtifact.instructionPC 130 = 0xf7 := by rfl
@[simp] theorem pc2960 : Artifact.submissionArtifact.instructionPC 131 = 0xf8 := by rfl
@[simp] theorem pc2961 : Artifact.submissionArtifact.instructionPC 132 = 0xfa := by rfl
@[simp] theorem pc2962 : Artifact.submissionArtifact.instructionPC 133 = 0xfb := by rfl
@[simp] theorem pc2963 : Artifact.submissionArtifact.instructionPC 134 = 0xfe := by rfl
@[simp] theorem pc2964 : Artifact.submissionArtifact.instructionPC 135 = 0xff := by rfl
@[simp] theorem pc2965 : Artifact.submissionArtifact.instructionPC 136 = 0x108 := by rfl
@[simp] theorem pc2966 : Artifact.submissionArtifact.instructionPC 137 = 0x10a := by rfl
@[simp] theorem pc2967 : Artifact.submissionArtifact.instructionPC 138 = 0x10b := by rfl
@[simp] theorem pc2968 : Artifact.submissionArtifact.instructionPC 139 = 0x10c := by rfl
@[simp] theorem pc2969 : Artifact.submissionArtifact.instructionPC 140 = 0x10d := by rfl
@[simp] theorem pc2970 : Artifact.submissionArtifact.instructionPC 141 = 0x10e := by rfl
@[simp] theorem pc2971 : Artifact.submissionArtifact.instructionPC 142 = 0x10f := by rfl
@[simp] theorem pc2972 : Artifact.submissionArtifact.instructionPC 143 = 0x110 := by rfl
@[simp] theorem pc2973 : Artifact.submissionArtifact.instructionPC 144 = 0x111 := by rfl
@[simp] theorem pc2974 : Artifact.submissionArtifact.instructionPC 145 = 0x112 := by rfl
@[simp] theorem pc2975 : Artifact.submissionArtifact.instructionPC 146 = 0x113 := by rfl
@[simp] theorem pc2976 : Artifact.submissionArtifact.instructionPC 147 = 0x114 := by rfl
@[simp] theorem pc2977 : Artifact.submissionArtifact.instructionPC 148 = 0x115 := by rfl
@[simp] theorem pc2978 : Artifact.submissionArtifact.instructionPC 149 = 0x116 := by rfl
@[simp] theorem pc2979 : Artifact.submissionArtifact.instructionPC 150 = 0x117 := by rfl
@[simp] theorem pc2980 : Artifact.submissionArtifact.instructionPC 151 = 0x118 := by rfl
@[simp] theorem pc2981 : Artifact.submissionArtifact.instructionPC 152 = 0x119 := by rfl
@[simp] theorem pc2982 : Artifact.submissionArtifact.instructionPC 153 = 0x11c := by rfl
@[simp] theorem pc2983 : Artifact.submissionArtifact.instructionPC 154 = 0x11d := by rfl
@[simp] theorem pc2984 : Artifact.submissionArtifact.instructionPC 155 = 0x132 := by rfl
@[simp] theorem pc2985 : Artifact.submissionArtifact.instructionPC 156 = 0x133 := by rfl
@[simp] theorem pc2986 : Artifact.submissionArtifact.instructionPC 157 = 0x134 := by rfl
@[simp] theorem pc2987 : Artifact.submissionArtifact.instructionPC 158 = 0x136 := by rfl
@[simp] theorem pc2988 : Artifact.submissionArtifact.instructionPC 159 = 0x137 := by rfl
@[simp] theorem pc2989 : Artifact.submissionArtifact.instructionPC 160 = 0x138 := by rfl
@[simp] theorem pc2990 : Artifact.submissionArtifact.instructionPC 161 = 0x139 := by rfl
@[simp] theorem pc2991 : Artifact.submissionArtifact.instructionPC 162 = 0x13a := by rfl
@[simp] theorem pc2992 : Artifact.submissionArtifact.instructionPC 163 = 0x13b := by rfl
@[simp] theorem pc2993 : Artifact.submissionArtifact.instructionPC 164 = 0x13d := by rfl
@[simp] theorem pc2994 : Artifact.submissionArtifact.instructionPC 165 = 0x13e := by rfl
@[simp] theorem pc2995 : Artifact.submissionArtifact.instructionPC 166 = 0x140 := by rfl
@[simp] theorem pc2996 : Artifact.submissionArtifact.instructionPC 167 = 0x141 := by rfl
@[simp] theorem pc2997 : Artifact.submissionArtifact.instructionPC 168 = 0x143 := by rfl
@[simp] theorem pc2998 : Artifact.submissionArtifact.instructionPC 169 = 0x144 := by rfl
@[simp] theorem pc2999 : Artifact.submissionArtifact.instructionPC 170 = 0x146 := by rfl
@[simp] theorem pc3000 : Artifact.submissionArtifact.instructionPC 171 = 0x147 := by rfl
@[simp] theorem pc3001 : Artifact.submissionArtifact.instructionPC 172 = 0x148 := by rfl
@[simp] theorem pc3002 : Artifact.submissionArtifact.instructionPC 173 = 0x14a := by rfl
@[simp] theorem pc3003 : Artifact.submissionArtifact.instructionPC 174 = 0x14b := by rfl
@[simp] theorem pc3004 : Artifact.submissionArtifact.instructionPC 175 = 0x14c := by rfl
@[simp] theorem pc3005 : Artifact.submissionArtifact.instructionPC 176 = 0x14d := by rfl
@[simp] theorem pc3006 : Artifact.submissionArtifact.instructionPC 177 = 0x14e := by rfl
@[simp] theorem pc3007 : Artifact.submissionArtifact.instructionPC 178 = 0x14f := by rfl
@[simp] theorem pc3008 : Artifact.submissionArtifact.instructionPC 179 = 0x150 := by rfl
@[simp] theorem pc3009 : Artifact.submissionArtifact.instructionPC 180 = 0x151 := by rfl
@[simp] theorem pc3010 : Artifact.submissionArtifact.instructionPC 181 = 0x152 := by rfl
@[simp] theorem pc3011 : Artifact.submissionArtifact.instructionPC 182 = 0x153 := by rfl
@[simp] theorem pc3012 : Artifact.submissionArtifact.instructionPC 183 = 0x154 := by rfl
@[simp] theorem pc3013 : Artifact.submissionArtifact.instructionPC 184 = 0x155 := by rfl
@[simp] theorem pc3014 : Artifact.submissionArtifact.instructionPC 185 = 0x156 := by rfl
@[simp] theorem pc3015 : Artifact.submissionArtifact.instructionPC 186 = 0x157 := by rfl
@[simp] theorem pc3016 : Artifact.submissionArtifact.instructionPC 187 = 0x158 := by rfl
@[simp] theorem pc3017 : Artifact.submissionArtifact.instructionPC 188 = 0x15a := by rfl
@[simp] theorem pc3018 : Artifact.submissionArtifact.instructionPC 189 = 0x15b := by rfl
@[simp] theorem pc3019 : Artifact.submissionArtifact.instructionPC 190 = 0x15c := by rfl
@[simp] theorem pc3020 : Artifact.submissionArtifact.instructionPC 191 = 0x15d := by rfl
@[simp] theorem pc3021 : Artifact.submissionArtifact.instructionPC 192 = 0x15f := by rfl
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan
