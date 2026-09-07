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
  [opAt 51 .JUMPDEST,
   pushAt 52 1 255,
   pushAt 53 0 0,
   opAt 54 .NOT,
   opAt 55 .DIV,
   pushAt 56 32 3244493450063667868678674439968361782956185527883176199882357678282131398018,
   opAt 57 (.Dup ⟨1, by decide⟩),
   pushAt 58 1 7,
   opAt 59 .SHL,
   opAt 60 (.Dup ⟨0, by decide⟩),
   opAt 61 .NOT,
   opAt 62 (.Swap ⟨0, by decide⟩),
   opAt 63 (.Swap ⟨2, by decide⟩),
   opAt 64 (.Dup ⟨2, by decide⟩),
   opAt 65 (.Dup ⟨2, by decide⟩),
   opAt 66 .AND,
   pushAt 67 0 0,
   pushAt 68 0 0,
   pushAt 69 0 0]

/-- Derive the expected word and test for a straddler. -/
def wordPath : List Located :=
  [opAt 70 .JUMPDEST, opAt 71 (.Dup ⟨0, by decide⟩),
   opAt 72 (.Dup ⟨5, by decide⟩), opAt 73 .MUL,
   opAt 74 (.Dup ⟨0, by decide⟩), opAt 75 (.Dup ⟨7, by decide⟩),
   opAt 76 .AND, opAt 77 (.Dup ⟨5, by decide⟩), opAt 78 .ADD,
   opAt 79 (.Dup ⟨1, by decide⟩), opAt 80 (.Dup ⟨9, by decide⟩),
   opAt 81 .XOR, opAt 82 (.Dup ⟨10, by decide⟩), opAt 83 .AND,
   opAt 84 .XOR, opAt 85 (.Dup ⟨3, by decide⟩), pushAt 86 1 255,
   opAt 87 .AND, pushAt 88 1 224, opAt 89 .EQ, pushAt 90 2 290,
   opAt 91 .JUMPI]

/-- Fold one word into the accumulator and advance. -/
def comparePath : List Located :=
  [opAt 92 .JUMPDEST, opAt 93 (.Dup ⟨3, by decide⟩),
   opAt 94 .CALLDATALOAD, opAt 95 .XOR, opAt 96 (.Dup ⟨4, by decide⟩),
   opAt 97 .OR, opAt 98 (.Swap ⟨3, by decide⟩), opAt 99 .POP,
   opAt 100 .POP, opAt 101 .JUMPDEST, pushAt 102 1 160,
   opAt 103 .ADD, pushAt 104 1 255, opAt 105 .AND,
   opAt 106 .JUMPDEST, opAt 107 .JUMPDEST,
   opAt 108 (.Swap ⟨0, by decide⟩), pushAt 109 1 32, opAt 110 .ADD,
   opAt 111 (.Swap ⟨0, by decide⟩), opAt 112 .JUMPDEST,
   opAt 113 (.Dup ⟨1, by decide⟩), pushAt 114 2 992, opAt 115 .GT,
   pushAt 116 1 171, opAt 117 .JUMPI]

/-- The padded tail word, the cleanup and the miss test. -/
def tailPath : List Located :=
  [pushAt 118 2 992, opAt 119 .CALLDATALOAD,
   pushAt 120 8 9848759918901945995, pushAt 121 1 192, opAt 122 .SHL,
   opAt 123 .XOR, opAt 124 (.Dup ⟨3, by decide⟩), opAt 125 .OR,
   opAt 126 (.Swap ⟨2, by decide⟩), opAt 127 .POP,
   opAt 128 (.Swap ⟨1, by decide⟩), opAt 129 (.Swap ⟨6, by decide⟩),
   opAt 130 .POP, opAt 131 .POP, opAt 132 .POP, opAt 133 .POP,
   opAt 134 .POP, opAt 135 .POP, opAt 136 .POP, pushAt 137 2 330,
   opAt 138 .JUMPI]

/-- Store and return the stored digest. -/
def returnPath : List Located :=
  [pushAt 139 20 766350606435067737561421097975693824639675460820,
   pushAt 140 0 0, opAt 141 .MSTORE, pushAt 142 1 32, pushAt 143 0 0,
   opAt 144 .RETURN]

/-- Shift the correction constant out of `M`. -/
def straddleCorrPath : List Located :=
  [opAt 145 .JUMPDEST, opAt 146 (.Dup ⟨6, by decide⟩),
   opAt 147 (.Dup ⟨4, by decide⟩), pushAt 148 1 8, opAt 149 .SHR,
   pushAt 150 1 5, opAt 151 .MUL, pushAt 152 1 27, opAt 153 .SUB,
   pushAt 154 1 8, opAt 155 .MUL, opAt 156 .SHR, pushAt 157 1 11,
   opAt 158 .MUL]

/-- Apply the correction to the expected word. -/
def straddleAddPath : List Located :=
  [opAt 159 (.Dup ⟨1, by decide⟩), opAt 160 (.Dup ⟨9, by decide⟩),
   opAt 161 .AND, opAt 162 (.Dup ⟨1, by decide⟩), opAt 163 .ADD,
   opAt 164 (.Dup ⟨2, by decide⟩), opAt 165 (.Dup ⟨12, by decide⟩),
   opAt 166 .AND, opAt 167 .XOR, opAt 168 (.Swap ⟨1, by decide⟩),
   opAt 169 .POP, opAt 170 .POP]

/-- Bump the scalar and rejoin the scan. -/
def straddleBackPath : List Located :=
  [opAt 171 (.Dup ⟨2, by decide⟩), pushAt 172 1 11, opAt 173 .ADD,
   opAt 174 (.Swap ⟨2, by decide⟩), opAt 175 .POP, pushAt 176 1 197,
   opAt 177 .JUMP]


@[simp] theorem pc2903 : Artifact.submissionArtifact.instructionPC 51 = 0x76 := by rfl
@[simp] theorem pc2904 : Artifact.submissionArtifact.instructionPC 52 = 0x77 := by rfl
@[simp] theorem pc2905 : Artifact.submissionArtifact.instructionPC 56 = 0x7c := by rfl
@[simp] theorem pc2906 : Artifact.submissionArtifact.instructionPC 61 = 0xa2 := by rfl
@[simp] theorem pc2907 : Artifact.submissionArtifact.instructionPC 63 = 0xa4 := by rfl
@[simp] theorem pc2908 : Artifact.submissionArtifact.instructionPC 64 = 0xa5 := by rfl
@[simp] theorem pc2909 : Artifact.submissionArtifact.instructionPC 65 = 0xa6 := by rfl
@[simp] theorem pc2910 : Artifact.submissionArtifact.instructionPC 66 = 0xa7 := by rfl
@[simp] theorem pc2911 : Artifact.submissionArtifact.instructionPC 67 = 0xa8 := by rfl
@[simp] theorem pc2912 : Artifact.submissionArtifact.instructionPC 68 = 0xa9 := by rfl
@[simp] theorem pc2913 : Artifact.submissionArtifact.instructionPC 69 = 0xaa := by rfl
@[simp] theorem pc2914 : Artifact.submissionArtifact.instructionPC 70 = 0xab := by rfl
@[simp] theorem pc2915 : Artifact.submissionArtifact.instructionPC 71 = 0xac := by rfl
@[simp] theorem pc2916 : Artifact.submissionArtifact.instructionPC 72 = 0xad := by rfl
@[simp] theorem pc2917 : Artifact.submissionArtifact.instructionPC 73 = 0xae := by rfl
@[simp] theorem pc2918 : Artifact.submissionArtifact.instructionPC 74 = 0xaf := by rfl
@[simp] theorem pc2919 : Artifact.submissionArtifact.instructionPC 75 = 0xb0 := by rfl
@[simp] theorem pc2920 : Artifact.submissionArtifact.instructionPC 76 = 0xb1 := by rfl
@[simp] theorem pc2921 : Artifact.submissionArtifact.instructionPC 77 = 0xb2 := by rfl
@[simp] theorem pc2922 : Artifact.submissionArtifact.instructionPC 78 = 0xb3 := by rfl
@[simp] theorem pc2923 : Artifact.submissionArtifact.instructionPC 79 = 0xb4 := by rfl
@[simp] theorem pc2924 : Artifact.submissionArtifact.instructionPC 80 = 0xb5 := by rfl
@[simp] theorem pc2925 : Artifact.submissionArtifact.instructionPC 81 = 0xb6 := by rfl
@[simp] theorem pc2926 : Artifact.submissionArtifact.instructionPC 82 = 0xb7 := by rfl
@[simp] theorem pc2927 : Artifact.submissionArtifact.instructionPC 83 = 0xb8 := by rfl
@[simp] theorem pc2928 : Artifact.submissionArtifact.instructionPC 84 = 0xb9 := by rfl
@[simp] theorem pc2929 : Artifact.submissionArtifact.instructionPC 85 = 0xba := by rfl
@[simp] theorem pc2930 : Artifact.submissionArtifact.instructionPC 86 = 0xbb := by rfl
@[simp] theorem pc2931 : Artifact.submissionArtifact.instructionPC 87 = 0xbd := by rfl
@[simp] theorem pc2932 : Artifact.submissionArtifact.instructionPC 88 = 0xbe := by rfl
@[simp] theorem pc2933 : Artifact.submissionArtifact.instructionPC 89 = 0xc0 := by rfl
@[simp] theorem pc2934 : Artifact.submissionArtifact.instructionPC 90 = 0xc1 := by rfl
@[simp] theorem pc2935 : Artifact.submissionArtifact.instructionPC 91 = 0xc4 := by rfl
@[simp] theorem pc2936 : Artifact.submissionArtifact.instructionPC 92 = 0xc5 := by rfl
@[simp] theorem pc2937 : Artifact.submissionArtifact.instructionPC 93 = 0xc6 := by rfl
@[simp] theorem pc2938 : Artifact.submissionArtifact.instructionPC 94 = 0xc7 := by rfl
@[simp] theorem pc2939 : Artifact.submissionArtifact.instructionPC 95 = 0xc8 := by rfl
@[simp] theorem pc2940 : Artifact.submissionArtifact.instructionPC 96 = 0xc9 := by rfl
@[simp] theorem pc2941 : Artifact.submissionArtifact.instructionPC 97 = 0xca := by rfl
@[simp] theorem pc2942 : Artifact.submissionArtifact.instructionPC 98 = 0xcb := by rfl
@[simp] theorem pc2943 : Artifact.submissionArtifact.instructionPC 99 = 0xcc := by rfl
@[simp] theorem pc2944 : Artifact.submissionArtifact.instructionPC 100 = 0xcd := by rfl
@[simp] theorem pc2945 : Artifact.submissionArtifact.instructionPC 101 = 0xce := by rfl
@[simp] theorem pc2946 : Artifact.submissionArtifact.instructionPC 102 = 0xcf := by rfl
@[simp] theorem pc2947 : Artifact.submissionArtifact.instructionPC 103 = 0xd1 := by rfl
@[simp] theorem pc2948 : Artifact.submissionArtifact.instructionPC 104 = 0xd2 := by rfl
@[simp] theorem pc2949 : Artifact.submissionArtifact.instructionPC 105 = 0xd4 := by rfl
@[simp] theorem pc2950 : Artifact.submissionArtifact.instructionPC 106 = 0xd5 := by rfl
@[simp] theorem pc2951 : Artifact.submissionArtifact.instructionPC 107 = 0xd6 := by rfl
@[simp] theorem pc2952 : Artifact.submissionArtifact.instructionPC 108 = 0xd7 := by rfl
@[simp] theorem pc2953 : Artifact.submissionArtifact.instructionPC 109 = 0xd8 := by rfl
@[simp] theorem pc2954 : Artifact.submissionArtifact.instructionPC 110 = 0xda := by rfl
@[simp] theorem pc2955 : Artifact.submissionArtifact.instructionPC 111 = 0xdb := by rfl
@[simp] theorem pc2956 : Artifact.submissionArtifact.instructionPC 112 = 0xdc := by rfl
@[simp] theorem pc2957 : Artifact.submissionArtifact.instructionPC 113 = 0xdd := by rfl
@[simp] theorem pc2958 : Artifact.submissionArtifact.instructionPC 114 = 0xde := by rfl
@[simp] theorem pc2959 : Artifact.submissionArtifact.instructionPC 115 = 0xe1 := by rfl
@[simp] theorem pc2960 : Artifact.submissionArtifact.instructionPC 116 = 0xe2 := by rfl
@[simp] theorem pc2961 : Artifact.submissionArtifact.instructionPC 117 = 0xe4 := by rfl
@[simp] theorem pc2962 : Artifact.submissionArtifact.instructionPC 118 = 0xe5 := by rfl
@[simp] theorem pc2963 : Artifact.submissionArtifact.instructionPC 119 = 0xe8 := by rfl
@[simp] theorem pc2964 : Artifact.submissionArtifact.instructionPC 120 = 0xe9 := by rfl
@[simp] theorem pc2965 : Artifact.submissionArtifact.instructionPC 121 = 0xf2 := by rfl
@[simp] theorem pc2966 : Artifact.submissionArtifact.instructionPC 122 = 0xf4 := by rfl
@[simp] theorem pc2967 : Artifact.submissionArtifact.instructionPC 123 = 0xf5 := by rfl
@[simp] theorem pc2968 : Artifact.submissionArtifact.instructionPC 124 = 0xf6 := by rfl
@[simp] theorem pc2969 : Artifact.submissionArtifact.instructionPC 125 = 0xf7 := by rfl
@[simp] theorem pc2970 : Artifact.submissionArtifact.instructionPC 126 = 0xf8 := by rfl
@[simp] theorem pc2971 : Artifact.submissionArtifact.instructionPC 127 = 0xf9 := by rfl
@[simp] theorem pc2972 : Artifact.submissionArtifact.instructionPC 128 = 0xfa := by rfl
@[simp] theorem pc2973 : Artifact.submissionArtifact.instructionPC 129 = 0xfb := by rfl
@[simp] theorem pc2974 : Artifact.submissionArtifact.instructionPC 130 = 0xfc := by rfl
@[simp] theorem pc2975 : Artifact.submissionArtifact.instructionPC 131 = 0xfd := by rfl
@[simp] theorem pc2976 : Artifact.submissionArtifact.instructionPC 132 = 0xfe := by rfl
@[simp] theorem pc2977 : Artifact.submissionArtifact.instructionPC 133 = 0xff := by rfl
@[simp] theorem pc2978 : Artifact.submissionArtifact.instructionPC 134 = 0x100 := by rfl
@[simp] theorem pc2979 : Artifact.submissionArtifact.instructionPC 135 = 0x101 := by rfl
@[simp] theorem pc2980 : Artifact.submissionArtifact.instructionPC 136 = 0x102 := by rfl
@[simp] theorem pc2981 : Artifact.submissionArtifact.instructionPC 137 = 0x103 := by rfl
@[simp] theorem pc2982 : Artifact.submissionArtifact.instructionPC 138 = 0x106 := by rfl
@[simp] theorem pc2983 : Artifact.submissionArtifact.instructionPC 139 = 0x107 := by rfl
@[simp] theorem pc2984 : Artifact.submissionArtifact.instructionPC 140 = 0x11c := by rfl
@[simp] theorem pc2985 : Artifact.submissionArtifact.instructionPC 141 = 0x11d := by rfl
@[simp] theorem pc2986 : Artifact.submissionArtifact.instructionPC 142 = 0x11e := by rfl
@[simp] theorem pc2987 : Artifact.submissionArtifact.instructionPC 143 = 0x120 := by rfl
@[simp] theorem pc2988 : Artifact.submissionArtifact.instructionPC 144 = 0x121 := by rfl
@[simp] theorem pc2989 : Artifact.submissionArtifact.instructionPC 145 = 0x122 := by rfl
@[simp] theorem pc2990 : Artifact.submissionArtifact.instructionPC 146 = 0x123 := by rfl
@[simp] theorem pc2991 : Artifact.submissionArtifact.instructionPC 147 = 0x124 := by rfl
@[simp] theorem pc2992 : Artifact.submissionArtifact.instructionPC 148 = 0x125 := by rfl
@[simp] theorem pc2993 : Artifact.submissionArtifact.instructionPC 149 = 0x127 := by rfl
@[simp] theorem pc2994 : Artifact.submissionArtifact.instructionPC 150 = 0x128 := by rfl
@[simp] theorem pc2995 : Artifact.submissionArtifact.instructionPC 151 = 0x12a := by rfl
@[simp] theorem pc2996 : Artifact.submissionArtifact.instructionPC 152 = 0x12b := by rfl
@[simp] theorem pc2997 : Artifact.submissionArtifact.instructionPC 153 = 0x12d := by rfl
@[simp] theorem pc2998 : Artifact.submissionArtifact.instructionPC 154 = 0x12e := by rfl
@[simp] theorem pc2999 : Artifact.submissionArtifact.instructionPC 155 = 0x130 := by rfl
@[simp] theorem pc3000 : Artifact.submissionArtifact.instructionPC 156 = 0x131 := by rfl
@[simp] theorem pc3001 : Artifact.submissionArtifact.instructionPC 157 = 0x132 := by rfl
@[simp] theorem pc3002 : Artifact.submissionArtifact.instructionPC 158 = 0x134 := by rfl
@[simp] theorem pc3003 : Artifact.submissionArtifact.instructionPC 159 = 0x135 := by rfl
@[simp] theorem pc3004 : Artifact.submissionArtifact.instructionPC 160 = 0x136 := by rfl
@[simp] theorem pc3005 : Artifact.submissionArtifact.instructionPC 161 = 0x137 := by rfl
@[simp] theorem pc3006 : Artifact.submissionArtifact.instructionPC 162 = 0x138 := by rfl
@[simp] theorem pc3007 : Artifact.submissionArtifact.instructionPC 163 = 0x139 := by rfl
@[simp] theorem pc3008 : Artifact.submissionArtifact.instructionPC 164 = 0x13a := by rfl
@[simp] theorem pc3009 : Artifact.submissionArtifact.instructionPC 165 = 0x13b := by rfl
@[simp] theorem pc3010 : Artifact.submissionArtifact.instructionPC 166 = 0x13c := by rfl
@[simp] theorem pc3011 : Artifact.submissionArtifact.instructionPC 167 = 0x13d := by rfl
@[simp] theorem pc3012 : Artifact.submissionArtifact.instructionPC 168 = 0x13e := by rfl
@[simp] theorem pc3013 : Artifact.submissionArtifact.instructionPC 169 = 0x13f := by rfl
@[simp] theorem pc3014 : Artifact.submissionArtifact.instructionPC 170 = 0x140 := by rfl
@[simp] theorem pc3015 : Artifact.submissionArtifact.instructionPC 171 = 0x141 := by rfl
@[simp] theorem pc3016 : Artifact.submissionArtifact.instructionPC 172 = 0x142 := by rfl
@[simp] theorem pc3017 : Artifact.submissionArtifact.instructionPC 173 = 0x144 := by rfl
@[simp] theorem pc3018 : Artifact.submissionArtifact.instructionPC 174 = 0x145 := by rfl
@[simp] theorem pc3019 : Artifact.submissionArtifact.instructionPC 175 = 0x146 := by rfl
@[simp] theorem pc3020 : Artifact.submissionArtifact.instructionPC 176 = 0x147 := by rfl
@[simp] theorem pc3021 : Artifact.submissionArtifact.instructionPC 177 = 0x149 := by rfl
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan
