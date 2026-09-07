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
  [pushAt 47 1 255,
   pushAt 48 0 0,
   opAt 49 .NOT,
   opAt 50 .DIV,
   pushAt 51 32 3244493450063667868678674439968361782956185527883176199882357678282131398018,
   opAt 52 (.Dup ⟨1, by decide⟩),
   pushAt 53 1 7,
   opAt 54 .SHL,
   opAt 55 (.Dup ⟨0, by decide⟩),
   opAt 56 .NOT,
   opAt 57 (.Swap ⟨0, by decide⟩),
   opAt 58 (.Swap ⟨2, by decide⟩),
   opAt 59 (.Dup ⟨2, by decide⟩),
   opAt 60 (.Dup ⟨2, by decide⟩),
   opAt 61 .AND,
   pushAt 62 0 0,
   pushAt 63 0 0,
   pushAt 64 0 0]

/-- Derive the expected word and test for a straddler. -/
def wordPath : List Located :=
  [opAt 65 .JUMPDEST, opAt 66 (.Dup ⟨0, by decide⟩),
   opAt 67 (.Dup ⟨5, by decide⟩), opAt 68 .MUL,
   opAt 69 (.Dup ⟨0, by decide⟩), opAt 70 (.Dup ⟨7, by decide⟩),
   opAt 71 .AND, opAt 72 (.Dup ⟨5, by decide⟩), opAt 73 .ADD,
   opAt 74 (.Dup ⟨1, by decide⟩), opAt 75 (.Dup ⟨9, by decide⟩),
   opAt 76 .XOR, opAt 77 (.Dup ⟨10, by decide⟩), opAt 78 .AND,
   opAt 79 .XOR, opAt 80 (.Dup ⟨3, by decide⟩), pushAt 81 1 255,
   opAt 82 .AND, pushAt 83 1 224, opAt 84 .EQ, pushAt 85 2 280,
   opAt 86 .JUMPI]

/-- Fold one word into the accumulator and advance. -/
def comparePath : List Located :=
  [opAt 87 .JUMPDEST, opAt 88 (.Dup ⟨3, by decide⟩),
   opAt 89 .CALLDATALOAD, opAt 90 .XOR, opAt 91 (.Dup ⟨4, by decide⟩),
   opAt 92 .OR, opAt 93 (.Swap ⟨3, by decide⟩), opAt 94 .POP,
   opAt 95 .POP, pushAt 96 1 160,
   opAt 97 .ADD, pushAt 98 1 255, opAt 99 .AND,
   opAt 100 (.Swap ⟨0, by decide⟩), pushAt 101 1 32, opAt 102 .ADD,
   opAt 103 (.Swap ⟨0, by decide⟩), opAt 104 (.Dup ⟨1, by decide⟩), pushAt 105 2 992, opAt 106 .GT,
   pushAt 107 1 165, opAt 108 .JUMPI]

/-- The padded tail word, the cleanup and the miss test. -/
def tailPath : List Located :=
  [pushAt 109 2 992, opAt 110 .CALLDATALOAD,
   pushAt 111 8 9848759918901945995, pushAt 112 1 192, opAt 113 .SHL,
   opAt 114 .XOR, opAt 115 (.Dup ⟨3, by decide⟩), opAt 116 .OR,
   opAt 117 (.Swap ⟨2, by decide⟩), opAt 118 .POP,
   opAt 119 (.Swap ⟨1, by decide⟩), opAt 120 (.Swap ⟨6, by decide⟩),
   opAt 121 .POP, opAt 122 .POP, opAt 123 .POP, opAt 124 .POP,
   opAt 125 .POP, opAt 126 .POP, opAt 127 .POP, pushAt 128 2 320,
   opAt 129 .JUMPI]

/-- Store and return the stored digest. -/
def returnPath : List Located :=
  [pushAt 130 20 766350606435067737561421097975693824639675460820,
   pushAt 131 0 0, opAt 132 .MSTORE, pushAt 133 1 32, pushAt 134 0 0,
   opAt 135 .RETURN]

/-- Shift the correction constant out of `M`. -/
def straddleCorrPath : List Located :=
  [opAt 136 .JUMPDEST, opAt 137 (.Dup ⟨6, by decide⟩),
   opAt 138 (.Dup ⟨4, by decide⟩), pushAt 139 1 8, opAt 140 .SHR,
   pushAt 141 1 5, opAt 142 .MUL, pushAt 143 1 27, opAt 144 .SUB,
   pushAt 145 1 8, opAt 146 .MUL, opAt 147 .SHR, pushAt 148 1 11,
   opAt 149 .MUL]

/-- Apply the correction to the expected word. -/
def straddleAddPath : List Located :=
  [opAt 150 (.Dup ⟨1, by decide⟩), opAt 151 (.Dup ⟨9, by decide⟩),
   opAt 152 .AND, opAt 153 (.Dup ⟨1, by decide⟩), opAt 154 .ADD,
   opAt 155 (.Dup ⟨2, by decide⟩), opAt 156 (.Dup ⟨12, by decide⟩),
   opAt 157 .AND, opAt 158 .XOR, opAt 159 (.Swap ⟨1, by decide⟩),
   opAt 160 .POP, opAt 161 .POP]

/-- Bump the scalar and rejoin the scan. -/
def straddleBackPath : List Located :=
  [opAt 162 (.Dup ⟨2, by decide⟩), pushAt 163 1 11, opAt 164 .ADD,
   opAt 165 (.Swap ⟨2, by decide⟩), opAt 166 .POP, pushAt 167 1 191,
   opAt 168 .JUMP]


@[simp] theorem pc2903 : Artifact.submissionArtifact.instructionPC 47 = 0x71 := by rfl
@[simp] theorem pc2904 : Artifact.submissionArtifact.instructionPC 47 = 0x71 := by rfl
@[simp] theorem pc2905 : Artifact.submissionArtifact.instructionPC 51 = 0x76 := by rfl
@[simp] theorem pc2906 : Artifact.submissionArtifact.instructionPC 56 = 0x9c := by rfl
@[simp] theorem pc2907 : Artifact.submissionArtifact.instructionPC 58 = 0x9e := by rfl
@[simp] theorem pc2908 : Artifact.submissionArtifact.instructionPC 59 = 0x9f := by rfl
@[simp] theorem pc2909 : Artifact.submissionArtifact.instructionPC 60 = 0xa0 := by rfl
@[simp] theorem pc2910 : Artifact.submissionArtifact.instructionPC 61 = 0xa1 := by rfl
@[simp] theorem pc2911 : Artifact.submissionArtifact.instructionPC 62 = 0xa2 := by rfl
@[simp] theorem pc2912 : Artifact.submissionArtifact.instructionPC 63 = 0xa3 := by rfl
@[simp] theorem pc2913 : Artifact.submissionArtifact.instructionPC 64 = 0xa4 := by rfl
@[simp] theorem pc2914 : Artifact.submissionArtifact.instructionPC 65 = 0xa5 := by rfl
@[simp] theorem pc2915 : Artifact.submissionArtifact.instructionPC 66 = 0xa6 := by rfl
@[simp] theorem pc2916 : Artifact.submissionArtifact.instructionPC 67 = 0xa7 := by rfl
@[simp] theorem pc2917 : Artifact.submissionArtifact.instructionPC 68 = 0xa8 := by rfl
@[simp] theorem pc2918 : Artifact.submissionArtifact.instructionPC 69 = 0xa9 := by rfl
@[simp] theorem pc2919 : Artifact.submissionArtifact.instructionPC 70 = 0xaa := by rfl
@[simp] theorem pc2920 : Artifact.submissionArtifact.instructionPC 71 = 0xab := by rfl
@[simp] theorem pc2921 : Artifact.submissionArtifact.instructionPC 72 = 0xac := by rfl
@[simp] theorem pc2922 : Artifact.submissionArtifact.instructionPC 73 = 0xad := by rfl
@[simp] theorem pc2923 : Artifact.submissionArtifact.instructionPC 74 = 0xae := by rfl
@[simp] theorem pc2924 : Artifact.submissionArtifact.instructionPC 75 = 0xaf := by rfl
@[simp] theorem pc2925 : Artifact.submissionArtifact.instructionPC 76 = 0xb0 := by rfl
@[simp] theorem pc2926 : Artifact.submissionArtifact.instructionPC 77 = 0xb1 := by rfl
@[simp] theorem pc2927 : Artifact.submissionArtifact.instructionPC 78 = 0xb2 := by rfl
@[simp] theorem pc2928 : Artifact.submissionArtifact.instructionPC 79 = 0xb3 := by rfl
@[simp] theorem pc2929 : Artifact.submissionArtifact.instructionPC 80 = 0xb4 := by rfl
@[simp] theorem pc2930 : Artifact.submissionArtifact.instructionPC 81 = 0xb5 := by rfl
@[simp] theorem pc2931 : Artifact.submissionArtifact.instructionPC 82 = 0xb7 := by rfl
@[simp] theorem pc2932 : Artifact.submissionArtifact.instructionPC 83 = 0xb8 := by rfl
@[simp] theorem pc2933 : Artifact.submissionArtifact.instructionPC 84 = 0xba := by rfl
@[simp] theorem pc2934 : Artifact.submissionArtifact.instructionPC 85 = 0xbb := by rfl
@[simp] theorem pc2935 : Artifact.submissionArtifact.instructionPC 86 = 0xbe := by rfl
@[simp] theorem pc2936 : Artifact.submissionArtifact.instructionPC 87 = 0xbf := by rfl
@[simp] theorem pc2937 : Artifact.submissionArtifact.instructionPC 88 = 0xc0 := by rfl
@[simp] theorem pc2938 : Artifact.submissionArtifact.instructionPC 89 = 0xc1 := by rfl
@[simp] theorem pc2939 : Artifact.submissionArtifact.instructionPC 90 = 0xc2 := by rfl
@[simp] theorem pc2940 : Artifact.submissionArtifact.instructionPC 91 = 0xc3 := by rfl
@[simp] theorem pc2941 : Artifact.submissionArtifact.instructionPC 92 = 0xc4 := by rfl
@[simp] theorem pc2942 : Artifact.submissionArtifact.instructionPC 93 = 0xc5 := by rfl
@[simp] theorem pc2943 : Artifact.submissionArtifact.instructionPC 94 = 0xc6 := by rfl
@[simp] theorem pc2944 : Artifact.submissionArtifact.instructionPC 95 = 0xc7 := by rfl
@[simp] theorem pc2945 : Artifact.submissionArtifact.instructionPC 96 = 0xc8 := by rfl
@[simp] theorem pc2946 : Artifact.submissionArtifact.instructionPC 96 = 0xc8 := by rfl
@[simp] theorem pc2947 : Artifact.submissionArtifact.instructionPC 97 = 0xca := by rfl
@[simp] theorem pc2948 : Artifact.submissionArtifact.instructionPC 98 = 0xcb := by rfl
@[simp] theorem pc2949 : Artifact.submissionArtifact.instructionPC 99 = 0xcd := by rfl
@[simp] theorem pc2950 : Artifact.submissionArtifact.instructionPC 100 = 0xce := by rfl
@[simp] theorem pc2951 : Artifact.submissionArtifact.instructionPC 100 = 0xce := by rfl
@[simp] theorem pc2952 : Artifact.submissionArtifact.instructionPC 100 = 0xce := by rfl
@[simp] theorem pc2953 : Artifact.submissionArtifact.instructionPC 101 = 0xcf := by rfl
@[simp] theorem pc2954 : Artifact.submissionArtifact.instructionPC 102 = 0xd1 := by rfl
@[simp] theorem pc2955 : Artifact.submissionArtifact.instructionPC 103 = 0xd2 := by rfl
@[simp] theorem pc2956 : Artifact.submissionArtifact.instructionPC 104 = 0xd3 := by rfl
@[simp] theorem pc2957 : Artifact.submissionArtifact.instructionPC 104 = 0xd3 := by rfl
@[simp] theorem pc2958 : Artifact.submissionArtifact.instructionPC 105 = 0xd4 := by rfl
@[simp] theorem pc2959 : Artifact.submissionArtifact.instructionPC 106 = 0xd7 := by rfl
@[simp] theorem pc2960 : Artifact.submissionArtifact.instructionPC 107 = 0xd8 := by rfl
@[simp] theorem pc2961 : Artifact.submissionArtifact.instructionPC 108 = 0xda := by rfl
@[simp] theorem pc2962 : Artifact.submissionArtifact.instructionPC 109 = 0xdb := by rfl
@[simp] theorem pc2963 : Artifact.submissionArtifact.instructionPC 110 = 0xde := by rfl
@[simp] theorem pc2964 : Artifact.submissionArtifact.instructionPC 111 = 0xdf := by rfl
@[simp] theorem pc2965 : Artifact.submissionArtifact.instructionPC 112 = 0xe8 := by rfl
@[simp] theorem pc2966 : Artifact.submissionArtifact.instructionPC 113 = 0xea := by rfl
@[simp] theorem pc2967 : Artifact.submissionArtifact.instructionPC 114 = 0xeb := by rfl
@[simp] theorem pc2968 : Artifact.submissionArtifact.instructionPC 115 = 0xec := by rfl
@[simp] theorem pc2969 : Artifact.submissionArtifact.instructionPC 116 = 0xed := by rfl
@[simp] theorem pc2970 : Artifact.submissionArtifact.instructionPC 117 = 0xee := by rfl
@[simp] theorem pc2971 : Artifact.submissionArtifact.instructionPC 118 = 0xef := by rfl
@[simp] theorem pc2972 : Artifact.submissionArtifact.instructionPC 119 = 0xf0 := by rfl
@[simp] theorem pc2973 : Artifact.submissionArtifact.instructionPC 120 = 0xf1 := by rfl
@[simp] theorem pc2974 : Artifact.submissionArtifact.instructionPC 121 = 0xf2 := by rfl
@[simp] theorem pc2975 : Artifact.submissionArtifact.instructionPC 122 = 0xf3 := by rfl
@[simp] theorem pc2976 : Artifact.submissionArtifact.instructionPC 123 = 0xf4 := by rfl
@[simp] theorem pc2977 : Artifact.submissionArtifact.instructionPC 124 = 0xf5 := by rfl
@[simp] theorem pc2978 : Artifact.submissionArtifact.instructionPC 125 = 0xf6 := by rfl
@[simp] theorem pc2979 : Artifact.submissionArtifact.instructionPC 126 = 0xf7 := by rfl
@[simp] theorem pc2980 : Artifact.submissionArtifact.instructionPC 127 = 0xf8 := by rfl
@[simp] theorem pc2981 : Artifact.submissionArtifact.instructionPC 128 = 0xf9 := by rfl
@[simp] theorem pc2982 : Artifact.submissionArtifact.instructionPC 129 = 0xfc := by rfl
@[simp] theorem pc2983 : Artifact.submissionArtifact.instructionPC 130 = 0xfd := by rfl
@[simp] theorem pc2984 : Artifact.submissionArtifact.instructionPC 131 = 0x112 := by rfl
@[simp] theorem pc2985 : Artifact.submissionArtifact.instructionPC 132 = 0x113 := by rfl
@[simp] theorem pc2986 : Artifact.submissionArtifact.instructionPC 133 = 0x114 := by rfl
@[simp] theorem pc2987 : Artifact.submissionArtifact.instructionPC 134 = 0x116 := by rfl
@[simp] theorem pc2988 : Artifact.submissionArtifact.instructionPC 135 = 0x117 := by rfl
@[simp] theorem pc2989 : Artifact.submissionArtifact.instructionPC 136 = 0x118 := by rfl
@[simp] theorem pc2990 : Artifact.submissionArtifact.instructionPC 137 = 0x119 := by rfl
@[simp] theorem pc2991 : Artifact.submissionArtifact.instructionPC 138 = 0x11a := by rfl
@[simp] theorem pc2992 : Artifact.submissionArtifact.instructionPC 139 = 0x11b := by rfl
@[simp] theorem pc2993 : Artifact.submissionArtifact.instructionPC 140 = 0x11d := by rfl
@[simp] theorem pc2994 : Artifact.submissionArtifact.instructionPC 141 = 0x11e := by rfl
@[simp] theorem pc2995 : Artifact.submissionArtifact.instructionPC 142 = 0x120 := by rfl
@[simp] theorem pc2996 : Artifact.submissionArtifact.instructionPC 143 = 0x121 := by rfl
@[simp] theorem pc2997 : Artifact.submissionArtifact.instructionPC 144 = 0x123 := by rfl
@[simp] theorem pc2998 : Artifact.submissionArtifact.instructionPC 145 = 0x124 := by rfl
@[simp] theorem pc2999 : Artifact.submissionArtifact.instructionPC 146 = 0x126 := by rfl
@[simp] theorem pc3000 : Artifact.submissionArtifact.instructionPC 147 = 0x127 := by rfl
@[simp] theorem pc3001 : Artifact.submissionArtifact.instructionPC 148 = 0x128 := by rfl
@[simp] theorem pc3002 : Artifact.submissionArtifact.instructionPC 149 = 0x12a := by rfl
@[simp] theorem pc3003 : Artifact.submissionArtifact.instructionPC 150 = 0x12b := by rfl
@[simp] theorem pc3004 : Artifact.submissionArtifact.instructionPC 151 = 0x12c := by rfl
@[simp] theorem pc3005 : Artifact.submissionArtifact.instructionPC 152 = 0x12d := by rfl
@[simp] theorem pc3006 : Artifact.submissionArtifact.instructionPC 153 = 0x12e := by rfl
@[simp] theorem pc3007 : Artifact.submissionArtifact.instructionPC 154 = 0x12f := by rfl
@[simp] theorem pc3008 : Artifact.submissionArtifact.instructionPC 155 = 0x130 := by rfl
@[simp] theorem pc3009 : Artifact.submissionArtifact.instructionPC 156 = 0x131 := by rfl
@[simp] theorem pc3010 : Artifact.submissionArtifact.instructionPC 157 = 0x132 := by rfl
@[simp] theorem pc3011 : Artifact.submissionArtifact.instructionPC 158 = 0x133 := by rfl
@[simp] theorem pc3012 : Artifact.submissionArtifact.instructionPC 159 = 0x134 := by rfl
@[simp] theorem pc3013 : Artifact.submissionArtifact.instructionPC 160 = 0x135 := by rfl
@[simp] theorem pc3014 : Artifact.submissionArtifact.instructionPC 161 = 0x136 := by rfl
@[simp] theorem pc3015 : Artifact.submissionArtifact.instructionPC 162 = 0x137 := by rfl
@[simp] theorem pc3016 : Artifact.submissionArtifact.instructionPC 163 = 0x138 := by rfl
@[simp] theorem pc3017 : Artifact.submissionArtifact.instructionPC 164 = 0x13a := by rfl
@[simp] theorem pc3018 : Artifact.submissionArtifact.instructionPC 165 = 0x13b := by rfl
@[simp] theorem pc3019 : Artifact.submissionArtifact.instructionPC 166 = 0x13c := by rfl
@[simp] theorem pc3020 : Artifact.submissionArtifact.instructionPC 167 = 0x13d := by rfl
@[simp] theorem pc3021 : Artifact.submissionArtifact.instructionPC 168 = 0x13f := by rfl
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan
