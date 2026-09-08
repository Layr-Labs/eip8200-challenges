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
  [opAt 59 .JUMPDEST,
   pushAt 60 1 255,
   pushAt 61 0 0,
   opAt 62 .NOT,
   opAt 63 .DIV,
   pushAt 64 32 3244493450063667868678674439968361782956185527883176199882357678282131398018,
   opAt 65 (.Dup ⟨1, by decide⟩),
   pushAt 66 1 7,
   opAt 67 .SHL,
   opAt 68 (.Dup ⟨0, by decide⟩),
   opAt 69 .NOT,
   opAt 70 (.Swap ⟨0, by decide⟩),
   opAt 71 (.Swap ⟨2, by decide⟩),
   opAt 72 (.Dup ⟨2, by decide⟩),
   opAt 73 (.Dup ⟨2, by decide⟩),
   opAt 74 .AND,
   pushAt 75 0 0,
   pushAt 76 0 0,
   pushAt 77 0 0]

/-- Derive the expected word and test for a straddler. -/
def wordPath : List Located :=
  [opAt 78 .JUMPDEST, opAt 79 (.Dup ⟨0, by decide⟩),
   opAt 80 (.Dup ⟨5, by decide⟩), opAt 81 .MUL,
   opAt 82 (.Dup ⟨0, by decide⟩), opAt 83 (.Dup ⟨7, by decide⟩),
   opAt 84 .AND, opAt 85 (.Dup ⟨5, by decide⟩), opAt 86 .ADD,
   opAt 87 (.Dup ⟨1, by decide⟩), opAt 88 (.Dup ⟨9, by decide⟩),
   opAt 89 .XOR, opAt 90 (.Dup ⟨10, by decide⟩), opAt 91 .AND,
   opAt 92 .XOR, opAt 93 (.Dup ⟨3, by decide⟩), pushAt 94 1 255,
   opAt 95 .AND, pushAt 96 1 224, opAt 97 .EQ, pushAt 98 2 306,
   opAt 99 .JUMPI]

/-- Fold one word into the accumulator and advance. -/
def comparePath : List Located :=
  [opAt 100 .JUMPDEST, opAt 101 (.Dup ⟨3, by decide⟩),
   opAt 102 .CALLDATALOAD, opAt 103 .XOR, opAt 104 (.Dup ⟨4, by decide⟩),
   opAt 105 .OR, opAt 106 (.Swap ⟨3, by decide⟩), opAt 107 .POP,
   opAt 108 .POP, pushAt 109 1 160,
   opAt 110 .ADD, pushAt 111 1 255, opAt 112 .AND,
   opAt 113 (.Swap ⟨0, by decide⟩), pushAt 114 1 32, opAt 115 .ADD,
   opAt 116 (.Swap ⟨0, by decide⟩), opAt 117 .JUMPDEST,
   opAt 123 (.Dup ⟨1, by decide⟩), pushAt 124 2 992, opAt 125 .GT,
   pushAt 126 1 183, opAt 127 .JUMPI]

/-- The padded tail word, the cleanup and the miss test. -/
def tailPath : List Located :=
  [pushAt 128 2 992, opAt 129 .CALLDATALOAD,
   pushAt 130 8 9848759918901945995, pushAt 131 1 192, opAt 132 .SHL,
   opAt 133 .XOR, opAt 134 (.Dup ⟨3, by decide⟩), opAt 135 .OR,
   opAt 136 (.Swap ⟨2, by decide⟩), opAt 137 .POP,
   opAt 138 (.Swap ⟨1, by decide⟩), opAt 139 (.Swap ⟨6, by decide⟩),
   opAt 140 .POP, opAt 141 .POP, opAt 142 .POP, opAt 143 .POP,
   opAt 144 .POP, opAt 145 .POP, opAt 146 .POP, pushAt 147 2 346,
   opAt 148 .JUMPI]

/-- Store and return the stored digest. -/
def returnPath : List Located :=
  [pushAt 149 20 766350606435067737561421097975693824639675460820,
   pushAt 150 0 0, opAt 151 .MSTORE, pushAt 152 1 32, pushAt 153 0 0,
   opAt 154 .RETURN]

/-- Shift the correction constant out of `M`. -/
def straddleCorrPath : List Located :=
  [opAt 155 .JUMPDEST, opAt 156 (.Dup ⟨6, by decide⟩),
   opAt 157 (.Dup ⟨4, by decide⟩), pushAt 158 1 8, opAt 159 .SHR,
   pushAt 160 1 5, opAt 161 .MUL, pushAt 162 1 27, opAt 163 .SUB,
   pushAt 164 1 3, opAt 165 .SHL, opAt 166 .SHR, pushAt 167 1 11,
   opAt 168 .MUL]

/-- Apply the correction to the expected word. -/
def straddleAddPath : List Located :=
  [opAt 169 (.Dup ⟨1, by decide⟩), opAt 170 (.Dup ⟨9, by decide⟩),
   opAt 171 .AND, opAt 172 (.Dup ⟨1, by decide⟩), opAt 173 .ADD,
   opAt 174 (.Dup ⟨2, by decide⟩), opAt 175 (.Dup ⟨12, by decide⟩),
   opAt 176 .AND, opAt 177 .XOR, opAt 178 (.Swap ⟨1, by decide⟩),
   opAt 179 .POP, opAt 180 .POP]

/-- Bump the scalar and rejoin the scan. -/
def straddleBackPath : List Located :=
  [opAt 181 (.Dup ⟨2, by decide⟩), pushAt 182 1 11, opAt 183 .ADD,
   opAt 184 (.Swap ⟨2, by decide⟩), opAt 185 .POP, pushAt 186 1 209,
   opAt 187 .JUMP]


@[simp] theorem pc2903 : Artifact.submissionArtifact.instructionPC 59 = 0x82 := by rfl
@[simp] theorem pc2904 : Artifact.submissionArtifact.instructionPC 60 = 0x83 := by rfl
@[simp] theorem pc2905 : Artifact.submissionArtifact.instructionPC 64 = 0x88 := by rfl
@[simp] theorem pc2906 : Artifact.submissionArtifact.instructionPC 69 = 0xae := by rfl
@[simp] theorem pc2907 : Artifact.submissionArtifact.instructionPC 71 = 0xb0 := by rfl
@[simp] theorem pc2908 : Artifact.submissionArtifact.instructionPC 72 = 0xb1 := by rfl
@[simp] theorem pc2909 : Artifact.submissionArtifact.instructionPC 73 = 0xb2 := by rfl
@[simp] theorem pc2910 : Artifact.submissionArtifact.instructionPC 74 = 0xb3 := by rfl
@[simp] theorem pc2911 : Artifact.submissionArtifact.instructionPC 75 = 0xb4 := by rfl
@[simp] theorem pc2912 : Artifact.submissionArtifact.instructionPC 76 = 0xb5 := by rfl
@[simp] theorem pc2913 : Artifact.submissionArtifact.instructionPC 77 = 0xb6 := by rfl
@[simp] theorem pc2914 : Artifact.submissionArtifact.instructionPC 78 = 0xb7 := by rfl
@[simp] theorem pc2915 : Artifact.submissionArtifact.instructionPC 79 = 0xb8 := by rfl
@[simp] theorem pc2916 : Artifact.submissionArtifact.instructionPC 80 = 0xb9 := by rfl
@[simp] theorem pc2917 : Artifact.submissionArtifact.instructionPC 81 = 0xba := by rfl
@[simp] theorem pc2918 : Artifact.submissionArtifact.instructionPC 82 = 0xbb := by rfl
@[simp] theorem pc2919 : Artifact.submissionArtifact.instructionPC 83 = 0xbc := by rfl
@[simp] theorem pc2920 : Artifact.submissionArtifact.instructionPC 84 = 0xbd := by rfl
@[simp] theorem pc2921 : Artifact.submissionArtifact.instructionPC 85 = 0xbe := by rfl
@[simp] theorem pc2922 : Artifact.submissionArtifact.instructionPC 86 = 0xbf := by rfl
@[simp] theorem pc2923 : Artifact.submissionArtifact.instructionPC 87 = 0xc0 := by rfl
@[simp] theorem pc2924 : Artifact.submissionArtifact.instructionPC 88 = 0xc1 := by rfl
@[simp] theorem pc2925 : Artifact.submissionArtifact.instructionPC 89 = 0xc2 := by rfl
@[simp] theorem pc2926 : Artifact.submissionArtifact.instructionPC 90 = 0xc3 := by rfl
@[simp] theorem pc2927 : Artifact.submissionArtifact.instructionPC 91 = 0xc4 := by rfl
@[simp] theorem pc2928 : Artifact.submissionArtifact.instructionPC 92 = 0xc5 := by rfl
@[simp] theorem pc2929 : Artifact.submissionArtifact.instructionPC 93 = 0xc6 := by rfl
@[simp] theorem pc2930 : Artifact.submissionArtifact.instructionPC 94 = 0xc7 := by rfl
@[simp] theorem pc2931 : Artifact.submissionArtifact.instructionPC 95 = 0xc9 := by rfl
@[simp] theorem pc2932 : Artifact.submissionArtifact.instructionPC 96 = 0xca := by rfl
@[simp] theorem pc2933 : Artifact.submissionArtifact.instructionPC 97 = 0xcc := by rfl
@[simp] theorem pc2934 : Artifact.submissionArtifact.instructionPC 98 = 0xcd := by rfl
@[simp] theorem pc2935 : Artifact.submissionArtifact.instructionPC 99 = 0xd0 := by rfl
@[simp] theorem pc2936 : Artifact.submissionArtifact.instructionPC 100 = 0xd1 := by rfl
@[simp] theorem pc2937 : Artifact.submissionArtifact.instructionPC 101 = 0xd2 := by rfl
@[simp] theorem pc2938 : Artifact.submissionArtifact.instructionPC 102 = 0xd3 := by rfl
@[simp] theorem pc2939 : Artifact.submissionArtifact.instructionPC 103 = 0xd4 := by rfl
@[simp] theorem pc2940 : Artifact.submissionArtifact.instructionPC 104 = 0xd5 := by rfl
@[simp] theorem pc2941 : Artifact.submissionArtifact.instructionPC 105 = 0xd6 := by rfl
@[simp] theorem pc2942 : Artifact.submissionArtifact.instructionPC 106 = 0xd7 := by rfl
@[simp] theorem pc2943 : Artifact.submissionArtifact.instructionPC 107 = 0xd8 := by rfl
@[simp] theorem pc2944 : Artifact.submissionArtifact.instructionPC 108 = 0xd9 := by rfl
@[simp] theorem pc2946 : Artifact.submissionArtifact.instructionPC 109 = 0xda := by rfl
@[simp] theorem pc2947 : Artifact.submissionArtifact.instructionPC 110 = 0xdc := by rfl
@[simp] theorem pc2948 : Artifact.submissionArtifact.instructionPC 111 = 0xdd := by rfl
@[simp] theorem pc2949 : Artifact.submissionArtifact.instructionPC 112 = 0xdf := by rfl
@[simp] theorem pc2952 : Artifact.submissionArtifact.instructionPC 113 = 0xe0 := by rfl
@[simp] theorem pc2953 : Artifact.submissionArtifact.instructionPC 114 = 0xe1 := by rfl
@[simp] theorem pc2954 : Artifact.submissionArtifact.instructionPC 115 = 0xe3 := by rfl
@[simp] theorem pc2955 : Artifact.submissionArtifact.instructionPC 116 = 0xe4 := by rfl
@[simp] theorem pc2956 : Artifact.submissionArtifact.instructionPC 117 = 0xe5 := by rfl
@[simp] theorem pc2957 : Artifact.submissionArtifact.instructionPC 123 = 0xed := by rfl
@[simp] theorem pc2958 : Artifact.submissionArtifact.instructionPC 124 = 0xee := by rfl
@[simp] theorem pc2959 : Artifact.submissionArtifact.instructionPC 125 = 0xf1 := by rfl
@[simp] theorem pc2960 : Artifact.submissionArtifact.instructionPC 126 = 0xf2 := by rfl
@[simp] theorem pc2961 : Artifact.submissionArtifact.instructionPC 127 = 0xf4 := by rfl
@[simp] theorem pc2962 : Artifact.submissionArtifact.instructionPC 128 = 0xf5 := by rfl
@[simp] theorem pc2963 : Artifact.submissionArtifact.instructionPC 129 = 0xf8 := by rfl
@[simp] theorem pc2964 : Artifact.submissionArtifact.instructionPC 130 = 0xf9 := by rfl
@[simp] theorem pc2965 : Artifact.submissionArtifact.instructionPC 131 = 0x102 := by rfl
@[simp] theorem pc2966 : Artifact.submissionArtifact.instructionPC 132 = 0x104 := by rfl
@[simp] theorem pc2967 : Artifact.submissionArtifact.instructionPC 133 = 0x105 := by rfl
@[simp] theorem pc2968 : Artifact.submissionArtifact.instructionPC 134 = 0x106 := by rfl
@[simp] theorem pc2969 : Artifact.submissionArtifact.instructionPC 135 = 0x107 := by rfl
@[simp] theorem pc2970 : Artifact.submissionArtifact.instructionPC 136 = 0x108 := by rfl
@[simp] theorem pc2971 : Artifact.submissionArtifact.instructionPC 137 = 0x109 := by rfl
@[simp] theorem pc2972 : Artifact.submissionArtifact.instructionPC 138 = 0x10a := by rfl
@[simp] theorem pc2973 : Artifact.submissionArtifact.instructionPC 139 = 0x10b := by rfl
@[simp] theorem pc2974 : Artifact.submissionArtifact.instructionPC 140 = 0x10c := by rfl
@[simp] theorem pc2975 : Artifact.submissionArtifact.instructionPC 141 = 0x10d := by rfl
@[simp] theorem pc2976 : Artifact.submissionArtifact.instructionPC 142 = 0x10e := by rfl
@[simp] theorem pc2977 : Artifact.submissionArtifact.instructionPC 143 = 0x10f := by rfl
@[simp] theorem pc2978 : Artifact.submissionArtifact.instructionPC 144 = 0x110 := by rfl
@[simp] theorem pc2979 : Artifact.submissionArtifact.instructionPC 145 = 0x111 := by rfl
@[simp] theorem pc2980 : Artifact.submissionArtifact.instructionPC 146 = 0x112 := by rfl
@[simp] theorem pc2981 : Artifact.submissionArtifact.instructionPC 147 = 0x113 := by rfl
@[simp] theorem pc2982 : Artifact.submissionArtifact.instructionPC 148 = 0x116 := by rfl
@[simp] theorem pc2983 : Artifact.submissionArtifact.instructionPC 149 = 0x117 := by rfl
@[simp] theorem pc2984 : Artifact.submissionArtifact.instructionPC 150 = 0x12c := by rfl
@[simp] theorem pc2985 : Artifact.submissionArtifact.instructionPC 151 = 0x12d := by rfl
@[simp] theorem pc2986 : Artifact.submissionArtifact.instructionPC 152 = 0x12e := by rfl
@[simp] theorem pc2987 : Artifact.submissionArtifact.instructionPC 153 = 0x130 := by rfl
@[simp] theorem pc2988 : Artifact.submissionArtifact.instructionPC 154 = 0x131 := by rfl
@[simp] theorem pc2989 : Artifact.submissionArtifact.instructionPC 155 = 0x132 := by rfl
@[simp] theorem pc2990 : Artifact.submissionArtifact.instructionPC 156 = 0x133 := by rfl
@[simp] theorem pc2991 : Artifact.submissionArtifact.instructionPC 157 = 0x134 := by rfl
@[simp] theorem pc2992 : Artifact.submissionArtifact.instructionPC 158 = 0x135 := by rfl
@[simp] theorem pc2993 : Artifact.submissionArtifact.instructionPC 159 = 0x137 := by rfl
@[simp] theorem pc2994 : Artifact.submissionArtifact.instructionPC 160 = 0x138 := by rfl
@[simp] theorem pc2995 : Artifact.submissionArtifact.instructionPC 161 = 0x13a := by rfl
@[simp] theorem pc2996 : Artifact.submissionArtifact.instructionPC 162 = 0x13b := by rfl
@[simp] theorem pc2997 : Artifact.submissionArtifact.instructionPC 163 = 0x13d := by rfl
@[simp] theorem pc2998 : Artifact.submissionArtifact.instructionPC 164 = 0x13e := by rfl
@[simp] theorem pc2999 : Artifact.submissionArtifact.instructionPC 165 = 0x140 := by rfl
@[simp] theorem pc3000 : Artifact.submissionArtifact.instructionPC 166 = 0x141 := by rfl
@[simp] theorem pc3001 : Artifact.submissionArtifact.instructionPC 167 = 0x142 := by rfl
@[simp] theorem pc3002 : Artifact.submissionArtifact.instructionPC 168 = 0x144 := by rfl
@[simp] theorem pc3003 : Artifact.submissionArtifact.instructionPC 169 = 0x145 := by rfl
@[simp] theorem pc3004 : Artifact.submissionArtifact.instructionPC 170 = 0x146 := by rfl
@[simp] theorem pc3005 : Artifact.submissionArtifact.instructionPC 171 = 0x147 := by rfl
@[simp] theorem pc3006 : Artifact.submissionArtifact.instructionPC 172 = 0x148 := by rfl
@[simp] theorem pc3007 : Artifact.submissionArtifact.instructionPC 173 = 0x149 := by rfl
@[simp] theorem pc3008 : Artifact.submissionArtifact.instructionPC 174 = 0x14a := by rfl
@[simp] theorem pc3009 : Artifact.submissionArtifact.instructionPC 175 = 0x14b := by rfl
@[simp] theorem pc3010 : Artifact.submissionArtifact.instructionPC 176 = 0x14c := by rfl
@[simp] theorem pc3011 : Artifact.submissionArtifact.instructionPC 177 = 0x14d := by rfl
@[simp] theorem pc3012 : Artifact.submissionArtifact.instructionPC 178 = 0x14e := by rfl
@[simp] theorem pc3013 : Artifact.submissionArtifact.instructionPC 179 = 0x14f := by rfl
@[simp] theorem pc3014 : Artifact.submissionArtifact.instructionPC 180 = 0x150 := by rfl
@[simp] theorem pc3015 : Artifact.submissionArtifact.instructionPC 181 = 0x151 := by rfl
@[simp] theorem pc3016 : Artifact.submissionArtifact.instructionPC 182 = 0x152 := by rfl
@[simp] theorem pc3017 : Artifact.submissionArtifact.instructionPC 183 = 0x154 := by rfl
@[simp] theorem pc3018 : Artifact.submissionArtifact.instructionPC 184 = 0x155 := by rfl
@[simp] theorem pc3019 : Artifact.submissionArtifact.instructionPC 185 = 0x156 := by rfl
@[simp] theorem pc3020 : Artifact.submissionArtifact.instructionPC 186 = 0x157 := by rfl
@[simp] theorem pc3021 : Artifact.submissionArtifact.instructionPC 187 = 0x159 := by rfl
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan
