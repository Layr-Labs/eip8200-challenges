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
  [pushAt 73 1 255,
   pushAt 74 0 0,
   opAt 75 .NOT,
   opAt 76 .DIV,
   pushAt 77 32 3244493450063667868678674439968361782956185527883176199882357678282131398013,
   opAt 78 (.Dup ⟨1, by decide⟩),
   pushAt 79 1 7,
   opAt 80 .SHL,
   opAt 81 (.Dup ⟨0, by decide⟩),
   opAt 82 .NOT,
   opAt 83 (.Swap ⟨0, by decide⟩),
   opAt 84 (.Swap ⟨2, by decide⟩),
   opAt 85 (.Dup ⟨2, by decide⟩),
   opAt 86 (.Dup ⟨2, by decide⟩),
   opAt 87 .AND,
   pushAt 88 0 0,
   pushAt 89 0 0,
   pushAt 90 0 0]

/-- Derive the expected word and test for a straddler. -/
def wordPath : List Located :=
  [opAt 91 .JUMPDEST, opAt 92 (.Dup ⟨0, by decide⟩),
   opAt 93 (.Dup ⟨5, by decide⟩), opAt 94 .MUL,
   opAt 95 (.Dup ⟨0, by decide⟩), opAt 96 (.Dup ⟨7, by decide⟩),
   opAt 97 .AND, opAt 98 (.Dup ⟨5, by decide⟩), opAt 99 .ADD,
   opAt 100 (.Dup ⟨1, by decide⟩), opAt 101 (.Dup ⟨9, by decide⟩),
   opAt 102 .XOR, opAt 103 (.Dup ⟨10, by decide⟩), opAt 104 .AND,
   opAt 105 .XOR, opAt 106 (.Dup ⟨3, by decide⟩), pushAt 107 1 255,
   opAt 108 .AND, pushAt 109 1 224, opAt 110 .EQ, pushAt 111 2 324,
   opAt 112 .JUMPI]

/-- Fold one word into the accumulator and advance. -/
def comparePath : List Located :=
  [opAt 113 .JUMPDEST, opAt 114 (.Dup ⟨3, by decide⟩),
   opAt 115 .CALLDATALOAD, opAt 116 .XOR, opAt 117 (.Dup ⟨4, by decide⟩),
   opAt 118 .OR, opAt 119 (.Swap ⟨3, by decide⟩), opAt 120 .POP,
   opAt 121 .POP, pushAt 122 1 160,
   opAt 123 .ADD, pushAt 124 1 255, opAt 125 .AND,
   opAt 126 (.Swap ⟨0, by decide⟩), pushAt 127 1 32, opAt 128 .ADD,
   opAt 129 (.Swap ⟨0, by decide⟩), opAt 130 .JUMPDEST,
   opAt 136 (.Dup ⟨1, by decide⟩), pushAt 137 2 992, opAt 138 .GT,
   pushAt 139 1 201, opAt 140 .JUMPI]

/-- The padded tail word, the cleanup and the miss test. -/
def tailPath : List Located :=
  [pushAt 141 2 992, opAt 142 .CALLDATALOAD,
   pushAt 143 8 9848759918901945990, pushAt 144 1 192, opAt 145 .SHL,
   opAt 146 .XOR, opAt 147 (.Dup ⟨3, by decide⟩), opAt 148 .OR,
   opAt 149 (.Swap ⟨2, by decide⟩), opAt 150 .POP,
   opAt 151 (.Swap ⟨1, by decide⟩), opAt 152 (.Swap ⟨6, by decide⟩),
   opAt 153 .POP, opAt 154 .POP, opAt 155 .POP, opAt 156 .POP,
   opAt 157 .POP, opAt 158 .POP, opAt 159 .POP, pushAt 160 2 364,
   opAt 161 .JUMPI]

/-- Store and return the stored digest. -/
def returnPath : List Located :=
  [pushAt 162 20 766350606435067737561421097975693824639675460815,
   pushAt 163 0 0, opAt 164 .MSTORE, pushAt 165 1 32, pushAt 166 0 0,
   opAt 167 .RETURN]

/-- Shift the correction constant out of `M`. -/
def straddleCorrPath : List Located :=
  [opAt 168 .JUMPDEST, opAt 169 (.Dup ⟨6, by decide⟩),
   opAt 170 (.Dup ⟨4, by decide⟩), pushAt 171 1 8, opAt 172 .SHR,
   pushAt 173 1 5, opAt 174 .MUL, pushAt 175 1 27, opAt 176 .SUB,
   pushAt 177 1 3, opAt 178 .SHL, opAt 179 .SHR, pushAt 180 1 11,
   opAt 181 .MUL]

/-- Apply the correction to the expected word. -/
def straddleAddPath : List Located :=
  [opAt 182 (.Dup ⟨1, by decide⟩), opAt 183 (.Dup ⟨9, by decide⟩),
   opAt 184 .AND, opAt 185 (.Dup ⟨1, by decide⟩), opAt 186 .ADD,
   opAt 187 (.Dup ⟨2, by decide⟩), opAt 188 (.Dup ⟨12, by decide⟩),
   opAt 189 .AND, opAt 190 .XOR, opAt 191 (.Swap ⟨1, by decide⟩),
   opAt 192 .POP, opAt 193 .POP]

/-- Bump the scalar and rejoin the scan. -/
def straddleBackPath : List Located :=
  [opAt 194 (.Dup ⟨2, by decide⟩), pushAt 195 1 11, opAt 196 .ADD,
   opAt 197 (.Swap ⟨2, by decide⟩), opAt 198 .POP, pushAt 199 1 227,
   opAt 200 .JUMP]


@[simp] theorem pc2903 : Artifact.submissionArtifact.instructionPC 64 = 0x88 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2904 : Artifact.submissionArtifact.instructionPC 73 = 0x95 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2905 : Artifact.submissionArtifact.instructionPC 77 = 0x9a := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2906 : Artifact.submissionArtifact.instructionPC 82 = 0xc0 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2907 : Artifact.submissionArtifact.instructionPC 84 = 0xc2 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2908 : Artifact.submissionArtifact.instructionPC 85 = 0xc3 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2909 : Artifact.submissionArtifact.instructionPC 86 = 0xc4 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2910 : Artifact.submissionArtifact.instructionPC 87 = 0xc5 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2911 : Artifact.submissionArtifact.instructionPC 88 = 0xc6 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2912 : Artifact.submissionArtifact.instructionPC 89 = 0xc7 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2913 : Artifact.submissionArtifact.instructionPC 90 = 0xc8 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2914 : Artifact.submissionArtifact.instructionPC 91 = 0xc9 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2915 : Artifact.submissionArtifact.instructionPC 92 = 0xca := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2916 : Artifact.submissionArtifact.instructionPC 93 = 0xcb := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2917 : Artifact.submissionArtifact.instructionPC 94 = 0xcc := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2918 : Artifact.submissionArtifact.instructionPC 95 = 0xcd := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2919 : Artifact.submissionArtifact.instructionPC 96 = 0xce := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2920 : Artifact.submissionArtifact.instructionPC 97 = 0xcf := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2921 : Artifact.submissionArtifact.instructionPC 98 = 0xd0 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2922 : Artifact.submissionArtifact.instructionPC 99 = 0xd1 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2923 : Artifact.submissionArtifact.instructionPC 100 = 0xd2 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2924 : Artifact.submissionArtifact.instructionPC 101 = 0xd3 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2925 : Artifact.submissionArtifact.instructionPC 102 = 0xd4 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2926 : Artifact.submissionArtifact.instructionPC 103 = 0xd5 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2927 : Artifact.submissionArtifact.instructionPC 104 = 0xd6 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2928 : Artifact.submissionArtifact.instructionPC 105 = 0xd7 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2929 : Artifact.submissionArtifact.instructionPC 106 = 0xd8 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2930 : Artifact.submissionArtifact.instructionPC 107 = 0xd9 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2931 : Artifact.submissionArtifact.instructionPC 108 = 0xdb := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2932 : Artifact.submissionArtifact.instructionPC 109 = 0xdc := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2933 : Artifact.submissionArtifact.instructionPC 110 = 0xde := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2934 : Artifact.submissionArtifact.instructionPC 111 = 0xdf := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2935 : Artifact.submissionArtifact.instructionPC 112 = 0xe2 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2936 : Artifact.submissionArtifact.instructionPC 113 = 0xe3 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2937 : Artifact.submissionArtifact.instructionPC 114 = 0xe4 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2938 : Artifact.submissionArtifact.instructionPC 115 = 0xe5 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2939 : Artifact.submissionArtifact.instructionPC 116 = 0xe6 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2940 : Artifact.submissionArtifact.instructionPC 117 = 0xe7 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2941 : Artifact.submissionArtifact.instructionPC 118 = 0xe8 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2942 : Artifact.submissionArtifact.instructionPC 119 = 0xe9 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2943 : Artifact.submissionArtifact.instructionPC 120 = 0xea := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2944 : Artifact.submissionArtifact.instructionPC 121 = 0xeb := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2946 : Artifact.submissionArtifact.instructionPC 122 = 0xec := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2947 : Artifact.submissionArtifact.instructionPC 123 = 0xee := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2948 : Artifact.submissionArtifact.instructionPC 124 = 0xef := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2949 : Artifact.submissionArtifact.instructionPC 125 = 0xf1 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2952 : Artifact.submissionArtifact.instructionPC 126 = 0xf2 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2953 : Artifact.submissionArtifact.instructionPC 127 = 0xf3 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2954 : Artifact.submissionArtifact.instructionPC 128 = 0xf5 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2955 : Artifact.submissionArtifact.instructionPC 129 = 0xf6 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2956 : Artifact.submissionArtifact.instructionPC 130 = 0xf7 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2957 : Artifact.submissionArtifact.instructionPC 136 = 0xff := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2958 : Artifact.submissionArtifact.instructionPC 137 = 0x100 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2959 : Artifact.submissionArtifact.instructionPC 138 = 0x103 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2960 : Artifact.submissionArtifact.instructionPC 139 = 0x104 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2961 : Artifact.submissionArtifact.instructionPC 140 = 0x106 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2962 : Artifact.submissionArtifact.instructionPC 141 = 0x107 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2963 : Artifact.submissionArtifact.instructionPC 142 = 0x10a := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2964 : Artifact.submissionArtifact.instructionPC 143 = 0x10b := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2965 : Artifact.submissionArtifact.instructionPC 144 = 0x114 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2966 : Artifact.submissionArtifact.instructionPC 145 = 0x116 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2967 : Artifact.submissionArtifact.instructionPC 146 = 0x117 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2968 : Artifact.submissionArtifact.instructionPC 147 = 0x118 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2969 : Artifact.submissionArtifact.instructionPC 148 = 0x119 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2970 : Artifact.submissionArtifact.instructionPC 149 = 0x11a := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2971 : Artifact.submissionArtifact.instructionPC 150 = 0x11b := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2972 : Artifact.submissionArtifact.instructionPC 151 = 0x11c := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2973 : Artifact.submissionArtifact.instructionPC 152 = 0x11d := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2974 : Artifact.submissionArtifact.instructionPC 153 = 0x11e := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2975 : Artifact.submissionArtifact.instructionPC 154 = 0x11f := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2976 : Artifact.submissionArtifact.instructionPC 155 = 0x120 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2977 : Artifact.submissionArtifact.instructionPC 156 = 0x121 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2978 : Artifact.submissionArtifact.instructionPC 157 = 0x122 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2979 : Artifact.submissionArtifact.instructionPC 158 = 0x123 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2980 : Artifact.submissionArtifact.instructionPC 159 = 0x124 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2981 : Artifact.submissionArtifact.instructionPC 160 = 0x125 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2982 : Artifact.submissionArtifact.instructionPC 161 = 0x128 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2983 : Artifact.submissionArtifact.instructionPC 162 = 0x129 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2984 : Artifact.submissionArtifact.instructionPC 163 = 0x13e := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2985 : Artifact.submissionArtifact.instructionPC 164 = 0x13f := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2986 : Artifact.submissionArtifact.instructionPC 165 = 0x140 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2987 : Artifact.submissionArtifact.instructionPC 166 = 0x142 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2988 : Artifact.submissionArtifact.instructionPC 167 = 0x143 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2989 : Artifact.submissionArtifact.instructionPC 168 = 0x144 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2990 : Artifact.submissionArtifact.instructionPC 169 = 0x145 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2991 : Artifact.submissionArtifact.instructionPC 170 = 0x146 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2992 : Artifact.submissionArtifact.instructionPC 171 = 0x147 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2993 : Artifact.submissionArtifact.instructionPC 172 = 0x149 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2994 : Artifact.submissionArtifact.instructionPC 173 = 0x14a := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2995 : Artifact.submissionArtifact.instructionPC 174 = 0x14c := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2996 : Artifact.submissionArtifact.instructionPC 175 = 0x14d := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2997 : Artifact.submissionArtifact.instructionPC 176 = 0x14f := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2998 : Artifact.submissionArtifact.instructionPC 177 = 0x150 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2999 : Artifact.submissionArtifact.instructionPC 178 = 0x152 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc3000 : Artifact.submissionArtifact.instructionPC 179 = 0x153 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc3001 : Artifact.submissionArtifact.instructionPC 180 = 0x154 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc3002 : Artifact.submissionArtifact.instructionPC 181 = 0x156 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc3003 : Artifact.submissionArtifact.instructionPC 182 = 0x157 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc3004 : Artifact.submissionArtifact.instructionPC 183 = 0x158 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc3005 : Artifact.submissionArtifact.instructionPC 184 = 0x159 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc3006 : Artifact.submissionArtifact.instructionPC 185 = 0x15a := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc3007 : Artifact.submissionArtifact.instructionPC 186 = 0x15b := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc3008 : Artifact.submissionArtifact.instructionPC 187 = 0x15c := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc3009 : Artifact.submissionArtifact.instructionPC 188 = 0x15d := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc3010 : Artifact.submissionArtifact.instructionPC 189 = 0x15e := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc3011 : Artifact.submissionArtifact.instructionPC 190 = 0x15f := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc3012 : Artifact.submissionArtifact.instructionPC 191 = 0x160 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc3013 : Artifact.submissionArtifact.instructionPC 192 = 0x161 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc3014 : Artifact.submissionArtifact.instructionPC 193 = 0x162 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc3015 : Artifact.submissionArtifact.instructionPC 194 = 0x163 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc3016 : Artifact.submissionArtifact.instructionPC 195 = 0x164 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc3017 : Artifact.submissionArtifact.instructionPC 196 = 0x166 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc3018 : Artifact.submissionArtifact.instructionPC 197 = 0x167 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc3019 : Artifact.submissionArtifact.instructionPC 198 = 0x168 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc3020 : Artifact.submissionArtifact.instructionPC 199 = 0x169 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc3021 : Artifact.submissionArtifact.instructionPC 200 = 0x16b := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan
