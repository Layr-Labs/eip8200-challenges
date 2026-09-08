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
  [opAt 54 .JUMPDEST,
   pushAt 55 1 255,
   pushAt 56 0 0,
   opAt 57 .NOT,
   opAt 58 .DIV,
   pushAt 59 32 3244493450063667868678674439968361782956185527883176199882357678282131398018,
   opAt 60 (.Dup ⟨1, by decide⟩),
   pushAt 61 1 7,
   opAt 62 .SHL,
   opAt 63 (.Dup ⟨0, by decide⟩),
   opAt 64 .NOT,
   opAt 65 (.Swap ⟨0, by decide⟩),
   opAt 66 (.Swap ⟨2, by decide⟩),
   opAt 67 (.Dup ⟨2, by decide⟩),
   opAt 68 (.Dup ⟨2, by decide⟩),
   opAt 69 .AND,
   pushAt 70 0 0,
   pushAt 71 0 0,
   pushAt 72 0 0]

/-- Derive the expected word and test for a straddler. -/
def wordPath : List Located :=
  [opAt 73 .JUMPDEST, opAt 74 (.Dup ⟨0, by decide⟩),
   opAt 75 (.Dup ⟨5, by decide⟩), opAt 76 .MUL,
   opAt 77 (.Dup ⟨0, by decide⟩), opAt 78 (.Dup ⟨7, by decide⟩),
   opAt 79 .AND, opAt 80 (.Dup ⟨5, by decide⟩), opAt 81 .ADD,
   opAt 82 (.Dup ⟨1, by decide⟩), opAt 83 (.Dup ⟨9, by decide⟩),
   opAt 84 .XOR, opAt 85 (.Dup ⟨10, by decide⟩), opAt 86 .AND,
   opAt 87 .XOR, opAt 88 (.Dup ⟨3, by decide⟩), pushAt 89 1 255,
   opAt 90 .AND, pushAt 91 1 224, opAt 92 .EQ, pushAt 93 2 299,
   opAt 94 .JUMPI]

/-- Fold one word into the accumulator and advance. -/
def comparePath : List Located :=
  [opAt 95 .JUMPDEST, opAt 96 (.Dup ⟨3, by decide⟩),
   opAt 97 .CALLDATALOAD, opAt 98 .XOR, opAt 99 (.Dup ⟨4, by decide⟩),
   opAt 100 .OR, opAt 101 (.Swap ⟨3, by decide⟩), opAt 102 .POP,
   opAt 103 .POP, pushAt 104 1 160,
   opAt 105 .ADD, pushAt 106 1 255, opAt 107 .AND,
   opAt 108 (.Swap ⟨0, by decide⟩), pushAt 109 1 32, opAt 110 .ADD,
   opAt 111 (.Swap ⟨0, by decide⟩), opAt 117 (.Dup ⟨1, by decide⟩), pushAt 118 2 992, opAt 119 .GT,
   pushAt 120 1 177, opAt 121 .JUMPI]

/-- The padded tail word, the cleanup and the miss test. -/
def tailPath : List Located :=
  [pushAt 122 2 992, opAt 123 .CALLDATALOAD,
   pushAt 124 8 9848759918901945995, pushAt 125 1 192, opAt 126 .SHL,
   opAt 127 .XOR, opAt 128 (.Dup ⟨3, by decide⟩), opAt 129 .OR,
   opAt 130 (.Swap ⟨2, by decide⟩), opAt 131 .POP,
   opAt 132 (.Swap ⟨1, by decide⟩), opAt 133 (.Swap ⟨6, by decide⟩),
   opAt 134 .POP, opAt 135 .POP, opAt 136 .POP, opAt 137 .POP,
   opAt 138 .POP, opAt 139 .POP, opAt 140 .POP, pushAt 141 2 339,
   opAt 142 .JUMPI]

/-- Store and return the stored digest. -/
def returnPath : List Located :=
  [pushAt 143 20 766350606435067737561421097975693824639675460820,
   pushAt 144 0 0, opAt 145 .MSTORE, pushAt 146 1 32, pushAt 147 0 0,
   opAt 148 .RETURN]

/-- Shift the correction constant out of `M`. -/
def straddleCorrPath : List Located :=
  [opAt 149 .JUMPDEST, opAt 150 (.Dup ⟨6, by decide⟩),
   opAt 151 (.Dup ⟨4, by decide⟩), pushAt 152 1 8, opAt 153 .SHR,
   pushAt 154 1 5, opAt 155 .MUL, pushAt 156 1 27, opAt 157 .SUB,
   pushAt 158 1 8, opAt 159 .MUL, opAt 160 .SHR, pushAt 161 1 11,
   opAt 162 .MUL]

/-- Apply the correction to the expected word. -/
def straddleAddPath : List Located :=
  [opAt 163 (.Dup ⟨1, by decide⟩), opAt 164 (.Dup ⟨9, by decide⟩),
   opAt 165 .AND, opAt 166 (.Dup ⟨1, by decide⟩), opAt 167 .ADD,
   opAt 168 (.Dup ⟨2, by decide⟩), opAt 169 (.Dup ⟨12, by decide⟩),
   opAt 170 .AND, opAt 171 .XOR, opAt 172 (.Swap ⟨1, by decide⟩),
   opAt 173 .POP, opAt 174 .POP]

/-- Bump the scalar and rejoin the scan. -/
def straddleBackPath : List Located :=
  [opAt 175 (.Dup ⟨2, by decide⟩), pushAt 176 1 11, opAt 177 .ADD,
   opAt 178 (.Swap ⟨2, by decide⟩), opAt 179 .POP, pushAt 180 1 203,
   opAt 181 .JUMP]


@[simp] theorem pc2903 : Artifact.submissionArtifact.instructionPC 54 = 0x7c := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2904 : Artifact.submissionArtifact.instructionPC 55 = 0x7d := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2905 : Artifact.submissionArtifact.instructionPC 59 = 0x82 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2906 : Artifact.submissionArtifact.instructionPC 64 = 0xa8 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2907 : Artifact.submissionArtifact.instructionPC 66 = 0xaa := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2908 : Artifact.submissionArtifact.instructionPC 67 = 0xab := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2909 : Artifact.submissionArtifact.instructionPC 68 = 0xac := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2910 : Artifact.submissionArtifact.instructionPC 69 = 0xad := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2911 : Artifact.submissionArtifact.instructionPC 70 = 0xae := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2912 : Artifact.submissionArtifact.instructionPC 71 = 0xaf := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2913 : Artifact.submissionArtifact.instructionPC 72 = 0xb0 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2914 : Artifact.submissionArtifact.instructionPC 73 = 0xb1 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2915 : Artifact.submissionArtifact.instructionPC 74 = 0xb2 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2916 : Artifact.submissionArtifact.instructionPC 75 = 0xb3 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2917 : Artifact.submissionArtifact.instructionPC 76 = 0xb4 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2918 : Artifact.submissionArtifact.instructionPC 77 = 0xb5 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2919 : Artifact.submissionArtifact.instructionPC 78 = 0xb6 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2920 : Artifact.submissionArtifact.instructionPC 79 = 0xb7 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2921 : Artifact.submissionArtifact.instructionPC 80 = 0xb8 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2922 : Artifact.submissionArtifact.instructionPC 81 = 0xb9 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2923 : Artifact.submissionArtifact.instructionPC 82 = 0xba := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2924 : Artifact.submissionArtifact.instructionPC 83 = 0xbb := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2925 : Artifact.submissionArtifact.instructionPC 84 = 0xbc := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2926 : Artifact.submissionArtifact.instructionPC 85 = 0xbd := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2927 : Artifact.submissionArtifact.instructionPC 86 = 0xbe := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2928 : Artifact.submissionArtifact.instructionPC 87 = 0xbf := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2929 : Artifact.submissionArtifact.instructionPC 88 = 0xc0 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2930 : Artifact.submissionArtifact.instructionPC 89 = 0xc1 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2931 : Artifact.submissionArtifact.instructionPC 90 = 0xc3 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2932 : Artifact.submissionArtifact.instructionPC 91 = 0xc4 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2933 : Artifact.submissionArtifact.instructionPC 92 = 0xc6 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2934 : Artifact.submissionArtifact.instructionPC 93 = 0xc7 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2935 : Artifact.submissionArtifact.instructionPC 94 = 0xca := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2936 : Artifact.submissionArtifact.instructionPC 95 = 0xcb := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2937 : Artifact.submissionArtifact.instructionPC 96 = 0xcc := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2938 : Artifact.submissionArtifact.instructionPC 97 = 0xcd := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2939 : Artifact.submissionArtifact.instructionPC 98 = 0xce := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2940 : Artifact.submissionArtifact.instructionPC 99 = 0xcf := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2941 : Artifact.submissionArtifact.instructionPC 100 = 0xd0 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2942 : Artifact.submissionArtifact.instructionPC 101 = 0xd1 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2943 : Artifact.submissionArtifact.instructionPC 102 = 0xd2 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2944 : Artifact.submissionArtifact.instructionPC 103 = 0xd3 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2946 : Artifact.submissionArtifact.instructionPC 104 = 0xd4 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2947 : Artifact.submissionArtifact.instructionPC 105 = 0xd6 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2948 : Artifact.submissionArtifact.instructionPC 106 = 0xd7 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2949 : Artifact.submissionArtifact.instructionPC 107 = 0xd9 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2952 : Artifact.submissionArtifact.instructionPC 108 = 0xda := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2953 : Artifact.submissionArtifact.instructionPC 109 = 0xdb := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2954 : Artifact.submissionArtifact.instructionPC 110 = 0xdd := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2955 : Artifact.submissionArtifact.instructionPC 111 = 0xde := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2956 : Artifact.submissionArtifact.instructionPC 112 = 0xdf := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2957 : Artifact.submissionArtifact.instructionPC 117 = 0xe6 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2958 : Artifact.submissionArtifact.instructionPC 118 = 0xe7 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2959 : Artifact.submissionArtifact.instructionPC 119 = 0xea := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2960 : Artifact.submissionArtifact.instructionPC 120 = 0xeb := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2961 : Artifact.submissionArtifact.instructionPC 121 = 0xed := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2962 : Artifact.submissionArtifact.instructionPC 122 = 0xee := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2963 : Artifact.submissionArtifact.instructionPC 123 = 0xf1 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2964 : Artifact.submissionArtifact.instructionPC 124 = 0xf2 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2965 : Artifact.submissionArtifact.instructionPC 125 = 0xfb := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2966 : Artifact.submissionArtifact.instructionPC 126 = 0xfd := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2967 : Artifact.submissionArtifact.instructionPC 127 = 0xfe := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2968 : Artifact.submissionArtifact.instructionPC 128 = 0xff := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2969 : Artifact.submissionArtifact.instructionPC 129 = 0x100 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2970 : Artifact.submissionArtifact.instructionPC 130 = 0x101 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2971 : Artifact.submissionArtifact.instructionPC 131 = 0x102 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2972 : Artifact.submissionArtifact.instructionPC 132 = 0x103 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2973 : Artifact.submissionArtifact.instructionPC 133 = 0x104 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2974 : Artifact.submissionArtifact.instructionPC 134 = 0x105 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2975 : Artifact.submissionArtifact.instructionPC 135 = 0x106 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2976 : Artifact.submissionArtifact.instructionPC 136 = 0x107 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2977 : Artifact.submissionArtifact.instructionPC 137 = 0x108 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2978 : Artifact.submissionArtifact.instructionPC 138 = 0x109 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2979 : Artifact.submissionArtifact.instructionPC 139 = 0x10a := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2980 : Artifact.submissionArtifact.instructionPC 140 = 0x10b := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2981 : Artifact.submissionArtifact.instructionPC 141 = 0x10c := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2982 : Artifact.submissionArtifact.instructionPC 142 = 0x10f := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2983 : Artifact.submissionArtifact.instructionPC 143 = 0x110 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2984 : Artifact.submissionArtifact.instructionPC 144 = 0x125 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2985 : Artifact.submissionArtifact.instructionPC 145 = 0x126 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2986 : Artifact.submissionArtifact.instructionPC 146 = 0x127 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2987 : Artifact.submissionArtifact.instructionPC 147 = 0x129 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2988 : Artifact.submissionArtifact.instructionPC 148 = 0x12a := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2989 : Artifact.submissionArtifact.instructionPC 149 = 0x12b := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2990 : Artifact.submissionArtifact.instructionPC 150 = 0x12c := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2991 : Artifact.submissionArtifact.instructionPC 151 = 0x12d := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2992 : Artifact.submissionArtifact.instructionPC 152 = 0x12e := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2993 : Artifact.submissionArtifact.instructionPC 153 = 0x130 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2994 : Artifact.submissionArtifact.instructionPC 154 = 0x131 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2995 : Artifact.submissionArtifact.instructionPC 155 = 0x133 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2996 : Artifact.submissionArtifact.instructionPC 156 = 0x134 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2997 : Artifact.submissionArtifact.instructionPC 157 = 0x136 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2998 : Artifact.submissionArtifact.instructionPC 158 = 0x137 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2999 : Artifact.submissionArtifact.instructionPC 159 = 0x139 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc3000 : Artifact.submissionArtifact.instructionPC 160 = 0x13a := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc3001 : Artifact.submissionArtifact.instructionPC 161 = 0x13b := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc3002 : Artifact.submissionArtifact.instructionPC 162 = 0x13d := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc3003 : Artifact.submissionArtifact.instructionPC 163 = 0x13e := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc3004 : Artifact.submissionArtifact.instructionPC 164 = 0x13f := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc3005 : Artifact.submissionArtifact.instructionPC 165 = 0x140 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc3006 : Artifact.submissionArtifact.instructionPC 166 = 0x141 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc3007 : Artifact.submissionArtifact.instructionPC 167 = 0x142 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc3008 : Artifact.submissionArtifact.instructionPC 168 = 0x143 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc3009 : Artifact.submissionArtifact.instructionPC 169 = 0x144 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc3010 : Artifact.submissionArtifact.instructionPC 170 = 0x145 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc3011 : Artifact.submissionArtifact.instructionPC 171 = 0x146 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc3012 : Artifact.submissionArtifact.instructionPC 172 = 0x147 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc3013 : Artifact.submissionArtifact.instructionPC 173 = 0x148 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc3014 : Artifact.submissionArtifact.instructionPC 174 = 0x149 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc3015 : Artifact.submissionArtifact.instructionPC 175 = 0x14a := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc3016 : Artifact.submissionArtifact.instructionPC 176 = 0x14b := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc3017 : Artifact.submissionArtifact.instructionPC 177 = 0x14d := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc3018 : Artifact.submissionArtifact.instructionPC 178 = 0x14e := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc3019 : Artifact.submissionArtifact.instructionPC 179 = 0x14f := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc3020 : Artifact.submissionArtifact.instructionPC 180 = 0x150 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc3021 : Artifact.submissionArtifact.instructionPC 181 = 0x152 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan
