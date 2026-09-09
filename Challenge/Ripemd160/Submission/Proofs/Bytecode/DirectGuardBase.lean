import Challenge.Ripemd160.Submission.Proofs.Bytecode.RepeatedByteWord
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ExactGuardSpec
import Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputCompactLogic
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedInputData
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedGuardSpec
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackCorrect
import Challenge.EvmProof.Memory

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open KnownInputCompactState

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

def sizePath : List Located :=
  [opAt 97 .JUMPDEST, opAt 98 .CALLDATASIZE, pushAt 99 2 1000,
   opAt 100 .XOR, pushAt 101 1 3, opAt 102 .JUMPI]

def checkEntryPath : List Located :=
  [pushAt 103 0 0, opAt 104 .CALLDATALOAD,
   opAt 105 (.Dup ⟨0, by decide⟩),
   pushAt 106 1 255, pushAt 107 0 0, opAt 108 .NOT, opAt 109 .DIV,
   pushAt 110 1 97, opAt 111 .MUL, opAt 112 .XOR,
   pushAt 113 2 254, opAt 114 .JUMPI,
   pushAt 115 0 0, pushAt 116 1 32]

def checkEarlyPath : List Located :=
  [pushAt 103 0 0, opAt 104 .CALLDATALOAD,
   opAt 105 (.Dup ⟨0, by decide⟩),
   pushAt 106 1 255, pushAt 107 0 0, opAt 108 .NOT, opAt 109 .DIV,
   pushAt 110 1 97, opAt 111 .MUL, opAt 112 .XOR,
   pushAt 113 2 254, opAt 114 .JUMPI,
   opAt 148 .JUMPDEST, opAt 149 .POP]

def loopPath : List Located :=
  [opAt 117 .JUMPDEST, opAt 118 (.Swap ⟨0, by decide⟩),
   opAt 119 (.Dup ⟨1, by decide⟩), opAt 120 .CALLDATALOAD,
   opAt 121 (.Dup ⟨3, by decide⟩), opAt 122 .XOR, opAt 123 .OR,
   opAt 124 (.Swap ⟨0, by decide⟩), pushAt 125 1 32, opAt 126 .ADD,
   pushAt 127 2 992, opAt 128 (.Dup ⟨1, by decide⟩), opAt 129 .LT,
   pushAt 130 1 196, opAt 131 .JUMPI]

def tailPath : List Located :=
  [opAt 132 .CALLDATALOAD, opAt 133 (.Dup ⟨2, by decide⟩),
   opAt 134 .XOR, pushAt 135 1 192, opAt 136 .SHR, opAt 137 .OR,
   opAt 138 (.Swap ⟨0, by decide⟩), opAt 139 .POP,
   pushAt 140 1 3, opAt 141 .JUMPI]

def returnPath : List Located :=
  [pushAt 142 21 972889429405991776604892044862621566948497025487,
   pushAt 143 0 0, opAt 144 .MSTORE, opAt 145 .MSIZE,
   pushAt 146 0 0, opAt 147 .RETURN]

def atPC (input : ByteArray) (pc : Nat) : State :=
  { initialState submissionBytecode input 0 with pc := UInt256.ofNat pc }

/-! The 6572-byte array stays opaque: only these projections of the initial
state are unfolded, so `simp` never normalizes it. -/

@[simp] theorem initialState_code (code calldata : ByteArray) (gas : Nat) :
    (initialState code calldata gas).executionEnv.code = code := rfl

@[simp] theorem initialState_halt (code calldata : ByteArray) (gas : Nat) :
    (initialState code calldata gas).halt = .Running := rfl

@[simp] theorem initialState_memory (code calldata : ByteArray) (gas : Nat) :
    (initialState code calldata gas).memory = ByteArray.empty := rfl

@[simp] theorem initialState_activeWords (code calldata : ByteArray) (gas : Nat) :
    (initialState code calldata gas).activeWords = 0 := rfl

attribute [simp] Challenge.Ripemd160.initialState_stack
  Challenge.Ripemd160.initialState_pc
  Challenge.Ripemd160.initialState_calldata

def sizeMatched (input : ByteArray) : State := atPC input 0xb1
def fallbackState (input : ByteArray) : State := atPC input 0x3

def loopState (input : ByteArray) (n : Nat) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 0xc4
    stack := [UInt256.ofNat (32 * (n + 1)), loopAcc input n, referenceWord input] }

def loopExitState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 0xd7
    stack := [UInt256.ofNat 992, loopAcc input 30, referenceWord input] }

def returnEntry (input : ByteArray) : State := atPC input 0xe3

def storeWord (memory : ByteArray) (address : Nat) (word : UInt256) : ByteArray :=
  MachineState.writeBytes memory (Data.Bytes.natToBytesPadded word.toNat 32) address

def answerMemory : ByteArray :=
  storeWord ByteArray.empty 0 ExactGuardSpec.paddedDigestWord

def returnedState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 0xfd
    memory := answerMemory
    activeWords := UInt256.ofNat 1
    halt := .Returned
    hReturn := MachineState.readPadded answerMemory 0 32 }

abbrev run := Challenge.EvmProof.Stepper.runLocatedBlock
  (artifact := Artifact.submissionArtifact) (fork := .Osaka)

/- Freeze the concrete direct-guard range so symbolic path reduction never
   unfolds the complete generated artifact merely to advance a program counter. -/
@[simp] theorem pc2813 :
    Artifact.submissionArtifact.instructionPC 97 = 0xa8 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2814 :
    Artifact.submissionArtifact.instructionPC 98 = 0xa9 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2815 :
    Artifact.submissionArtifact.instructionPC 99 = 0xaa := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2816 :
    Artifact.submissionArtifact.instructionPC 100 = 0xad := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2817 :
    Artifact.submissionArtifact.instructionPC 101 = 0xae := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2818 :
    Artifact.submissionArtifact.instructionPC 102 = 0xb0 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2819 :
    Artifact.submissionArtifact.instructionPC 103 = 0xb1 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2820 :
    Artifact.submissionArtifact.instructionPC 104 = 0xb2 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2821 :
    Artifact.submissionArtifact.instructionPC 105 = 0xb3 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2822 :
    Artifact.submissionArtifact.instructionPC 106 = 0xb4 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2823 :
    Artifact.submissionArtifact.instructionPC 112 = 0xbc := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2824 :
    Artifact.submissionArtifact.instructionPC 113 = 0xbd := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2825 :
    Artifact.submissionArtifact.instructionPC 114 = 0xc0 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2826 :
    Artifact.submissionArtifact.instructionPC 115 = 0xc1 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2827 :
    Artifact.submissionArtifact.instructionPC 116 = 0xc2 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2828 :
    Artifact.submissionArtifact.instructionPC 117 = 0xc4 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2829 :
    Artifact.submissionArtifact.instructionPC 118 = 0xc5 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2830 :
    Artifact.submissionArtifact.instructionPC 119 = 0xc6 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2831 :
    Artifact.submissionArtifact.instructionPC 120 = 0xc7 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2832 :
    Artifact.submissionArtifact.instructionPC 121 = 0xc8 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2833 :
    Artifact.submissionArtifact.instructionPC 122 = 0xc9 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2834 :
    Artifact.submissionArtifact.instructionPC 123 = 0xca := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2835 :
    Artifact.submissionArtifact.instructionPC 124 = 0xcb := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2836 :
    Artifact.submissionArtifact.instructionPC 125 = 0xcc := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2837 :
    Artifact.submissionArtifact.instructionPC 126 = 0xce := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2838 :
    Artifact.submissionArtifact.instructionPC 127 = 0xcf := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2839 :
    Artifact.submissionArtifact.instructionPC 128 = 0xd2 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2840 :
    Artifact.submissionArtifact.instructionPC 129 = 0xd3 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2841 :
    Artifact.submissionArtifact.instructionPC 130 = 0xd4 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2842 :
    Artifact.submissionArtifact.instructionPC 131 = 0xd6 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2843 :
    Artifact.submissionArtifact.instructionPC 132 = 0xd7 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2844 :
    Artifact.submissionArtifact.instructionPC 133 = 0xd8 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2845 :
    Artifact.submissionArtifact.instructionPC 134 = 0xd9 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2846 :
    Artifact.submissionArtifact.instructionPC 135 = 0xda := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2847 :
    Artifact.submissionArtifact.instructionPC 136 = 0xdc := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2848 :
    Artifact.submissionArtifact.instructionPC 137 = 0xdd := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2849 :
    Artifact.submissionArtifact.instructionPC 138 = 0xde := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2850 :
    Artifact.submissionArtifact.instructionPC 138 = 0xde := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2851 :
    Artifact.submissionArtifact.instructionPC 139 = 0xdf := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2852 :
    Artifact.submissionArtifact.instructionPC 140 = 0xe0 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2853 :
    Artifact.submissionArtifact.instructionPC 141 = 0xe2 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2854 :
    Artifact.submissionArtifact.instructionPC 142 = 0xe3 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2855 :
    Artifact.submissionArtifact.instructionPC 143 = 0xf9 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2856 :
    Artifact.submissionArtifact.instructionPC 144 = 0xfa := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2857 :
    Artifact.submissionArtifact.instructionPC 145 = 0xfb := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2858 :
    Artifact.submissionArtifact.instructionPC 146 = 0xfc := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2859 :
    Artifact.submissionArtifact.instructionPC 147 = 0xfd := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2860 :
    Artifact.submissionArtifact.instructionPC 148 = 0xfe := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2861 :
    Artifact.submissionArtifact.instructionPC 149 = 0xff := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2862 :
    Artifact.submissionArtifact.instructionPC 150 = 0x100 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2863 :
    Artifact.submissionArtifact.instructionPC 150 = 0x100 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl

end Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard
