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
  [opAt 101 .JUMPDEST, opAt 102 .CALLDATASIZE, opAt 103 (.Dup ⟨0, by decide⟩),
   pushAt 104 2 256, opAt 105 .EQ, opAt 106 (.Swap ⟨0, by decide⟩),
   pushAt 107 2 1000, opAt 108 .EQ, opAt 109 .OR, opAt 110 .ISZERO,
   pushAt 111 1 3, opAt 112 .JUMPI]

def checkEntryPath : List Located :=
  [pushAt 113 0 0, opAt 114 .CALLDATALOAD,
   opAt 115 (.Dup ⟨0, by decide⟩),
   pushAt 116 32 KnownInputData.fullWord,
   opAt 117 .JUMPDEST, opAt 118 .JUMPDEST, opAt 119 .JUMPDEST,
   opAt 120 .JUMPDEST, opAt 121 .JUMPDEST, opAt 122 .XOR,
   pushAt 123 2 298, opAt 124 .JUMPI,
   pushAt 125 0 0, pushAt 126 1 32]

def checkEarlyPath : List Located :=
  [pushAt 113 0 0, opAt 114 .CALLDATALOAD,
   opAt 115 (.Dup ⟨0, by decide⟩),
   pushAt 116 32 KnownInputData.fullWord,
   opAt 117 .JUMPDEST, opAt 118 .JUMPDEST, opAt 119 .JUMPDEST,
   opAt 120 .JUMPDEST, opAt 121 .JUMPDEST, opAt 122 .XOR,
   pushAt 123 2 298, opAt 124 .JUMPI,
   opAt 158 .JUMPDEST, opAt 159 .POP]

def loopPath : List Located :=
  [opAt 127 .JUMPDEST, opAt 128 (.Swap ⟨0, by decide⟩),
   opAt 129 (.Dup ⟨1, by decide⟩), opAt 130 .CALLDATALOAD,
   opAt 131 (.Dup ⟨3, by decide⟩), opAt 132 .XOR, opAt 133 .OR,
   opAt 134 (.Swap ⟨0, by decide⟩), pushAt 135 1 32, opAt 136 .ADD,
   pushAt 137 2 992, opAt 138 (.Dup ⟨1, by decide⟩), opAt 139 .LT,
   pushAt 140 1 240, opAt 141 .JUMPI]

def tailPath : List Located :=
  [opAt 142 .CALLDATALOAD, opAt 143 (.Dup ⟨2, by decide⟩),
   opAt 144 .XOR, pushAt 145 1 192, opAt 146 .SHR, opAt 147 .OR,
   opAt 148 (.Swap ⟨0, by decide⟩), opAt 149 .POP,
   pushAt 150 1 3, opAt 151 .JUMPI]

def returnPath : List Located :=
  [pushAt 152 20 972889429405991776604892044862621566948497025487,
   pushAt 153 0 0, opAt 154 .MSTORE, pushAt 155 1 32,
   pushAt 156 0 0, opAt 157 .RETURN]

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

def sizeMatched (input : ByteArray) : State := atPC input 0xbf
def fallbackState (input : ByteArray) : State := atPC input 0x3

def loopState (input : ByteArray) (n : Nat) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 0xf0
    stack := [UInt256.ofNat (32 * (n + 1)), loopAcc input n, referenceWord input] }

def loopExitState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 0x103
    stack := [UInt256.ofNat 992, loopAcc input 30, referenceWord input] }

def returnEntry (input : ByteArray) : State := atPC input 0x10f

def storeWord (memory : ByteArray) (address : Nat) (word : UInt256) : ByteArray :=
  MachineState.writeBytes memory (Data.Bytes.natToBytesPadded word.toNat 32) address

def answerMemory : ByteArray :=
  storeWord ByteArray.empty 0 ExactGuardSpec.paddedDigestWord

def returnedState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 0x129
    memory := answerMemory
    activeWords := UInt256.ofNat 1
    halt := .Returned
    hReturn := MachineState.readPadded answerMemory 0 32 }

abbrev run := Challenge.EvmProof.Stepper.runLocatedBlock
  (artifact := Artifact.submissionArtifact) (fork := .Osaka)

/- Freeze the concrete direct-guard range so symbolic path reduction never
   unfolds the complete generated artifact merely to advance a program counter. -/
@[simp] theorem pc_cls98 :
    Artifact.submissionArtifact.instructionPC 98 = 0xa9 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_cls99 :
    Artifact.submissionArtifact.instructionPC 99 = 0xaa := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_cls101 :
    Artifact.submissionArtifact.instructionPC 101 = 0xae := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_cls103 :
    Artifact.submissionArtifact.instructionPC 103 = 0xb0 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_cls104 :
    Artifact.submissionArtifact.instructionPC 104 = 0xb1 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_cls105 :
    Artifact.submissionArtifact.instructionPC 105 = 0xb4 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_cls106 :
    Artifact.submissionArtifact.instructionPC 106 = 0xb5 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_cls108 :
    Artifact.submissionArtifact.instructionPC 108 = 0xb9 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_cls109 :
    Artifact.submissionArtifact.instructionPC 109 = 0xba := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_cls110 :
    Artifact.submissionArtifact.instructionPC 110 = 0xbb := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2813 :
    Artifact.submissionArtifact.instructionPC 97 = 0xa8 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2814 :
    Artifact.submissionArtifact.instructionPC 102 = 0xaf := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2815 :
    Artifact.submissionArtifact.instructionPC 107 = 0xb6 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2816 :
    Artifact.submissionArtifact.instructionPC 100 = 0xad := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2817 :
    Artifact.submissionArtifact.instructionPC 111 = 0xbc := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2818 :
    Artifact.submissionArtifact.instructionPC 112 = 0xbe := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2819 :
    Artifact.submissionArtifact.instructionPC 113 = 0xbf := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2820 :
    Artifact.submissionArtifact.instructionPC 114 = 0xc0 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2821 :
    Artifact.submissionArtifact.instructionPC 115 = 0xc1 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2822 :
    Artifact.submissionArtifact.instructionPC 116 = 0xc2 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2823 :
    Artifact.submissionArtifact.instructionPC 122 = 0xe8 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2824 :
    Artifact.submissionArtifact.instructionPC 123 = 0xe9 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2825 :
    Artifact.submissionArtifact.instructionPC 124 = 0xec := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2826 :
    Artifact.submissionArtifact.instructionPC 125 = 0xed := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2827 :
    Artifact.submissionArtifact.instructionPC 126 = 0xee := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2828 :
    Artifact.submissionArtifact.instructionPC 127 = 0xf0 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2829 :
    Artifact.submissionArtifact.instructionPC 128 = 0xf1 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2830 :
    Artifact.submissionArtifact.instructionPC 129 = 0xf2 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2831 :
    Artifact.submissionArtifact.instructionPC 130 = 0xf3 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2832 :
    Artifact.submissionArtifact.instructionPC 131 = 0xf4 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2833 :
    Artifact.submissionArtifact.instructionPC 132 = 0xf5 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2834 :
    Artifact.submissionArtifact.instructionPC 133 = 0xf6 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2835 :
    Artifact.submissionArtifact.instructionPC 134 = 0xf7 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2836 :
    Artifact.submissionArtifact.instructionPC 135 = 0xf8 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2837 :
    Artifact.submissionArtifact.instructionPC 136 = 0xfa := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2838 :
    Artifact.submissionArtifact.instructionPC 137 = 0xfb := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2839 :
    Artifact.submissionArtifact.instructionPC 138 = 0xfe := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2840 :
    Artifact.submissionArtifact.instructionPC 139 = 0xff := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2841 :
    Artifact.submissionArtifact.instructionPC 140 = 0x100 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2842 :
    Artifact.submissionArtifact.instructionPC 141 = 0x102 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2843 :
    Artifact.submissionArtifact.instructionPC 142 = 0x103 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2844 :
    Artifact.submissionArtifact.instructionPC 143 = 0x104 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2845 :
    Artifact.submissionArtifact.instructionPC 144 = 0x105 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2846 :
    Artifact.submissionArtifact.instructionPC 145 = 0x106 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2847 :
    Artifact.submissionArtifact.instructionPC 146 = 0x108 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2848 :
    Artifact.submissionArtifact.instructionPC 147 = 0x109 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2849 :
    Artifact.submissionArtifact.instructionPC 148 = 0x10a := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2850 :
    Artifact.submissionArtifact.instructionPC 148 = 0x10a := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2851 :
    Artifact.submissionArtifact.instructionPC 149 = 0x10b := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2852 :
    Artifact.submissionArtifact.instructionPC 150 = 0x10c := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2853 :
    Artifact.submissionArtifact.instructionPC 151 = 0x10e := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2854 :
    Artifact.submissionArtifact.instructionPC 152 = 0x10f := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2855 :
    Artifact.submissionArtifact.instructionPC 153 = 0x124 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2856 :
    Artifact.submissionArtifact.instructionPC 154 = 0x125 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2857 :
    Artifact.submissionArtifact.instructionPC 155 = 0x126 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2858 :
    Artifact.submissionArtifact.instructionPC 156 = 0x128 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2859 :
    Artifact.submissionArtifact.instructionPC 157 = 0x129 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2860 :
    Artifact.submissionArtifact.instructionPC 158 = 0x12a := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2861 :
    Artifact.submissionArtifact.instructionPC 159 = 0x12b := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2862 :
    Artifact.submissionArtifact.instructionPC 160 = 0x12c := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2863 :
    Artifact.submissionArtifact.instructionPC 160 = 0x12c := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl

end Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard
