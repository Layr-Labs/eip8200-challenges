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
  [opAt 2985 .JUMPDEST, opAt 2986 .CALLDATASIZE, pushAt 2987 2 1000,
   opAt 2988 .XOR, pushAt 2989 2 979, opAt 2990 .JUMPI]

def checkEntryPath : List Located :=
  [pushAt 2991 0 0, opAt 2992 .CALLDATALOAD,
   opAt 2993 (.Dup ⟨0, by decide⟩),
   pushAt 2994 32 KnownInputData.fullWord, opAt 2995 .XOR,
   pushAt 2996 2 4950, opAt 2997 .JUMPI,
   pushAt 2998 0 0, pushAt 2999 1 32]

def checkEarlyPath : List Located :=
  [pushAt 2991 0 0, opAt 2992 .CALLDATALOAD,
   opAt 2993 (.Dup ⟨0, by decide⟩),
   pushAt 2994 32 KnownInputData.fullWord, opAt 2995 .XOR,
   pushAt 2996 2 4950, opAt 2997 .JUMPI,
   opAt 3032 .JUMPDEST, opAt 3033 .POP,
   pushAt 3034 2 4956, opAt 3035 .JUMP]

def loopPath : List Located :=
  [opAt 3000 .JUMPDEST, opAt 3001 (.Swap ⟨0, by decide⟩),
   opAt 3002 (.Dup ⟨1, by decide⟩), opAt 3003 .CALLDATALOAD,
   opAt 3004 (.Dup ⟨3, by decide⟩), opAt 3005 .XOR, opAt 3006 .OR,
   opAt 3007 (.Swap ⟨0, by decide⟩), pushAt 3008 1 32, opAt 3009 .ADD,
   pushAt 3010 2 992, opAt 3011 (.Dup ⟨1, by decide⟩), opAt 3012 .LT,
   pushAt 3013 2 4889, opAt 3014 .JUMPI]

def tailPath : List Located :=
  [opAt 3015 .CALLDATALOAD, opAt 3016 (.Dup ⟨2, by decide⟩),
   opAt 3017 .XOR, pushAt 3018 1 192, opAt 3019 .SHR, opAt 3020 .OR,
   opAt 3021 .JUMPDEST, opAt 3022 (.Swap ⟨0, by decide⟩), opAt 3023 .POP,
   pushAt 3024 2 979, opAt 3025 .JUMPI]

def returnPath : List Located :=
  [pushAt 3026 20 972889429405991776604892044862621566948497025487,
   pushAt 3027 0 0, opAt 3028 .MSTORE, pushAt 3029 1 32,
   pushAt 3030 0 0, opAt 3031 .RETURN]

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

def sizeMatched (input : ByteArray) : State := atPC input 0x12ed
def fallbackState (input : ByteArray) : State := atPC input 0x3d3

def loopState (input : ByteArray) (n : Nat) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 0x1319
    stack := [UInt256.ofNat (32 * (n + 1)), loopAcc input n, referenceWord input] }

def loopExitState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 0x132d
    stack := [UInt256.ofNat 992, loopAcc input 30, referenceWord input] }

def returnEntry (input : ByteArray) : State := atPC input 0x133b

def storeWord (memory : ByteArray) (address : Nat) (word : UInt256) : ByteArray :=
  MachineState.writeBytes memory (Data.Bytes.natToBytesPadded word.toNat 32) address

def answerMemory : ByteArray :=
  storeWord ByteArray.empty 0 ExactGuardSpec.paddedDigestWord

def returnedState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 0x1355
    memory := answerMemory
    activeWords := UInt256.ofNat 1
    halt := .Returned
    hReturn := MachineState.readPadded answerMemory 0 32 }

abbrev run := Challenge.EvmProof.Stepper.runLocatedBlock
  (artifact := Artifact.submissionArtifact) (fork := .Osaka)

/- Freeze the concrete direct-guard range so symbolic path reduction never
   unfolds the complete generated artifact merely to advance a program counter. -/
@[simp] theorem pc2813 :
    Artifact.submissionArtifact.instructionPC 2985 = 4835 := by rfl
@[simp] theorem pc2814 :
    Artifact.submissionArtifact.instructionPC 2986 = 4836 := by rfl
@[simp] theorem pc2815 :
    Artifact.submissionArtifact.instructionPC 2987 = 4837 := by rfl
@[simp] theorem pc2816 :
    Artifact.submissionArtifact.instructionPC 2988 = 4840 := by rfl
@[simp] theorem pc2817 :
    Artifact.submissionArtifact.instructionPC 2989 = 4841 := by rfl
@[simp] theorem pc2818 :
    Artifact.submissionArtifact.instructionPC 2990 = 4844 := by rfl
@[simp] theorem pc2819 :
    Artifact.submissionArtifact.instructionPC 2991 = 4845 := by rfl
@[simp] theorem pc2820 :
    Artifact.submissionArtifact.instructionPC 2992 = 4846 := by rfl
@[simp] theorem pc2821 :
    Artifact.submissionArtifact.instructionPC 2993 = 4847 := by rfl
@[simp] theorem pc2822 :
    Artifact.submissionArtifact.instructionPC 2994 = 4848 := by rfl
@[simp] theorem pc2823 :
    Artifact.submissionArtifact.instructionPC 2995 = 4881 := by rfl
@[simp] theorem pc2824 :
    Artifact.submissionArtifact.instructionPC 2996 = 4882 := by rfl
@[simp] theorem pc2825 :
    Artifact.submissionArtifact.instructionPC 2997 = 4885 := by rfl
@[simp] theorem pc2826 :
    Artifact.submissionArtifact.instructionPC 2998 = 4886 := by rfl
@[simp] theorem pc2827 :
    Artifact.submissionArtifact.instructionPC 2999 = 4887 := by rfl
@[simp] theorem pc2828 :
    Artifact.submissionArtifact.instructionPC 3000 = 4889 := by rfl
@[simp] theorem pc2829 :
    Artifact.submissionArtifact.instructionPC 3001 = 4890 := by rfl
@[simp] theorem pc2830 :
    Artifact.submissionArtifact.instructionPC 3002 = 4891 := by rfl
@[simp] theorem pc2831 :
    Artifact.submissionArtifact.instructionPC 3003 = 4892 := by rfl
@[simp] theorem pc2832 :
    Artifact.submissionArtifact.instructionPC 3004 = 4893 := by rfl
@[simp] theorem pc2833 :
    Artifact.submissionArtifact.instructionPC 3005 = 4894 := by rfl
@[simp] theorem pc2834 :
    Artifact.submissionArtifact.instructionPC 3006 = 4895 := by rfl
@[simp] theorem pc2835 :
    Artifact.submissionArtifact.instructionPC 3007 = 4896 := by rfl
@[simp] theorem pc2836 :
    Artifact.submissionArtifact.instructionPC 3008 = 4897 := by rfl
@[simp] theorem pc2837 :
    Artifact.submissionArtifact.instructionPC 3009 = 4899 := by rfl
@[simp] theorem pc2838 :
    Artifact.submissionArtifact.instructionPC 3010 = 4900 := by rfl
@[simp] theorem pc2839 :
    Artifact.submissionArtifact.instructionPC 3011 = 4903 := by rfl
@[simp] theorem pc2840 :
    Artifact.submissionArtifact.instructionPC 3012 = 4904 := by rfl
@[simp] theorem pc2841 :
    Artifact.submissionArtifact.instructionPC 3013 = 4905 := by rfl
@[simp] theorem pc2842 :
    Artifact.submissionArtifact.instructionPC 3014 = 4908 := by rfl
@[simp] theorem pc2843 :
    Artifact.submissionArtifact.instructionPC 3015 = 4909 := by rfl
@[simp] theorem pc2844 :
    Artifact.submissionArtifact.instructionPC 3016 = 4910 := by rfl
@[simp] theorem pc2845 :
    Artifact.submissionArtifact.instructionPC 3017 = 4911 := by rfl
@[simp] theorem pc2846 :
    Artifact.submissionArtifact.instructionPC 3018 = 4912 := by rfl
@[simp] theorem pc2847 :
    Artifact.submissionArtifact.instructionPC 3019 = 4914 := by rfl
@[simp] theorem pc2848 :
    Artifact.submissionArtifact.instructionPC 3020 = 4915 := by rfl
@[simp] theorem pc2849 :
    Artifact.submissionArtifact.instructionPC 3021 = 4916 := by rfl
@[simp] theorem pc2850 :
    Artifact.submissionArtifact.instructionPC 3022 = 4917 := by rfl
@[simp] theorem pc2851 :
    Artifact.submissionArtifact.instructionPC 3023 = 4918 := by rfl
@[simp] theorem pc2852 :
    Artifact.submissionArtifact.instructionPC 3024 = 4919 := by rfl
@[simp] theorem pc2853 :
    Artifact.submissionArtifact.instructionPC 3025 = 4922 := by rfl
@[simp] theorem pc2854 :
    Artifact.submissionArtifact.instructionPC 3026 = 4923 := by rfl
@[simp] theorem pc2855 :
    Artifact.submissionArtifact.instructionPC 3027 = 4944 := by rfl
@[simp] theorem pc2856 :
    Artifact.submissionArtifact.instructionPC 3028 = 4945 := by rfl
@[simp] theorem pc2857 :
    Artifact.submissionArtifact.instructionPC 3029 = 4946 := by rfl
@[simp] theorem pc2858 :
    Artifact.submissionArtifact.instructionPC 3030 = 4948 := by rfl
@[simp] theorem pc2859 :
    Artifact.submissionArtifact.instructionPC 3031 = 4949 := by rfl
@[simp] theorem pc2860 :
    Artifact.submissionArtifact.instructionPC 3032 = 4950 := by rfl
@[simp] theorem pc2861 :
    Artifact.submissionArtifact.instructionPC 3033 = 4951 := by rfl
@[simp] theorem pc2862 :
    Artifact.submissionArtifact.instructionPC 3034 = 4952 := by rfl
@[simp] theorem pc2863 :
    Artifact.submissionArtifact.instructionPC 3035 = 4955 := by rfl

end Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard
