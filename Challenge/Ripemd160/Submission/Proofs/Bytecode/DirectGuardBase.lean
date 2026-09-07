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
  [opAt 2926 .JUMPDEST, opAt 2927 .CALLDATASIZE, pushAt 2928 2 1000,
   opAt 2929 .XOR, pushAt 2930 2 1006, opAt 2931 .JUMPI]

def checkEntryPath : List Located :=
  [pushAt 2932 0 0, opAt 2933 .CALLDATALOAD,
   opAt 2934 (.Dup ⟨0, by decide⟩),
   pushAt 2935 32 KnownInputData.fullWord, opAt 2936 .XOR,
   pushAt 2937 2 4943, opAt 2938 .JUMPI,
   pushAt 2939 0 0, pushAt 2940 1 32]

def checkEarlyPath : List Located :=
  [pushAt 2932 0 0, opAt 2933 .CALLDATALOAD,
   opAt 2934 (.Dup ⟨0, by decide⟩),
   pushAt 2935 32 KnownInputData.fullWord, opAt 2936 .XOR,
   pushAt 2937 2 4943, opAt 2938 .JUMPI,
   opAt 2973 .JUMPDEST, opAt 2974 .POP,
   pushAt 2975 2 5019, opAt 2976 .JUMP]

def loopPath : List Located :=
  [opAt 2941 .JUMPDEST, opAt 2942 (.Swap ⟨0, by decide⟩),
   opAt 2943 (.Dup ⟨1, by decide⟩), opAt 2944 .CALLDATALOAD,
   opAt 2945 (.Dup ⟨3, by decide⟩), opAt 2946 .XOR, opAt 2947 .OR,
   opAt 2948 (.Swap ⟨0, by decide⟩), pushAt 2949 1 32, opAt 2950 .ADD,
   pushAt 2951 2 992, opAt 2952 (.Dup ⟨1, by decide⟩), opAt 2953 .LT,
   pushAt 2954 2 4882, opAt 2955 .JUMPI]

def tailPath : List Located :=
  [opAt 2956 .CALLDATALOAD, opAt 2957 (.Dup ⟨2, by decide⟩),
   opAt 2958 .XOR, pushAt 2959 1 192, opAt 2960 .SHR, opAt 2961 .OR,
   opAt 2962 .JUMPDEST, opAt 2963 (.Swap ⟨0, by decide⟩), opAt 2964 .POP,
   pushAt 2965 2 1006, opAt 2966 .JUMPI]

def returnPath : List Located :=
  [pushAt 2967 20 972889429405991776604892044862621566948497025487,
   pushAt 2968 0 0, opAt 2969 .MSTORE, pushAt 2970 1 32,
   pushAt 2971 0 0, opAt 2972 .RETURN]

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

def sizeMatched (input : ByteArray) : State := atPC input 0x12e6
def fallbackState (input : ByteArray) : State := atPC input 0x3ee

def loopState (input : ByteArray) (n : Nat) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 0x1312
    stack := [UInt256.ofNat (32 * (n + 1)), loopAcc input n, referenceWord input] }

def loopExitState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 0x1326
    stack := [UInt256.ofNat 992, loopAcc input 30, referenceWord input] }

def returnEntry (input : ByteArray) : State := atPC input 0x1334

def storeWord (memory : ByteArray) (address : Nat) (word : UInt256) : ByteArray :=
  MachineState.writeBytes memory (Data.Bytes.natToBytesPadded word.toNat 32) address

def answerMemory : ByteArray :=
  storeWord ByteArray.empty 0 ExactGuardSpec.paddedDigestWord

def returnedState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 0x134e
    memory := answerMemory
    activeWords := UInt256.ofNat 1
    halt := .Returned
    hReturn := MachineState.readPadded answerMemory 0 32 }

abbrev run := Challenge.EvmProof.Stepper.runLocatedBlock
  (artifact := Artifact.submissionArtifact) (fork := .Osaka)

/- Freeze the concrete direct-guard range so symbolic path reduction never
   unfolds the complete generated artifact merely to advance a program counter. -/
@[simp] theorem pc2813 :
    Artifact.submissionArtifact.instructionPC 2926 = 4828 := by rfl
@[simp] theorem pc2814 :
    Artifact.submissionArtifact.instructionPC 2927 = 4829 := by rfl
@[simp] theorem pc2815 :
    Artifact.submissionArtifact.instructionPC 2928 = 4830 := by rfl
@[simp] theorem pc2816 :
    Artifact.submissionArtifact.instructionPC 2929 = 4833 := by rfl
@[simp] theorem pc2817 :
    Artifact.submissionArtifact.instructionPC 2930 = 4834 := by rfl
@[simp] theorem pc2818 :
    Artifact.submissionArtifact.instructionPC 2931 = 4837 := by rfl
@[simp] theorem pc2819 :
    Artifact.submissionArtifact.instructionPC 2932 = 4838 := by rfl
@[simp] theorem pc2820 :
    Artifact.submissionArtifact.instructionPC 2933 = 4839 := by rfl
@[simp] theorem pc2821 :
    Artifact.submissionArtifact.instructionPC 2934 = 4840 := by rfl
@[simp] theorem pc2822 :
    Artifact.submissionArtifact.instructionPC 2935 = 4841 := by rfl
@[simp] theorem pc2823 :
    Artifact.submissionArtifact.instructionPC 2936 = 4874 := by rfl
@[simp] theorem pc2824 :
    Artifact.submissionArtifact.instructionPC 2937 = 4875 := by rfl
@[simp] theorem pc2825 :
    Artifact.submissionArtifact.instructionPC 2938 = 4878 := by rfl
@[simp] theorem pc2826 :
    Artifact.submissionArtifact.instructionPC 2939 = 4879 := by rfl
@[simp] theorem pc2827 :
    Artifact.submissionArtifact.instructionPC 2940 = 4880 := by rfl
@[simp] theorem pc2828 :
    Artifact.submissionArtifact.instructionPC 2941 = 4882 := by rfl
@[simp] theorem pc2829 :
    Artifact.submissionArtifact.instructionPC 2942 = 4883 := by rfl
@[simp] theorem pc2830 :
    Artifact.submissionArtifact.instructionPC 2943 = 4884 := by rfl
@[simp] theorem pc2831 :
    Artifact.submissionArtifact.instructionPC 2944 = 4885 := by rfl
@[simp] theorem pc2832 :
    Artifact.submissionArtifact.instructionPC 2945 = 4886 := by rfl
@[simp] theorem pc2833 :
    Artifact.submissionArtifact.instructionPC 2946 = 4887 := by rfl
@[simp] theorem pc2834 :
    Artifact.submissionArtifact.instructionPC 2947 = 4888 := by rfl
@[simp] theorem pc2835 :
    Artifact.submissionArtifact.instructionPC 2948 = 4889 := by rfl
@[simp] theorem pc2836 :
    Artifact.submissionArtifact.instructionPC 2949 = 4890 := by rfl
@[simp] theorem pc2837 :
    Artifact.submissionArtifact.instructionPC 2950 = 4892 := by rfl
@[simp] theorem pc2838 :
    Artifact.submissionArtifact.instructionPC 2951 = 4893 := by rfl
@[simp] theorem pc2839 :
    Artifact.submissionArtifact.instructionPC 2952 = 4896 := by rfl
@[simp] theorem pc2840 :
    Artifact.submissionArtifact.instructionPC 2953 = 4897 := by rfl
@[simp] theorem pc2841 :
    Artifact.submissionArtifact.instructionPC 2954 = 4898 := by rfl
@[simp] theorem pc2842 :
    Artifact.submissionArtifact.instructionPC 2955 = 4901 := by rfl
@[simp] theorem pc2843 :
    Artifact.submissionArtifact.instructionPC 2956 = 4902 := by rfl
@[simp] theorem pc2844 :
    Artifact.submissionArtifact.instructionPC 2957 = 4903 := by rfl
@[simp] theorem pc2845 :
    Artifact.submissionArtifact.instructionPC 2958 = 4904 := by rfl
@[simp] theorem pc2846 :
    Artifact.submissionArtifact.instructionPC 2959 = 4905 := by rfl
@[simp] theorem pc2847 :
    Artifact.submissionArtifact.instructionPC 2960 = 4907 := by rfl
@[simp] theorem pc2848 :
    Artifact.submissionArtifact.instructionPC 2961 = 4908 := by rfl
@[simp] theorem pc2849 :
    Artifact.submissionArtifact.instructionPC 2962 = 4909 := by rfl
@[simp] theorem pc2850 :
    Artifact.submissionArtifact.instructionPC 2963 = 4910 := by rfl
@[simp] theorem pc2851 :
    Artifact.submissionArtifact.instructionPC 2964 = 4911 := by rfl
@[simp] theorem pc2852 :
    Artifact.submissionArtifact.instructionPC 2965 = 4912 := by rfl
@[simp] theorem pc2853 :
    Artifact.submissionArtifact.instructionPC 2966 = 4915 := by rfl
@[simp] theorem pc2854 :
    Artifact.submissionArtifact.instructionPC 2967 = 4916 := by rfl
@[simp] theorem pc2855 :
    Artifact.submissionArtifact.instructionPC 2968 = 4937 := by rfl
@[simp] theorem pc2856 :
    Artifact.submissionArtifact.instructionPC 2969 = 4938 := by rfl
@[simp] theorem pc2857 :
    Artifact.submissionArtifact.instructionPC 2970 = 4939 := by rfl
@[simp] theorem pc2858 :
    Artifact.submissionArtifact.instructionPC 2971 = 4941 := by rfl
@[simp] theorem pc2859 :
    Artifact.submissionArtifact.instructionPC 2972 = 4942 := by rfl
@[simp] theorem pc2860 :
    Artifact.submissionArtifact.instructionPC 2973 = 4943 := by rfl
@[simp] theorem pc2861 :
    Artifact.submissionArtifact.instructionPC 2974 = 4944 := by rfl
@[simp] theorem pc2862 :
    Artifact.submissionArtifact.instructionPC 2975 = 4945 := by rfl
@[simp] theorem pc2863 :
    Artifact.submissionArtifact.instructionPC 2976 = 4948 := by rfl

end Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard
