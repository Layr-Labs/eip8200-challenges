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
  [opAt 2919 .JUMPDEST, opAt 2920 .CALLDATASIZE, pushAt 2921 2 1000,
   opAt 2922 .XOR, pushAt 2923 2 1006, opAt 2924 .JUMPI]

def checkEntryPath : List Located :=
  [pushAt 2925 0 0, opAt 2926 .CALLDATALOAD,
   opAt 2927 (.Dup ⟨0, by decide⟩),
   pushAt 2928 32 KnownInputData.fullWord, opAt 2929 .XOR,
   pushAt 2930 2 4952, opAt 2931 .JUMPI,
   pushAt 2932 0 0, pushAt 2933 1 32]

def checkEarlyPath : List Located :=
  [pushAt 2925 0 0, opAt 2926 .CALLDATALOAD,
   opAt 2927 (.Dup ⟨0, by decide⟩),
   pushAt 2928 32 KnownInputData.fullWord, opAt 2929 .XOR,
   pushAt 2930 2 4952, opAt 2931 .JUMPI,
   opAt 2966 .JUMPDEST, opAt 2967 .POP,
   pushAt 2968 2 5028, opAt 2969 .JUMP]

def loopPath : List Located :=
  [opAt 2934 .JUMPDEST, opAt 2935 (.Swap ⟨0, by decide⟩),
   opAt 2936 (.Dup ⟨1, by decide⟩), opAt 2937 .CALLDATALOAD,
   opAt 2938 (.Dup ⟨3, by decide⟩), opAt 2939 .XOR, opAt 2940 .OR,
   opAt 2941 (.Swap ⟨0, by decide⟩), pushAt 2942 1 32, opAt 2943 .ADD,
   pushAt 2944 2 992, opAt 2945 (.Dup ⟨1, by decide⟩), opAt 2946 .LT,
   pushAt 2947 2 4891, opAt 2948 .JUMPI]

def tailPath : List Located :=
  [opAt 2949 .CALLDATALOAD, opAt 2950 (.Dup ⟨2, by decide⟩),
   opAt 2951 .XOR, pushAt 2952 1 192, opAt 2953 .SHR, opAt 2954 .OR,
   opAt 2955 .JUMPDEST, opAt 2956 (.Swap ⟨0, by decide⟩), opAt 2957 .POP,
   pushAt 2958 2 1006, opAt 2959 .JUMPI]

def returnPath : List Located :=
  [pushAt 2960 20 972889429405991776604892044862621566948497025487,
   pushAt 2961 0 0, opAt 2962 .MSTORE, pushAt 2963 1 32,
   pushAt 2964 0 0, opAt 2965 .RETURN]

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

def sizeMatched (input : ByteArray) : State := atPC input 0x12ef
def fallbackState (input : ByteArray) : State := atPC input 0x3ee

def loopState (input : ByteArray) (n : Nat) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 0x131b
    stack := [UInt256.ofNat (32 * (n + 1)), loopAcc input n, referenceWord input] }

def loopExitState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 0x132f
    stack := [UInt256.ofNat 992, loopAcc input 30, referenceWord input] }

def returnEntry (input : ByteArray) : State := atPC input 0x133d

def storeWord (memory : ByteArray) (address : Nat) (word : UInt256) : ByteArray :=
  MachineState.writeBytes memory (Data.Bytes.natToBytesPadded word.toNat 32) address

def answerMemory : ByteArray :=
  storeWord ByteArray.empty 0 ExactGuardSpec.paddedDigestWord

def returnedState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 0x1357
    memory := answerMemory
    activeWords := UInt256.ofNat 1
    halt := .Returned
    hReturn := MachineState.readPadded answerMemory 0 32 }

abbrev run := Challenge.EvmProof.Stepper.runLocatedBlock
  (artifact := Artifact.submissionArtifact) (fork := .Osaka)

/- Freeze the concrete direct-guard range so symbolic path reduction never
   unfolds the complete generated artifact merely to advance a program counter. -/
@[simp] theorem pc2813 :
    Artifact.submissionArtifact.instructionPC 2919 = 4837 := by rfl
@[simp] theorem pc2814 :
    Artifact.submissionArtifact.instructionPC 2920 = 4838 := by rfl
@[simp] theorem pc2815 :
    Artifact.submissionArtifact.instructionPC 2921 = 4839 := by rfl
@[simp] theorem pc2816 :
    Artifact.submissionArtifact.instructionPC 2922 = 4842 := by rfl
@[simp] theorem pc2817 :
    Artifact.submissionArtifact.instructionPC 2923 = 4843 := by rfl
@[simp] theorem pc2818 :
    Artifact.submissionArtifact.instructionPC 2924 = 4846 := by rfl
@[simp] theorem pc2819 :
    Artifact.submissionArtifact.instructionPC 2925 = 4847 := by rfl
@[simp] theorem pc2820 :
    Artifact.submissionArtifact.instructionPC 2926 = 4848 := by rfl
@[simp] theorem pc2821 :
    Artifact.submissionArtifact.instructionPC 2927 = 4849 := by rfl
@[simp] theorem pc2822 :
    Artifact.submissionArtifact.instructionPC 2928 = 4850 := by rfl
@[simp] theorem pc2823 :
    Artifact.submissionArtifact.instructionPC 2929 = 4883 := by rfl
@[simp] theorem pc2824 :
    Artifact.submissionArtifact.instructionPC 2930 = 4884 := by rfl
@[simp] theorem pc2825 :
    Artifact.submissionArtifact.instructionPC 2931 = 4887 := by rfl
@[simp] theorem pc2826 :
    Artifact.submissionArtifact.instructionPC 2932 = 4888 := by rfl
@[simp] theorem pc2827 :
    Artifact.submissionArtifact.instructionPC 2933 = 4889 := by rfl
@[simp] theorem pc2828 :
    Artifact.submissionArtifact.instructionPC 2934 = 4891 := by rfl
@[simp] theorem pc2829 :
    Artifact.submissionArtifact.instructionPC 2935 = 4892 := by rfl
@[simp] theorem pc2830 :
    Artifact.submissionArtifact.instructionPC 2936 = 4893 := by rfl
@[simp] theorem pc2831 :
    Artifact.submissionArtifact.instructionPC 2937 = 4894 := by rfl
@[simp] theorem pc2832 :
    Artifact.submissionArtifact.instructionPC 2938 = 4895 := by rfl
@[simp] theorem pc2833 :
    Artifact.submissionArtifact.instructionPC 2939 = 4896 := by rfl
@[simp] theorem pc2834 :
    Artifact.submissionArtifact.instructionPC 2940 = 4897 := by rfl
@[simp] theorem pc2835 :
    Artifact.submissionArtifact.instructionPC 2941 = 4898 := by rfl
@[simp] theorem pc2836 :
    Artifact.submissionArtifact.instructionPC 2942 = 4899 := by rfl
@[simp] theorem pc2837 :
    Artifact.submissionArtifact.instructionPC 2943 = 4901 := by rfl
@[simp] theorem pc2838 :
    Artifact.submissionArtifact.instructionPC 2944 = 4902 := by rfl
@[simp] theorem pc2839 :
    Artifact.submissionArtifact.instructionPC 2945 = 4905 := by rfl
@[simp] theorem pc2840 :
    Artifact.submissionArtifact.instructionPC 2946 = 4906 := by rfl
@[simp] theorem pc2841 :
    Artifact.submissionArtifact.instructionPC 2947 = 4907 := by rfl
@[simp] theorem pc2842 :
    Artifact.submissionArtifact.instructionPC 2948 = 4910 := by rfl
@[simp] theorem pc2843 :
    Artifact.submissionArtifact.instructionPC 2949 = 4911 := by rfl
@[simp] theorem pc2844 :
    Artifact.submissionArtifact.instructionPC 2950 = 4912 := by rfl
@[simp] theorem pc2845 :
    Artifact.submissionArtifact.instructionPC 2951 = 4913 := by rfl
@[simp] theorem pc2846 :
    Artifact.submissionArtifact.instructionPC 2952 = 4914 := by rfl
@[simp] theorem pc2847 :
    Artifact.submissionArtifact.instructionPC 2953 = 4916 := by rfl
@[simp] theorem pc2848 :
    Artifact.submissionArtifact.instructionPC 2954 = 4917 := by rfl
@[simp] theorem pc2849 :
    Artifact.submissionArtifact.instructionPC 2955 = 4918 := by rfl
@[simp] theorem pc2850 :
    Artifact.submissionArtifact.instructionPC 2956 = 4919 := by rfl
@[simp] theorem pc2851 :
    Artifact.submissionArtifact.instructionPC 2957 = 4920 := by rfl
@[simp] theorem pc2852 :
    Artifact.submissionArtifact.instructionPC 2958 = 4921 := by rfl
@[simp] theorem pc2853 :
    Artifact.submissionArtifact.instructionPC 2959 = 4924 := by rfl
@[simp] theorem pc2854 :
    Artifact.submissionArtifact.instructionPC 2960 = 4925 := by rfl
@[simp] theorem pc2855 :
    Artifact.submissionArtifact.instructionPC 2961 = 4946 := by rfl
@[simp] theorem pc2856 :
    Artifact.submissionArtifact.instructionPC 2962 = 4947 := by rfl
@[simp] theorem pc2857 :
    Artifact.submissionArtifact.instructionPC 2963 = 4948 := by rfl
@[simp] theorem pc2858 :
    Artifact.submissionArtifact.instructionPC 2964 = 4950 := by rfl
@[simp] theorem pc2859 :
    Artifact.submissionArtifact.instructionPC 2965 = 4951 := by rfl
@[simp] theorem pc2860 :
    Artifact.submissionArtifact.instructionPC 2966 = 4952 := by rfl
@[simp] theorem pc2861 :
    Artifact.submissionArtifact.instructionPC 2967 = 4953 := by rfl
@[simp] theorem pc2862 :
    Artifact.submissionArtifact.instructionPC 2968 = 4954 := by rfl
@[simp] theorem pc2863 :
    Artifact.submissionArtifact.instructionPC 2969 = 4957 := by rfl

end Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard
