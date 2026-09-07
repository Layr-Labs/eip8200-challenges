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
  [opAt 2997 .JUMPDEST, opAt 2998 .CALLDATASIZE, pushAt 2999 2 1000,
   opAt 3000 .XOR, pushAt 3001 2 979, opAt 3002 .JUMPI]

def checkEntryPath : List Located :=
  [pushAt 3003 0 0, opAt 3004 .CALLDATALOAD,
   opAt 3005 (.Dup ⟨0, by decide⟩),
   pushAt 3006 32 KnownInputData.fullWord, opAt 3007 .XOR,
   pushAt 3008 2 4962, opAt 3009 .JUMPI,
   pushAt 3010 0 0, pushAt 3011 1 32]

def checkEarlyPath : List Located :=
  [pushAt 3003 0 0, opAt 3004 .CALLDATALOAD,
   opAt 3005 (.Dup ⟨0, by decide⟩),
   pushAt 3006 32 KnownInputData.fullWord, opAt 3007 .XOR,
   pushAt 3008 2 4962, opAt 3009 .JUMPI,
   opAt 3044 .JUMPDEST, opAt 3045 .POP,
   pushAt 3046 2 4968, opAt 3047 .JUMP]

def loopPath : List Located :=
  [opAt 3012 .JUMPDEST, opAt 3013 (.Swap ⟨0, by decide⟩),
   opAt 3014 (.Dup ⟨1, by decide⟩), opAt 3015 .CALLDATALOAD,
   opAt 3016 (.Dup ⟨3, by decide⟩), opAt 3017 .XOR, opAt 3018 .OR,
   opAt 3019 (.Swap ⟨0, by decide⟩), pushAt 3020 1 32, opAt 3021 .ADD,
   pushAt 3022 2 992, opAt 3023 (.Dup ⟨1, by decide⟩), opAt 3024 .LT,
   pushAt 3025 2 4901, opAt 3026 .JUMPI]

def tailPath : List Located :=
  [opAt 3027 .CALLDATALOAD, opAt 3028 (.Dup ⟨2, by decide⟩),
   opAt 3029 .XOR, pushAt 3030 1 192, opAt 3031 .SHR, opAt 3032 .OR,
   opAt 3033 .JUMPDEST, opAt 3034 (.Swap ⟨0, by decide⟩), opAt 3035 .POP,
   pushAt 3036 2 979, opAt 3037 .JUMPI]

def returnPath : List Located :=
  [pushAt 3038 20 972889429405991776604892044862621566948497025487,
   pushAt 3039 0 0, opAt 3040 .MSTORE, pushAt 3041 1 32,
   pushAt 3042 0 0, opAt 3043 .RETURN]

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

def sizeMatched (input : ByteArray) : State := atPC input 0x12f9
def fallbackState (input : ByteArray) : State := atPC input 0x3d3

def loopState (input : ByteArray) (n : Nat) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 0x1325
    stack := [UInt256.ofNat (32 * (n + 1)), loopAcc input n, referenceWord input] }

def loopExitState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 0x1339
    stack := [UInt256.ofNat 992, loopAcc input 30, referenceWord input] }

def returnEntry (input : ByteArray) : State := atPC input 0x1347

def storeWord (memory : ByteArray) (address : Nat) (word : UInt256) : ByteArray :=
  MachineState.writeBytes memory (Data.Bytes.natToBytesPadded word.toNat 32) address

def answerMemory : ByteArray :=
  storeWord ByteArray.empty 0 ExactGuardSpec.paddedDigestWord

def returnedState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 0x1361
    memory := answerMemory
    activeWords := UInt256.ofNat 1
    halt := .Returned
    hReturn := MachineState.readPadded answerMemory 0 32 }

abbrev run := Challenge.EvmProof.Stepper.runLocatedBlock
  (artifact := Artifact.submissionArtifact) (fork := .Osaka)

/- Freeze the concrete direct-guard range so symbolic path reduction never
   unfolds the complete generated artifact merely to advance a program counter. -/
@[simp] theorem pc2813 :
    Artifact.submissionArtifact.instructionPC 2997 = 4847 := by rfl
@[simp] theorem pc2814 :
    Artifact.submissionArtifact.instructionPC 2998 = 4848 := by rfl
@[simp] theorem pc2815 :
    Artifact.submissionArtifact.instructionPC 2999 = 4849 := by rfl
@[simp] theorem pc2816 :
    Artifact.submissionArtifact.instructionPC 3000 = 4852 := by rfl
@[simp] theorem pc2817 :
    Artifact.submissionArtifact.instructionPC 3001 = 4853 := by rfl
@[simp] theorem pc2818 :
    Artifact.submissionArtifact.instructionPC 3002 = 4856 := by rfl
@[simp] theorem pc2819 :
    Artifact.submissionArtifact.instructionPC 3003 = 4857 := by rfl
@[simp] theorem pc2820 :
    Artifact.submissionArtifact.instructionPC 3004 = 4858 := by rfl
@[simp] theorem pc2821 :
    Artifact.submissionArtifact.instructionPC 3005 = 4859 := by rfl
@[simp] theorem pc2822 :
    Artifact.submissionArtifact.instructionPC 3006 = 4860 := by rfl
@[simp] theorem pc2823 :
    Artifact.submissionArtifact.instructionPC 3007 = 4893 := by rfl
@[simp] theorem pc2824 :
    Artifact.submissionArtifact.instructionPC 3008 = 4894 := by rfl
@[simp] theorem pc2825 :
    Artifact.submissionArtifact.instructionPC 3009 = 4897 := by rfl
@[simp] theorem pc2826 :
    Artifact.submissionArtifact.instructionPC 3010 = 4898 := by rfl
@[simp] theorem pc2827 :
    Artifact.submissionArtifact.instructionPC 3011 = 4899 := by rfl
@[simp] theorem pc2828 :
    Artifact.submissionArtifact.instructionPC 3012 = 4901 := by rfl
@[simp] theorem pc2829 :
    Artifact.submissionArtifact.instructionPC 3013 = 4902 := by rfl
@[simp] theorem pc2830 :
    Artifact.submissionArtifact.instructionPC 3014 = 4903 := by rfl
@[simp] theorem pc2831 :
    Artifact.submissionArtifact.instructionPC 3015 = 4904 := by rfl
@[simp] theorem pc2832 :
    Artifact.submissionArtifact.instructionPC 3016 = 4905 := by rfl
@[simp] theorem pc2833 :
    Artifact.submissionArtifact.instructionPC 3017 = 4906 := by rfl
@[simp] theorem pc2834 :
    Artifact.submissionArtifact.instructionPC 3018 = 4907 := by rfl
@[simp] theorem pc2835 :
    Artifact.submissionArtifact.instructionPC 3019 = 4908 := by rfl
@[simp] theorem pc2836 :
    Artifact.submissionArtifact.instructionPC 3020 = 4909 := by rfl
@[simp] theorem pc2837 :
    Artifact.submissionArtifact.instructionPC 3021 = 4911 := by rfl
@[simp] theorem pc2838 :
    Artifact.submissionArtifact.instructionPC 3022 = 4912 := by rfl
@[simp] theorem pc2839 :
    Artifact.submissionArtifact.instructionPC 3023 = 4915 := by rfl
@[simp] theorem pc2840 :
    Artifact.submissionArtifact.instructionPC 3024 = 4916 := by rfl
@[simp] theorem pc2841 :
    Artifact.submissionArtifact.instructionPC 3025 = 4917 := by rfl
@[simp] theorem pc2842 :
    Artifact.submissionArtifact.instructionPC 3026 = 4920 := by rfl
@[simp] theorem pc2843 :
    Artifact.submissionArtifact.instructionPC 3027 = 4921 := by rfl
@[simp] theorem pc2844 :
    Artifact.submissionArtifact.instructionPC 3028 = 4922 := by rfl
@[simp] theorem pc2845 :
    Artifact.submissionArtifact.instructionPC 3029 = 4923 := by rfl
@[simp] theorem pc2846 :
    Artifact.submissionArtifact.instructionPC 3030 = 4924 := by rfl
@[simp] theorem pc2847 :
    Artifact.submissionArtifact.instructionPC 3031 = 4926 := by rfl
@[simp] theorem pc2848 :
    Artifact.submissionArtifact.instructionPC 3032 = 4927 := by rfl
@[simp] theorem pc2849 :
    Artifact.submissionArtifact.instructionPC 3033 = 4928 := by rfl
@[simp] theorem pc2850 :
    Artifact.submissionArtifact.instructionPC 3034 = 4929 := by rfl
@[simp] theorem pc2851 :
    Artifact.submissionArtifact.instructionPC 3035 = 4930 := by rfl
@[simp] theorem pc2852 :
    Artifact.submissionArtifact.instructionPC 3036 = 4931 := by rfl
@[simp] theorem pc2853 :
    Artifact.submissionArtifact.instructionPC 3037 = 4934 := by rfl
@[simp] theorem pc2854 :
    Artifact.submissionArtifact.instructionPC 3038 = 4935 := by rfl
@[simp] theorem pc2855 :
    Artifact.submissionArtifact.instructionPC 3039 = 4956 := by rfl
@[simp] theorem pc2856 :
    Artifact.submissionArtifact.instructionPC 3040 = 4957 := by rfl
@[simp] theorem pc2857 :
    Artifact.submissionArtifact.instructionPC 3041 = 4958 := by rfl
@[simp] theorem pc2858 :
    Artifact.submissionArtifact.instructionPC 3042 = 4960 := by rfl
@[simp] theorem pc2859 :
    Artifact.submissionArtifact.instructionPC 3043 = 4961 := by rfl
@[simp] theorem pc2860 :
    Artifact.submissionArtifact.instructionPC 3044 = 4962 := by rfl
@[simp] theorem pc2861 :
    Artifact.submissionArtifact.instructionPC 3045 = 4963 := by rfl
@[simp] theorem pc2862 :
    Artifact.submissionArtifact.instructionPC 3046 = 4964 := by rfl
@[simp] theorem pc2863 :
    Artifact.submissionArtifact.instructionPC 3047 = 4967 := by rfl

end Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard
