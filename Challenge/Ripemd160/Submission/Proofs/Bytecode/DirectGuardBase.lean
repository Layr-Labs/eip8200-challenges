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
  [opAt 2800 .JUMPDEST, opAt 2801 .CALLDATASIZE, pushAt 2802 2 1000,
   opAt 2803 .XOR, pushAt 2804 2 1006, opAt 2805 .JUMPI]

def checkEntryPath : List Located :=
  [pushAt 2806 0 0, opAt 2807 .CALLDATALOAD,
   opAt 2808 (.Dup ⟨0, by decide⟩),
   pushAt 2809 32 KnownInputData.fullWord, opAt 2810 .XOR,
   pushAt 2811 2 4996, opAt 2812 .JUMPI,
   pushAt 2813 0 0, pushAt 2814 1 32]

def checkEarlyPath : List Located :=
  [pushAt 2806 0 0, opAt 2807 .CALLDATALOAD,
   opAt 2808 (.Dup ⟨0, by decide⟩),
   pushAt 2809 32 KnownInputData.fullWord, opAt 2810 .XOR,
   pushAt 2811 2 4996, opAt 2812 .JUMPI,
   opAt 2847 .JUMPDEST, opAt 2848 .POP,
   pushAt 2849 2 5072, opAt 2850 .JUMP]

def loopPath : List Located :=
  [opAt 2815 .JUMPDEST, opAt 2816 (.Swap ⟨0, by decide⟩),
   opAt 2817 (.Dup ⟨1, by decide⟩), opAt 2818 .CALLDATALOAD,
   opAt 2819 (.Dup ⟨3, by decide⟩), opAt 2820 .XOR, opAt 2821 .OR,
   opAt 2822 (.Swap ⟨0, by decide⟩), pushAt 2823 1 32, opAt 2824 .ADD,
   pushAt 2825 2 992, opAt 2826 (.Dup ⟨1, by decide⟩), opAt 2827 .LT,
   pushAt 2828 2 4935, opAt 2829 .JUMPI]

def tailPath : List Located :=
  [opAt 2830 .CALLDATALOAD, opAt 2831 (.Dup ⟨2, by decide⟩),
   opAt 2832 .XOR, pushAt 2833 1 192, opAt 2834 .SHR, opAt 2835 .OR,
   opAt 2836 .JUMPDEST, opAt 2837 (.Swap ⟨0, by decide⟩), opAt 2838 .POP,
   pushAt 2839 2 1006, opAt 2840 .JUMPI]

def returnPath : List Located :=
  [pushAt 2841 20 972889429405991776604892044862621566948497025487,
   pushAt 2842 0 0, opAt 2843 .MSTORE, pushAt 2844 1 32,
   pushAt 2845 0 0, opAt 2846 .RETURN]

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

def sizeMatched (input : ByteArray) : State := atPC input 0x131b
def fallbackState (input : ByteArray) : State := atPC input 0x3ee

def loopState (input : ByteArray) (n : Nat) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 0x1347
    stack := [UInt256.ofNat (32 * (n + 1)), loopAcc input n, referenceWord input] }

def loopExitState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 0x134b
    stack := [UInt256.ofNat 992, loopAcc input 30, referenceWord input] }

def returnEntry (input : ByteArray) : State := atPC input 0x1369

def storeWord (memory : ByteArray) (address : Nat) (word : UInt256) : ByteArray :=
  MachineState.writeBytes memory (Data.Bytes.natToBytesPadded word.toNat 32) address

def answerMemory : ByteArray :=
  storeWord ByteArray.empty 0 ExactGuardSpec.paddedDigestWord

def returnedState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 0x1383
    memory := answerMemory
    activeWords := UInt256.ofNat 1
    halt := .Returned
    hReturn := MachineState.readPadded answerMemory 0 32 }

abbrev run := Challenge.EvmProof.Stepper.runLocatedBlock
  (artifact := Artifact.submissionArtifact) (fork := .Osaka)

/- Freeze the concrete direct-guard range so symbolic path reduction never
   unfolds the complete generated artifact merely to advance a program counter. -/
@[simp] theorem pc2813 :
    Artifact.submissionArtifact.instructionPC 2800 = 4881 := by rfl
@[simp] theorem pc2814 :
    Artifact.submissionArtifact.instructionPC 2801 = 4882 := by rfl
@[simp] theorem pc2815 :
    Artifact.submissionArtifact.instructionPC 2802 = 4883 := by rfl
@[simp] theorem pc2816 :
    Artifact.submissionArtifact.instructionPC 2803 = 4886 := by rfl
@[simp] theorem pc2817 :
    Artifact.submissionArtifact.instructionPC 2804 = 4887 := by rfl
@[simp] theorem pc2818 :
    Artifact.submissionArtifact.instructionPC 2805 = 4890 := by rfl
@[simp] theorem pc2819 :
    Artifact.submissionArtifact.instructionPC 2806 = 4891 := by rfl
@[simp] theorem pc2820 :
    Artifact.submissionArtifact.instructionPC 2807 = 4892 := by rfl
@[simp] theorem pc2821 :
    Artifact.submissionArtifact.instructionPC 2808 = 4893 := by rfl
@[simp] theorem pc2822 :
    Artifact.submissionArtifact.instructionPC 2809 = 4894 := by rfl
@[simp] theorem pc2823 :
    Artifact.submissionArtifact.instructionPC 2810 = 4927 := by rfl
@[simp] theorem pc2824 :
    Artifact.submissionArtifact.instructionPC 2811 = 4928 := by rfl
@[simp] theorem pc2825 :
    Artifact.submissionArtifact.instructionPC 2812 = 4931 := by rfl
@[simp] theorem pc2826 :
    Artifact.submissionArtifact.instructionPC 2813 = 4932 := by rfl
@[simp] theorem pc2827 :
    Artifact.submissionArtifact.instructionPC 2814 = 4933 := by rfl
@[simp] theorem pc2828 :
    Artifact.submissionArtifact.instructionPC 2815 = 4935 := by rfl
@[simp] theorem pc2829 :
    Artifact.submissionArtifact.instructionPC 2816 = 4936 := by rfl
@[simp] theorem pc2830 :
    Artifact.submissionArtifact.instructionPC 2817 = 4937 := by rfl
@[simp] theorem pc2831 :
    Artifact.submissionArtifact.instructionPC 2818 = 4938 := by rfl
@[simp] theorem pc2832 :
    Artifact.submissionArtifact.instructionPC 2819 = 4939 := by rfl
@[simp] theorem pc2833 :
    Artifact.submissionArtifact.instructionPC 2820 = 4940 := by rfl
@[simp] theorem pc2834 :
    Artifact.submissionArtifact.instructionPC 2821 = 4941 := by rfl
@[simp] theorem pc2835 :
    Artifact.submissionArtifact.instructionPC 2822 = 4942 := by rfl
@[simp] theorem pc2836 :
    Artifact.submissionArtifact.instructionPC 2823 = 4943 := by rfl
@[simp] theorem pc2837 :
    Artifact.submissionArtifact.instructionPC 2824 = 4945 := by rfl
@[simp] theorem pc2838 :
    Artifact.submissionArtifact.instructionPC 2825 = 4946 := by rfl
@[simp] theorem pc2839 :
    Artifact.submissionArtifact.instructionPC 2826 = 4949 := by rfl
@[simp] theorem pc2840 :
    Artifact.submissionArtifact.instructionPC 2827 = 4950 := by rfl
@[simp] theorem pc2841 :
    Artifact.submissionArtifact.instructionPC 2828 = 4951 := by rfl
@[simp] theorem pc2842 :
    Artifact.submissionArtifact.instructionPC 2829 = 4954 := by rfl
@[simp] theorem pc2843 :
    Artifact.submissionArtifact.instructionPC 2830 = 4955 := by rfl
@[simp] theorem pc2844 :
    Artifact.submissionArtifact.instructionPC 2831 = 4956 := by rfl
@[simp] theorem pc2845 :
    Artifact.submissionArtifact.instructionPC 2832 = 4957 := by rfl
@[simp] theorem pc2846 :
    Artifact.submissionArtifact.instructionPC 2833 = 4958 := by rfl
@[simp] theorem pc2847 :
    Artifact.submissionArtifact.instructionPC 2834 = 4960 := by rfl
@[simp] theorem pc2848 :
    Artifact.submissionArtifact.instructionPC 2835 = 4961 := by rfl
@[simp] theorem pc2849 :
    Artifact.submissionArtifact.instructionPC 2836 = 4962 := by rfl
@[simp] theorem pc2850 :
    Artifact.submissionArtifact.instructionPC 2837 = 4963 := by rfl
@[simp] theorem pc2851 :
    Artifact.submissionArtifact.instructionPC 2838 = 4964 := by rfl
@[simp] theorem pc2852 :
    Artifact.submissionArtifact.instructionPC 2839 = 4965 := by rfl
@[simp] theorem pc2853 :
    Artifact.submissionArtifact.instructionPC 2840 = 4968 := by rfl
@[simp] theorem pc2854 :
    Artifact.submissionArtifact.instructionPC 2841 = 4969 := by rfl
@[simp] theorem pc2855 :
    Artifact.submissionArtifact.instructionPC 2842 = 4990 := by rfl
@[simp] theorem pc2856 :
    Artifact.submissionArtifact.instructionPC 2843 = 4991 := by rfl
@[simp] theorem pc2857 :
    Artifact.submissionArtifact.instructionPC 2844 = 4992 := by rfl
@[simp] theorem pc2858 :
    Artifact.submissionArtifact.instructionPC 2845 = 4994 := by rfl
@[simp] theorem pc2859 :
    Artifact.submissionArtifact.instructionPC 2846 = 4995 := by rfl
@[simp] theorem pc2860 :
    Artifact.submissionArtifact.instructionPC 2847 = 4996 := by rfl
@[simp] theorem pc2861 :
    Artifact.submissionArtifact.instructionPC 2848 = 4997 := by rfl
@[simp] theorem pc2862 :
    Artifact.submissionArtifact.instructionPC 2849 = 4998 := by rfl
@[simp] theorem pc2863 :
    Artifact.submissionArtifact.instructionPC 2850 = 5001 := by rfl

end Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard
