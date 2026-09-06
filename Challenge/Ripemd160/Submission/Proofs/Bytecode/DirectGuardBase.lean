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
  [opAt 2813 .JUMPDEST, opAt 2814 .CALLDATASIZE, pushAt 2815 2 1000,
   opAt 2816 .XOR, pushAt 2817 2 1006, opAt 2818 .JUMPI]

def checkEntryPath : List Located :=
  [pushAt 2819 0 0, opAt 2820 .CALLDATALOAD,
   opAt 2821 (.Dup ⟨0, by decide⟩),
   pushAt 2822 32 KnownInputData.fullWord, opAt 2823 .XOR,
   pushAt 2824 2 4929, opAt 2825 .JUMPI,
   pushAt 2826 0 0, pushAt 2827 1 32]

def checkEarlyPath : List Located :=
  [pushAt 2819 0 0, opAt 2820 .CALLDATALOAD,
   opAt 2821 (.Dup ⟨0, by decide⟩),
   pushAt 2822 32 KnownInputData.fullWord, opAt 2823 .XOR,
   pushAt 2824 2 4929, opAt 2825 .JUMPI,
   opAt 2860 .JUMPDEST, opAt 2861 .POP,
   pushAt 2862 2 5005, opAt 2863 .JUMP]

def loopPath : List Located :=
  [opAt 2828 .JUMPDEST, opAt 2829 (.Swap ⟨0, by decide⟩),
   opAt 2830 (.Dup ⟨1, by decide⟩), opAt 2831 .CALLDATALOAD,
   opAt 2832 (.Dup ⟨3, by decide⟩), opAt 2833 .XOR, opAt 2834 .OR,
   opAt 2835 (.Swap ⟨0, by decide⟩), pushAt 2836 1 32, opAt 2837 .ADD,
   pushAt 2838 2 992, opAt 2839 (.Dup ⟨1, by decide⟩), opAt 2840 .LT,
   pushAt 2841 2 4868, opAt 2842 .JUMPI]

def tailPath : List Located :=
  [opAt 2843 .CALLDATALOAD, opAt 2844 (.Dup ⟨2, by decide⟩),
   opAt 2845 .XOR, pushAt 2846 1 192, opAt 2847 .SHR, opAt 2848 .OR,
   opAt 2849 .JUMPDEST, opAt 2850 (.Swap ⟨0, by decide⟩), opAt 2851 .POP,
   pushAt 2852 2 1006, opAt 2853 .JUMPI]

def returnPath : List Located :=
  [pushAt 2854 20 972889429405991776604892044862621566948497025487,
   pushAt 2855 0 0, opAt 2856 .MSTORE, pushAt 2857 1 32,
   pushAt 2858 0 0, opAt 2859 .RETURN]

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

def sizeMatched (input : ByteArray) : State := atPC input 0x12d8
def fallbackState (input : ByteArray) : State := atPC input 0x3ee

def loopState (input : ByteArray) (n : Nat) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 0x1304
    stack := [UInt256.ofNat (32 * (n + 1)), loopAcc input n, referenceWord input] }

def loopExitState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 0x1318
    stack := [UInt256.ofNat 992, loopAcc input 30, referenceWord input] }

def returnEntry (input : ByteArray) : State := atPC input 0x1326

def storeWord (memory : ByteArray) (address : Nat) (word : UInt256) : ByteArray :=
  MachineState.writeBytes memory (Data.Bytes.natToBytesPadded word.toNat 32) address

def answerMemory : ByteArray :=
  storeWord ByteArray.empty 0 ExactGuardSpec.paddedDigestWord

def returnedState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 0x1340
    memory := answerMemory
    activeWords := UInt256.ofNat 1
    halt := .Returned
    hReturn := MachineState.readPadded answerMemory 0 32 }

abbrev run := Challenge.EvmProof.Stepper.runLocatedBlock
  (artifact := Artifact.submissionArtifact) (fork := .Osaka)

/- Freeze the concrete direct-guard range so symbolic path reduction never
   unfolds the complete generated artifact merely to advance a program counter. -/
@[simp] theorem pc2813 :
    Artifact.submissionArtifact.instructionPC 2813 = 4814 := by rfl
@[simp] theorem pc2814 :
    Artifact.submissionArtifact.instructionPC 2814 = 4815 := by rfl
@[simp] theorem pc2815 :
    Artifact.submissionArtifact.instructionPC 2815 = 4816 := by rfl
@[simp] theorem pc2816 :
    Artifact.submissionArtifact.instructionPC 2816 = 4819 := by rfl
@[simp] theorem pc2817 :
    Artifact.submissionArtifact.instructionPC 2817 = 4820 := by rfl
@[simp] theorem pc2818 :
    Artifact.submissionArtifact.instructionPC 2818 = 4823 := by rfl
@[simp] theorem pc2819 :
    Artifact.submissionArtifact.instructionPC 2819 = 4824 := by rfl
@[simp] theorem pc2820 :
    Artifact.submissionArtifact.instructionPC 2820 = 4825 := by rfl
@[simp] theorem pc2821 :
    Artifact.submissionArtifact.instructionPC 2821 = 4826 := by rfl
@[simp] theorem pc2822 :
    Artifact.submissionArtifact.instructionPC 2822 = 4827 := by rfl
@[simp] theorem pc2823 :
    Artifact.submissionArtifact.instructionPC 2823 = 4860 := by rfl
@[simp] theorem pc2824 :
    Artifact.submissionArtifact.instructionPC 2824 = 4861 := by rfl
@[simp] theorem pc2825 :
    Artifact.submissionArtifact.instructionPC 2825 = 4864 := by rfl
@[simp] theorem pc2826 :
    Artifact.submissionArtifact.instructionPC 2826 = 4865 := by rfl
@[simp] theorem pc2827 :
    Artifact.submissionArtifact.instructionPC 2827 = 4866 := by rfl
@[simp] theorem pc2828 :
    Artifact.submissionArtifact.instructionPC 2828 = 4868 := by rfl
@[simp] theorem pc2829 :
    Artifact.submissionArtifact.instructionPC 2829 = 4869 := by rfl
@[simp] theorem pc2830 :
    Artifact.submissionArtifact.instructionPC 2830 = 4870 := by rfl
@[simp] theorem pc2831 :
    Artifact.submissionArtifact.instructionPC 2831 = 4871 := by rfl
@[simp] theorem pc2832 :
    Artifact.submissionArtifact.instructionPC 2832 = 4872 := by rfl
@[simp] theorem pc2833 :
    Artifact.submissionArtifact.instructionPC 2833 = 4873 := by rfl
@[simp] theorem pc2834 :
    Artifact.submissionArtifact.instructionPC 2834 = 4874 := by rfl
@[simp] theorem pc2835 :
    Artifact.submissionArtifact.instructionPC 2835 = 4875 := by rfl
@[simp] theorem pc2836 :
    Artifact.submissionArtifact.instructionPC 2836 = 4876 := by rfl
@[simp] theorem pc2837 :
    Artifact.submissionArtifact.instructionPC 2837 = 4878 := by rfl
@[simp] theorem pc2838 :
    Artifact.submissionArtifact.instructionPC 2838 = 4879 := by rfl
@[simp] theorem pc2839 :
    Artifact.submissionArtifact.instructionPC 2839 = 4882 := by rfl
@[simp] theorem pc2840 :
    Artifact.submissionArtifact.instructionPC 2840 = 4883 := by rfl
@[simp] theorem pc2841 :
    Artifact.submissionArtifact.instructionPC 2841 = 4884 := by rfl
@[simp] theorem pc2842 :
    Artifact.submissionArtifact.instructionPC 2842 = 4887 := by rfl
@[simp] theorem pc2843 :
    Artifact.submissionArtifact.instructionPC 2843 = 4888 := by rfl
@[simp] theorem pc2844 :
    Artifact.submissionArtifact.instructionPC 2844 = 4889 := by rfl
@[simp] theorem pc2845 :
    Artifact.submissionArtifact.instructionPC 2845 = 4890 := by rfl
@[simp] theorem pc2846 :
    Artifact.submissionArtifact.instructionPC 2846 = 4891 := by rfl
@[simp] theorem pc2847 :
    Artifact.submissionArtifact.instructionPC 2847 = 4893 := by rfl
@[simp] theorem pc2848 :
    Artifact.submissionArtifact.instructionPC 2848 = 4894 := by rfl
@[simp] theorem pc2849 :
    Artifact.submissionArtifact.instructionPC 2849 = 4895 := by rfl
@[simp] theorem pc2850 :
    Artifact.submissionArtifact.instructionPC 2850 = 4896 := by rfl
@[simp] theorem pc2851 :
    Artifact.submissionArtifact.instructionPC 2851 = 4897 := by rfl
@[simp] theorem pc2852 :
    Artifact.submissionArtifact.instructionPC 2852 = 4898 := by rfl
@[simp] theorem pc2853 :
    Artifact.submissionArtifact.instructionPC 2853 = 4901 := by rfl
@[simp] theorem pc2854 :
    Artifact.submissionArtifact.instructionPC 2854 = 4902 := by rfl
@[simp] theorem pc2855 :
    Artifact.submissionArtifact.instructionPC 2855 = 4923 := by rfl
@[simp] theorem pc2856 :
    Artifact.submissionArtifact.instructionPC 2856 = 4924 := by rfl
@[simp] theorem pc2857 :
    Artifact.submissionArtifact.instructionPC 2857 = 4925 := by rfl
@[simp] theorem pc2858 :
    Artifact.submissionArtifact.instructionPC 2858 = 4927 := by rfl
@[simp] theorem pc2859 :
    Artifact.submissionArtifact.instructionPC 2859 = 4928 := by rfl
@[simp] theorem pc2860 :
    Artifact.submissionArtifact.instructionPC 2860 = 4929 := by rfl
@[simp] theorem pc2861 :
    Artifact.submissionArtifact.instructionPC 2861 = 4930 := by rfl
@[simp] theorem pc2862 :
    Artifact.submissionArtifact.instructionPC 2862 = 4931 := by rfl
@[simp] theorem pc2863 :
    Artifact.submissionArtifact.instructionPC 2863 = 4934 := by rfl

end Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard
