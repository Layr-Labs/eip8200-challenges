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
  [opAt 2780 .JUMPDEST, opAt 2781 .CALLDATASIZE, pushAt 2782 2 1000,
   opAt 2783 .XOR, pushAt 2784 2 1006, opAt 2785 .JUMPI]

def checkEntryPath : List Located :=
  [pushAt 2786 0 0, opAt 2787 .CALLDATALOAD,
   opAt 2788 (.Dup ⟨0, by decide⟩),
   pushAt 2789 32 KnownInputData.fullWord, opAt 2790 .XOR,
   pushAt 2791 2 5372, opAt 2792 .JUMPI,
   pushAt 2793 0 0, pushAt 2794 1 32]

def checkEarlyPath : List Located :=
  [pushAt 2786 0 0, opAt 2787 .CALLDATALOAD,
   opAt 2788 (.Dup ⟨0, by decide⟩),
   pushAt 2789 32 KnownInputData.fullWord, opAt 2790 .XOR,
   pushAt 2791 2 5372, opAt 2792 .JUMPI,
   opAt 2827 .JUMPDEST, opAt 2828 .POP,
   pushAt 2829 2 5448, opAt 2830 .JUMP]

def loopPath : List Located :=
  [opAt 2795 .JUMPDEST, opAt 2796 (.Swap ⟨0, by decide⟩),
   opAt 2797 (.Dup ⟨1, by decide⟩), opAt 2798 .CALLDATALOAD,
   opAt 2799 (.Dup ⟨3, by decide⟩), opAt 2800 .XOR, opAt 2801 .OR,
   opAt 2802 (.Swap ⟨0, by decide⟩), pushAt 2803 1 32, opAt 2804 .ADD,
   pushAt 2805 2 992, opAt 2806 (.Dup ⟨1, by decide⟩), opAt 2807 .LT,
   pushAt 2808 2 5311, opAt 2809 .JUMPI]

def tailPath : List Located :=
  [opAt 2810 .CALLDATALOAD, opAt 2811 (.Dup ⟨2, by decide⟩),
   opAt 2812 .XOR, pushAt 2813 1 192, opAt 2814 .SHR, opAt 2815 .OR,
   opAt 2816 .JUMPDEST, opAt 2817 (.Swap ⟨0, by decide⟩), opAt 2818 .POP,
   pushAt 2819 2 1006, opAt 2820 .JUMPI]

def returnPath : List Located :=
  [pushAt 2821 20 972889429405991776604892044862621566948497025487,
   pushAt 2822 0 0, opAt 2823 .MSTORE, pushAt 2824 1 32,
   pushAt 2825 0 0, opAt 2826 .RETURN]

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

def sizeMatched (input : ByteArray) : State := atPC input 0x1493
def fallbackState (input : ByteArray) : State := atPC input 0x3ee

def loopState (input : ByteArray) (n : Nat) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 0x14bf
    stack := [UInt256.ofNat (32 * (n + 1)), loopAcc input n, referenceWord input] }

def loopExitState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 0x14d3
    stack := [UInt256.ofNat 992, loopAcc input 30, referenceWord input] }

def returnEntry (input : ByteArray) : State := atPC input 0x14e1

def storeWord (memory : ByteArray) (address : Nat) (word : UInt256) : ByteArray :=
  MachineState.writeBytes memory (Data.Bytes.natToBytesPadded word.toNat 32) address

def answerMemory : ByteArray :=
  storeWord ByteArray.empty 0 ExactGuardSpec.paddedDigestWord

def returnedState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 0x14fb
    memory := answerMemory
    activeWords := UInt256.ofNat 1
    halt := .Returned
    hReturn := MachineState.readPadded answerMemory 0 32 }

abbrev run := Challenge.EvmProof.Stepper.runLocatedBlock
  (artifact := Artifact.submissionArtifact) (fork := .Osaka)

/- Freeze the concrete direct-guard range so symbolic path reduction never
   unfolds the complete generated artifact merely to advance a program counter. -/
@[simp] theorem pc2813 :
    Artifact.submissionArtifact.instructionPC 2780 = 5257 := by rfl
@[simp] theorem pc2814 :
    Artifact.submissionArtifact.instructionPC 2781 = 5258 := by rfl
@[simp] theorem pc2815 :
    Artifact.submissionArtifact.instructionPC 2782 = 5259 := by rfl
@[simp] theorem pc2816 :
    Artifact.submissionArtifact.instructionPC 2783 = 5262 := by rfl
@[simp] theorem pc2817 :
    Artifact.submissionArtifact.instructionPC 2784 = 5263 := by rfl
@[simp] theorem pc2818 :
    Artifact.submissionArtifact.instructionPC 2785 = 5266 := by rfl
@[simp] theorem pc2819 :
    Artifact.submissionArtifact.instructionPC 2786 = 5267 := by rfl
@[simp] theorem pc2820 :
    Artifact.submissionArtifact.instructionPC 2787 = 5268 := by rfl
@[simp] theorem pc2821 :
    Artifact.submissionArtifact.instructionPC 2788 = 5269 := by rfl
@[simp] theorem pc2822 :
    Artifact.submissionArtifact.instructionPC 2789 = 5270 := by rfl
@[simp] theorem pc2823 :
    Artifact.submissionArtifact.instructionPC 2790 = 5303 := by rfl
@[simp] theorem pc2824 :
    Artifact.submissionArtifact.instructionPC 2791 = 5304 := by rfl
@[simp] theorem pc2825 :
    Artifact.submissionArtifact.instructionPC 2792 = 5307 := by rfl
@[simp] theorem pc2826 :
    Artifact.submissionArtifact.instructionPC 2793 = 5308 := by rfl
@[simp] theorem pc2827 :
    Artifact.submissionArtifact.instructionPC 2794 = 5309 := by rfl
@[simp] theorem pc2828 :
    Artifact.submissionArtifact.instructionPC 2795 = 5311 := by rfl
@[simp] theorem pc2829 :
    Artifact.submissionArtifact.instructionPC 2796 = 5312 := by rfl
@[simp] theorem pc2830 :
    Artifact.submissionArtifact.instructionPC 2797 = 5313 := by rfl
@[simp] theorem pc2831 :
    Artifact.submissionArtifact.instructionPC 2798 = 5314 := by rfl
@[simp] theorem pc2832 :
    Artifact.submissionArtifact.instructionPC 2799 = 5315 := by rfl
@[simp] theorem pc2833 :
    Artifact.submissionArtifact.instructionPC 2800 = 5316 := by rfl
@[simp] theorem pc2834 :
    Artifact.submissionArtifact.instructionPC 2801 = 5317 := by rfl
@[simp] theorem pc2835 :
    Artifact.submissionArtifact.instructionPC 2802 = 5318 := by rfl
@[simp] theorem pc2836 :
    Artifact.submissionArtifact.instructionPC 2803 = 5319 := by rfl
@[simp] theorem pc2837 :
    Artifact.submissionArtifact.instructionPC 2804 = 5321 := by rfl
@[simp] theorem pc2838 :
    Artifact.submissionArtifact.instructionPC 2805 = 5322 := by rfl
@[simp] theorem pc2839 :
    Artifact.submissionArtifact.instructionPC 2806 = 5325 := by rfl
@[simp] theorem pc2840 :
    Artifact.submissionArtifact.instructionPC 2807 = 5326 := by rfl
@[simp] theorem pc2841 :
    Artifact.submissionArtifact.instructionPC 2808 = 5327 := by rfl
@[simp] theorem pc2842 :
    Artifact.submissionArtifact.instructionPC 2809 = 5330 := by rfl
@[simp] theorem pc2843 :
    Artifact.submissionArtifact.instructionPC 2810 = 5331 := by rfl
@[simp] theorem pc2844 :
    Artifact.submissionArtifact.instructionPC 2811 = 5332 := by rfl
@[simp] theorem pc2845 :
    Artifact.submissionArtifact.instructionPC 2812 = 5333 := by rfl
@[simp] theorem pc2846 :
    Artifact.submissionArtifact.instructionPC 2813 = 5334 := by rfl
@[simp] theorem pc2847 :
    Artifact.submissionArtifact.instructionPC 2814 = 5336 := by rfl
@[simp] theorem pc2848 :
    Artifact.submissionArtifact.instructionPC 2815 = 5337 := by rfl
@[simp] theorem pc2849 :
    Artifact.submissionArtifact.instructionPC 2816 = 5338 := by rfl
@[simp] theorem pc2850 :
    Artifact.submissionArtifact.instructionPC 2817 = 5339 := by rfl
@[simp] theorem pc2851 :
    Artifact.submissionArtifact.instructionPC 2818 = 5340 := by rfl
@[simp] theorem pc2852 :
    Artifact.submissionArtifact.instructionPC 2819 = 5341 := by rfl
@[simp] theorem pc2853 :
    Artifact.submissionArtifact.instructionPC 2820 = 5344 := by rfl
@[simp] theorem pc2854 :
    Artifact.submissionArtifact.instructionPC 2821 = 5345 := by rfl
@[simp] theorem pc2855 :
    Artifact.submissionArtifact.instructionPC 2822 = 5366 := by rfl
@[simp] theorem pc2856 :
    Artifact.submissionArtifact.instructionPC 2823 = 5367 := by rfl
@[simp] theorem pc2857 :
    Artifact.submissionArtifact.instructionPC 2824 = 5368 := by rfl
@[simp] theorem pc2858 :
    Artifact.submissionArtifact.instructionPC 2825 = 5370 := by rfl
@[simp] theorem pc2859 :
    Artifact.submissionArtifact.instructionPC 2826 = 5371 := by rfl
@[simp] theorem pc2860 :
    Artifact.submissionArtifact.instructionPC 2827 = 5372 := by rfl
@[simp] theorem pc2861 :
    Artifact.submissionArtifact.instructionPC 2828 = 5373 := by rfl
@[simp] theorem pc2862 :
    Artifact.submissionArtifact.instructionPC 2829 = 5374 := by rfl
@[simp] theorem pc2863 :
    Artifact.submissionArtifact.instructionPC 2830 = 5377 := by rfl

end Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard
