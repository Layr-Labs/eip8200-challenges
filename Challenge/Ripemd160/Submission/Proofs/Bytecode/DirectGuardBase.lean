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
  [opAt 3601 .JUMPDEST, opAt 3602 .CALLDATASIZE, pushAt 3603 2 1000,
   opAt 3604 .XOR, pushAt 3605 2 972, opAt 3606 .JUMPI]

def checkEntryPath : List Located :=
  [pushAt 3607 0 0, opAt 3608 .CALLDATALOAD,
   opAt 3609 (.Dup ⟨0, by decide⟩),
   pushAt 3610 1 255, pushAt 3611 0 0, opAt 3612 .NOT, opAt 3613 .DIV,
   pushAt 3614 1 97, opAt 3615 .MUL, opAt 3616 .XOR,
   pushAt 3617 2 5133, opAt 3618 .JUMPI,
   pushAt 3619 0 0, pushAt 3620 1 32]

def checkEarlyPath : List Located :=
  [pushAt 3607 0 0, opAt 3608 .CALLDATALOAD,
   opAt 3609 (.Dup ⟨0, by decide⟩),
   pushAt 3610 1 255, pushAt 3611 0 0, opAt 3612 .NOT, opAt 3613 .DIV,
   pushAt 3614 1 97, opAt 3615 .MUL, opAt 3616 .XOR,
   pushAt 3617 2 5133, opAt 3618 .JUMPI,
   opAt 3653 .JUMPDEST, opAt 3654 .POP,
   pushAt 3655 2 5139, opAt 3656 .POP]

def loopPath : List Located :=
  [opAt 3621 .JUMPDEST, opAt 3622 (.Swap ⟨0, by decide⟩),
   opAt 3623 (.Dup ⟨1, by decide⟩), opAt 3624 .CALLDATALOAD,
   opAt 3625 (.Dup ⟨3, by decide⟩), opAt 3626 .XOR, opAt 3627 .OR,
   opAt 3628 (.Swap ⟨0, by decide⟩), pushAt 3629 1 32, opAt 3630 .ADD,
   pushAt 3631 2 992, opAt 3632 (.Dup ⟨1, by decide⟩), opAt 3633 .LT,
   pushAt 3634 2 5072, opAt 3635 .JUMPI]

def tailPath : List Located :=
  [opAt 3636 .CALLDATALOAD, opAt 3637 (.Dup ⟨2, by decide⟩),
   opAt 3638 .XOR, pushAt 3639 1 192, opAt 3640 .SHR, opAt 3641 .OR,
   opAt 3642 .JUMPDEST, opAt 3643 (.Swap ⟨0, by decide⟩), opAt 3644 .POP,
   pushAt 3645 2 972, opAt 3646 .JUMPI]

def returnPath : List Located :=
  [pushAt 3647 20 972889429405991776604892044862621566948497025487,
   pushAt 3648 0 0, opAt 3649 .MSTORE, pushAt 3650 1 32,
   pushAt 3651 0 0, opAt 3652 .RETURN]

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

def sizeMatched (input : ByteArray) : State := atPC input 0x13bd
def fallbackState (input : ByteArray) : State := atPC input 0x3cc

def loopState (input : ByteArray) (n : Nat) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 0x13d0
    stack := [UInt256.ofNat (32 * (n + 1)), loopAcc input n, referenceWord input] }

def loopExitState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 0x13e4
    stack := [UInt256.ofNat 992, loopAcc input 30, referenceWord input] }

def returnEntry (input : ByteArray) : State := atPC input 0x13f2

def storeWord (memory : ByteArray) (address : Nat) (word : UInt256) : ByteArray :=
  MachineState.writeBytes memory (Data.Bytes.natToBytesPadded word.toNat 32) address

def answerMemory : ByteArray :=
  storeWord ByteArray.empty 0 ExactGuardSpec.paddedDigestWord

def returnedState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 0x140c
    memory := answerMemory
    activeWords := UInt256.ofNat 1
    halt := .Returned
    hReturn := MachineState.readPadded answerMemory 0 32 }

abbrev run := Challenge.EvmProof.Stepper.runLocatedBlock
  (artifact := Artifact.submissionArtifact) (fork := .Osaka)

/- Freeze the concrete direct-guard range so symbolic path reduction never
   unfolds the complete generated artifact merely to advance a program counter. -/
@[simp] theorem pc2813 :
    Artifact.submissionArtifact.instructionPC 3601 = 0x13b3 := by rfl
@[simp] theorem pc2814 :
    Artifact.submissionArtifact.instructionPC 3602 = 0x13b4 := by rfl
@[simp] theorem pc2815 :
    Artifact.submissionArtifact.instructionPC 3603 = 0x13b5 := by rfl
@[simp] theorem pc2816 :
    Artifact.submissionArtifact.instructionPC 3604 = 0x13b8 := by rfl
@[simp] theorem pc2817 :
    Artifact.submissionArtifact.instructionPC 3605 = 0x13b9 := by rfl
@[simp] theorem pc2818 :
    Artifact.submissionArtifact.instructionPC 3606 = 0x13bc := by rfl
@[simp] theorem pc2819 :
    Artifact.submissionArtifact.instructionPC 3607 = 0x13bd := by rfl
@[simp] theorem pc2820 :
    Artifact.submissionArtifact.instructionPC 3608 = 0x13be := by rfl
@[simp] theorem pc2821 :
    Artifact.submissionArtifact.instructionPC 3609 = 0x13bf := by rfl
@[simp] theorem pc2822 :
    Artifact.submissionArtifact.instructionPC 3610 = 0x13c0 := by rfl
@[simp] theorem pc2823 :
    Artifact.submissionArtifact.instructionPC 3616 = 0x13c8 := by rfl
@[simp] theorem pc2824 :
    Artifact.submissionArtifact.instructionPC 3617 = 0x13c9 := by rfl
@[simp] theorem pc2825 :
    Artifact.submissionArtifact.instructionPC 3618 = 0x13cc := by rfl
@[simp] theorem pc2826 :
    Artifact.submissionArtifact.instructionPC 3619 = 0x13cd := by rfl
@[simp] theorem pc2827 :
    Artifact.submissionArtifact.instructionPC 3620 = 0x13ce := by rfl
@[simp] theorem pc2828 :
    Artifact.submissionArtifact.instructionPC 3621 = 0x13d0 := by rfl
@[simp] theorem pc2829 :
    Artifact.submissionArtifact.instructionPC 3622 = 0x13d1 := by rfl
@[simp] theorem pc2830 :
    Artifact.submissionArtifact.instructionPC 3623 = 0x13d2 := by rfl
@[simp] theorem pc2831 :
    Artifact.submissionArtifact.instructionPC 3624 = 0x13d3 := by rfl
@[simp] theorem pc2832 :
    Artifact.submissionArtifact.instructionPC 3625 = 0x13d4 := by rfl
@[simp] theorem pc2833 :
    Artifact.submissionArtifact.instructionPC 3626 = 0x13d5 := by rfl
@[simp] theorem pc2834 :
    Artifact.submissionArtifact.instructionPC 3627 = 0x13d6 := by rfl
@[simp] theorem pc2835 :
    Artifact.submissionArtifact.instructionPC 3628 = 0x13d7 := by rfl
@[simp] theorem pc2836 :
    Artifact.submissionArtifact.instructionPC 3629 = 0x13d8 := by rfl
@[simp] theorem pc2837 :
    Artifact.submissionArtifact.instructionPC 3630 = 0x13da := by rfl
@[simp] theorem pc2838 :
    Artifact.submissionArtifact.instructionPC 3631 = 0x13db := by rfl
@[simp] theorem pc2839 :
    Artifact.submissionArtifact.instructionPC 3632 = 0x13de := by rfl
@[simp] theorem pc2840 :
    Artifact.submissionArtifact.instructionPC 3633 = 0x13df := by rfl
@[simp] theorem pc2841 :
    Artifact.submissionArtifact.instructionPC 3634 = 0x13e0 := by rfl
@[simp] theorem pc2842 :
    Artifact.submissionArtifact.instructionPC 3635 = 0x13e3 := by rfl
@[simp] theorem pc2843 :
    Artifact.submissionArtifact.instructionPC 3636 = 0x13e4 := by rfl
@[simp] theorem pc2844 :
    Artifact.submissionArtifact.instructionPC 3637 = 0x13e5 := by rfl
@[simp] theorem pc2845 :
    Artifact.submissionArtifact.instructionPC 3638 = 0x13e6 := by rfl
@[simp] theorem pc2846 :
    Artifact.submissionArtifact.instructionPC 3639 = 0x13e7 := by rfl
@[simp] theorem pc2847 :
    Artifact.submissionArtifact.instructionPC 3640 = 0x13e9 := by rfl
@[simp] theorem pc2848 :
    Artifact.submissionArtifact.instructionPC 3641 = 0x13ea := by rfl
@[simp] theorem pc2849 :
    Artifact.submissionArtifact.instructionPC 3642 = 0x13eb := by rfl
@[simp] theorem pc2850 :
    Artifact.submissionArtifact.instructionPC 3643 = 0x13ec := by rfl
@[simp] theorem pc2851 :
    Artifact.submissionArtifact.instructionPC 3644 = 0x13ed := by rfl
@[simp] theorem pc2852 :
    Artifact.submissionArtifact.instructionPC 3645 = 0x13ee := by rfl
@[simp] theorem pc2853 :
    Artifact.submissionArtifact.instructionPC 3646 = 0x13f1 := by rfl
@[simp] theorem pc2854 :
    Artifact.submissionArtifact.instructionPC 3647 = 0x13f2 := by rfl
@[simp] theorem pc2855 :
    Artifact.submissionArtifact.instructionPC 3648 = 0x1407 := by rfl
@[simp] theorem pc2856 :
    Artifact.submissionArtifact.instructionPC 3649 = 0x1408 := by rfl
@[simp] theorem pc2857 :
    Artifact.submissionArtifact.instructionPC 3650 = 0x1409 := by rfl
@[simp] theorem pc2858 :
    Artifact.submissionArtifact.instructionPC 3651 = 0x140b := by rfl
@[simp] theorem pc2859 :
    Artifact.submissionArtifact.instructionPC 3652 = 0x140c := by rfl
@[simp] theorem pc2860 :
    Artifact.submissionArtifact.instructionPC 3653 = 0x140d := by rfl
@[simp] theorem pc2861 :
    Artifact.submissionArtifact.instructionPC 3654 = 0x140e := by rfl
@[simp] theorem pc2862 :
    Artifact.submissionArtifact.instructionPC 3655 = 0x140f := by rfl
@[simp] theorem pc2863 :
    Artifact.submissionArtifact.instructionPC 3656 = 0x1412 := by rfl

end Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard
