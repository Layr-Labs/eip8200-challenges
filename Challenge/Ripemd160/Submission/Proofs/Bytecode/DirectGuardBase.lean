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
  [opAt 3376 .JUMPDEST, opAt 3377 .CALLDATASIZE, pushAt 3378 2 1000,
   opAt 3379 .XOR, pushAt 3380 2 1004, opAt 3381 .JUMPI]

def checkEntryPath : List Located :=
  [pushAt 3382 0 0, opAt 3383 .CALLDATALOAD,
   opAt 3384 (.Dup ⟨0, by decide⟩),
   pushAt 3385 1 255, pushAt 3386 0 0, opAt 3387 .NOT, opAt 3388 .DIV,
   pushAt 3389 1 97, opAt 3390 .MUL, opAt 3391 .XOR,
   pushAt 3392 2 5118, opAt 3393 .JUMPI,
   pushAt 3394 0 0, pushAt 3395 1 32]

def checkEarlyPath : List Located :=
  [pushAt 3382 0 0, opAt 3383 .CALLDATALOAD,
   opAt 3384 (.Dup ⟨0, by decide⟩),
   pushAt 3385 1 255, pushAt 3386 0 0, opAt 3387 .NOT, opAt 3388 .DIV,
   pushAt 3389 1 97, opAt 3390 .MUL, opAt 3391 .XOR,
   pushAt 3392 2 5118, opAt 3393 .JUMPI,
   opAt 3428 .JUMPDEST, opAt 3429 .POP,
   pushAt 3430 2 5124, opAt 3431 .JUMP]

def loopPath : List Located :=
  [opAt 3396 .JUMPDEST, opAt 3397 (.Swap ⟨0, by decide⟩),
   opAt 3398 (.Dup ⟨1, by decide⟩), opAt 3399 .CALLDATALOAD,
   opAt 3400 (.Dup ⟨3, by decide⟩), opAt 3401 .XOR, opAt 3402 .OR,
   opAt 3403 (.Swap ⟨0, by decide⟩), pushAt 3404 1 32, opAt 3405 .ADD,
   pushAt 3406 2 992, opAt 3407 (.Dup ⟨1, by decide⟩), opAt 3408 .LT,
   pushAt 3409 2 5057, opAt 3410 .JUMPI]

def tailPath : List Located :=
  [opAt 3411 .CALLDATALOAD, opAt 3412 (.Dup ⟨2, by decide⟩),
   opAt 3413 .XOR, pushAt 3414 1 192, opAt 3415 .SHR, opAt 3416 .OR,
   opAt 3417 .JUMPDEST, opAt 3418 (.Swap ⟨0, by decide⟩), opAt 3419 .POP,
   pushAt 3420 2 1004, opAt 3421 .JUMPI]

def returnPath : List Located :=
  [pushAt 3422 20 972889429405991776604892044862621566948497025487,
   pushAt 3423 0 0, opAt 3424 .MSTORE, pushAt 3425 1 32,
   pushAt 3426 0 0, opAt 3427 .RETURN]

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

def sizeMatched (input : ByteArray) : State := atPC input 0x13ae
def fallbackState (input : ByteArray) : State := atPC input 0x3ec

def loopState (input : ByteArray) (n : Nat) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 0x13c1
    stack := [UInt256.ofNat (32 * (n + 1)), loopAcc input n, referenceWord input] }

def loopExitState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 0x13d5
    stack := [UInt256.ofNat 992, loopAcc input 30, referenceWord input] }

def returnEntry (input : ByteArray) : State := atPC input 0x13e3

def storeWord (memory : ByteArray) (address : Nat) (word : UInt256) : ByteArray :=
  MachineState.writeBytes memory (Data.Bytes.natToBytesPadded word.toNat 32) address

def answerMemory : ByteArray :=
  storeWord ByteArray.empty 0 ExactGuardSpec.paddedDigestWord

def returnedState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 0x13fd
    memory := answerMemory
    activeWords := UInt256.ofNat 1
    halt := .Returned
    hReturn := MachineState.readPadded answerMemory 0 32 }

abbrev run := Challenge.EvmProof.Stepper.runLocatedBlock
  (artifact := Artifact.submissionArtifact) (fork := .Osaka)

/- Freeze the concrete direct-guard range so symbolic path reduction never
   unfolds the complete generated artifact merely to advance a program counter. -/
@[simp] theorem pc2813 :
    Artifact.submissionArtifact.instructionPC 3376 = 0x13a4 := by rfl
@[simp] theorem pc2814 :
    Artifact.submissionArtifact.instructionPC 3377 = 0x13a5 := by rfl
@[simp] theorem pc2815 :
    Artifact.submissionArtifact.instructionPC 3378 = 0x13a6 := by rfl
@[simp] theorem pc2816 :
    Artifact.submissionArtifact.instructionPC 3379 = 0x13a9 := by rfl
@[simp] theorem pc2817 :
    Artifact.submissionArtifact.instructionPC 3380 = 0x13aa := by rfl
@[simp] theorem pc2818 :
    Artifact.submissionArtifact.instructionPC 3381 = 0x13ad := by rfl
@[simp] theorem pc2819 :
    Artifact.submissionArtifact.instructionPC 3382 = 0x13ae := by rfl
@[simp] theorem pc2820 :
    Artifact.submissionArtifact.instructionPC 3383 = 0x13af := by rfl
@[simp] theorem pc2821 :
    Artifact.submissionArtifact.instructionPC 3384 = 0x13b0 := by rfl
@[simp] theorem pc2822 :
    Artifact.submissionArtifact.instructionPC 3385 = 0x13b1 := by rfl
@[simp] theorem pc2823 :
    Artifact.submissionArtifact.instructionPC 3391 = 0x13b9 := by rfl
@[simp] theorem pc2824 :
    Artifact.submissionArtifact.instructionPC 3392 = 0x13ba := by rfl
@[simp] theorem pc2825 :
    Artifact.submissionArtifact.instructionPC 3393 = 0x13bd := by rfl
@[simp] theorem pc2826 :
    Artifact.submissionArtifact.instructionPC 3394 = 0x13be := by rfl
@[simp] theorem pc2827 :
    Artifact.submissionArtifact.instructionPC 3395 = 0x13bf := by rfl
@[simp] theorem pc2828 :
    Artifact.submissionArtifact.instructionPC 3396 = 0x13c1 := by rfl
@[simp] theorem pc2829 :
    Artifact.submissionArtifact.instructionPC 3397 = 0x13c2 := by rfl
@[simp] theorem pc2830 :
    Artifact.submissionArtifact.instructionPC 3398 = 0x13c3 := by rfl
@[simp] theorem pc2831 :
    Artifact.submissionArtifact.instructionPC 3399 = 0x13c4 := by rfl
@[simp] theorem pc2832 :
    Artifact.submissionArtifact.instructionPC 3400 = 0x13c5 := by rfl
@[simp] theorem pc2833 :
    Artifact.submissionArtifact.instructionPC 3401 = 0x13c6 := by rfl
@[simp] theorem pc2834 :
    Artifact.submissionArtifact.instructionPC 3402 = 0x13c7 := by rfl
@[simp] theorem pc2835 :
    Artifact.submissionArtifact.instructionPC 3403 = 0x13c8 := by rfl
@[simp] theorem pc2836 :
    Artifact.submissionArtifact.instructionPC 3404 = 0x13c9 := by rfl
@[simp] theorem pc2837 :
    Artifact.submissionArtifact.instructionPC 3405 = 0x13cb := by rfl
@[simp] theorem pc2838 :
    Artifact.submissionArtifact.instructionPC 3406 = 0x13cc := by rfl
@[simp] theorem pc2839 :
    Artifact.submissionArtifact.instructionPC 3407 = 0x13cf := by rfl
@[simp] theorem pc2840 :
    Artifact.submissionArtifact.instructionPC 3408 = 0x13d0 := by rfl
@[simp] theorem pc2841 :
    Artifact.submissionArtifact.instructionPC 3409 = 0x13d1 := by rfl
@[simp] theorem pc2842 :
    Artifact.submissionArtifact.instructionPC 3410 = 0x13d4 := by rfl
@[simp] theorem pc2843 :
    Artifact.submissionArtifact.instructionPC 3411 = 0x13d5 := by rfl
@[simp] theorem pc2844 :
    Artifact.submissionArtifact.instructionPC 3412 = 0x13d6 := by rfl
@[simp] theorem pc2845 :
    Artifact.submissionArtifact.instructionPC 3413 = 0x13d7 := by rfl
@[simp] theorem pc2846 :
    Artifact.submissionArtifact.instructionPC 3414 = 0x13d8 := by rfl
@[simp] theorem pc2847 :
    Artifact.submissionArtifact.instructionPC 3415 = 0x13da := by rfl
@[simp] theorem pc2848 :
    Artifact.submissionArtifact.instructionPC 3416 = 0x13db := by rfl
@[simp] theorem pc2849 :
    Artifact.submissionArtifact.instructionPC 3417 = 0x13dc := by rfl
@[simp] theorem pc2850 :
    Artifact.submissionArtifact.instructionPC 3418 = 0x13dd := by rfl
@[simp] theorem pc2851 :
    Artifact.submissionArtifact.instructionPC 3419 = 0x13de := by rfl
@[simp] theorem pc2852 :
    Artifact.submissionArtifact.instructionPC 3420 = 0x13df := by rfl
@[simp] theorem pc2853 :
    Artifact.submissionArtifact.instructionPC 3421 = 0x13e2 := by rfl
@[simp] theorem pc2854 :
    Artifact.submissionArtifact.instructionPC 3422 = 0x13e3 := by rfl
@[simp] theorem pc2855 :
    Artifact.submissionArtifact.instructionPC 3423 = 0x13f8 := by rfl
@[simp] theorem pc2856 :
    Artifact.submissionArtifact.instructionPC 3424 = 0x13f9 := by rfl
@[simp] theorem pc2857 :
    Artifact.submissionArtifact.instructionPC 3425 = 0x13fa := by rfl
@[simp] theorem pc2858 :
    Artifact.submissionArtifact.instructionPC 3426 = 0x13fc := by rfl
@[simp] theorem pc2859 :
    Artifact.submissionArtifact.instructionPC 3427 = 0x13fd := by rfl
@[simp] theorem pc2860 :
    Artifact.submissionArtifact.instructionPC 3428 = 0x13fe := by rfl
@[simp] theorem pc2861 :
    Artifact.submissionArtifact.instructionPC 3429 = 0x13ff := by rfl
@[simp] theorem pc2862 :
    Artifact.submissionArtifact.instructionPC 3430 = 0x1400 := by rfl
@[simp] theorem pc2863 :
    Artifact.submissionArtifact.instructionPC 3431 = 0x1403 := by rfl

end Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard
