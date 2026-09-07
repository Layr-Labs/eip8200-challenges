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
  [opAt 3414 .JUMPDEST, opAt 3415 .CALLDATASIZE, pushAt 3416 2 1000,
   opAt 3417 .XOR, pushAt 3418 2 1004, opAt 3419 .JUMPI]

def checkEntryPath : List Located :=
  [pushAt 3420 0 0, opAt 3421 .CALLDATALOAD,
   opAt 3422 (.Dup ⟨0, by decide⟩),
   pushAt 3423 1 255, pushAt 3424 0 0, opAt 3425 .NOT, opAt 3426 .DIV,
   pushAt 3427 1 97, opAt 3428 .MUL, opAt 3429 .XOR,
   pushAt 3430 2 5078, opAt 3431 .JUMPI,
   pushAt 3432 0 0, pushAt 3433 1 32]

def checkEarlyPath : List Located :=
  [pushAt 3420 0 0, opAt 3421 .CALLDATALOAD,
   opAt 3422 (.Dup ⟨0, by decide⟩),
   pushAt 3423 1 255, pushAt 3424 0 0, opAt 3425 .NOT, opAt 3426 .DIV,
   pushAt 3427 1 97, opAt 3428 .MUL, opAt 3429 .XOR,
   pushAt 3430 2 5078, opAt 3431 .JUMPI,
   opAt 3466 .JUMPDEST, opAt 3467 .POP,
   pushAt 3468 2 5084, opAt 3469 .POP]

def loopPath : List Located :=
  [opAt 3434 .JUMPDEST, opAt 3435 (.Swap ⟨0, by decide⟩),
   opAt 3436 (.Dup ⟨1, by decide⟩), opAt 3437 .CALLDATALOAD,
   opAt 3438 (.Dup ⟨3, by decide⟩), opAt 3439 .XOR, opAt 3440 .OR,
   opAt 3441 (.Swap ⟨0, by decide⟩), pushAt 3442 1 32, opAt 3443 .ADD,
   pushAt 3444 2 992, opAt 3445 (.Dup ⟨1, by decide⟩), opAt 3446 .LT,
   pushAt 3447 2 5017, opAt 3448 .JUMPI]

def tailPath : List Located :=
  [opAt 3449 .CALLDATALOAD, opAt 3450 (.Dup ⟨2, by decide⟩),
   opAt 3451 .XOR, pushAt 3452 1 192, opAt 3453 .SHR, opAt 3454 .OR,
   opAt 3455 .JUMPDEST, opAt 3456 (.Swap ⟨0, by decide⟩), opAt 3457 .POP,
   pushAt 3458 2 1004, opAt 3459 .JUMPI]

def returnPath : List Located :=
  [pushAt 3460 20 972889429405991776604892044862621566948497025487,
   pushAt 3461 0 0, opAt 3462 .MSTORE, pushAt 3463 1 32,
   pushAt 3464 0 0, opAt 3465 .RETURN]

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

def sizeMatched (input : ByteArray) : State := atPC input 0x1386
def fallbackState (input : ByteArray) : State := atPC input 0x3ec

def loopState (input : ByteArray) (n : Nat) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 0x1399
    stack := [UInt256.ofNat (32 * (n + 1)), loopAcc input n, referenceWord input] }

def loopExitState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 0x13ad
    stack := [UInt256.ofNat 992, loopAcc input 30, referenceWord input] }

def returnEntry (input : ByteArray) : State := atPC input 0x13bb

def storeWord (memory : ByteArray) (address : Nat) (word : UInt256) : ByteArray :=
  MachineState.writeBytes memory (Data.Bytes.natToBytesPadded word.toNat 32) address

def answerMemory : ByteArray :=
  storeWord ByteArray.empty 0 ExactGuardSpec.paddedDigestWord

def returnedState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 0x13d5
    memory := answerMemory
    activeWords := UInt256.ofNat 1
    halt := .Returned
    hReturn := MachineState.readPadded answerMemory 0 32 }

abbrev run := Challenge.EvmProof.Stepper.runLocatedBlock
  (artifact := Artifact.submissionArtifact) (fork := .Osaka)

/- Freeze the concrete direct-guard range so symbolic path reduction never
   unfolds the complete generated artifact merely to advance a program counter. -/
@[simp] theorem pc2813 :
    Artifact.submissionArtifact.instructionPC 3414 = 0x137c := by rfl
@[simp] theorem pc2814 :
    Artifact.submissionArtifact.instructionPC 3415 = 0x137d := by rfl
@[simp] theorem pc2815 :
    Artifact.submissionArtifact.instructionPC 3416 = 0x137e := by rfl
@[simp] theorem pc2816 :
    Artifact.submissionArtifact.instructionPC 3417 = 0x1381 := by rfl
@[simp] theorem pc2817 :
    Artifact.submissionArtifact.instructionPC 3418 = 0x1382 := by rfl
@[simp] theorem pc2818 :
    Artifact.submissionArtifact.instructionPC 3419 = 0x1385 := by rfl
@[simp] theorem pc2819 :
    Artifact.submissionArtifact.instructionPC 3420 = 0x1386 := by rfl
@[simp] theorem pc2820 :
    Artifact.submissionArtifact.instructionPC 3421 = 0x1387 := by rfl
@[simp] theorem pc2821 :
    Artifact.submissionArtifact.instructionPC 3422 = 0x1388 := by rfl
@[simp] theorem pc2822 :
    Artifact.submissionArtifact.instructionPC 3423 = 0x1389 := by rfl
@[simp] theorem pc2823 :
    Artifact.submissionArtifact.instructionPC 3429 = 0x1391 := by rfl
@[simp] theorem pc2824 :
    Artifact.submissionArtifact.instructionPC 3430 = 0x1392 := by rfl
@[simp] theorem pc2825 :
    Artifact.submissionArtifact.instructionPC 3431 = 0x1395 := by rfl
@[simp] theorem pc2826 :
    Artifact.submissionArtifact.instructionPC 3432 = 0x1396 := by rfl
@[simp] theorem pc2827 :
    Artifact.submissionArtifact.instructionPC 3433 = 0x1397 := by rfl
@[simp] theorem pc2828 :
    Artifact.submissionArtifact.instructionPC 3434 = 0x1399 := by rfl
@[simp] theorem pc2829 :
    Artifact.submissionArtifact.instructionPC 3435 = 0x139a := by rfl
@[simp] theorem pc2830 :
    Artifact.submissionArtifact.instructionPC 3436 = 0x139b := by rfl
@[simp] theorem pc2831 :
    Artifact.submissionArtifact.instructionPC 3437 = 0x139c := by rfl
@[simp] theorem pc2832 :
    Artifact.submissionArtifact.instructionPC 3438 = 0x139d := by rfl
@[simp] theorem pc2833 :
    Artifact.submissionArtifact.instructionPC 3439 = 0x139e := by rfl
@[simp] theorem pc2834 :
    Artifact.submissionArtifact.instructionPC 3440 = 0x139f := by rfl
@[simp] theorem pc2835 :
    Artifact.submissionArtifact.instructionPC 3441 = 0x13a0 := by rfl
@[simp] theorem pc2836 :
    Artifact.submissionArtifact.instructionPC 3442 = 0x13a1 := by rfl
@[simp] theorem pc2837 :
    Artifact.submissionArtifact.instructionPC 3443 = 0x13a3 := by rfl
@[simp] theorem pc2838 :
    Artifact.submissionArtifact.instructionPC 3444 = 0x13a4 := by rfl
@[simp] theorem pc2839 :
    Artifact.submissionArtifact.instructionPC 3445 = 0x13a7 := by rfl
@[simp] theorem pc2840 :
    Artifact.submissionArtifact.instructionPC 3446 = 0x13a8 := by rfl
@[simp] theorem pc2841 :
    Artifact.submissionArtifact.instructionPC 3447 = 0x13a9 := by rfl
@[simp] theorem pc2842 :
    Artifact.submissionArtifact.instructionPC 3448 = 0x13ac := by rfl
@[simp] theorem pc2843 :
    Artifact.submissionArtifact.instructionPC 3449 = 0x13ad := by rfl
@[simp] theorem pc2844 :
    Artifact.submissionArtifact.instructionPC 3450 = 0x13ae := by rfl
@[simp] theorem pc2845 :
    Artifact.submissionArtifact.instructionPC 3451 = 0x13af := by rfl
@[simp] theorem pc2846 :
    Artifact.submissionArtifact.instructionPC 3452 = 0x13b0 := by rfl
@[simp] theorem pc2847 :
    Artifact.submissionArtifact.instructionPC 3453 = 0x13b2 := by rfl
@[simp] theorem pc2848 :
    Artifact.submissionArtifact.instructionPC 3454 = 0x13b3 := by rfl
@[simp] theorem pc2849 :
    Artifact.submissionArtifact.instructionPC 3455 = 0x13b4 := by rfl
@[simp] theorem pc2850 :
    Artifact.submissionArtifact.instructionPC 3456 = 0x13b5 := by rfl
@[simp] theorem pc2851 :
    Artifact.submissionArtifact.instructionPC 3457 = 0x13b6 := by rfl
@[simp] theorem pc2852 :
    Artifact.submissionArtifact.instructionPC 3458 = 0x13b7 := by rfl
@[simp] theorem pc2853 :
    Artifact.submissionArtifact.instructionPC 3459 = 0x13ba := by rfl
@[simp] theorem pc2854 :
    Artifact.submissionArtifact.instructionPC 3460 = 0x13bb := by rfl
@[simp] theorem pc2855 :
    Artifact.submissionArtifact.instructionPC 3461 = 0x13d0 := by rfl
@[simp] theorem pc2856 :
    Artifact.submissionArtifact.instructionPC 3462 = 0x13d1 := by rfl
@[simp] theorem pc2857 :
    Artifact.submissionArtifact.instructionPC 3463 = 0x13d2 := by rfl
@[simp] theorem pc2858 :
    Artifact.submissionArtifact.instructionPC 3464 = 0x13d4 := by rfl
@[simp] theorem pc2859 :
    Artifact.submissionArtifact.instructionPC 3465 = 0x13d5 := by rfl
@[simp] theorem pc2860 :
    Artifact.submissionArtifact.instructionPC 3466 = 0x13d6 := by rfl
@[simp] theorem pc2861 :
    Artifact.submissionArtifact.instructionPC 3467 = 0x13d7 := by rfl
@[simp] theorem pc2862 :
    Artifact.submissionArtifact.instructionPC 3468 = 0x13d8 := by rfl
@[simp] theorem pc2863 :
    Artifact.submissionArtifact.instructionPC 3469 = 0x13db := by rfl

end Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard
