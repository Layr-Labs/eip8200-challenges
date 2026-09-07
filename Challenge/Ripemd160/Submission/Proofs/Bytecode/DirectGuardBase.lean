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
  [opAt 3403 .JUMPDEST, opAt 3404 .CALLDATASIZE, pushAt 3405 2 1000,
   opAt 3406 .XOR, pushAt 3407 2 972, opAt 3408 .JUMPI]

def checkEntryPath : List Located :=
  [pushAt 3409 0 0, opAt 3410 .CALLDATALOAD,
   opAt 3411 (.Dup ⟨0, by decide⟩),
   pushAt 3412 1 255, pushAt 3413 0 0, opAt 3414 .NOT, opAt 3415 .DIV,
   pushAt 3416 1 97, opAt 3417 .MUL, opAt 3418 .XOR,
   pushAt 3419 2 5037, opAt 3420 .JUMPI,
   pushAt 3421 0 0, pushAt 3422 1 32]

def checkEarlyPath : List Located :=
  [pushAt 3409 0 0, opAt 3410 .CALLDATALOAD,
   opAt 3411 (.Dup ⟨0, by decide⟩),
   pushAt 3412 1 255, pushAt 3413 0 0, opAt 3414 .NOT, opAt 3415 .DIV,
   pushAt 3416 1 97, opAt 3417 .MUL, opAt 3418 .XOR,
   pushAt 3419 2 5037, opAt 3420 .JUMPI,
   opAt 3455 .JUMPDEST, opAt 3456 .POP,
   pushAt 3457 2 5043, opAt 3458 .POP]

def loopPath : List Located :=
  [opAt 3423 .JUMPDEST, opAt 3424 (.Swap ⟨0, by decide⟩),
   opAt 3425 (.Dup ⟨1, by decide⟩), opAt 3426 .CALLDATALOAD,
   opAt 3427 (.Dup ⟨3, by decide⟩), opAt 3428 .XOR, opAt 3429 .OR,
   opAt 3430 (.Swap ⟨0, by decide⟩), pushAt 3431 1 32, opAt 3432 .ADD,
   pushAt 3433 2 992, opAt 3434 (.Dup ⟨1, by decide⟩), opAt 3435 .LT,
   pushAt 3436 2 4976, opAt 3437 .JUMPI]

def tailPath : List Located :=
  [opAt 3438 .CALLDATALOAD, opAt 3439 (.Dup ⟨2, by decide⟩),
   opAt 3440 .XOR, pushAt 3441 1 192, opAt 3442 .SHR, opAt 3443 .OR,
   opAt 3444 .JUMPDEST, opAt 3445 (.Swap ⟨0, by decide⟩), opAt 3446 .POP,
   pushAt 3447 2 972, opAt 3448 .JUMPI]

def returnPath : List Located :=
  [pushAt 3449 20 972889429405991776604892044862621566948497025487,
   pushAt 3450 0 0, opAt 3451 .MSTORE, pushAt 3452 1 32,
   pushAt 3453 0 0, opAt 3454 .RETURN]

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

def sizeMatched (input : ByteArray) : State := atPC input 0x135d
def fallbackState (input : ByteArray) : State := atPC input 0x3cc

def loopState (input : ByteArray) (n : Nat) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 0x1370
    stack := [UInt256.ofNat (32 * (n + 1)), loopAcc input n, referenceWord input] }

def loopExitState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 0x1384
    stack := [UInt256.ofNat 992, loopAcc input 30, referenceWord input] }

def returnEntry (input : ByteArray) : State := atPC input 0x1392

def storeWord (memory : ByteArray) (address : Nat) (word : UInt256) : ByteArray :=
  MachineState.writeBytes memory (Data.Bytes.natToBytesPadded word.toNat 32) address

def answerMemory : ByteArray :=
  storeWord ByteArray.empty 0 ExactGuardSpec.paddedDigestWord

def returnedState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 0x13ac
    memory := answerMemory
    activeWords := UInt256.ofNat 1
    halt := .Returned
    hReturn := MachineState.readPadded answerMemory 0 32 }

abbrev run := Challenge.EvmProof.Stepper.runLocatedBlock
  (artifact := Artifact.submissionArtifact) (fork := .Osaka)

/- Freeze the concrete direct-guard range so symbolic path reduction never
   unfolds the complete generated artifact merely to advance a program counter. -/
@[simp] theorem pc2813 :
    Artifact.submissionArtifact.instructionPC 3403 = 0x1353 := by rfl
@[simp] theorem pc2814 :
    Artifact.submissionArtifact.instructionPC 3404 = 0x1354 := by rfl
@[simp] theorem pc2815 :
    Artifact.submissionArtifact.instructionPC 3405 = 0x1355 := by rfl
@[simp] theorem pc2816 :
    Artifact.submissionArtifact.instructionPC 3406 = 0x1358 := by rfl
@[simp] theorem pc2817 :
    Artifact.submissionArtifact.instructionPC 3407 = 0x1359 := by rfl
@[simp] theorem pc2818 :
    Artifact.submissionArtifact.instructionPC 3408 = 0x135c := by rfl
@[simp] theorem pc2819 :
    Artifact.submissionArtifact.instructionPC 3409 = 0x135d := by rfl
@[simp] theorem pc2820 :
    Artifact.submissionArtifact.instructionPC 3410 = 0x135e := by rfl
@[simp] theorem pc2821 :
    Artifact.submissionArtifact.instructionPC 3411 = 0x135f := by rfl
@[simp] theorem pc2822 :
    Artifact.submissionArtifact.instructionPC 3412 = 0x1360 := by rfl
@[simp] theorem pc2823 :
    Artifact.submissionArtifact.instructionPC 3418 = 0x1368 := by rfl
@[simp] theorem pc2824 :
    Artifact.submissionArtifact.instructionPC 3419 = 0x1369 := by rfl
@[simp] theorem pc2825 :
    Artifact.submissionArtifact.instructionPC 3420 = 0x136c := by rfl
@[simp] theorem pc2826 :
    Artifact.submissionArtifact.instructionPC 3421 = 0x136d := by rfl
@[simp] theorem pc2827 :
    Artifact.submissionArtifact.instructionPC 3422 = 0x136e := by rfl
@[simp] theorem pc2828 :
    Artifact.submissionArtifact.instructionPC 3423 = 0x1370 := by rfl
@[simp] theorem pc2829 :
    Artifact.submissionArtifact.instructionPC 3424 = 0x1371 := by rfl
@[simp] theorem pc2830 :
    Artifact.submissionArtifact.instructionPC 3425 = 0x1372 := by rfl
@[simp] theorem pc2831 :
    Artifact.submissionArtifact.instructionPC 3426 = 0x1373 := by rfl
@[simp] theorem pc2832 :
    Artifact.submissionArtifact.instructionPC 3427 = 0x1374 := by rfl
@[simp] theorem pc2833 :
    Artifact.submissionArtifact.instructionPC 3428 = 0x1375 := by rfl
@[simp] theorem pc2834 :
    Artifact.submissionArtifact.instructionPC 3429 = 0x1376 := by rfl
@[simp] theorem pc2835 :
    Artifact.submissionArtifact.instructionPC 3430 = 0x1377 := by rfl
@[simp] theorem pc2836 :
    Artifact.submissionArtifact.instructionPC 3431 = 0x1378 := by rfl
@[simp] theorem pc2837 :
    Artifact.submissionArtifact.instructionPC 3432 = 0x137a := by rfl
@[simp] theorem pc2838 :
    Artifact.submissionArtifact.instructionPC 3433 = 0x137b := by rfl
@[simp] theorem pc2839 :
    Artifact.submissionArtifact.instructionPC 3434 = 0x137e := by rfl
@[simp] theorem pc2840 :
    Artifact.submissionArtifact.instructionPC 3435 = 0x137f := by rfl
@[simp] theorem pc2841 :
    Artifact.submissionArtifact.instructionPC 3436 = 0x1380 := by rfl
@[simp] theorem pc2842 :
    Artifact.submissionArtifact.instructionPC 3437 = 0x1383 := by rfl
@[simp] theorem pc2843 :
    Artifact.submissionArtifact.instructionPC 3438 = 0x1384 := by rfl
@[simp] theorem pc2844 :
    Artifact.submissionArtifact.instructionPC 3439 = 0x1385 := by rfl
@[simp] theorem pc2845 :
    Artifact.submissionArtifact.instructionPC 3440 = 0x1386 := by rfl
@[simp] theorem pc2846 :
    Artifact.submissionArtifact.instructionPC 3441 = 0x1387 := by rfl
@[simp] theorem pc2847 :
    Artifact.submissionArtifact.instructionPC 3442 = 0x1389 := by rfl
@[simp] theorem pc2848 :
    Artifact.submissionArtifact.instructionPC 3443 = 0x138a := by rfl
@[simp] theorem pc2849 :
    Artifact.submissionArtifact.instructionPC 3444 = 0x138b := by rfl
@[simp] theorem pc2850 :
    Artifact.submissionArtifact.instructionPC 3445 = 0x138c := by rfl
@[simp] theorem pc2851 :
    Artifact.submissionArtifact.instructionPC 3446 = 0x138d := by rfl
@[simp] theorem pc2852 :
    Artifact.submissionArtifact.instructionPC 3447 = 0x138e := by rfl
@[simp] theorem pc2853 :
    Artifact.submissionArtifact.instructionPC 3448 = 0x1391 := by rfl
@[simp] theorem pc2854 :
    Artifact.submissionArtifact.instructionPC 3449 = 0x1392 := by rfl
@[simp] theorem pc2855 :
    Artifact.submissionArtifact.instructionPC 3450 = 0x13a7 := by rfl
@[simp] theorem pc2856 :
    Artifact.submissionArtifact.instructionPC 3451 = 0x13a8 := by rfl
@[simp] theorem pc2857 :
    Artifact.submissionArtifact.instructionPC 3452 = 0x13a9 := by rfl
@[simp] theorem pc2858 :
    Artifact.submissionArtifact.instructionPC 3453 = 0x13ab := by rfl
@[simp] theorem pc2859 :
    Artifact.submissionArtifact.instructionPC 3454 = 0x13ac := by rfl
@[simp] theorem pc2860 :
    Artifact.submissionArtifact.instructionPC 3455 = 0x13ad := by rfl
@[simp] theorem pc2861 :
    Artifact.submissionArtifact.instructionPC 3456 = 0x13ae := by rfl
@[simp] theorem pc2862 :
    Artifact.submissionArtifact.instructionPC 3457 = 0x13af := by rfl
@[simp] theorem pc2863 :
    Artifact.submissionArtifact.instructionPC 3458 = 0x13b2 := by rfl

end Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard
