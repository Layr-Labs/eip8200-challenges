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
  [opAt 2500 .JUMPDEST, opAt 2501 .CALLDATASIZE, pushAt 2502 2 1000,
   opAt 2503 .XOR, pushAt 2504 2 649, opAt 2505 .JUMPI]

def checkEntryPath : List Located :=
  [pushAt 2506 0 0, opAt 2507 .CALLDATALOAD,
   opAt 2508 (.Dup ⟨0, by decide⟩),
   pushAt 2509 32 KnownInputData.fullWord, opAt 2510 .XOR,
   pushAt 2511 2 4996, opAt 2512 .JUMPI,
   pushAt 2513 0 0, pushAt 2514 1 32]

def checkEarlyPath : List Located :=
  [pushAt 2506 0 0, opAt 2507 .CALLDATALOAD,
   opAt 2508 (.Dup ⟨0, by decide⟩),
   pushAt 2509 32 KnownInputData.fullWord, opAt 2510 .XOR,
   pushAt 2511 2 4996, opAt 2512 .JUMPI,
   opAt 2547 .JUMPDEST, opAt 2548 .POP,
   pushAt 2549 2 5072, opAt 2550 .JUMP]

def loopPath : List Located :=
  [opAt 2515 .JUMPDEST, opAt 2516 (.Swap ⟨0, by decide⟩),
   opAt 2517 (.Dup ⟨1, by decide⟩), opAt 2518 .CALLDATALOAD,
   opAt 2519 (.Dup ⟨3, by decide⟩), opAt 2520 .XOR, opAt 2521 .OR,
   opAt 2522 (.Swap ⟨0, by decide⟩), pushAt 2523 1 32, opAt 2524 .ADD,
   pushAt 2525 2 992, opAt 2526 (.Dup ⟨1, by decide⟩), opAt 2527 .LT,
   pushAt 2528 2 4935, opAt 2529 .JUMPI]

def tailPath : List Located :=
  [opAt 2530 .CALLDATALOAD, opAt 2531 (.Dup ⟨2, by decide⟩),
   opAt 2532 .XOR, pushAt 2533 1 192, opAt 2534 .SHR, opAt 2535 .OR,
   opAt 2536 .JUMPDEST, opAt 2537 (.Swap ⟨0, by decide⟩), opAt 2538 .POP,
   pushAt 2539 2 649, opAt 2540 .JUMPI]

def returnPath : List Located :=
  [pushAt 2541 20 972889429405991776604892044862621566948497025487,
   pushAt 2542 0 0, opAt 2543 .MSTORE, pushAt 2544 1 32,
   pushAt 2545 0 0, opAt 2546 .RETURN]

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
def fallbackState (input : ByteArray) : State := atPC input 0x289

def loopState (input : ByteArray) (n : Nat) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 0x1347
    stack := [UInt256.ofNat (32 * (n + 1)), loopAcc input n, referenceWord input] }

def loopExitState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 0x135b
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
    Artifact.submissionArtifact.instructionPC 2500 = 4881 := by rfl
@[simp] theorem pc2814 :
    Artifact.submissionArtifact.instructionPC 2501 = 4882 := by rfl
@[simp] theorem pc2815 :
    Artifact.submissionArtifact.instructionPC 2502 = 4883 := by rfl
@[simp] theorem pc2816 :
    Artifact.submissionArtifact.instructionPC 2503 = 4886 := by rfl
@[simp] theorem pc2817 :
    Artifact.submissionArtifact.instructionPC 2504 = 4887 := by rfl
@[simp] theorem pc2818 :
    Artifact.submissionArtifact.instructionPC 2505 = 4890 := by rfl
@[simp] theorem pc2819 :
    Artifact.submissionArtifact.instructionPC 2506 = 4891 := by rfl
@[simp] theorem pc2820 :
    Artifact.submissionArtifact.instructionPC 2507 = 4892 := by rfl
@[simp] theorem pc2821 :
    Artifact.submissionArtifact.instructionPC 2508 = 4893 := by rfl
@[simp] theorem pc2822 :
    Artifact.submissionArtifact.instructionPC 2509 = 4894 := by rfl
@[simp] theorem pc2823 :
    Artifact.submissionArtifact.instructionPC 2510 = 4927 := by rfl
@[simp] theorem pc2824 :
    Artifact.submissionArtifact.instructionPC 2511 = 4928 := by rfl
@[simp] theorem pc2825 :
    Artifact.submissionArtifact.instructionPC 2512 = 4931 := by rfl
@[simp] theorem pc2826 :
    Artifact.submissionArtifact.instructionPC 2513 = 4932 := by rfl
@[simp] theorem pc2827 :
    Artifact.submissionArtifact.instructionPC 2514 = 4933 := by rfl
@[simp] theorem pc2828 :
    Artifact.submissionArtifact.instructionPC 2515 = 4935 := by rfl
@[simp] theorem pc2829 :
    Artifact.submissionArtifact.instructionPC 2516 = 4936 := by rfl
@[simp] theorem pc2830 :
    Artifact.submissionArtifact.instructionPC 2517 = 4937 := by rfl
@[simp] theorem pc2831 :
    Artifact.submissionArtifact.instructionPC 2518 = 4938 := by rfl
@[simp] theorem pc2832 :
    Artifact.submissionArtifact.instructionPC 2519 = 4939 := by rfl
@[simp] theorem pc2833 :
    Artifact.submissionArtifact.instructionPC 2520 = 4940 := by rfl
@[simp] theorem pc2834 :
    Artifact.submissionArtifact.instructionPC 2521 = 4941 := by rfl
@[simp] theorem pc2835 :
    Artifact.submissionArtifact.instructionPC 2522 = 4942 := by rfl
@[simp] theorem pc2836 :
    Artifact.submissionArtifact.instructionPC 2523 = 4943 := by rfl
@[simp] theorem pc2837 :
    Artifact.submissionArtifact.instructionPC 2524 = 4945 := by rfl
@[simp] theorem pc2838 :
    Artifact.submissionArtifact.instructionPC 2525 = 4946 := by rfl
@[simp] theorem pc2839 :
    Artifact.submissionArtifact.instructionPC 2526 = 4949 := by rfl
@[simp] theorem pc2840 :
    Artifact.submissionArtifact.instructionPC 2527 = 4950 := by rfl
@[simp] theorem pc2841 :
    Artifact.submissionArtifact.instructionPC 2528 = 4951 := by rfl
@[simp] theorem pc2842 :
    Artifact.submissionArtifact.instructionPC 2529 = 4954 := by rfl
@[simp] theorem pc2843 :
    Artifact.submissionArtifact.instructionPC 2530 = 4955 := by rfl
@[simp] theorem pc2844 :
    Artifact.submissionArtifact.instructionPC 2531 = 4956 := by rfl
@[simp] theorem pc2845 :
    Artifact.submissionArtifact.instructionPC 2532 = 4957 := by rfl
@[simp] theorem pc2846 :
    Artifact.submissionArtifact.instructionPC 2533 = 4958 := by rfl
@[simp] theorem pc2847 :
    Artifact.submissionArtifact.instructionPC 2534 = 4960 := by rfl
@[simp] theorem pc2848 :
    Artifact.submissionArtifact.instructionPC 2535 = 4961 := by rfl
@[simp] theorem pc2849 :
    Artifact.submissionArtifact.instructionPC 2536 = 4962 := by rfl
@[simp] theorem pc2850 :
    Artifact.submissionArtifact.instructionPC 2537 = 4963 := by rfl
@[simp] theorem pc2851 :
    Artifact.submissionArtifact.instructionPC 2538 = 4964 := by rfl
@[simp] theorem pc2852 :
    Artifact.submissionArtifact.instructionPC 2539 = 4965 := by rfl
@[simp] theorem pc2853 :
    Artifact.submissionArtifact.instructionPC 2540 = 4968 := by rfl
@[simp] theorem pc2854 :
    Artifact.submissionArtifact.instructionPC 2541 = 4969 := by rfl
@[simp] theorem pc2855 :
    Artifact.submissionArtifact.instructionPC 2542 = 4990 := by rfl
@[simp] theorem pc2856 :
    Artifact.submissionArtifact.instructionPC 2543 = 4991 := by rfl
@[simp] theorem pc2857 :
    Artifact.submissionArtifact.instructionPC 2544 = 4992 := by rfl
@[simp] theorem pc2858 :
    Artifact.submissionArtifact.instructionPC 2545 = 4994 := by rfl
@[simp] theorem pc2859 :
    Artifact.submissionArtifact.instructionPC 2546 = 4995 := by rfl
@[simp] theorem pc2860 :
    Artifact.submissionArtifact.instructionPC 2547 = 4996 := by rfl
@[simp] theorem pc2861 :
    Artifact.submissionArtifact.instructionPC 2548 = 4997 := by rfl
@[simp] theorem pc2862 :
    Artifact.submissionArtifact.instructionPC 2549 = 4998 := by rfl
@[simp] theorem pc2863 :
    Artifact.submissionArtifact.instructionPC 2550 = 5001 := by rfl

end Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard
