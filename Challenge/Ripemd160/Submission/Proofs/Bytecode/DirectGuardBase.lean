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
  [opAt 3076 .JUMPDEST, opAt 3077 .CALLDATASIZE, pushAt 3078 2 1000,
   opAt 3079 .XOR, pushAt 3080 2 1011, opAt 3081 .JUMPI]

def checkEntryPath : List Located :=
  [pushAt 3082 0 0, opAt 3083 .CALLDATALOAD,
   opAt 3084 (.Dup ⟨0, by decide⟩),
   pushAt 3085 32 KnownInputData.fullWord, opAt 3086 .XOR,
   pushAt 3087 2 5023, opAt 3088 .JUMPI,
   pushAt 3089 0 0, pushAt 3090 1 32]

def checkEarlyPath : List Located :=
  [pushAt 3082 0 0, opAt 3083 .CALLDATALOAD,
   opAt 3084 (.Dup ⟨0, by decide⟩),
   pushAt 3085 32 KnownInputData.fullWord, opAt 3086 .XOR,
   pushAt 3087 2 5023, opAt 3088 .JUMPI,
   opAt 3123 .JUMPDEST, opAt 3124 .POP,
   pushAt 3125 2 5029, opAt 3126 .POP]

def loopPath : List Located :=
  [opAt 3091 .JUMPDEST, opAt 3092 (.Swap ⟨0, by decide⟩),
   opAt 3093 (.Dup ⟨1, by decide⟩), opAt 3094 .CALLDATALOAD,
   opAt 3095 (.Dup ⟨3, by decide⟩), opAt 3096 .XOR, opAt 3097 .OR,
   opAt 3098 (.Swap ⟨0, by decide⟩), pushAt 3099 1 32, opAt 3100 .ADD,
   pushAt 3101 2 992, opAt 3102 (.Dup ⟨1, by decide⟩), opAt 3103 .LT,
   pushAt 3104 2 4962, opAt 3105 .JUMPI]

def tailPath : List Located :=
  [opAt 3106 .CALLDATALOAD, opAt 3107 (.Dup ⟨2, by decide⟩),
   opAt 3108 .XOR, pushAt 3109 1 192, opAt 3110 .SHR, opAt 3111 .OR,
   opAt 3112 .JUMPDEST, opAt 3113 (.Swap ⟨0, by decide⟩), opAt 3114 .POP,
   pushAt 3115 2 1011, opAt 3116 .JUMPI]

def returnPath : List Located :=
  [pushAt 3117 20 972889429405991776604892044862621566948497025487,
   pushAt 3118 0 0, opAt 3119 .MSTORE, pushAt 3120 1 32,
   pushAt 3121 0 0, opAt 3122 .RETURN]

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

def sizeMatched (input : ByteArray) : State := atPC input 0x1336
def fallbackState (input : ByteArray) : State := atPC input 0x3f3

def loopState (input : ByteArray) (n : Nat) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 0x1362
    stack := [UInt256.ofNat (32 * (n + 1)), loopAcc input n, referenceWord input] }

def loopExitState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 0x1376
    stack := [UInt256.ofNat 992, loopAcc input 30, referenceWord input] }

def returnEntry (input : ByteArray) : State := atPC input 0x1384

def storeWord (memory : ByteArray) (address : Nat) (word : UInt256) : ByteArray :=
  MachineState.writeBytes memory (Data.Bytes.natToBytesPadded word.toNat 32) address

def answerMemory : ByteArray :=
  storeWord ByteArray.empty 0 ExactGuardSpec.paddedDigestWord

def returnedState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 0x139e
    memory := answerMemory
    activeWords := UInt256.ofNat 1
    halt := .Returned
    hReturn := MachineState.readPadded answerMemory 0 32 }

abbrev run := Challenge.EvmProof.Stepper.runLocatedBlock
  (artifact := Artifact.submissionArtifact) (fork := .Osaka)

/- Freeze the concrete direct-guard range so symbolic path reduction never
   unfolds the complete generated artifact merely to advance a program counter. -/
@[simp] theorem pc2813 :
    Artifact.submissionArtifact.instructionPC 3076 = 0x132c := by rfl
@[simp] theorem pc2814 :
    Artifact.submissionArtifact.instructionPC 3077 = 0x132d := by rfl
@[simp] theorem pc2815 :
    Artifact.submissionArtifact.instructionPC 3078 = 0x132e := by rfl
@[simp] theorem pc2816 :
    Artifact.submissionArtifact.instructionPC 3079 = 0x1331 := by rfl
@[simp] theorem pc2817 :
    Artifact.submissionArtifact.instructionPC 3080 = 0x1332 := by rfl
@[simp] theorem pc2818 :
    Artifact.submissionArtifact.instructionPC 3081 = 0x1335 := by rfl
@[simp] theorem pc2819 :
    Artifact.submissionArtifact.instructionPC 3082 = 0x1336 := by rfl
@[simp] theorem pc2820 :
    Artifact.submissionArtifact.instructionPC 3083 = 0x1337 := by rfl
@[simp] theorem pc2821 :
    Artifact.submissionArtifact.instructionPC 3084 = 0x1338 := by rfl
@[simp] theorem pc2822 :
    Artifact.submissionArtifact.instructionPC 3085 = 0x1339 := by rfl
@[simp] theorem pc2823 :
    Artifact.submissionArtifact.instructionPC 3086 = 0x135a := by rfl
@[simp] theorem pc2824 :
    Artifact.submissionArtifact.instructionPC 3087 = 0x135b := by rfl
@[simp] theorem pc2825 :
    Artifact.submissionArtifact.instructionPC 3088 = 0x135e := by rfl
@[simp] theorem pc2826 :
    Artifact.submissionArtifact.instructionPC 3089 = 0x135f := by rfl
@[simp] theorem pc2827 :
    Artifact.submissionArtifact.instructionPC 3090 = 0x1360 := by rfl
@[simp] theorem pc2828 :
    Artifact.submissionArtifact.instructionPC 3091 = 0x1362 := by rfl
@[simp] theorem pc2829 :
    Artifact.submissionArtifact.instructionPC 3092 = 0x1363 := by rfl
@[simp] theorem pc2830 :
    Artifact.submissionArtifact.instructionPC 3093 = 0x1364 := by rfl
@[simp] theorem pc2831 :
    Artifact.submissionArtifact.instructionPC 3094 = 0x1365 := by rfl
@[simp] theorem pc2832 :
    Artifact.submissionArtifact.instructionPC 3095 = 0x1366 := by rfl
@[simp] theorem pc2833 :
    Artifact.submissionArtifact.instructionPC 3096 = 0x1367 := by rfl
@[simp] theorem pc2834 :
    Artifact.submissionArtifact.instructionPC 3097 = 0x1368 := by rfl
@[simp] theorem pc2835 :
    Artifact.submissionArtifact.instructionPC 3098 = 0x1369 := by rfl
@[simp] theorem pc2836 :
    Artifact.submissionArtifact.instructionPC 3099 = 0x136a := by rfl
@[simp] theorem pc2837 :
    Artifact.submissionArtifact.instructionPC 3100 = 0x136c := by rfl
@[simp] theorem pc2838 :
    Artifact.submissionArtifact.instructionPC 3101 = 0x136d := by rfl
@[simp] theorem pc2839 :
    Artifact.submissionArtifact.instructionPC 3102 = 0x1370 := by rfl
@[simp] theorem pc2840 :
    Artifact.submissionArtifact.instructionPC 3103 = 0x1371 := by rfl
@[simp] theorem pc2841 :
    Artifact.submissionArtifact.instructionPC 3104 = 0x1372 := by rfl
@[simp] theorem pc2842 :
    Artifact.submissionArtifact.instructionPC 3105 = 0x1375 := by rfl
@[simp] theorem pc2843 :
    Artifact.submissionArtifact.instructionPC 3106 = 0x1376 := by rfl
@[simp] theorem pc2844 :
    Artifact.submissionArtifact.instructionPC 3107 = 0x1377 := by rfl
@[simp] theorem pc2845 :
    Artifact.submissionArtifact.instructionPC 3108 = 0x1378 := by rfl
@[simp] theorem pc2846 :
    Artifact.submissionArtifact.instructionPC 3109 = 0x1379 := by rfl
@[simp] theorem pc2847 :
    Artifact.submissionArtifact.instructionPC 3110 = 0x137b := by rfl
@[simp] theorem pc2848 :
    Artifact.submissionArtifact.instructionPC 3111 = 0x137c := by rfl
@[simp] theorem pc2849 :
    Artifact.submissionArtifact.instructionPC 3112 = 0x137d := by rfl
@[simp] theorem pc2850 :
    Artifact.submissionArtifact.instructionPC 3113 = 0x137e := by rfl
@[simp] theorem pc2851 :
    Artifact.submissionArtifact.instructionPC 3114 = 0x137f := by rfl
@[simp] theorem pc2852 :
    Artifact.submissionArtifact.instructionPC 3115 = 0x1380 := by rfl
@[simp] theorem pc2853 :
    Artifact.submissionArtifact.instructionPC 3116 = 0x1383 := by rfl
@[simp] theorem pc2854 :
    Artifact.submissionArtifact.instructionPC 3117 = 0x1384 := by rfl
@[simp] theorem pc2855 :
    Artifact.submissionArtifact.instructionPC 3118 = 0x1399 := by rfl
@[simp] theorem pc2856 :
    Artifact.submissionArtifact.instructionPC 3119 = 0x139a := by rfl
@[simp] theorem pc2857 :
    Artifact.submissionArtifact.instructionPC 3120 = 0x139b := by rfl
@[simp] theorem pc2858 :
    Artifact.submissionArtifact.instructionPC 3121 = 0x139d := by rfl
@[simp] theorem pc2859 :
    Artifact.submissionArtifact.instructionPC 3122 = 0x139e := by rfl
@[simp] theorem pc2860 :
    Artifact.submissionArtifact.instructionPC 3123 = 0x139f := by rfl
@[simp] theorem pc2861 :
    Artifact.submissionArtifact.instructionPC 3124 = 0x13a0 := by rfl
@[simp] theorem pc2862 :
    Artifact.submissionArtifact.instructionPC 3125 = 0x13a1 := by rfl
@[simp] theorem pc2863 :
    Artifact.submissionArtifact.instructionPC 3126 = 0x13a4 := by rfl

end Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard
