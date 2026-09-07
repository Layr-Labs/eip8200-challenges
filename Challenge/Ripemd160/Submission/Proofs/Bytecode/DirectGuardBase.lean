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
  [opAt 3268 .JUMPDEST, opAt 3269 .CALLDATASIZE, pushAt 3270 2 1000,
   opAt 3271 .XOR, pushAt 3272 2 1011, opAt 3273 .JUMPI]

def checkEntryPath : List Located :=
  [pushAt 3274 0 0, opAt 3275 .CALLDATALOAD,
   opAt 3276 (.Dup ⟨0, by decide⟩),
   pushAt 3277 1 255, pushAt 3278 0 0, opAt 3279 .NOT, opAt 3280 .DIV,
   pushAt 3281 1 97, opAt 3282 .MUL, opAt 3283 .XOR,
   pushAt 3284 2 5144, opAt 3285 .JUMPI,
   pushAt 3286 0 0, pushAt 3287 1 32]

def checkEarlyPath : List Located :=
  [pushAt 3274 0 0, opAt 3275 .CALLDATALOAD,
   opAt 3276 (.Dup ⟨0, by decide⟩),
   pushAt 3277 1 255, pushAt 3278 0 0, opAt 3279 .NOT, opAt 3280 .DIV,
   pushAt 3281 1 97, opAt 3282 .MUL, opAt 3283 .XOR,
   pushAt 3284 2 5144, opAt 3285 .JUMPI,
   opAt 3320 .JUMPDEST, opAt 3321 .POP,
   pushAt 3322 2 5150, opAt 3323 .POP]

def loopPath : List Located :=
  [opAt 3288 .JUMPDEST, opAt 3289 (.Swap ⟨0, by decide⟩),
   opAt 3290 (.Dup ⟨1, by decide⟩), opAt 3291 .CALLDATALOAD,
   opAt 3292 (.Dup ⟨3, by decide⟩), opAt 3293 .XOR, opAt 3294 .OR,
   opAt 3295 (.Swap ⟨0, by decide⟩), pushAt 3296 1 32, opAt 3297 .ADD,
   pushAt 3298 2 992, opAt 3299 (.Dup ⟨1, by decide⟩), opAt 3300 .LT,
   pushAt 3301 2 5083, opAt 3302 .JUMPI]

def tailPath : List Located :=
  [opAt 3303 .CALLDATALOAD, opAt 3304 (.Dup ⟨2, by decide⟩),
   opAt 3305 .XOR, pushAt 3306 1 192, opAt 3307 .SHR, opAt 3308 .OR,
   opAt 3309 .JUMPDEST, opAt 3310 (.Swap ⟨0, by decide⟩), opAt 3311 .POP,
   pushAt 3312 2 1011, opAt 3313 .JUMPI]

def returnPath : List Located :=
  [pushAt 3314 20 972889429405991776604892044862621566948497025487,
   pushAt 3315 0 0, opAt 3316 .MSTORE, pushAt 3317 1 32,
   pushAt 3318 0 0, opAt 3319 .RETURN]

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

def sizeMatched (input : ByteArray) : State := atPC input 0x13c8
def fallbackState (input : ByteArray) : State := atPC input 0x3f3

def loopState (input : ByteArray) (n : Nat) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 0x13db
    stack := [UInt256.ofNat (32 * (n + 1)), loopAcc input n, referenceWord input] }

def loopExitState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 0x13ef
    stack := [UInt256.ofNat 992, loopAcc input 30, referenceWord input] }

def returnEntry (input : ByteArray) : State := atPC input 0x13fd

def storeWord (memory : ByteArray) (address : Nat) (word : UInt256) : ByteArray :=
  MachineState.writeBytes memory (Data.Bytes.natToBytesPadded word.toNat 32) address

def answerMemory : ByteArray :=
  storeWord ByteArray.empty 0 ExactGuardSpec.paddedDigestWord

def returnedState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 0x1417
    memory := answerMemory
    activeWords := UInt256.ofNat 1
    halt := .Returned
    hReturn := MachineState.readPadded answerMemory 0 32 }

abbrev run := Challenge.EvmProof.Stepper.runLocatedBlock
  (artifact := Artifact.submissionArtifact) (fork := .Osaka)

/- Freeze the concrete direct-guard range so symbolic path reduction never
   unfolds the complete generated artifact merely to advance a program counter. -/
@[simp] theorem pc2813 :
    Artifact.submissionArtifact.instructionPC 3268 = 0x13be := by rfl
@[simp] theorem pc2814 :
    Artifact.submissionArtifact.instructionPC 3269 = 0x13bf := by rfl
@[simp] theorem pc2815 :
    Artifact.submissionArtifact.instructionPC 3270 = 0x13c0 := by rfl
@[simp] theorem pc2816 :
    Artifact.submissionArtifact.instructionPC 3271 = 0x13c3 := by rfl
@[simp] theorem pc2817 :
    Artifact.submissionArtifact.instructionPC 3272 = 0x13c4 := by rfl
@[simp] theorem pc2818 :
    Artifact.submissionArtifact.instructionPC 3273 = 0x13c7 := by rfl
@[simp] theorem pc2819 :
    Artifact.submissionArtifact.instructionPC 3274 = 0x13c8 := by rfl
@[simp] theorem pc2820 :
    Artifact.submissionArtifact.instructionPC 3275 = 0x13c9 := by rfl
@[simp] theorem pc2821 :
    Artifact.submissionArtifact.instructionPC 3276 = 0x13ca := by rfl
@[simp] theorem pc2822 :
    Artifact.submissionArtifact.instructionPC 3277 = 0x13cb := by rfl
@[simp] theorem pc2823 :
    Artifact.submissionArtifact.instructionPC 3283 = 0x13d3 := by rfl
@[simp] theorem pc2824 :
    Artifact.submissionArtifact.instructionPC 3284 = 0x13d4 := by rfl
@[simp] theorem pc2825 :
    Artifact.submissionArtifact.instructionPC 3285 = 0x13d7 := by rfl
@[simp] theorem pc2826 :
    Artifact.submissionArtifact.instructionPC 3286 = 0x13d8 := by rfl
@[simp] theorem pc2827 :
    Artifact.submissionArtifact.instructionPC 3287 = 0x13d9 := by rfl
@[simp] theorem pc2828 :
    Artifact.submissionArtifact.instructionPC 3288 = 0x13db := by rfl
@[simp] theorem pc2829 :
    Artifact.submissionArtifact.instructionPC 3289 = 0x13dc := by rfl
@[simp] theorem pc2830 :
    Artifact.submissionArtifact.instructionPC 3290 = 0x13dd := by rfl
@[simp] theorem pc2831 :
    Artifact.submissionArtifact.instructionPC 3291 = 0x13de := by rfl
@[simp] theorem pc2832 :
    Artifact.submissionArtifact.instructionPC 3292 = 0x13df := by rfl
@[simp] theorem pc2833 :
    Artifact.submissionArtifact.instructionPC 3293 = 0x13e0 := by rfl
@[simp] theorem pc2834 :
    Artifact.submissionArtifact.instructionPC 3294 = 0x13e1 := by rfl
@[simp] theorem pc2835 :
    Artifact.submissionArtifact.instructionPC 3295 = 0x13e2 := by rfl
@[simp] theorem pc2836 :
    Artifact.submissionArtifact.instructionPC 3296 = 0x13e3 := by rfl
@[simp] theorem pc2837 :
    Artifact.submissionArtifact.instructionPC 3297 = 0x13e5 := by rfl
@[simp] theorem pc2838 :
    Artifact.submissionArtifact.instructionPC 3298 = 0x13e6 := by rfl
@[simp] theorem pc2839 :
    Artifact.submissionArtifact.instructionPC 3299 = 0x13e9 := by rfl
@[simp] theorem pc2840 :
    Artifact.submissionArtifact.instructionPC 3300 = 0x13ea := by rfl
@[simp] theorem pc2841 :
    Artifact.submissionArtifact.instructionPC 3301 = 0x13eb := by rfl
@[simp] theorem pc2842 :
    Artifact.submissionArtifact.instructionPC 3302 = 0x13ee := by rfl
@[simp] theorem pc2843 :
    Artifact.submissionArtifact.instructionPC 3303 = 0x13ef := by rfl
@[simp] theorem pc2844 :
    Artifact.submissionArtifact.instructionPC 3304 = 0x13f0 := by rfl
@[simp] theorem pc2845 :
    Artifact.submissionArtifact.instructionPC 3305 = 0x13f1 := by rfl
@[simp] theorem pc2846 :
    Artifact.submissionArtifact.instructionPC 3306 = 0x13f2 := by rfl
@[simp] theorem pc2847 :
    Artifact.submissionArtifact.instructionPC 3307 = 0x13f4 := by rfl
@[simp] theorem pc2848 :
    Artifact.submissionArtifact.instructionPC 3308 = 0x13f5 := by rfl
@[simp] theorem pc2849 :
    Artifact.submissionArtifact.instructionPC 3309 = 0x13f6 := by rfl
@[simp] theorem pc2850 :
    Artifact.submissionArtifact.instructionPC 3310 = 0x13f7 := by rfl
@[simp] theorem pc2851 :
    Artifact.submissionArtifact.instructionPC 3311 = 0x13f8 := by rfl
@[simp] theorem pc2852 :
    Artifact.submissionArtifact.instructionPC 3312 = 0x13f9 := by rfl
@[simp] theorem pc2853 :
    Artifact.submissionArtifact.instructionPC 3313 = 0x13fc := by rfl
@[simp] theorem pc2854 :
    Artifact.submissionArtifact.instructionPC 3314 = 0x13fd := by rfl
@[simp] theorem pc2855 :
    Artifact.submissionArtifact.instructionPC 3315 = 0x1412 := by rfl
@[simp] theorem pc2856 :
    Artifact.submissionArtifact.instructionPC 3316 = 0x1413 := by rfl
@[simp] theorem pc2857 :
    Artifact.submissionArtifact.instructionPC 3317 = 0x1414 := by rfl
@[simp] theorem pc2858 :
    Artifact.submissionArtifact.instructionPC 3318 = 0x1416 := by rfl
@[simp] theorem pc2859 :
    Artifact.submissionArtifact.instructionPC 3319 = 0x1417 := by rfl
@[simp] theorem pc2860 :
    Artifact.submissionArtifact.instructionPC 3320 = 0x1418 := by rfl
@[simp] theorem pc2861 :
    Artifact.submissionArtifact.instructionPC 3321 = 0x1419 := by rfl
@[simp] theorem pc2862 :
    Artifact.submissionArtifact.instructionPC 3322 = 0x141a := by rfl
@[simp] theorem pc2863 :
    Artifact.submissionArtifact.instructionPC 3323 = 0x141d := by rfl

end Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard
