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
  [opAt 3313 .JUMPDEST, opAt 3314 .CALLDATASIZE, pushAt 3315 2 1000,
   opAt 3316 .XOR, pushAt 3317 2 972, opAt 3318 .JUMPI]

def checkEntryPath : List Located :=
  [pushAt 3319 0 0, opAt 3320 .CALLDATALOAD,
   opAt 3321 (.Dup ⟨0, by decide⟩),
   pushAt 3322 1 255, pushAt 3323 0 0, opAt 3324 .NOT, opAt 3325 .DIV,
   pushAt 3326 1 97, opAt 3327 .MUL, opAt 3328 .XOR,
   pushAt 3329 2 5018, opAt 3330 .JUMPI,
   pushAt 3331 0 0, pushAt 3332 1 32]

def checkEarlyPath : List Located :=
  [pushAt 3319 0 0, opAt 3320 .CALLDATALOAD,
   opAt 3321 (.Dup ⟨0, by decide⟩),
   pushAt 3322 1 255, pushAt 3323 0 0, opAt 3324 .NOT, opAt 3325 .DIV,
   pushAt 3326 1 97, opAt 3327 .MUL, opAt 3328 .XOR,
   pushAt 3329 2 5018, opAt 3330 .JUMPI,
   opAt 3365 .JUMPDEST, opAt 3366 .POP,
   pushAt 3367 2 5024, opAt 3368 .JUMP]

def loopPath : List Located :=
  [opAt 3333 .JUMPDEST, opAt 3334 (.Swap ⟨0, by decide⟩),
   opAt 3335 (.Dup ⟨1, by decide⟩), opAt 3336 .CALLDATALOAD,
   opAt 3337 (.Dup ⟨3, by decide⟩), opAt 3338 .XOR, opAt 3339 .OR,
   opAt 3340 (.Swap ⟨0, by decide⟩), pushAt 3341 1 32, opAt 3342 .ADD,
   pushAt 3343 2 992, opAt 3344 (.Dup ⟨1, by decide⟩), opAt 3345 .LT,
   pushAt 3346 2 4957, opAt 3347 .JUMPI]

def tailPath : List Located :=
  [opAt 3348 .CALLDATALOAD, opAt 3349 (.Dup ⟨2, by decide⟩),
   opAt 3350 .XOR, pushAt 3351 1 192, opAt 3352 .SHR, opAt 3353 .OR,
   opAt 3354 .JUMPDEST, opAt 3355 (.Swap ⟨0, by decide⟩), opAt 3356 .POP,
   pushAt 3357 2 972, opAt 3358 .JUMPI]

def returnPath : List Located :=
  [pushAt 3359 20 972889429405991776604892044862621566948497025487,
   pushAt 3360 0 0, opAt 3361 .MSTORE, pushAt 3362 1 32,
   pushAt 3363 0 0, opAt 3364 .RETURN]

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

def sizeMatched (input : ByteArray) : State := atPC input 0x134a
def fallbackState (input : ByteArray) : State := atPC input 0x3cc

def loopState (input : ByteArray) (n : Nat) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 0x135d
    stack := [UInt256.ofNat (32 * (n + 1)), loopAcc input n, referenceWord input] }

def loopExitState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 0x1371
    stack := [UInt256.ofNat 992, loopAcc input 30, referenceWord input] }

def returnEntry (input : ByteArray) : State := atPC input 0x137f

def storeWord (memory : ByteArray) (address : Nat) (word : UInt256) : ByteArray :=
  MachineState.writeBytes memory (Data.Bytes.natToBytesPadded word.toNat 32) address

def answerMemory : ByteArray :=
  storeWord ByteArray.empty 0 ExactGuardSpec.paddedDigestWord

def returnedState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 0x1399
    memory := answerMemory
    activeWords := UInt256.ofNat 1
    halt := .Returned
    hReturn := MachineState.readPadded answerMemory 0 32 }

abbrev run := Challenge.EvmProof.Stepper.runLocatedBlock
  (artifact := Artifact.submissionArtifact) (fork := .Osaka)

/- Freeze the concrete direct-guard range so symbolic path reduction never
   unfolds the complete generated artifact merely to advance a program counter. -/
@[simp] theorem pc2813 :
    Artifact.submissionArtifact.instructionPC 3313 = 0x1340 := by rfl
@[simp] theorem pc2814 :
    Artifact.submissionArtifact.instructionPC 3314 = 0x1341 := by rfl
@[simp] theorem pc2815 :
    Artifact.submissionArtifact.instructionPC 3315 = 0x1342 := by rfl
@[simp] theorem pc2816 :
    Artifact.submissionArtifact.instructionPC 3316 = 0x1345 := by rfl
@[simp] theorem pc2817 :
    Artifact.submissionArtifact.instructionPC 3317 = 0x1346 := by rfl
@[simp] theorem pc2818 :
    Artifact.submissionArtifact.instructionPC 3318 = 0x1349 := by rfl
@[simp] theorem pc2819 :
    Artifact.submissionArtifact.instructionPC 3319 = 0x134a := by rfl
@[simp] theorem pc2820 :
    Artifact.submissionArtifact.instructionPC 3320 = 0x134b := by rfl
@[simp] theorem pc2821 :
    Artifact.submissionArtifact.instructionPC 3321 = 0x134c := by rfl
@[simp] theorem pc2822 :
    Artifact.submissionArtifact.instructionPC 3322 = 0x134d := by rfl
@[simp] theorem pc2823 :
    Artifact.submissionArtifact.instructionPC 3328 = 0x1355 := by rfl
@[simp] theorem pc2824 :
    Artifact.submissionArtifact.instructionPC 3329 = 0x1356 := by rfl
@[simp] theorem pc2825 :
    Artifact.submissionArtifact.instructionPC 3330 = 0x1359 := by rfl
@[simp] theorem pc2826 :
    Artifact.submissionArtifact.instructionPC 3331 = 0x135a := by rfl
@[simp] theorem pc2827 :
    Artifact.submissionArtifact.instructionPC 3332 = 0x135b := by rfl
@[simp] theorem pc2828 :
    Artifact.submissionArtifact.instructionPC 3333 = 0x135d := by rfl
@[simp] theorem pc2829 :
    Artifact.submissionArtifact.instructionPC 3334 = 0x135e := by rfl
@[simp] theorem pc2830 :
    Artifact.submissionArtifact.instructionPC 3335 = 0x135f := by rfl
@[simp] theorem pc2831 :
    Artifact.submissionArtifact.instructionPC 3336 = 0x1360 := by rfl
@[simp] theorem pc2832 :
    Artifact.submissionArtifact.instructionPC 3337 = 0x1361 := by rfl
@[simp] theorem pc2833 :
    Artifact.submissionArtifact.instructionPC 3338 = 0x1362 := by rfl
@[simp] theorem pc2834 :
    Artifact.submissionArtifact.instructionPC 3339 = 0x1363 := by rfl
@[simp] theorem pc2835 :
    Artifact.submissionArtifact.instructionPC 3340 = 0x1364 := by rfl
@[simp] theorem pc2836 :
    Artifact.submissionArtifact.instructionPC 3341 = 0x1365 := by rfl
@[simp] theorem pc2837 :
    Artifact.submissionArtifact.instructionPC 3342 = 0x1367 := by rfl
@[simp] theorem pc2838 :
    Artifact.submissionArtifact.instructionPC 3343 = 0x1368 := by rfl
@[simp] theorem pc2839 :
    Artifact.submissionArtifact.instructionPC 3344 = 0x136b := by rfl
@[simp] theorem pc2840 :
    Artifact.submissionArtifact.instructionPC 3345 = 0x136c := by rfl
@[simp] theorem pc2841 :
    Artifact.submissionArtifact.instructionPC 3346 = 0x136d := by rfl
@[simp] theorem pc2842 :
    Artifact.submissionArtifact.instructionPC 3347 = 0x1370 := by rfl
@[simp] theorem pc2843 :
    Artifact.submissionArtifact.instructionPC 3348 = 0x1371 := by rfl
@[simp] theorem pc2844 :
    Artifact.submissionArtifact.instructionPC 3349 = 0x1372 := by rfl
@[simp] theorem pc2845 :
    Artifact.submissionArtifact.instructionPC 3350 = 0x1373 := by rfl
@[simp] theorem pc2846 :
    Artifact.submissionArtifact.instructionPC 3351 = 0x1374 := by rfl
@[simp] theorem pc2847 :
    Artifact.submissionArtifact.instructionPC 3352 = 0x1376 := by rfl
@[simp] theorem pc2848 :
    Artifact.submissionArtifact.instructionPC 3353 = 0x1377 := by rfl
@[simp] theorem pc2849 :
    Artifact.submissionArtifact.instructionPC 3354 = 0x1378 := by rfl
@[simp] theorem pc2850 :
    Artifact.submissionArtifact.instructionPC 3355 = 0x1379 := by rfl
@[simp] theorem pc2851 :
    Artifact.submissionArtifact.instructionPC 3356 = 0x137a := by rfl
@[simp] theorem pc2852 :
    Artifact.submissionArtifact.instructionPC 3357 = 0x137b := by rfl
@[simp] theorem pc2853 :
    Artifact.submissionArtifact.instructionPC 3358 = 0x137e := by rfl
@[simp] theorem pc2854 :
    Artifact.submissionArtifact.instructionPC 3359 = 0x137f := by rfl
@[simp] theorem pc2855 :
    Artifact.submissionArtifact.instructionPC 3360 = 0x1394 := by rfl
@[simp] theorem pc2856 :
    Artifact.submissionArtifact.instructionPC 3361 = 0x1395 := by rfl
@[simp] theorem pc2857 :
    Artifact.submissionArtifact.instructionPC 3362 = 0x1396 := by rfl
@[simp] theorem pc2858 :
    Artifact.submissionArtifact.instructionPC 3363 = 0x1398 := by rfl
@[simp] theorem pc2859 :
    Artifact.submissionArtifact.instructionPC 3364 = 0x1399 := by rfl
@[simp] theorem pc2860 :
    Artifact.submissionArtifact.instructionPC 3365 = 0x139a := by rfl
@[simp] theorem pc2861 :
    Artifact.submissionArtifact.instructionPC 3366 = 0x139b := by rfl
@[simp] theorem pc2862 :
    Artifact.submissionArtifact.instructionPC 3367 = 0x139c := by rfl
@[simp] theorem pc2863 :
    Artifact.submissionArtifact.instructionPC 3368 = 0x139f := by rfl

end Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard
