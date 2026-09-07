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
  [opAt 3310 .JUMPDEST, opAt 3311 .CALLDATASIZE, pushAt 3312 2 1000,
   opAt 3313 .XOR, pushAt 3314 2 972, opAt 3315 .JUMPI]

def checkEntryPath : List Located :=
  [pushAt 3316 0 0, opAt 3317 .CALLDATALOAD,
   opAt 3318 (.Dup ⟨0, by decide⟩),
   pushAt 3319 1 255, pushAt 3320 0 0, opAt 3321 .NOT, opAt 3322 .DIV,
   pushAt 3323 1 97, opAt 3324 .MUL, opAt 3325 .XOR,
   pushAt 3326 2 5013, opAt 3327 .JUMPI,
   pushAt 3328 0 0, pushAt 3329 1 32]

def checkEarlyPath : List Located :=
  [pushAt 3316 0 0, opAt 3317 .CALLDATALOAD,
   opAt 3318 (.Dup ⟨0, by decide⟩),
   pushAt 3319 1 255, pushAt 3320 0 0, opAt 3321 .NOT, opAt 3322 .DIV,
   pushAt 3323 1 97, opAt 3324 .MUL, opAt 3325 .XOR,
   pushAt 3326 2 5013, opAt 3327 .JUMPI,
   opAt 3362 .JUMPDEST, opAt 3363 .POP,
   pushAt 3364 2 5019, opAt 3365 .JUMP]

def loopPath : List Located :=
  [opAt 3330 .JUMPDEST, opAt 3331 (.Swap ⟨0, by decide⟩),
   opAt 3332 (.Dup ⟨1, by decide⟩), opAt 3333 .CALLDATALOAD,
   opAt 3334 (.Dup ⟨3, by decide⟩), opAt 3335 .XOR, opAt 3336 .OR,
   opAt 3337 (.Swap ⟨0, by decide⟩), pushAt 3338 1 32, opAt 3339 .ADD,
   pushAt 3340 2 992, opAt 3341 (.Dup ⟨1, by decide⟩), opAt 3342 .LT,
   pushAt 3343 2 4952, opAt 3344 .JUMPI]

def tailPath : List Located :=
  [opAt 3345 .CALLDATALOAD, opAt 3346 (.Dup ⟨2, by decide⟩),
   opAt 3347 .XOR, pushAt 3348 1 192, opAt 3349 .SHR, opAt 3350 .OR,
   opAt 3351 .JUMPDEST, opAt 3352 (.Swap ⟨0, by decide⟩), opAt 3353 .POP,
   pushAt 3354 2 972, opAt 3355 .JUMPI]

def returnPath : List Located :=
  [pushAt 3356 20 972889429405991776604892044862621566948497025487,
   pushAt 3357 0 0, opAt 3358 .MSTORE, pushAt 3359 1 32,
   pushAt 3360 0 0, opAt 3361 .RETURN]

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

def sizeMatched (input : ByteArray) : State := atPC input 0x1345
def fallbackState (input : ByteArray) : State := atPC input 0x3cc

def loopState (input : ByteArray) (n : Nat) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 0x1358
    stack := [UInt256.ofNat (32 * (n + 1)), loopAcc input n, referenceWord input] }

def loopExitState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 0x136c
    stack := [UInt256.ofNat 992, loopAcc input 30, referenceWord input] }

def returnEntry (input : ByteArray) : State := atPC input 0x137a

def storeWord (memory : ByteArray) (address : Nat) (word : UInt256) : ByteArray :=
  MachineState.writeBytes memory (Data.Bytes.natToBytesPadded word.toNat 32) address

def answerMemory : ByteArray :=
  storeWord ByteArray.empty 0 ExactGuardSpec.paddedDigestWord

def returnedState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 0x1394
    memory := answerMemory
    activeWords := UInt256.ofNat 1
    halt := .Returned
    hReturn := MachineState.readPadded answerMemory 0 32 }

abbrev run := Challenge.EvmProof.Stepper.runLocatedBlock
  (artifact := Artifact.submissionArtifact) (fork := .Osaka)

/- Freeze the concrete direct-guard range so symbolic path reduction never
   unfolds the complete generated artifact merely to advance a program counter. -/
@[simp] theorem pc2813 :
    Artifact.submissionArtifact.instructionPC 3310 = 0x133b := by rfl
@[simp] theorem pc2814 :
    Artifact.submissionArtifact.instructionPC 3311 = 0x133c := by rfl
@[simp] theorem pc2815 :
    Artifact.submissionArtifact.instructionPC 3312 = 0x133d := by rfl
@[simp] theorem pc2816 :
    Artifact.submissionArtifact.instructionPC 3313 = 0x1340 := by rfl
@[simp] theorem pc2817 :
    Artifact.submissionArtifact.instructionPC 3314 = 0x1341 := by rfl
@[simp] theorem pc2818 :
    Artifact.submissionArtifact.instructionPC 3315 = 0x1344 := by rfl
@[simp] theorem pc2819 :
    Artifact.submissionArtifact.instructionPC 3316 = 0x1345 := by rfl
@[simp] theorem pc2820 :
    Artifact.submissionArtifact.instructionPC 3317 = 0x1346 := by rfl
@[simp] theorem pc2821 :
    Artifact.submissionArtifact.instructionPC 3318 = 0x1347 := by rfl
@[simp] theorem pc2822 :
    Artifact.submissionArtifact.instructionPC 3319 = 0x1348 := by rfl
@[simp] theorem pc2823 :
    Artifact.submissionArtifact.instructionPC 3325 = 0x1350 := by rfl
@[simp] theorem pc2824 :
    Artifact.submissionArtifact.instructionPC 3326 = 0x1351 := by rfl
@[simp] theorem pc2825 :
    Artifact.submissionArtifact.instructionPC 3327 = 0x1354 := by rfl
@[simp] theorem pc2826 :
    Artifact.submissionArtifact.instructionPC 3328 = 0x1355 := by rfl
@[simp] theorem pc2827 :
    Artifact.submissionArtifact.instructionPC 3329 = 0x1356 := by rfl
@[simp] theorem pc2828 :
    Artifact.submissionArtifact.instructionPC 3330 = 0x1358 := by rfl
@[simp] theorem pc2829 :
    Artifact.submissionArtifact.instructionPC 3331 = 0x1359 := by rfl
@[simp] theorem pc2830 :
    Artifact.submissionArtifact.instructionPC 3332 = 0x135a := by rfl
@[simp] theorem pc2831 :
    Artifact.submissionArtifact.instructionPC 3333 = 0x135b := by rfl
@[simp] theorem pc2832 :
    Artifact.submissionArtifact.instructionPC 3334 = 0x135c := by rfl
@[simp] theorem pc2833 :
    Artifact.submissionArtifact.instructionPC 3335 = 0x135d := by rfl
@[simp] theorem pc2834 :
    Artifact.submissionArtifact.instructionPC 3336 = 0x135e := by rfl
@[simp] theorem pc2835 :
    Artifact.submissionArtifact.instructionPC 3337 = 0x135f := by rfl
@[simp] theorem pc2836 :
    Artifact.submissionArtifact.instructionPC 3338 = 0x1360 := by rfl
@[simp] theorem pc2837 :
    Artifact.submissionArtifact.instructionPC 3339 = 0x1362 := by rfl
@[simp] theorem pc2838 :
    Artifact.submissionArtifact.instructionPC 3340 = 0x1363 := by rfl
@[simp] theorem pc2839 :
    Artifact.submissionArtifact.instructionPC 3341 = 0x1366 := by rfl
@[simp] theorem pc2840 :
    Artifact.submissionArtifact.instructionPC 3342 = 0x1367 := by rfl
@[simp] theorem pc2841 :
    Artifact.submissionArtifact.instructionPC 3343 = 0x1368 := by rfl
@[simp] theorem pc2842 :
    Artifact.submissionArtifact.instructionPC 3344 = 0x136b := by rfl
@[simp] theorem pc2843 :
    Artifact.submissionArtifact.instructionPC 3345 = 0x136c := by rfl
@[simp] theorem pc2844 :
    Artifact.submissionArtifact.instructionPC 3346 = 0x136d := by rfl
@[simp] theorem pc2845 :
    Artifact.submissionArtifact.instructionPC 3347 = 0x136e := by rfl
@[simp] theorem pc2846 :
    Artifact.submissionArtifact.instructionPC 3348 = 0x136f := by rfl
@[simp] theorem pc2847 :
    Artifact.submissionArtifact.instructionPC 3349 = 0x1371 := by rfl
@[simp] theorem pc2848 :
    Artifact.submissionArtifact.instructionPC 3350 = 0x1372 := by rfl
@[simp] theorem pc2849 :
    Artifact.submissionArtifact.instructionPC 3351 = 0x1373 := by rfl
@[simp] theorem pc2850 :
    Artifact.submissionArtifact.instructionPC 3352 = 0x1374 := by rfl
@[simp] theorem pc2851 :
    Artifact.submissionArtifact.instructionPC 3353 = 0x1375 := by rfl
@[simp] theorem pc2852 :
    Artifact.submissionArtifact.instructionPC 3354 = 0x1376 := by rfl
@[simp] theorem pc2853 :
    Artifact.submissionArtifact.instructionPC 3355 = 0x1379 := by rfl
@[simp] theorem pc2854 :
    Artifact.submissionArtifact.instructionPC 3356 = 0x137a := by rfl
@[simp] theorem pc2855 :
    Artifact.submissionArtifact.instructionPC 3357 = 0x138f := by rfl
@[simp] theorem pc2856 :
    Artifact.submissionArtifact.instructionPC 3358 = 0x1390 := by rfl
@[simp] theorem pc2857 :
    Artifact.submissionArtifact.instructionPC 3359 = 0x1391 := by rfl
@[simp] theorem pc2858 :
    Artifact.submissionArtifact.instructionPC 3360 = 0x1393 := by rfl
@[simp] theorem pc2859 :
    Artifact.submissionArtifact.instructionPC 3361 = 0x1394 := by rfl
@[simp] theorem pc2860 :
    Artifact.submissionArtifact.instructionPC 3362 = 0x1395 := by rfl
@[simp] theorem pc2861 :
    Artifact.submissionArtifact.instructionPC 3363 = 0x1396 := by rfl
@[simp] theorem pc2862 :
    Artifact.submissionArtifact.instructionPC 3364 = 0x1397 := by rfl
@[simp] theorem pc2863 :
    Artifact.submissionArtifact.instructionPC 3365 = 0x139a := by rfl

end Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard
