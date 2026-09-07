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
  [opAt 3222 .JUMPDEST, opAt 3223 .CALLDATASIZE, pushAt 3224 2 1000,
   opAt 3225 .XOR, pushAt 3226 2 1011, opAt 3227 .JUMPI]

def checkEntryPath : List Located :=
  [pushAt 3228 0 0, opAt 3229 .CALLDATALOAD,
   opAt 3230 (.Dup ⟨0, by decide⟩),
   pushAt 3231 32 KnownInputData.fullWord, opAt 3232 .XOR,
   pushAt 3233 2 5078, opAt 3234 .JUMPI,
   pushAt 3235 0 0, pushAt 3236 1 32]

def checkEarlyPath : List Located :=
  [pushAt 3228 0 0, opAt 3229 .CALLDATALOAD,
   opAt 3230 (.Dup ⟨0, by decide⟩),
   pushAt 3231 32 KnownInputData.fullWord, opAt 3232 .XOR,
   pushAt 3233 2 5078, opAt 3234 .JUMPI,
   opAt 3269 .JUMPDEST, opAt 3270 .POP,
   pushAt 3271 2 5084, opAt 3272 .JUMP]

def loopPath : List Located :=
  [opAt 3237 .JUMPDEST, opAt 3238 (.Swap ⟨0, by decide⟩),
   opAt 3239 (.Dup ⟨1, by decide⟩), opAt 3240 .CALLDATALOAD,
   opAt 3241 (.Dup ⟨3, by decide⟩), opAt 3242 .XOR, opAt 3243 .OR,
   opAt 3244 (.Swap ⟨0, by decide⟩), pushAt 3245 1 32, opAt 3246 .ADD,
   pushAt 3247 2 992, opAt 3248 (.Dup ⟨1, by decide⟩), opAt 3249 .LT,
   pushAt 3250 2 5017, opAt 3251 .JUMPI]

def tailPath : List Located :=
  [opAt 3252 .CALLDATALOAD, opAt 3253 (.Dup ⟨2, by decide⟩),
   opAt 3254 .XOR, pushAt 3255 1 192, opAt 3256 .SHR, opAt 3257 .OR,
   opAt 3258 .JUMPDEST, opAt 3259 (.Swap ⟨0, by decide⟩), opAt 3260 .POP,
   pushAt 3261 2 1011, opAt 3262 .JUMPI]

def returnPath : List Located :=
  [pushAt 3263 20 972889429405991776604892044862621566948497025487,
   pushAt 3264 0 0, opAt 3265 .MSTORE, pushAt 3266 1 32,
   pushAt 3267 0 0, opAt 3268 .RETURN]

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

def sizeMatched (input : ByteArray) : State := atPC input 0x136d
def fallbackState (input : ByteArray) : State := atPC input 0x3f3

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
    Artifact.submissionArtifact.instructionPC 3222 = 0x1363 := by rfl
@[simp] theorem pc2814 :
    Artifact.submissionArtifact.instructionPC 3223 = 0x1364 := by rfl
@[simp] theorem pc2815 :
    Artifact.submissionArtifact.instructionPC 3224 = 0x1365 := by rfl
@[simp] theorem pc2816 :
    Artifact.submissionArtifact.instructionPC 3225 = 0x1368 := by rfl
@[simp] theorem pc2817 :
    Artifact.submissionArtifact.instructionPC 3226 = 0x1369 := by rfl
@[simp] theorem pc2818 :
    Artifact.submissionArtifact.instructionPC 3227 = 0x136c := by rfl
@[simp] theorem pc2819 :
    Artifact.submissionArtifact.instructionPC 3228 = 0x136d := by rfl
@[simp] theorem pc2820 :
    Artifact.submissionArtifact.instructionPC 3229 = 0x136e := by rfl
@[simp] theorem pc2821 :
    Artifact.submissionArtifact.instructionPC 3230 = 0x136f := by rfl
@[simp] theorem pc2822 :
    Artifact.submissionArtifact.instructionPC 3231 = 0x1370 := by rfl
@[simp] theorem pc2823 :
    Artifact.submissionArtifact.instructionPC 3232 = 0x1391 := by rfl
@[simp] theorem pc2824 :
    Artifact.submissionArtifact.instructionPC 3233 = 0x1392 := by rfl
@[simp] theorem pc2825 :
    Artifact.submissionArtifact.instructionPC 3234 = 0x1395 := by rfl
@[simp] theorem pc2826 :
    Artifact.submissionArtifact.instructionPC 3235 = 0x1396 := by rfl
@[simp] theorem pc2827 :
    Artifact.submissionArtifact.instructionPC 3236 = 0x1397 := by rfl
@[simp] theorem pc2828 :
    Artifact.submissionArtifact.instructionPC 3237 = 0x1399 := by rfl
@[simp] theorem pc2829 :
    Artifact.submissionArtifact.instructionPC 3238 = 0x139a := by rfl
@[simp] theorem pc2830 :
    Artifact.submissionArtifact.instructionPC 3239 = 0x139b := by rfl
@[simp] theorem pc2831 :
    Artifact.submissionArtifact.instructionPC 3240 = 0x139c := by rfl
@[simp] theorem pc2832 :
    Artifact.submissionArtifact.instructionPC 3241 = 0x139d := by rfl
@[simp] theorem pc2833 :
    Artifact.submissionArtifact.instructionPC 3242 = 0x139e := by rfl
@[simp] theorem pc2834 :
    Artifact.submissionArtifact.instructionPC 3243 = 0x139f := by rfl
@[simp] theorem pc2835 :
    Artifact.submissionArtifact.instructionPC 3244 = 0x13a0 := by rfl
@[simp] theorem pc2836 :
    Artifact.submissionArtifact.instructionPC 3245 = 0x13a1 := by rfl
@[simp] theorem pc2837 :
    Artifact.submissionArtifact.instructionPC 3246 = 0x13a3 := by rfl
@[simp] theorem pc2838 :
    Artifact.submissionArtifact.instructionPC 3247 = 0x13a4 := by rfl
@[simp] theorem pc2839 :
    Artifact.submissionArtifact.instructionPC 3248 = 0x13a7 := by rfl
@[simp] theorem pc2840 :
    Artifact.submissionArtifact.instructionPC 3249 = 0x13a8 := by rfl
@[simp] theorem pc2841 :
    Artifact.submissionArtifact.instructionPC 3250 = 0x13a9 := by rfl
@[simp] theorem pc2842 :
    Artifact.submissionArtifact.instructionPC 3251 = 0x13ac := by rfl
@[simp] theorem pc2843 :
    Artifact.submissionArtifact.instructionPC 3252 = 0x13ad := by rfl
@[simp] theorem pc2844 :
    Artifact.submissionArtifact.instructionPC 3253 = 0x13ae := by rfl
@[simp] theorem pc2845 :
    Artifact.submissionArtifact.instructionPC 3254 = 0x13af := by rfl
@[simp] theorem pc2846 :
    Artifact.submissionArtifact.instructionPC 3255 = 0x13b0 := by rfl
@[simp] theorem pc2847 :
    Artifact.submissionArtifact.instructionPC 3256 = 0x13b2 := by rfl
@[simp] theorem pc2848 :
    Artifact.submissionArtifact.instructionPC 3257 = 0x13b3 := by rfl
@[simp] theorem pc2849 :
    Artifact.submissionArtifact.instructionPC 3258 = 0x13b4 := by rfl
@[simp] theorem pc2850 :
    Artifact.submissionArtifact.instructionPC 3259 = 0x13b5 := by rfl
@[simp] theorem pc2851 :
    Artifact.submissionArtifact.instructionPC 3260 = 0x13b6 := by rfl
@[simp] theorem pc2852 :
    Artifact.submissionArtifact.instructionPC 3261 = 0x13b7 := by rfl
@[simp] theorem pc2853 :
    Artifact.submissionArtifact.instructionPC 3262 = 0x13ba := by rfl
@[simp] theorem pc2854 :
    Artifact.submissionArtifact.instructionPC 3263 = 0x13bb := by rfl
@[simp] theorem pc2855 :
    Artifact.submissionArtifact.instructionPC 3264 = 0x13d0 := by rfl
@[simp] theorem pc2856 :
    Artifact.submissionArtifact.instructionPC 3265 = 0x13d1 := by rfl
@[simp] theorem pc2857 :
    Artifact.submissionArtifact.instructionPC 3266 = 0x13d2 := by rfl
@[simp] theorem pc2858 :
    Artifact.submissionArtifact.instructionPC 3267 = 0x13d4 := by rfl
@[simp] theorem pc2859 :
    Artifact.submissionArtifact.instructionPC 3268 = 0x13d5 := by rfl
@[simp] theorem pc2860 :
    Artifact.submissionArtifact.instructionPC 3269 = 0x13d6 := by rfl
@[simp] theorem pc2861 :
    Artifact.submissionArtifact.instructionPC 3270 = 0x13d7 := by rfl
@[simp] theorem pc2862 :
    Artifact.submissionArtifact.instructionPC 3271 = 0x13d8 := by rfl
@[simp] theorem pc2863 :
    Artifact.submissionArtifact.instructionPC 3272 = 0x13db := by rfl

end Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard
