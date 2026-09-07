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
  [opAt 2976 .JUMPDEST, opAt 2977 .CALLDATASIZE, pushAt 2978 2 1000,
   opAt 2979 .XOR, pushAt 2980 2 1011, opAt 2981 .JUMPI]

def checkEntryPath : List Located :=
  [pushAt 2982 0 0, opAt 2983 .CALLDATALOAD,
   opAt 2984 (.Dup ⟨0, by decide⟩),
   pushAt 2985 32 KnownInputData.fullWord, opAt 2986 .XOR,
   pushAt 2987 2 4927, opAt 2988 .JUMPI,
   pushAt 2989 0 0, pushAt 2990 1 32]

def checkEarlyPath : List Located :=
  [pushAt 2982 0 0, opAt 2983 .CALLDATALOAD,
   opAt 2984 (.Dup ⟨0, by decide⟩),
   pushAt 2985 32 KnownInputData.fullWord, opAt 2986 .XOR,
   pushAt 2987 2 4927, opAt 2988 .JUMPI,
   opAt 3023 .JUMPDEST, opAt 3024 .POP,
   pushAt 3025 2 4933, opAt 3026 .POP]

def loopPath : List Located :=
  [opAt 2991 .JUMPDEST, opAt 2992 (.Swap ⟨0, by decide⟩),
   opAt 2993 (.Dup ⟨1, by decide⟩), opAt 2994 .CALLDATALOAD,
   opAt 2995 (.Dup ⟨3, by decide⟩), opAt 2996 .XOR, opAt 2997 .OR,
   opAt 2998 (.Swap ⟨0, by decide⟩), pushAt 2999 1 32, opAt 3000 .ADD,
   pushAt 3001 2 992, opAt 3002 (.Dup ⟨1, by decide⟩), opAt 3003 .LT,
   pushAt 3004 2 4866, opAt 3005 .JUMPI]

def tailPath : List Located :=
  [opAt 3006 .CALLDATALOAD, opAt 3007 (.Dup ⟨2, by decide⟩),
   opAt 3008 .XOR, pushAt 3009 1 192, opAt 3010 .SHR, opAt 3011 .OR,
   opAt 3012 .JUMPDEST, opAt 3013 (.Swap ⟨0, by decide⟩), opAt 3014 .POP,
   pushAt 3015 2 1011, opAt 3016 .JUMPI]

def returnPath : List Located :=
  [pushAt 3017 20 972889429405991776604892044862621566948497025487,
   pushAt 3018 0 0, opAt 3019 .MSTORE, pushAt 3020 1 32,
   pushAt 3021 0 0, opAt 3022 .RETURN]

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

def sizeMatched (input : ByteArray) : State := atPC input 0x12d6
def fallbackState (input : ByteArray) : State := atPC input 0x3f3

def loopState (input : ByteArray) (n : Nat) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 0x1302
    stack := [UInt256.ofNat (32 * (n + 1)), loopAcc input n, referenceWord input] }

def loopExitState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 0x1316
    stack := [UInt256.ofNat 992, loopAcc input 30, referenceWord input] }

def returnEntry (input : ByteArray) : State := atPC input 0x1324

def storeWord (memory : ByteArray) (address : Nat) (word : UInt256) : ByteArray :=
  MachineState.writeBytes memory (Data.Bytes.natToBytesPadded word.toNat 32) address

def answerMemory : ByteArray :=
  storeWord ByteArray.empty 0 ExactGuardSpec.paddedDigestWord

def returnedState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 0x133e
    memory := answerMemory
    activeWords := UInt256.ofNat 1
    halt := .Returned
    hReturn := MachineState.readPadded answerMemory 0 32 }

abbrev run := Challenge.EvmProof.Stepper.runLocatedBlock
  (artifact := Artifact.submissionArtifact) (fork := .Osaka)

/- Freeze the concrete direct-guard range so symbolic path reduction never
   unfolds the complete generated artifact merely to advance a program counter. -/
@[simp] theorem pc2813 :
    Artifact.submissionArtifact.instructionPC 2976 = 0x12cc := by rfl
@[simp] theorem pc2814 :
    Artifact.submissionArtifact.instructionPC 2977 = 0x12cd := by rfl
@[simp] theorem pc2815 :
    Artifact.submissionArtifact.instructionPC 2978 = 0x12ce := by rfl
@[simp] theorem pc2816 :
    Artifact.submissionArtifact.instructionPC 2979 = 0x12d1 := by rfl
@[simp] theorem pc2817 :
    Artifact.submissionArtifact.instructionPC 2980 = 0x12d2 := by rfl
@[simp] theorem pc2818 :
    Artifact.submissionArtifact.instructionPC 2981 = 0x12d5 := by rfl
@[simp] theorem pc2819 :
    Artifact.submissionArtifact.instructionPC 2982 = 0x12d6 := by rfl
@[simp] theorem pc2820 :
    Artifact.submissionArtifact.instructionPC 2983 = 0x12d7 := by rfl
@[simp] theorem pc2821 :
    Artifact.submissionArtifact.instructionPC 2984 = 0x12d8 := by rfl
@[simp] theorem pc2822 :
    Artifact.submissionArtifact.instructionPC 2985 = 0x12d9 := by rfl
@[simp] theorem pc2823 :
    Artifact.submissionArtifact.instructionPC 2986 = 0x12fa := by rfl
@[simp] theorem pc2824 :
    Artifact.submissionArtifact.instructionPC 2987 = 0x12fb := by rfl
@[simp] theorem pc2825 :
    Artifact.submissionArtifact.instructionPC 2988 = 0x12fe := by rfl
@[simp] theorem pc2826 :
    Artifact.submissionArtifact.instructionPC 2989 = 0x12ff := by rfl
@[simp] theorem pc2827 :
    Artifact.submissionArtifact.instructionPC 2990 = 0x1300 := by rfl
@[simp] theorem pc2828 :
    Artifact.submissionArtifact.instructionPC 2991 = 0x1302 := by rfl
@[simp] theorem pc2829 :
    Artifact.submissionArtifact.instructionPC 2992 = 0x1303 := by rfl
@[simp] theorem pc2830 :
    Artifact.submissionArtifact.instructionPC 2993 = 0x1304 := by rfl
@[simp] theorem pc2831 :
    Artifact.submissionArtifact.instructionPC 2994 = 0x1305 := by rfl
@[simp] theorem pc2832 :
    Artifact.submissionArtifact.instructionPC 2995 = 0x1306 := by rfl
@[simp] theorem pc2833 :
    Artifact.submissionArtifact.instructionPC 2996 = 0x1307 := by rfl
@[simp] theorem pc2834 :
    Artifact.submissionArtifact.instructionPC 2997 = 0x1308 := by rfl
@[simp] theorem pc2835 :
    Artifact.submissionArtifact.instructionPC 2998 = 0x1309 := by rfl
@[simp] theorem pc2836 :
    Artifact.submissionArtifact.instructionPC 2999 = 0x130a := by rfl
@[simp] theorem pc2837 :
    Artifact.submissionArtifact.instructionPC 3000 = 0x130c := by rfl
@[simp] theorem pc2838 :
    Artifact.submissionArtifact.instructionPC 3001 = 0x130d := by rfl
@[simp] theorem pc2839 :
    Artifact.submissionArtifact.instructionPC 3002 = 0x1310 := by rfl
@[simp] theorem pc2840 :
    Artifact.submissionArtifact.instructionPC 3003 = 0x1311 := by rfl
@[simp] theorem pc2841 :
    Artifact.submissionArtifact.instructionPC 3004 = 0x1312 := by rfl
@[simp] theorem pc2842 :
    Artifact.submissionArtifact.instructionPC 3005 = 0x1315 := by rfl
@[simp] theorem pc2843 :
    Artifact.submissionArtifact.instructionPC 3006 = 0x1316 := by rfl
@[simp] theorem pc2844 :
    Artifact.submissionArtifact.instructionPC 3007 = 0x1317 := by rfl
@[simp] theorem pc2845 :
    Artifact.submissionArtifact.instructionPC 3008 = 0x1318 := by rfl
@[simp] theorem pc2846 :
    Artifact.submissionArtifact.instructionPC 3009 = 0x1319 := by rfl
@[simp] theorem pc2847 :
    Artifact.submissionArtifact.instructionPC 3010 = 0x131b := by rfl
@[simp] theorem pc2848 :
    Artifact.submissionArtifact.instructionPC 3011 = 0x131c := by rfl
@[simp] theorem pc2849 :
    Artifact.submissionArtifact.instructionPC 3012 = 0x131d := by rfl
@[simp] theorem pc2850 :
    Artifact.submissionArtifact.instructionPC 3013 = 0x131e := by rfl
@[simp] theorem pc2851 :
    Artifact.submissionArtifact.instructionPC 3014 = 0x131f := by rfl
@[simp] theorem pc2852 :
    Artifact.submissionArtifact.instructionPC 3015 = 0x1320 := by rfl
@[simp] theorem pc2853 :
    Artifact.submissionArtifact.instructionPC 3016 = 0x1323 := by rfl
@[simp] theorem pc2854 :
    Artifact.submissionArtifact.instructionPC 3017 = 0x1324 := by rfl
@[simp] theorem pc2855 :
    Artifact.submissionArtifact.instructionPC 3018 = 0x1339 := by rfl
@[simp] theorem pc2856 :
    Artifact.submissionArtifact.instructionPC 3019 = 0x133a := by rfl
@[simp] theorem pc2857 :
    Artifact.submissionArtifact.instructionPC 3020 = 0x133b := by rfl
@[simp] theorem pc2858 :
    Artifact.submissionArtifact.instructionPC 3021 = 0x133d := by rfl
@[simp] theorem pc2859 :
    Artifact.submissionArtifact.instructionPC 3022 = 0x133e := by rfl
@[simp] theorem pc2860 :
    Artifact.submissionArtifact.instructionPC 3023 = 0x133f := by rfl
@[simp] theorem pc2861 :
    Artifact.submissionArtifact.instructionPC 3024 = 0x1340 := by rfl
@[simp] theorem pc2862 :
    Artifact.submissionArtifact.instructionPC 3025 = 0x1341 := by rfl
@[simp] theorem pc2863 :
    Artifact.submissionArtifact.instructionPC 3026 = 0x1344 := by rfl

end Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard
