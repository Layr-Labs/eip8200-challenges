import Challenge.EvmProof.Stepper
import Challenge.Ripemd160.ProofSupport.InitialState
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Artifact
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned376GuardSpec
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned376ScanLogic
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScanLogic

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned376Scan

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open Patterned376InputData Patterned376Digest Patterned376GuardSpec
open PatternedScanLogic

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
  [ opAt 2903 .JUMPDEST,
   opAt 2904 .CALLDATASIZE,
   pushAt 2905 2 376,
   opAt 2906 .XOR,
   pushAt 2907 2 1006,
   opAt 2908 .JUMPI]

def enterPath : List Located :=
  [ pushAt 2909 0 0,
   pushAt 2910 0 0]

def loopPath : List Located :=
  [ opAt 2911 .JUMPDEST,
   pushAt 2912 1 251,
   opAt 2913 (.Dup ⟨1, by decide⟩),
   opAt 2914 .DIV,
   pushAt 2915 1 11,
   opAt 2916 .MUL,
   opAt 2917 (.Dup ⟨1, by decide⟩),
   pushAt 2918 1 37,
   opAt 2919 .MUL,
   opAt 2920 .ADD,
   pushAt 2921 1 7,
   opAt 2922 .ADD,
   pushAt 2923 1 255,
   opAt 2924 .AND,
   opAt 2925 (.Dup ⟨1, by decide⟩),
   opAt 2926 .CALLDATALOAD,
   pushAt 2927 0 0,
   opAt 2928 .BYTE,
   opAt 2929 .XOR,
   opAt 2930 (.Swap ⟨0, by decide⟩),
   opAt 2931 (.Swap ⟨1, by decide⟩),
   opAt 2932 .OR,
   opAt 2933 (.Swap ⟨0, by decide⟩),
   pushAt 2934 1 1,
   opAt 2935 .ADD,
   pushAt 2936 2 376,
   opAt 2937 (.Dup ⟨1, by decide⟩),
   opAt 2938 .LT,
   pushAt 2939 2 5017,
   opAt 2940 .JUMPI]

def exitPath : List Located :=
  [ opAt 2941 .POP,
   pushAt 2942 2 1006,
   opAt 2943 .JUMPI]

def returnPath : List Located :=
  [ pushAt 2944 20 1409020389675646681432984939370312113762541159597,
   pushAt 2945 0 0,
   opAt 2946 .MSTORE,
   pushAt 2947 1 32,
   pushAt 2948 0 0,
   opAt 2949 .RETURN]

def atPC (input : ByteArray) (pc : Nat) : State :=
  { initialState submissionBytecode input 0 with pc := UInt256.ofNat pc }

def size376Entry (input : ByteArray) : State := atPC input 5005
def sizeMatched (input : ByteArray) : State := atPC input 5015

def loopState (input : ByteArray) (n : Nat) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 5017
    stack := [UInt256.ofNat n, scanAcc input n] }

def patterned376Entry (input : ByteArray) : State := loopState input 0

def loopExitState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 5057
    stack := [UInt256.ofNat 376, scanAcc input 376] }

def hitEntry (input : ByteArray) : State := atPC input 5062
def fallbackState (input : ByteArray) : State := atPC input 1006

def storeWord (memory : ByteArray) (address : Nat) (word : UInt256) : ByteArray :=
  MachineState.writeBytes memory (Data.Bytes.natToBytesPadded word.toNat 32) address

def answerMemory : ByteArray := storeWord ByteArray.empty 0 paddedDigestWord

def returnedState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 5088
    memory := answerMemory
    activeWords := UInt256.ofNat 1
    halt := .Returned
    hReturn := MachineState.readPadded answerMemory 0 32 }

abbrev run := Challenge.EvmProof.Stepper.runLocatedBlock
  (artifact := Artifact.submissionArtifact) (fork := .Osaka)

@[simp] theorem pc2903 : Artifact.submissionArtifact.instructionPC 2903 = 5005 := by rfl
@[simp] theorem pc2904 : Artifact.submissionArtifact.instructionPC 2904 = 5006 := by rfl
@[simp] theorem pc2905 : Artifact.submissionArtifact.instructionPC 2905 = 5007 := by rfl
@[simp] theorem pc2906 : Artifact.submissionArtifact.instructionPC 2906 = 5010 := by rfl
@[simp] theorem pc2907 : Artifact.submissionArtifact.instructionPC 2907 = 5011 := by rfl
@[simp] theorem pc2908 : Artifact.submissionArtifact.instructionPC 2908 = 5014 := by rfl
@[simp] theorem pc2909 : Artifact.submissionArtifact.instructionPC 2909 = 5015 := by rfl
@[simp] theorem pc2910 : Artifact.submissionArtifact.instructionPC 2910 = 5016 := by rfl
@[simp] theorem pc2911 : Artifact.submissionArtifact.instructionPC 2911 = 5017 := by rfl
@[simp] theorem pc2912 : Artifact.submissionArtifact.instructionPC 2912 = 5018 := by rfl
@[simp] theorem pc2913 : Artifact.submissionArtifact.instructionPC 2913 = 5020 := by rfl
@[simp] theorem pc2914 : Artifact.submissionArtifact.instructionPC 2914 = 5021 := by rfl
@[simp] theorem pc2915 : Artifact.submissionArtifact.instructionPC 2915 = 5022 := by rfl
@[simp] theorem pc2916 : Artifact.submissionArtifact.instructionPC 2916 = 5024 := by rfl
@[simp] theorem pc2917 : Artifact.submissionArtifact.instructionPC 2917 = 5025 := by rfl
@[simp] theorem pc2918 : Artifact.submissionArtifact.instructionPC 2918 = 5026 := by rfl
@[simp] theorem pc2919 : Artifact.submissionArtifact.instructionPC 2919 = 5028 := by rfl
@[simp] theorem pc2920 : Artifact.submissionArtifact.instructionPC 2920 = 5029 := by rfl
@[simp] theorem pc2921 : Artifact.submissionArtifact.instructionPC 2921 = 5030 := by rfl
@[simp] theorem pc2922 : Artifact.submissionArtifact.instructionPC 2922 = 5032 := by rfl
@[simp] theorem pc2923 : Artifact.submissionArtifact.instructionPC 2923 = 5033 := by rfl
@[simp] theorem pc2924 : Artifact.submissionArtifact.instructionPC 2924 = 5035 := by rfl
@[simp] theorem pc2925 : Artifact.submissionArtifact.instructionPC 2925 = 5036 := by rfl
@[simp] theorem pc2926 : Artifact.submissionArtifact.instructionPC 2926 = 5037 := by rfl
@[simp] theorem pc2927 : Artifact.submissionArtifact.instructionPC 2927 = 5038 := by rfl
@[simp] theorem pc2928 : Artifact.submissionArtifact.instructionPC 2928 = 5039 := by rfl
@[simp] theorem pc2929 : Artifact.submissionArtifact.instructionPC 2929 = 5040 := by rfl
@[simp] theorem pc2930 : Artifact.submissionArtifact.instructionPC 2930 = 5041 := by rfl
@[simp] theorem pc2931 : Artifact.submissionArtifact.instructionPC 2931 = 5042 := by rfl
@[simp] theorem pc2932 : Artifact.submissionArtifact.instructionPC 2932 = 5043 := by rfl
@[simp] theorem pc2933 : Artifact.submissionArtifact.instructionPC 2933 = 5044 := by rfl
@[simp] theorem pc2934 : Artifact.submissionArtifact.instructionPC 2934 = 5045 := by rfl
@[simp] theorem pc2935 : Artifact.submissionArtifact.instructionPC 2935 = 5047 := by rfl
@[simp] theorem pc2936 : Artifact.submissionArtifact.instructionPC 2936 = 5048 := by rfl
@[simp] theorem pc2937 : Artifact.submissionArtifact.instructionPC 2937 = 5051 := by rfl
@[simp] theorem pc2938 : Artifact.submissionArtifact.instructionPC 2938 = 5052 := by rfl
@[simp] theorem pc2939 : Artifact.submissionArtifact.instructionPC 2939 = 5053 := by rfl
@[simp] theorem pc2940 : Artifact.submissionArtifact.instructionPC 2940 = 5056 := by rfl
@[simp] theorem pc2941 : Artifact.submissionArtifact.instructionPC 2941 = 5057 := by rfl
@[simp] theorem pc2942 : Artifact.submissionArtifact.instructionPC 2942 = 5058 := by rfl
@[simp] theorem pc2943 : Artifact.submissionArtifact.instructionPC 2943 = 5061 := by rfl
@[simp] theorem pc2944 : Artifact.submissionArtifact.instructionPC 2944 = 5062 := by rfl
@[simp] theorem pc2945 : Artifact.submissionArtifact.instructionPC 2945 = 5083 := by rfl
@[simp] theorem pc2946 : Artifact.submissionArtifact.instructionPC 2946 = 5084 := by rfl
@[simp] theorem pc2947 : Artifact.submissionArtifact.instructionPC 2947 = 5085 := by rfl
@[simp] theorem pc2948 : Artifact.submissionArtifact.instructionPC 2948 = 5087 := by rfl
@[simp] theorem pc2949 : Artifact.submissionArtifact.instructionPC 2949 = 5088 := by rfl

def sound (path : List Located) {s t : State}
    (h : run path s = some t)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code := by rfl)
    (hfork : s.fork = .Osaka := by rfl)
    (hrun : s.halt = .Running := by rfl)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false := by
        exact deployAddress_not_precompile) : GasSteps s t :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka
    path hcode hfork h hrun hnp

def loopJumpPath : List Located := [opAt 2940 .JUMPI]

def loopBranchState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 5056
    stack := [UInt256.ofNat 5017, 0, UInt256.ofNat 376, scanAcc input 376] }

theorem validJumpDest_138d :
    Decode.isValidJumpDest submissionBytecode 0x138d = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 2903 (by rfl)

theorem validJumpDest_1399 :
    Decode.isValidJumpDest submissionBytecode 0x1399 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 2911 (by rfl)

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned376Scan
