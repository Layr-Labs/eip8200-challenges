import Challenge.EvmProof.Stepper
import Challenge.Ripemd160.ProofSupport.InitialState
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Artifact
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedGuardSpec
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScanLogic

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open PatternedInputData PatternedDigest PatternedGuardSpec

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

def entryPath : List Located := []

def loopPath : List Located :=
  [opAt 2864 .JUMPDEST,
   pushAt 2865 1 251,
   opAt 2866 (.Dup ⟨1, by decide⟩), opAt 2867 .DIV,
   pushAt 2868 1 11, opAt 2869 .MUL,
   opAt 2870 (.Dup ⟨1, by decide⟩),
   pushAt 2871 1 37, opAt 2872 .MUL,
   opAt 2873 .ADD, pushAt 2874 1 7, opAt 2875 .ADD,
   pushAt 2876 1 255, opAt 2877 .AND,
   opAt 2878 (.Dup ⟨1, by decide⟩),
   opAt 2879 .CALLDATALOAD,
   pushAt 2880 0 0, opAt 2881 .BYTE,
   opAt 2882 .XOR,
   opAt 2883 (.Swap ⟨0, by decide⟩),
   opAt 2884 (.Swap ⟨1, by decide⟩),
   opAt 2885 .OR,
   opAt 2886 (.Swap ⟨0, by decide⟩),
   pushAt 2887 1 1, opAt 2888 .ADD,
   pushAt 2889 2 1000,
   opAt 2890 (.Dup ⟨1, by decide⟩), opAt 2891 .LT,
   pushAt 2892 2 4933, opAt 2893 .JUMPI]

def exitPath : List Located :=
  [opAt 2894 .POP, pushAt 2895 2 1006, opAt 2896 .JUMPI]

def returnPath : List Located :=
  [pushAt 2897 20 766350606435067737561421097975693824639675460820,
   pushAt 2898 0 0, opAt 2899 .MSTORE,
   pushAt 2900 1 32, pushAt 2901 0 0, opAt 2902 .RETURN]

def atPC (input : ByteArray) (pc : Nat) : State :=
  { initialState submissionBytecode input 0 with pc := UInt256.ofNat pc }

abbrev calldataByte := PatternedScanLogic.calldataByte
abbrev expectedWord := PatternedScanLogic.expectedWord
abbrev scanAcc := PatternedScanLogic.scanAcc

def loopState (input : ByteArray) (n : Nat) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 4933
    stack := [UInt256.ofNat n, scanAcc input n] }

def patternedEntry (input : ByteArray) : State := loopState input 0

def loopExitState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 4973
    stack := [UInt256.ofNat 1000, scanAcc input 1000] }

def hitEntry (input : ByteArray) : State := atPC input 4978
def fallbackState (input : ByteArray) : State := atPC input 1006

def storeWord (memory : ByteArray) (address : Nat) (word : UInt256) : ByteArray :=
  MachineState.writeBytes memory (Data.Bytes.natToBytesPadded word.toNat 32) address

def answerMemory : ByteArray := storeWord ByteArray.empty 0 paddedDigestWord

def returnedState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 5004
    memory := answerMemory
    activeWords := UInt256.ofNat 1
    halt := .Returned
    hReturn := MachineState.readPadded answerMemory 0 32 }

abbrev run := Challenge.EvmProof.Stepper.runLocatedBlock
  (artifact := Artifact.submissionArtifact) (fork := .Osaka)

@[simp] theorem pc2864 : Artifact.submissionArtifact.instructionPC 2864 = 4933 := by rfl
@[simp] theorem pc2865 : Artifact.submissionArtifact.instructionPC 2865 = 4934 := by rfl
@[simp] theorem pc2866 : Artifact.submissionArtifact.instructionPC 2866 = 4936 := by rfl
@[simp] theorem pc2867 : Artifact.submissionArtifact.instructionPC 2867 = 4937 := by rfl
@[simp] theorem pc2868 : Artifact.submissionArtifact.instructionPC 2868 = 4938 := by rfl
@[simp] theorem pc2869 : Artifact.submissionArtifact.instructionPC 2869 = 4940 := by rfl
@[simp] theorem pc2870 : Artifact.submissionArtifact.instructionPC 2870 = 4941 := by rfl
@[simp] theorem pc2871 : Artifact.submissionArtifact.instructionPC 2871 = 4942 := by rfl
@[simp] theorem pc2872 : Artifact.submissionArtifact.instructionPC 2872 = 4944 := by rfl
@[simp] theorem pc2873 : Artifact.submissionArtifact.instructionPC 2873 = 4945 := by rfl
@[simp] theorem pc2874 : Artifact.submissionArtifact.instructionPC 2874 = 4946 := by rfl
@[simp] theorem pc2875 : Artifact.submissionArtifact.instructionPC 2875 = 4948 := by rfl
@[simp] theorem pc2876 : Artifact.submissionArtifact.instructionPC 2876 = 4949 := by rfl
@[simp] theorem pc2877 : Artifact.submissionArtifact.instructionPC 2877 = 4951 := by rfl
@[simp] theorem pc2878 : Artifact.submissionArtifact.instructionPC 2878 = 4952 := by rfl
@[simp] theorem pc2879 : Artifact.submissionArtifact.instructionPC 2879 = 4953 := by rfl
@[simp] theorem pc2880 : Artifact.submissionArtifact.instructionPC 2880 = 4954 := by rfl
@[simp] theorem pc2881 : Artifact.submissionArtifact.instructionPC 2881 = 4955 := by rfl
@[simp] theorem pc2882 : Artifact.submissionArtifact.instructionPC 2882 = 4956 := by rfl
@[simp] theorem pc2883 : Artifact.submissionArtifact.instructionPC 2883 = 4957 := by rfl
@[simp] theorem pc2884 : Artifact.submissionArtifact.instructionPC 2884 = 4958 := by rfl
@[simp] theorem pc2885 : Artifact.submissionArtifact.instructionPC 2885 = 4959 := by rfl
@[simp] theorem pc2886 : Artifact.submissionArtifact.instructionPC 2886 = 4960 := by rfl
@[simp] theorem pc2887 : Artifact.submissionArtifact.instructionPC 2887 = 4961 := by rfl
@[simp] theorem pc2888 : Artifact.submissionArtifact.instructionPC 2888 = 4963 := by rfl
@[simp] theorem pc2889 : Artifact.submissionArtifact.instructionPC 2889 = 4964 := by rfl
@[simp] theorem pc2890 : Artifact.submissionArtifact.instructionPC 2890 = 4967 := by rfl
@[simp] theorem pc2891 : Artifact.submissionArtifact.instructionPC 2891 = 4968 := by rfl
@[simp] theorem pc2892 : Artifact.submissionArtifact.instructionPC 2892 = 4969 := by rfl
@[simp] theorem pc2893 : Artifact.submissionArtifact.instructionPC 2893 = 4972 := by rfl
@[simp] theorem pc2894 : Artifact.submissionArtifact.instructionPC 2894 = 4973 := by rfl
@[simp] theorem pc2895 : Artifact.submissionArtifact.instructionPC 2895 = 4974 := by rfl
@[simp] theorem pc2896 : Artifact.submissionArtifact.instructionPC 2896 = 4977 := by rfl
@[simp] theorem pc2897 : Artifact.submissionArtifact.instructionPC 2897 = 4978 := by rfl
@[simp] theorem pc2898 : Artifact.submissionArtifact.instructionPC 2898 = 4999 := by rfl
@[simp] theorem pc2899 : Artifact.submissionArtifact.instructionPC 2899 = 5000 := by rfl
@[simp] theorem pc2900 : Artifact.submissionArtifact.instructionPC 2900 = 5001 := by rfl
@[simp] theorem pc2901 : Artifact.submissionArtifact.instructionPC 2901 = 5003 := by rfl
@[simp] theorem pc2902 : Artifact.submissionArtifact.instructionPC 2902 = 5004 := by rfl

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

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan
