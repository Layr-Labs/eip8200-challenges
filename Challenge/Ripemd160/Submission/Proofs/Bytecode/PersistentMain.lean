import Challenge.Ripemd160.Submission.Proofs.Bytecode.Execution
set_option warningAsError true
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PersistentMain
open EvmSemantics EvmSemantics.EVM
abbrev initializedState (input : ByteArray) : State := Execution.mainStart input
@[simp] theorem initializedState_pc (input : ByteArray) :
    (initializedState input).pc = UInt256.ofNat (Artifact.instructionPC 179) := by
  rw [PersistentOuterPCs.alias_179]
  rfl
@[simp] theorem initializedState_stack (input : ByteArray) :
    (initializedState input).stack = [] := by rfl
@[simp] theorem initializedState_halt (input : ByteArray) :
    (initializedState input).halt = .Running := by rfl
@[simp] theorem initializedState_fork (input : ByteArray) :
    (initializedState input).fork = .Osaka := by rfl
@[simp] theorem initializedState_code (input : ByteArray) :
    (initializedState input).executionEnv.code = submissionBytecode := by rfl
@[simp] theorem initializedState_codeAddr (input : ByteArray) :
    (initializedState input).executionEnv.codeAddr = deployAddress := by rfl
 def gasSteps_initialize (input : ByteArray)
    (entryPrefix : Challenge.EvmProof.GasSteps (initialState submissionBytecode input 0)
      (Execution.atPC input 276)) :
    Challenge.EvmProof.GasSteps (initialState submissionBytecode input 0)
      (initializedState input) := Execution.gasSteps_entry input entryPrefix
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PersistentMain
