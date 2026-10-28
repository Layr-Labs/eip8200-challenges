import Challenge.Ripemd160.Submission.Local20261028.ColdExecution
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.Control.Main
open EvmSemantics EvmSemantics.EVM
abbrev initializedState (input : ByteArray) : State := Control.Execution.mainStart input
@[simp] theorem initializedState_pc (input : ByteArray) :
    (initializedState input).pc = UInt256.ofNat (Control.Artifact.instructionPC 134) := by rfl
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
      (Control.Execution.atPC input 246)) :
    Challenge.EvmProof.GasSteps (initialState submissionBytecode input 0)
      (initializedState input) := Control.Execution.gasSteps_entry input entryPrefix
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.Control.Main
