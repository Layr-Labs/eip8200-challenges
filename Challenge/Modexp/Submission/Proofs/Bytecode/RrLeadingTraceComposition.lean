import Challenge.Modexp.Submission.Proofs.Bytecode.RrLeadingTraceJump

set_option warningAsError true
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.RrLeadingTraceCore

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler

/-- Complete artifact-independent helper trace, composed from opaque leaves. -/
theorem run_helper (template : State) (mem : ByteArray)
    (n bsize esize msize : Nat) (hn2 : 2 ≤ n) (hn32 : n ≤ 32)
    (hsize : MachineState.readWord mem 9344 = UInt256.ofNat (32 * n))
    (hjump : Decode.isValidJumpDest template.executionEnv.code 1569 = true) :
    runInstructions helperProgram (entryState template mem n bsize esize msize) =
      some (exitState template mem n bsize esize msize) := by
  unfold helperProgram
  exact runInstructions_append_some (copyProgram ++ counterProgram) jumpProgram
    (entryState template mem n bsize esize msize)
    (counterState template mem n bsize esize msize)
    (exitState template mem n bsize esize msize)
    (runInstructions_append_some copyProgram counterProgram
      (entryState template mem n bsize esize msize)
      (copiedState template mem n bsize esize msize)
      (counterState template mem n bsize esize msize)
      (run_copy template mem n bsize esize msize hn32 hsize)
      (run_counter template mem n bsize esize msize hn2 hn32))
    (run_jump template mem n bsize esize msize hjump)

/-! Exact non-local-state preservation.  The symbolic evaluator does not
decrement gas; the future `runInstr_sound` lift supplies the separately
accounted `GasSteps.cost`. -/

@[simp] theorem exit_gasAvailable (template : State) (mem : ByteArray)
    (n bsize esize msize : Nat) :
    (exitState template mem n bsize esize msize).gasAvailable =
      template.gasAvailable := rfl

@[simp] theorem exit_accountMap (template : State) (mem : ByteArray)
    (n bsize esize msize : Nat) :
    (exitState template mem n bsize esize msize).accountMap =
      template.accountMap := rfl

@[simp] theorem exit_substate (template : State) (mem : ByteArray)
    (n bsize esize msize : Nat) :
    (exitState template mem n bsize esize msize).substate =
      template.substate := rfl

@[simp] theorem exit_executionEnv (template : State) (mem : ByteArray)
    (n bsize esize msize : Nat) :
    (exitState template mem n bsize esize msize).executionEnv =
      template.executionEnv := rfl

@[simp] theorem exit_returnData (template : State) (mem : ByteArray)
    (n bsize esize msize : Nat) :
    (exitState template mem n bsize esize msize).returnData =
      template.returnData := rfl

@[simp] theorem exit_hReturn (template : State) (mem : ByteArray)
    (n bsize esize msize : Nat) :
    (exitState template mem n bsize esize msize).hReturn =
      template.hReturn := rfl

@[simp] theorem exit_execLength (template : State) (mem : ByteArray)
    (n bsize esize msize : Nat) :
    (exitState template mem n bsize esize msize).execLength =
      template.execLength := rfl

@[simp] theorem exit_halt (template : State) (mem : ByteArray)
    (n bsize esize msize : Nat) :
    (exitState template mem n bsize esize msize).halt = template.halt := rfl

@[simp] theorem exit_callStack (template : State) (mem : ByteArray)
    (n bsize esize msize : Nat) :
    (exitState template mem n bsize esize msize).callStack =
      template.callStack := rfl

end Challenge.Modexp.Submission.Proofs.Fast.RrLeadingTraceCore
