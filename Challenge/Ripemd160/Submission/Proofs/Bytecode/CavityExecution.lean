import Challenge.Ripemd160.Submission.Proofs.Bytecode.CavitySites
import Challenge.Ripemd160.Submission.Proofs.Bytecode.CavityCaps

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.CavityExecution

open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTemplate StackRoundTrace QuadRoundTemplate CavityQuadGroup CavityParams
open CavitySites CavityCaps CavityFragmentChain

theorem left_first_end : leftBridge1.push.pc = leftFirst.endPC := by rfl
theorem left_second_start : leftSecond.startPC = leftBridge1.destination.pc.succ := by rfl
theorem left_entry_end : leftFirst.startPC = leftEntry.destination.pc.succ := by rfl
theorem left_return_start : leftReturn.push.pc = leftSecond.endPC := by rfl

theorem right_first_end : rightBridge1.push.pc = rightFirst.endPC := by rfl
theorem right_second_start : rightSecond.startPC = rightBridge1.destination.pc.succ := by rfl
theorem right_entry_end : rightFirst.startPC = rightEntry.destination.pc.succ := by rfl
theorem right_return_start : rightReturn.push.pc = rightSecond.endPC := by rfl

noncomputable def left_core (s : State) (w : Compression.EvmWorking)
    (rho : List UInt256) (hfit : ∀ k, (left k).Fits s)
    (hstack : rho.length < 1007) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = A.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (stateAt s leftFirst.startPC w rho)
      (stateAt s leftSecond.endPC (leftResult s w) rho) := by
  have hwhole := run_leftCode s leftFirst.startPC w rho hfit hstack hrun
  have g := gasSteps_twoPieces (leftCode.take 320) (leftCode.drop 320)
    leftFirst leftSecond leftBridge1 left_first_end left_second_start
    (fun i hi => left_advances i (List.mem_of_mem_take hi))
    (fun i hi => left_advances i (List.mem_of_mem_drop hi))
    (stateAt s leftFirst.startPC w rho)
    (stateAt s (pcAfter leftFirst.startPC leftCode) (leftResult s w) rho)
    rfl (by simpa only [List.take_append_drop] using hwhole)
    (left_prefix_cap s leftFirst.startPC w rho hstack)
    hcode hfork hrun hnp
  exact g

noncomputable def right_core (s : State) (w : Compression.EvmWorking)
    (rho : List UInt256) (hfit : ∀ k, (right k).Fits s)
    (hstack : rho.length < 1007) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = A.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (stateAt s rightFirst.startPC w rho)
      (stateAt s rightSecond.endPC (rightResult s w) rho) := by
  have hwhole := run_rightCode s rightFirst.startPC w rho hfit hstack hrun
  have g := gasSteps_twoPieces (rightCode.take 298) (rightCode.drop 298)
    rightFirst rightSecond rightBridge1 right_first_end right_second_start
    (fun i hi => right_advances i (List.mem_of_mem_take hi))
    (fun i hi => right_advances i (List.mem_of_mem_drop hi))
    (stateAt s rightFirst.startPC w rho)
    (stateAt s (pcAfter rightFirst.startPC rightCode) (rightResult s w) rho)
    rfl (by simpa only [List.take_append_drop] using hwhole)
    (right_prefix_cap s rightFirst.startPC w rho hstack)
    hcode hfork hrun hnp
  exact g

noncomputable def left_group (s : State) (w : Compression.EvmWorking)
    (rho : List UInt256) (hfit : ∀ k, (left k).Fits s)
    (hstack : rho.length < 1007) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = A.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (stateAt s leftEntry.push.pc w rho)
      (stateAt s leftReturn.destination.pc.succ (leftResult s w) rho) := by
  have hcap (work : Compression.EvmWorking) :
      ([work.a, work.b, work.c, work.d, work.e] ++ factor :: rho).length < 1023 := by
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  have enter := gasSteps_bridge leftEntry s
    ([w.a, w.b, w.c, w.d, w.e] ++ factor :: rho) (hcap w) hcode hfork hrun hnp
  have core := left_core s w rho hfit hstack hrun hcode hfork hnp
  rw [left_entry_end] at core
  have ret := gasSteps_bridge leftReturn s
    ([(leftResult s w).a, (leftResult s w).b, (leftResult s w).c,
      (leftResult s w).d, (leftResult s w).e] ++ factor :: rho)
    (hcap (leftResult s w)) hcode hfork hrun hnp
  rw [left_return_start] at ret
  exact (enter.trans core).trans ret

noncomputable def right_group (s : State) (w : Compression.EvmWorking)
    (rho : List UInt256) (hfit : ∀ k, (right k).Fits s)
    (hstack : rho.length < 1007) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = A.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (stateAt s rightEntry.push.pc w rho)
      (stateAt s rightReturn.destination.pc.succ (rightResult s w) rho) := by
  have hcap (work : Compression.EvmWorking) :
      ([work.a, work.b, work.c, work.d, work.e] ++ factor :: rho).length < 1023 := by
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  have enter := gasSteps_bridge rightEntry s
    ([w.a, w.b, w.c, w.d, w.e] ++ factor :: rho) (hcap w) hcode hfork hrun hnp
  have core := right_core s w rho hfit hstack hrun hcode hfork hnp
  rw [right_entry_end] at core
  have ret := gasSteps_bridge rightReturn s
    ([(rightResult s w).a, (rightResult s w).b, (rightResult s w).c,
      (rightResult s w).d, (rightResult s w).e] ++ factor :: rho)
    (hcap (rightResult s w)) hcode hfork hrun hnp
  rw [right_return_start] at ret
  exact (enter.trans core).trans ret

#print axioms left_core
#print axioms right_core
#print axioms left_group
#print axioms right_group

end Challenge.Ripemd160.Submission.Proofs.Bytecode.CavityExecution
