import Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedMaskCavitySites
import Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedMaskCaps
import Challenge.Ripemd160.Submission.Proofs.Bytecode.CavityFragmentCap

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedMaskCavityExecution

open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTemplate StackRoundTrace QuadRoundTemplate CavityQuadGroup CavityFragmentChain
open CachedMaskQuadGroup CachedMaskParams CachedMaskCaps CachedMaskCavitySites

theorem left0_first_end : left0Bridge1.push.pc = left0First.endPC := by rfl
theorem left0_second_start : left0Second.startPC = left0Bridge1.destination.pc.succ := by rfl
theorem left0_entry_end : left0First.startPC = left0Entry.destination.pc.succ := by rfl
theorem left0_return_start : left0Return.push.pc = left0Second.endPC := by rfl

noncomputable def left0_core (s : State) (w : Compression.EvmWorking)
    (rho : List UInt256) (hfit : ∀ k, ((left 0) k).Fits s)
    (hstack : rho.length < 1006) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = A.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (stateAt s left0First.startPC w (mask :: rho))
      (stateAt s left0Second.endPC (fourResult (left 0) s w) (mask :: rho)) := by
  have hwhole := run_leftCode 0 s left0First.startPC w rho hfit hstack hrun

  have g := gasSteps_twoPieces ((leftCode 0).take 407) ((leftCode 0).drop 407)
    left0First left0Second left0Bridge1 left0_first_end left0_second_start
    (fun i hi => left_advances 0 i (List.mem_of_mem_take hi))
    (fun i hi => left_advances 0 i (List.mem_of_mem_drop hi))
    (stateAt s left0First.startPC w (mask :: rho))
    (stateAt s (pcAfter left0First.startPC (leftCode 0)) (fourResult (left 0) s w) (mask :: rho))
    rfl (by simpa only [List.take_append_drop] using hwhole)
    (left_prefix_cap 0 407 left0_total s left0First.startPC w rho hstack) hcode hfork hrun hnp
  exact g

noncomputable def left0_group (s : State) (w : Compression.EvmWorking)
    (rho : List UInt256) (hfit : ∀ k, ((left 0) k).Fits s)
    (hstack : rho.length < 1006) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = A.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (stateAt s left0Entry.push.pc w (mask :: rho))
      (stateAt s left0Return.destination.pc.succ (fourResult (left 0) s w) (mask :: rho)) := by
  have hcap (work : Compression.EvmWorking) :
      ([work.a, work.b, work.c, work.d, work.e] ++ factor :: (mask :: rho)).length < 1023 := by
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  have enter := gasSteps_bridge left0Entry s
    ([w.a, w.b, w.c, w.d, w.e] ++ factor :: (mask :: rho)) (hcap w) hcode hfork hrun hnp
  have core := left0_core s w rho hfit hstack hrun hcode hfork hnp
  rw [left0_entry_end] at core
  have ret := gasSteps_bridge left0Return s
    ([(fourResult (left 0) s w).a, (fourResult (left 0) s w).b, (fourResult (left 0) s w).c, (fourResult (left 0) s w).d, (fourResult (left 0) s w).e] ++ factor :: (mask :: rho))
    (hcap (fourResult (left 0) s w)) hcode hfork hrun hnp
  rw [left0_return_start] at ret
  exact (enter.trans core).trans ret

#print axioms left0_core
#print axioms left0_group

theorem left2_first_end : left2Bridge1.push.pc = left2First.endPC := by rfl
theorem left2_second_start : left2Second.startPC = left2Bridge1.destination.pc.succ := by rfl
theorem left2_entry_end : left2First.startPC = left2Entry.destination.pc.succ := by rfl
theorem left2_return_start : left2Return.push.pc = left2Third.endPC := by rfl

theorem left2_middle_end : left2Bridge2.push.pc = left2Second.endPC := by rfl
theorem left2_third_start : left2Third.startPC = left2Bridge2.destination.pc.succ := by rfl

noncomputable def left2_core (s : State) (w : Compression.EvmWorking)
    (rho : List UInt256) (hfit : ∀ k, ((left 2) k).Fits s)
    (hstack : rho.length < 1006) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = A.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (stateAt s left2First.startPC w (mask :: rho))
      (stateAt s left2Third.endPC (fourResult (left 2) s w) (mask :: rho)) := by
  have hwhole := run_leftCode 2 s left2First.startPC w rho hfit hstack hrun

  let result := stateAt s (pcAfter left2First.startPC (leftCode 2))
    (fourResult (left 2) s w) (mask :: rho)
  apply CavityFragmentCap.gasSteps_splice_cap
    ((leftCode 2).take 181) ((leftCode 2).drop 181)
    left2First left2Bridge1 left2_first_end
    (fun i hi => left_advances 2 i (List.mem_of_mem_take hi))
    (fun i hi => left_advances 2 i (List.mem_of_mem_drop hi))
    (stateAt s left2First.startPC w (mask :: rho)) result
    (stateAt s left2Third.endPC (fourResult (left 2) s w) (mask :: rho))
    rfl (by simpa only [List.take_append_drop] using hwhole)
    (left_prefix_cap 2 181 left2_total s left2First.startPC w rho hstack) hcode hfork hrun hnp
  intro middle hpc henv hrunMiddle hcapMiddle hraw
  have hsplit :
      ((leftCode 2).drop 181).take 210 ++ (leftCode 2).drop 391 =
        (leftCode 2).drop 181 := by
    rw [show (leftCode 2).drop 391 = ((leftCode 2).drop 181).drop 210 by
      rw [List.drop_drop]]
    exact List.take_append_drop 210 ((leftCode 2).drop 181)
  have hrawSplit :
      runInstrSeq (((leftCode 2).drop 181).take 210 ++ (leftCode 2).drop 391) middle =
        some {result with pc := pcAfter middle.pc ((leftCode 2).drop 181)} := by
    rw [hsplit]
    exact hraw
  have g := gasSteps_twoPieces
    (((leftCode 2).drop 181).take 210) ((leftCode 2).drop 391)
    left2Second left2Third left2Bridge2 left2_middle_end left2_third_start
    (fun i hi => left_advances 2 i (List.mem_of_mem_drop (List.mem_of_mem_take hi)))
    (fun i hi => left_advances 2 i (List.mem_of_mem_drop hi))
    middle {result with pc := pcAfter middle.pc ((leftCode 2).drop 181)}
    (hpc.trans left2_second_start.symm) hrawSplit (left2_middle_cap middle hcapMiddle)
    (by rw [henv]; exact hcode)
    (by change middle.executionEnv.fork = .Osaka; rw [henv]; exact hfork)
    hrunMiddle (by rw [henv]; exact hnp)
  exact g

noncomputable def left2_group (s : State) (w : Compression.EvmWorking)
    (rho : List UInt256) (hfit : ∀ k, ((left 2) k).Fits s)
    (hstack : rho.length < 1006) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = A.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (stateAt s left2Entry.push.pc w (mask :: rho))
      (stateAt s left2Return.destination.pc.succ (fourResult (left 2) s w) (mask :: rho)) := by
  have hcap (work : Compression.EvmWorking) :
      ([work.a, work.b, work.c, work.d, work.e] ++ factor :: (mask :: rho)).length < 1023 := by
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  have enter := gasSteps_bridge left2Entry s
    ([w.a, w.b, w.c, w.d, w.e] ++ factor :: (mask :: rho)) (hcap w) hcode hfork hrun hnp
  have core := left2_core s w rho hfit hstack hrun hcode hfork hnp
  rw [left2_entry_end] at core
  have ret := gasSteps_bridge left2Return s
    ([(fourResult (left 2) s w).a, (fourResult (left 2) s w).b, (fourResult (left 2) s w).c, (fourResult (left 2) s w).d, (fourResult (left 2) s w).e] ++ factor :: (mask :: rho))
    (hcap (fourResult (left 2) s w)) hcode hfork hrun hnp
  rw [left2_return_start] at ret
  exact (enter.trans core).trans ret

#print axioms left2_core
#print axioms left2_group

theorem right_first_end : rightBridge1.push.pc = rightFirst.endPC := by rfl
theorem right_second_start : rightSecond.startPC = rightBridge1.destination.pc.succ := by rfl
theorem right_entry_end : rightFirst.startPC = rightEntry.destination.pc.succ := by rfl
theorem right_return_start : rightReturn.push.pc = rightSecond.endPC := by rfl

noncomputable def right_core (s : State) (w : Compression.EvmWorking) (a b c d e : UInt256)
    (rho : List UInt256) (hfit : ∀ k, (right k).Fits s)
    (hstack : rho.length < 1001) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = A.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (stateAt s rightFirst.startPC w (a :: b :: c :: d :: e :: mask :: rho))
      (stateAt s rightSecond.endPC (fourResult right s w) (a :: b :: c :: d :: e :: mask :: rho)) := by
  have hwhole := run_rightCode s rightFirst.startPC w a b c d e rho hfit hstack hrun

  have g := gasSteps_twoPieces (rightCode.take 380) (rightCode.drop 380)
    rightFirst rightSecond rightBridge1 right_first_end right_second_start
    (fun i hi => right_advances i (List.mem_of_mem_take hi))
    (fun i hi => right_advances i (List.mem_of_mem_drop hi))
    (stateAt s rightFirst.startPC w (a :: b :: c :: d :: e :: mask :: rho))
    (stateAt s (pcAfter rightFirst.startPC rightCode) (fourResult right s w) (a :: b :: c :: d :: e :: mask :: rho))
    rfl (by simpa only [List.take_append_drop] using hwhole)
    (right_prefix_cap s rightFirst.startPC w a b c d e rho hstack) hcode hfork hrun hnp
  exact g

noncomputable def right_group (s : State) (w : Compression.EvmWorking) (a b c d e : UInt256)
    (rho : List UInt256) (hfit : ∀ k, (right k).Fits s)
    (hstack : rho.length < 1001) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = A.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (stateAt s rightEntry.push.pc w (a :: b :: c :: d :: e :: mask :: rho))
      (stateAt s rightReturn.destination.pc.succ (fourResult right s w) (a :: b :: c :: d :: e :: mask :: rho)) := by
  have hcap (work : Compression.EvmWorking) :
      ([work.a, work.b, work.c, work.d, work.e] ++ factor :: (a :: b :: c :: d :: e :: mask :: rho)).length < 1023 := by
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  have enter := gasSteps_bridge rightEntry s
    ([w.a, w.b, w.c, w.d, w.e] ++ factor :: (a :: b :: c :: d :: e :: mask :: rho)) (hcap w) hcode hfork hrun hnp
  have core := right_core s w a b c d e rho hfit hstack hrun hcode hfork hnp
  rw [right_entry_end] at core
  have ret := gasSteps_bridge rightReturn s
    ([(fourResult right s w).a, (fourResult right s w).b, (fourResult right s w).c, (fourResult right s w).d, (fourResult right s w).e] ++ factor :: (a :: b :: c :: d :: e :: mask :: rho))
    (hcap (fourResult right s w)) hcode hfork hrun hnp
  rw [right_return_start] at ret
  exact (enter.trans core).trans ret

#print axioms right_core
#print axioms right_group

end Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedMaskCavityExecution
