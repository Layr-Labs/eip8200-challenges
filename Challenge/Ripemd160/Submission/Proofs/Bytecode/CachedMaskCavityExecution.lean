import Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedMaskCavitySites
import Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedMaskCaps
import Challenge.Ripemd160.Submission.Proofs.Bytecode.CavityFragmentChain

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedMaskCavityExecution

open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTemplate StackRoundTrace QuadRoundTemplate CavityQuadGroup
open CachedMaskQuadGroup CachedMaskParams CachedMaskCaps CachedMaskCavitySites

noncomputable def left0_core (s : State) (w : Compression.EvmWorking)
    (rho : List UInt256) (hfit : ∀ k, ((left 0) k).Fits s)
    (hstack : rho.length < 1006) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = A.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (stateAt s left0First.startPC w (mask :: rho))
      (stateAt s left0First.endPC (fourResult (left 0) s w) (mask :: rho)) := by
  have hwhole := run_leftCode 0 s left0First.startPC w rho hfit hstack hrun
  rw [← CavityFragmentChain.site_end left0First] at hwhole
  apply Stepper.runLocatedBlock_sound A .Osaka left0First.path
  · simpa [stateAt, roundEntry] using hcode
  · simpa [stateAt, roundEntry] using hfork
  · rw [PairMultiplyLift.runLocatedBlock_eq_raw left0First (left_advances 0)
      (stateAt s left0First.startPC w (mask :: rho)) rfl]
    exact hwhole
  · simpa [stateAt, roundEntry] using hrun
  · simpa [stateAt, roundEntry] using hnp

theorem left0_entry_end : left0First.startPC = left0Entry.destination.pc.succ := by rfl
theorem left0_return_start : left0Return.push.pc = left0First.endPC := by rfl

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
    ([(fourResult (left 0) s w).a, (fourResult (left 0) s w).b,
      (fourResult (left 0) s w).c, (fourResult (left 0) s w).d,
      (fourResult (left 0) s w).e] ++ factor :: (mask :: rho))
    (hcap (fourResult (left 0) s w)) hcode hfork hrun hnp
  rw [left0_return_start] at ret
  exact (enter.trans core).trans ret

noncomputable def left2_core (s : State) (w : Compression.EvmWorking)
    (rho : List UInt256) (hfit : ∀ k, ((left 2) k).Fits s)
    (hstack : rho.length < 1006) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = A.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (stateAt s left2First.startPC w (mask :: rho))
      (stateAt s left2First.endPC (fourResult (left 2) s w) (mask :: rho)) := by
  have hwhole := run_leftCode 2 s left2First.startPC w rho hfit hstack hrun
  rw [← CavityFragmentChain.site_end left2First] at hwhole
  apply Stepper.runLocatedBlock_sound A .Osaka left2First.path
  · simpa [stateAt, roundEntry] using hcode
  · simpa [stateAt, roundEntry] using hfork
  · rw [PairMultiplyLift.runLocatedBlock_eq_raw left2First (left_advances 2)
      (stateAt s left2First.startPC w (mask :: rho)) rfl]
    exact hwhole
  · simpa [stateAt, roundEntry] using hrun
  · simpa [stateAt, roundEntry] using hnp

theorem left2_entry_end : left2First.startPC = left2Entry.destination.pc.succ := by rfl
theorem left2_return_start : left2Return.push.pc = left2First.endPC := by rfl

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
    ([(fourResult (left 2) s w).a, (fourResult (left 2) s w).b,
      (fourResult (left 2) s w).c, (fourResult (left 2) s w).d,
      (fourResult (left 2) s w).e] ++ factor :: (mask :: rho))
    (hcap (fourResult (left 2) s w)) hcode hfork hrun hnp
  rw [left2_return_start] at ret
  exact (enter.trans core).trans ret

noncomputable def right_core (s : State) (w : Compression.EvmWorking) (a b c d e : UInt256)
    (rho : List UInt256) (hfit : ∀ k, (right k).Fits s)
    (hstack : rho.length < 1001) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = A.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (stateAt s rightFirst.startPC w (a :: b :: c :: d :: e :: mask :: rho))
      (stateAt s rightFirst.endPC (fourResult right s w)
        (a :: b :: c :: d :: e :: mask :: rho)) := by
  have hwhole := run_rightCode s rightFirst.startPC w a b c d e rho hfit hstack hrun
  rw [← CavityFragmentChain.site_end rightFirst] at hwhole
  apply Stepper.runLocatedBlock_sound A .Osaka rightFirst.path
  · simpa [stateAt, roundEntry] using hcode
  · simpa [stateAt, roundEntry] using hfork
  · rw [PairMultiplyLift.runLocatedBlock_eq_raw rightFirst right_advances
      (stateAt s rightFirst.startPC w (a :: b :: c :: d :: e :: mask :: rho)) rfl]
    exact hwhole
  · simpa [stateAt, roundEntry] using hrun
  · simpa [stateAt, roundEntry] using hnp

theorem right_entry_end : rightFirst.startPC = rightEntry.destination.pc.succ := by rfl
theorem right_return_start : rightReturn.push.pc = rightFirst.endPC := by rfl

noncomputable def right_group (s : State) (w : Compression.EvmWorking) (a b c d e : UInt256)
    (rho : List UInt256) (hfit : ∀ k, (right k).Fits s)
    (hstack : rho.length < 1001) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = A.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (stateAt s rightEntry.push.pc w (a :: b :: c :: d :: e :: mask :: rho))
      (stateAt s rightReturn.destination.pc.succ (fourResult right s w)
        (a :: b :: c :: d :: e :: mask :: rho)) := by
  have hcap (work : Compression.EvmWorking) :
      ([work.a, work.b, work.c, work.d, work.e] ++ factor ::
        (a :: b :: c :: d :: e :: mask :: rho)).length < 1023 := by
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  have enter := gasSteps_bridge rightEntry s
    ([w.a, w.b, w.c, w.d, w.e] ++ factor ::
      (a :: b :: c :: d :: e :: mask :: rho)) (hcap w) hcode hfork hrun hnp
  have core := right_core s w a b c d e rho hfit hstack hrun hcode hfork hnp
  rw [right_entry_end] at core
  have ret := gasSteps_bridge rightReturn s
    ([(fourResult right s w).a, (fourResult right s w).b,
      (fourResult right s w).c, (fourResult right s w).d,
      (fourResult right s w).e] ++ factor ::
      (a :: b :: c :: d :: e :: mask :: rho))
    (hcap (fourResult right s w)) hcode hfork hrun hnp
  rw [right_return_start] at ret
  exact (enter.trans core).trans ret

#print axioms left0_core
#print axioms left0_group
#print axioms left2_core
#print axioms left2_group
#print axioms right_core
#print axioms right_group

end Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedMaskCavityExecution
