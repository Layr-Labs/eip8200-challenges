import Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedMaskCavitySites
import Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedMaskCaps
import Challenge.Ripemd160.Submission.Proofs.Bytecode.CavityFragmentChain

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.FourthInlineExecution

open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTemplate StackRoundTrace QuadRoundTemplate CavityQuadGroup
open CachedMaskQuadGroup CachedMaskParams CachedMaskCaps CachedMaskCavitySites

noncomputable def left4_core (s : State) (w : Compression.EvmWorking)
    (rho : List UInt256) (hfit : ∀ k, ((left 4) k).Fits s)
    (hstack : rho.length < 1006) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = A.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (stateAt s left4First.startPC w (mask :: rho))
      (stateAt s left4First.endPC (fourResult (left 4) s w) (mask :: rho)) := by
  have hwhole := run_leftCode 4 s left4First.startPC w rho hfit hstack hrun
  rw [← CavityFragmentChain.site_end left4First] at hwhole
  apply Stepper.runLocatedBlock_sound A .Osaka left4First.path
  · simpa [stateAt, roundEntry] using hcode
  · simpa [stateAt, roundEntry] using hfork
  · rw [PairMultiplyLift.runLocatedBlock_eq_raw left4First (left_advances 4)
      (stateAt s left4First.startPC w (mask :: rho)) rfl]
    exact hwhole
  · simpa [stateAt, roundEntry] using hrun
  · simpa [stateAt, roundEntry] using hnp

theorem return_start : left4Return.push.pc = left4First.endPC := by rfl

noncomputable def left4_group (s : State) (w : Compression.EvmWorking)
    (rho : List UInt256) (hfit : ∀ k, ((left 4) k).Fits s)
    (hstack : rho.length < 1006) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = A.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (stateAt s left4First.startPC w (mask :: rho))
      (stateAt s left4Return.destination.pc.succ (fourResult (left 4) s w) (mask :: rho)) := by
  have core := left4_core s w rho hfit hstack hrun hcode hfork hnp
  have hcap (work : Compression.EvmWorking) :
      ([work.a, work.b, work.c, work.d, work.e] ++ factor :: (mask :: rho)).length < 1023 := by
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  have ret := gasSteps_bridge left4Return s
    ([(fourResult (left 4) s w).a, (fourResult (left 4) s w).b,
      (fourResult (left 4) s w).c, (fourResult (left 4) s w).d,
      (fourResult (left 4) s w).e] ++ factor :: (mask :: rho))
    (hcap (fourResult (left 4) s w)) hcode hfork hrun hnp
  rw [return_start] at ret
  exact core.trans ret

#print axioms left4_core
#print axioms left4_group

end Challenge.Ripemd160.Submission.Proofs.Bytecode.FourthInlineExecution
