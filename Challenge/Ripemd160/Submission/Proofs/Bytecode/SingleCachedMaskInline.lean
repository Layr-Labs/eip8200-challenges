import Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedMaskQuadGroup
import Challenge.Ripemd160.Submission.Proofs.Bytecode.CavityFragmentChain

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.SingleCachedMaskInline

open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTemplate StackRoundTrace CavityQuadGroup CachedMaskQuadGroup

def gasSteps_right {artifact : ProgramArtifact} {fork : Fork}
    (q : Params) (site : GenericRoundSite artifact fork (code q 5))
    (s : State) (w : Compression.EvmWorking) (a b c d e : UInt256)
    (rho : List UInt256) (hfit : q.Fits s) (hstack : rho.length < 1001)
    (hcode : s.executionEnv.code = artifact.code) (hfork : s.fork = fork)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (stateAt s site.startPC w (a :: b :: c :: d :: e :: mask :: rho))
      (stateAt s site.endPC (q.apply s w) (a :: b :: c :: d :: e :: mask :: rho)) := by
  have hraw := CachedMaskQuadGroup.run_right q s site.startPC w a b c d e rho
    hfit hstack hrun
  rw [← CavityFragmentChain.site_end site] at hraw
  apply Stepper.runLocatedBlock_sound artifact fork site.path
  · exact hcode
  · exact hfork
  · rw [PairMultiplyLift.runLocatedBlock_eq_raw site
      (CachedMaskQuadGroup.advances q 5) _ rfl]
    exact hraw
  · exact hrun
  · exact hnp

def gasSteps_destination {artifact : ProgramArtifact} {fork : Fork}
    (site : LocatedSite artifact fork)
    (hinstr : site.located.instruction = .op .JUMPDEST)
    (s : State) (stack : List UInt256) (hstack : stack.length < 1024)
    (hcode : s.executionEnv.code = artifact.code) (hfork : s.fork = fork)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := site.pc, stack := stack}
      {s with pc := site.pc.succ, stack := stack} := by
  apply Stepper.runLocatedBlock_sound artifact fork [site.located]
  · exact hcode
  · exact hfork
  · simp [Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
      hinstr, site.pc_eq, hrun, hstack]
  · exact hrun
  · exact hnp

#print axioms gasSteps_right
#print axioms gasSteps_destination

end Challenge.Ripemd160.Submission.Proofs.Bytecode.SingleCachedMaskInline
