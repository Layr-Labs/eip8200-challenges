import Challenge.EvmProof.Stepper
import Challenge.Ripemd160.Submission.H39Memo.DispatchState
import Challenge.Ripemd160.Submission.H39Memo.DispatchTable

set_option warningAsError true
set_option maxRecDepth 40000

namespace Challenge.Ripemd160.Submission.H39Memo.DispatchCompose

open EvmSemantics
open EvmSemantics.EVM
open Challenge.EvmProof

def siteOutputEntry (s : State)
    (site : Challenge.Ripemd160.Submission.H39Memo.DispatchTable.PatternSite) : State :=
  Challenge.Ripemd160.Submission.H39Memo.DispatchState.outputEntry s site.outputPC

def siteReturnState (s : State)
    (site : Challenge.Ripemd160.Submission.H39Memo.DispatchTable.PatternSite)
    (digest : UInt256) : State :=
  Challenge.Ripemd160.Submission.H39Memo.DispatchState.returned
    (siteOutputEntry s site) site.returnPC digest

theorem runLocatedBlock_append
    {artifact : ProgramArtifact} {fork : Fork}
    (left right : List (Stepper.Located artifact fork)) (s t u : State)
    (hleft : Stepper.runLocatedBlock left s = some t)
    (hrunning : t.halt = .Running)
    (hright : Stepper.runLocatedBlock right t = some u) :
    Stepper.runLocatedBlock (left ++ right) s = some u := by
  exact Stepper.runLocatedBlock_append left right s t u hleft hrunning hright

def gasSteps_of_runLocatedBlock
    {artifact : ProgramArtifact} {fork : Fork}
    (path : List (Stepper.Located artifact fork)) (s t : State)
    (hcode : s.executionEnv.code = artifact.code)
    (hfork : s.fork = fork)
    (hresult : Stepper.runLocatedBlock path s = some t)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps s t := by
  exact Stepper.runLocatedBlock_sound artifact fork path hcode hfork hresult hrun hnp

def gasSteps_compose {s t u : State}
    (hst : GasSteps s t) (htu : GasSteps t u) :
    GasSteps s u := by
  exact GasSteps.trans hst htu

@[simp] theorem siteOutputEntry_executionEnv (s : State)
    (site : Challenge.Ripemd160.Submission.H39Memo.DispatchTable.PatternSite) :
    (siteOutputEntry s site).executionEnv = s.executionEnv := by
  rfl

@[simp] theorem siteReturnState_pc (s : State)
    (site : Challenge.Ripemd160.Submission.H39Memo.DispatchTable.PatternSite)
    (digest : UInt256) :
    (siteReturnState s site digest).pc = UInt256.ofNat site.returnPC := by
  rfl

@[simp] theorem siteReturnState_memory (s : State)
    (site : Challenge.Ripemd160.Submission.H39Memo.DispatchTable.PatternSite)
    (digest : UInt256) :
    (siteReturnState s site digest).memory =
      MachineState.writeBytes s.memory
        (Data.Bytes.natToBytesPadded digest.toNat 32) 0 := by
  rfl

end Challenge.Ripemd160.Submission.H39Memo.DispatchCompose
