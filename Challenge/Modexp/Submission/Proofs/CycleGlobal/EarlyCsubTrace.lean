import Challenge.Modexp.Submission.Proofs.CycleGlobal.FastDefs
import Challenge.Modexp.Submission.Proofs.CycleGlobal.Binding
import Challenge.Modexp.Submission.Proofs.CycleGlobal.CsubCore
import Challenge.Modexp.Submission.Proofs.Fast.EarlyCsubModel
import Challenge.Modexp.Submission.Proofs.CycleGlobal.EarlyCsubInstructions

noncomputable section
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000

namespace CycleSubmission.Global.Fast.Csub
open Challenge.Modexp
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Fast.Csub
open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel
open EarlyCsub

def csEntryState (s : State) (mem : ByteArray) (dst ret : UInt256) (rest : List UInt256) : State :=
  EarlyCsub.atState s mem 3442 dst ret rest

/-- Every guard outcome reaches the caller with the specified result memory. -/
def gasSteps_csub (s : State) (memory : ByteArray) (n : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) (hn : 2 ≤ n) (hn32 : n ≤ 8)
    (hjump : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode ret.toNat = true)
    (hml : MachineState.readWord memory 2752 = UInt256.ofNat (32*n-32))
    (htl : MachineState.readWord memory 2784 = UInt256.ofNat (2080+32*n))
    (hs32 : MachineState.readWord (csStep memory n n).memory 2688 = UInt256.ofNat (32*n))
    (hdstFit : pdst.toNat+32*n ≤ 2816)
    (htn : (MachineState.readWord (csStep memory n n).memory 2080).toNat ≤ 1)
    (hfast : n = 4 ∨ n = 8) :
    Challenge.EvmProof.GasSteps (csEntryState s memory pdst ret rest)
      (csReturnedState s memory n n pdst ret rest) := by
  have hc := checkBlock.steps
    (environment (csEntryState s memory pdst ret rest) hcode hfork hrun hnp) rfl
    (run_check s memory pdst ret rest hcap hact hcode)
  by_cases hskip : Skip memory
  · rw [if_pos hskip] at hc
    have hs : MachineState.readWord memory 2688 = UInt256.ofNat (32*n) := by
      rw [csStep_readWord_disjoint memory n 2688 (by omega) (by omega) n le_rfl] at hs32
      exact hs32
    have hk := copyBlock.steps
      (environment (atState s memory 3706 pdst ret rest) hcode hfork hrun hnp) rfl
      (run_copy s memory n pdst ret rest hcap hact hn hn32 hcode hs hdstFit hjump)
    simpa only [csReturnedState,if_pos hskip,copiedState] using hc.trans hk
  · rw [if_neg hskip] at hc
    have hj := jumpBlock.steps
      (environment (atState s memory 3458 pdst ret rest) hcode hfork hrun hnp) rfl
      (run_jump s memory pdst ret rest hcap hcode)
    have hk := gasSteps_csub_sub s memory n pdst ret rest hcap hcode hfork hrun hnp
      hact hn hn32 hjump hml htl hs32 hdstFit htn hfast
    have hc' : Challenge.EvmProof.GasSteps (csEntryState s memory pdst ret rest)
        (subEntryState s memory pdst ret rest) := hc.trans hj
    simpa only [csReturnedState,if_neg hskip,subReturnedState] using hc'.trans hk

end CycleSubmission.Global.Fast.Csub
