import Challenge.Modexp.Submission.Proofs.Fast.EarlyCsubModel
import Challenge.Modexp.Submission.Proofs.Fast.EarlyCsubInstructions

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000

namespace Challenge.Modexp.Submission.Proofs.Fast.Csub
open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel
open EarlyCsub

/-- Every guard outcome reaches the caller with the specified result memory. -/
def gasSteps_csub (s : State) (memory : ByteArray) (n : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat) (hn : 2 ≤ n) (hn32 : n ≤ 32)
    (hjump : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode ret.toNat = true)
    (hml : MachineState.readWord memory 9408 = UInt256.ofNat (32*n-32))
    (htl : MachineState.readWord memory 9440 = UInt256.ofNat (8224+32*n))
    (hs32 : MachineState.readWord (csStep memory n n).memory 9344 = UInt256.ofNat (32*n))
    (hdstFit : pdst.toNat+32*n ≤ 9472)
    (htn : (MachineState.readWord (csStep memory n n).memory 8224).toNat ≤ 1) :
    Challenge.EvmProof.GasSteps (csEntryState s memory pdst ret rest)
      (csReturnedState s memory n n pdst ret rest) := by
  have hc := checkBlock.steps
    (environment (csEntryState s memory pdst ret rest) hcode hfork hrun hnp) rfl
    (run_check s memory pdst ret rest hcap hact hcode)
  by_cases hskip : Skip memory
  · rw [if_pos hskip] at hc
    have hj := jumpBlock.steps
      (environment (atState s memory 4660 pdst ret rest) hcode hfork hrun hnp) rfl
      (run_jump s memory pdst ret rest hcap hcode)
    have hs : MachineState.readWord memory 9344 = UInt256.ofNat (32*n) := by
      rw [csStep_readWord_disjoint memory n 9344 (by omega) (by omega) n le_rfl] at hs32
      exact hs32
    have hk := copyBlock.steps
      (environment (atState s memory 5062 pdst ret rest) hcode hfork hrun hnp) rfl
      (run_copy s memory n pdst ret rest hcap hact hn hn32 hcode hs hdstFit hjump)
    simpa only [csReturnedState,if_pos hskip,copiedState] using hc.trans (hj.trans hk)
  · rw [if_neg hskip] at hc
    have hk := gasSteps_csub_sub s memory n pdst ret rest hcap hcode hfork hrun hnp
      hact hn hn32 hjump hml htl hs32 hdstFit htn
    have hc' : Challenge.EvmProof.GasSteps (csEntryState s memory pdst ret rest)
        (subEntryState s memory pdst ret rest) := hc
    simpa only [csReturnedState,if_neg hskip,subReturnedState] using hc'.trans hk

end Challenge.Modexp.Submission.Proofs.Fast.Csub
