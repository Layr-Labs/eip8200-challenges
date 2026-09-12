import Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionLoop
set_option warningAsError true
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionScan
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open RecognitionSites RecognitionMovement RecognitionBodyRaw RecognitionLoop RecognitionAccumulator

def hitState (s : State) (n : Nat) (rho : List UInt256) : State :=
  atState s 4793 (frame (endFrame s n) rho)

def gasSteps_hit (s : State) (e : Env s) (n : Nat) (rho : List UInt256)
    (hs : rho.length ≤ 990) (hn : Allowed n) (hsize : s.executionEnv.calldata.size = n)
    (hzero : resultAcc s.executionEnv.calldata n = 0) :
    GasSteps (atState s 108 rho) (hitState s n rho) := by
  have hz : (endFrame s n).acc.toNat = 0 := by
    rw [endFrame_acc s n hn hsize, hzero]
    rfl
  exact (gasSteps_accumulate s e n rho hs hn hsize).trans
    (gasSteps_finish_yes s e (endFrame s n) rho hs hz)

def gasSteps_miss (s : State) (e : Env s) (n : Nat) (rho : List UInt256)
    (hs : rho.length ≤ 990) (hn : Allowed n) (hsize : s.executionEnv.calldata.size = n)
    (hzero : resultAcc s.executionEnv.calldata n ≠ 0) :
    GasSteps (atState s 108 rho) (atState s 335 rho) := by
  have hz : (endFrame s n).acc.toNat ≠ 0 := by
    intro h
    apply hzero
    apply Challenge.EvmProof.Word.word_ext
    change (resultAcc s.executionEnv.calldata n).toNat = 0
    simpa only [endFrame_acc s n hn hsize] using h
  exact (gasSteps_accumulate s e n rho hs hn hsize).trans
    ((gasSteps_finish_no s e (endFrame s n) rho hs hz).trans
      (gasSteps_cleanup s e (endFrame s n) rho hs))

#print axioms gasSteps_hit
#print axioms gasSteps_miss
end Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionScan
