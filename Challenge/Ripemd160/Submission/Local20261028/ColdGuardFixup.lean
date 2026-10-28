import Challenge.Ripemd160.Submission.Local20261028.ColdGuardSteps
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 100000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.Control.ColdGuardFixup
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace StackRoundTemplate Local20261028
def gasSteps_high (s : State) (h : Compression.HashState) (off limit : UInt256)
    (rho : List UInt256) (hstack : rho.length ≤ 860) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = CandidateArtifact.artifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hsize : s.executionEnv.calldata.size < 2^256)
    (hne : s.executionEnv.calldata.size ≠ 32)
    (hactive : 34 ≤ s.activeWords.toNat)
    (hlim : limit = UInt256.ofNat s.executionEnv.calldata.size) :
    GasSteps {s with pc := UInt256.ofNat 143, stack := StaggerPersistentFrame.frame h off limit rho}
      {FirstEntry.high s with pc := UInt256.ofNat 9998, stack := StaggerPersistentFrame.frame h off (UInt256.ofNat 9949) rho} := by
  have heq : UInt256.eq (UInt256.ofNat 32) limit = UInt256.ofNat 0 := by
    rw [hlim]
    have hw : (UInt256.ofNat s.executionEnv.calldata.size).toNat = s.executionEnv.calldata.size := by
      rw [Word.word_toNat_ofNat, Nat.mod_eq_of_lt hsize]
    unfold UInt256.eq
    rw [hw, if_neg (by simpa using Ne.symm hne)]
  let high := FirstEntry.high s
  let frame := StaggerPersistentFrame.frame h off (UInt256.ofNat 9949) rho
  have cap : frame.length+1 < 1024 := by simp [frame,StaggerPersistentFrame.frame]; omega
  have base : frame.length < 1024 := by omega
  have e : FirstEntry.Env s := ⟨hcode,hfork,hrun,hnp⟩
  have eh : FirstEntry.Env high := ⟨e.code,e.fork,e.running,e.noPrecompile⟩
  have g1 := gasSteps_special s e h off limit rho hstack hactive heq
  have g2 := gasSteps_jump high eh frame cap
  have g3 := gasSteps_join high eh frame base
  exact g1.trans (g2.trans g3)
#print axioms gasSteps_special
#print axioms gasSteps_jump
#print axioms gasSteps_join
#print axioms run_special
#print axioms gasSteps_high
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.Control.ColdGuardFixup
