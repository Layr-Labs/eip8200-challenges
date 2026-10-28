import Challenge.Ripemd160.Submission.Local20261028.ColdGuardFixup
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.Control.ColdGuardFixup
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof Local20261028

theorem high_memory (s : State) (hmemsize : 194 ≤ s.memory.size)
    (hzero : ∀ a, 162 ≤ a → a < 194 → s.memory[a]?.getD 0 = 0) :
    (FirstEntry.high s).memory = wMemory s.memory dirtyB dirtyC := by
  have hb : dirtyB = (128 : UInt8) := by decide +kernel
  have hc : dirtyC = (1 : UInt8) := by decide +kernel
  rw [hb,hc]
  change PairedScheduleMemory.writeWord s.memory 162 Control.Shared32Scratch.highWord = Control.Shared32Scratch.sparseMemory s.memory
  exact (Control.Shared32Scratch.sparse_eq_writeWord s.memory hmemsize hzero).symm

def gasSteps_partial (s : State) (h : Compression.HashState) (off limit : UInt256)
    (rho : List UInt256) (hstack : rho.length ≤ 860) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = CandidateArtifact.artifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hsize : s.executionEnv.calldata.size < 2^256)
    (hne : s.executionEnv.calldata.size ≠ 32)
    (hactive : 34 ≤ s.activeWords.toNat)
    (hmemsize : 194 ≤ s.memory.size)
    (hzero : ∀ a, 162 ≤ a → a < 194 → s.memory[a]?.getD 0 = 0)
    (hlim : limit = UInt256.ofNat s.executionEnv.calldata.size) :
    GasSteps {s with pc := UInt256.ofNat 143, stack := StaggerPersistentFrame.frame h off limit rho}
      { s with
        pc := UInt256.ofNat 9998
        stack := StaggerPersistentFrame.frame h off (UInt256.ofNat 9949) rho
        memory := wMemory s.memory dirtyB dirtyC } := by
  have g := gasSteps_high s h off limit rho hstack hrun hcode hfork hnp hsize hne hactive hlim
  have hm := high_memory s hmemsize hzero
  dsimp only [FirstEntry.high] at hm g
  rw [hm] at g
  exact g
#print axioms high_memory
#print axioms gasSteps_partial
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.Control.ColdGuardFixup
