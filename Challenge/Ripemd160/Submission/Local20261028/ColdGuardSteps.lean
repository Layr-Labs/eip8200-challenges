import Challenge.Ripemd160.Submission.Local20261028.ColdGuardRaw
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.Control.ColdGuardFixup
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace StackRoundTemplate Local20261028

def gasSteps_special (s : State) (e : FirstEntry.Env s) (h : Compression.HashState) (off limit : UInt256)
    (rho : List UInt256) (hs : rho.length ≤ 860) (ha : 34 ≤ s.activeWords.toNat)
    (ht : UInt256.isTrue (UInt256.ofNat 32 - limit)) :
    GasSteps {s with pc := UInt256.ofNat 143, stack := StaggerPersistentFrame.frame h off limit rho}
      {FirstEntry.high s with pc := UInt256.ofNat 6382, stack := StaggerPersistentFrame.frame h off (UInt256.ofNat 4882) rho} := by
  apply PadLift.gasSteps_of_raw ControlSites.specialSite {s with pc := UInt256.ofNat 143, stack := StaggerPersistentFrame.frame h off limit rho}
    {FirstEntry.high s with pc := UInt256.ofNat 6382, stack := StaggerPersistentFrame.frame h off (UInt256.ofNat 4882) rho}
    e.code e.fork e.running e.noPrecompile ControlSites.special_pc.symm
  · apply PadLift.advancesAll_sound; decide +kernel
  · exact run_special s h off limit rho hs e.running ha ht (by rw [e.code]; exact valid9997)

def gasSteps_join (s : State) (e : FirstEntry.Env s) (frame : List UInt256) (hc : frame.length < 1024) :
    GasSteps {s with pc := UInt256.ofNat 6382, stack := frame}
      {s with pc := UInt256.ofNat 6383, stack := frame} := by
  apply PadLift.gasSteps_of_raw joinSite {s with pc := UInt256.ofNat 6382, stack := frame}
    {s with pc := UInt256.ofNat 6383, stack := frame}
    e.code e.fork e.running e.noPrecompile join_pc.symm
  · apply PadLift.advancesAll_sound; decide +kernel
  · simp [joinCode,runInstrSeq,DataStepper.runInstr,hc]; rfl


#print axioms gasSteps_special
#print axioms gasSteps_join
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.Control.ColdGuardFixup
