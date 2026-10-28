import Challenge.Ripemd160.Submission.Local20261028.ColdGuardRaw
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.Control.ColdGuardFixup
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace StackRoundTemplate Local20261028

def gasSteps_special (s : State) (e : FirstEntry.Env s) (h : Compression.HashState) (off limit : UInt256)
    (rho : List UInt256) (hs : rho.length ≤ 860) (ha : 34 ≤ s.activeWords.toNat)
    (he : UInt256.eq (UInt256.ofNat 32) limit = UInt256.ofNat 0) :
    GasSteps {s with pc := UInt256.ofNat 143, stack := StaggerPersistentFrame.frame h off limit rho}
      {FirstEntry.high s with pc := UInt256.ofNat 188, stack := StaggerPersistentFrame.frame h off (UInt256.ofNat 9949) rho} := by
  apply PadLift.gasSteps_of_raw ControlSites.specialSite {s with pc := UInt256.ofNat 143, stack := StaggerPersistentFrame.frame h off limit rho}
    {FirstEntry.high s with pc := UInt256.ofNat 188, stack := StaggerPersistentFrame.frame h off (UInt256.ofNat 9949) rho}
    e.code e.fork e.running e.noPrecompile ControlSites.special_pc.symm
  · apply PadLift.advancesAll_sound; decide +kernel
  · exact run_special s h off limit rho hs e.running ha he

def gasSteps_jump (s : State) (e : FirstEntry.Env s) (frame : List UInt256) (hc : frame.length + 1 < 1024) :
    GasSteps {s with pc := UInt256.ofNat 188, stack := frame}
      {s with pc := UInt256.ofNat 9997, stack := frame} := by
  apply PadLift.gasSteps_of_raw jumpSite {s with pc := UInt256.ofNat 188, stack := frame}
    {s with pc := UInt256.ofNat 9997, stack := frame}
    e.code e.fork e.running e.noPrecompile jump_pc.symm
  · apply PadLift.advancesAll_sound; decide +kernel
  · have hv : Decode.isValidJumpDest s.executionEnv.code 9997 = true := by rw [e.code]; exact valid9997
    have hb : frame.length < 1024 := by omega
    simp [jumpCode,runInstrSeq,DataStepper.runInstr,e.running,hv,hc,hb]

def gasSteps_join (s : State) (e : FirstEntry.Env s) (frame : List UInt256) (hc : frame.length < 1024) :
    GasSteps {s with pc := UInt256.ofNat 9997, stack := frame}
      {s with pc := UInt256.ofNat 9998, stack := frame} := by
  apply PadLift.gasSteps_of_raw joinSite {s with pc := UInt256.ofNat 9997, stack := frame}
    {s with pc := UInt256.ofNat 9998, stack := frame}
    e.code e.fork e.running e.noPrecompile join_pc.symm
  · apply PadLift.advancesAll_sound; decide +kernel
  · simp [joinCode,runInstrSeq,DataStepper.runInstr,hc]; rfl


#print axioms gasSteps_special
#print axioms gasSteps_jump
#print axioms gasSteps_join
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.Control.ColdGuardFixup
