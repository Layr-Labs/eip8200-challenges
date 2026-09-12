import Challenge.Ripemd160.Submission.Proofs.Bytecode.PersistentStaggerPrepare
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PersistentStaggerTailBridge
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PersistentStaggerBlock
open Challenge.Ripemd160 EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open PersistentStaggerTable PersistentStaggerFunctional StaggerPersistentFrame

def gasSteps (s : State) (input : ByteArray) (i : Nat) (h : Compression.HashState)
    (limit : UInt256) (rho : List UInt256) (hs : rho.length ≤ 890)
    (hfit : CalldataFits input) (hi : i < DriverTrace.blockCount input) (ctx : Context s input)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hr : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 466, stack := frame h (DriverTrace.blockOffsetWord i) limit rho}
      {scheduledState s i with pc := UInt256.ofNat 4724, stack := frame (result (scheduledState s i).memory h) (DriverTrace.blockOffsetWord i) limit rho} := by
  let q := scheduledState s i
  let off := DriverTrace.blockOffsetWord i
  have gp := PersistentStaggerPrepare.gasSteps_prepare s input i h limit rho hs hfit hi ctx hcode hfork hr hnp
  have gb := StaggerPersistentBootstrapBridge.gasSteps_body q h off limit rho (by omega) hr
    (by change 35 ≤ (scheduledState s i).activeWords.toNat
        have ha := scheduled_active s input i hfit hi
        omega) hcode hfork hnp
  have gt := PersistentStaggerTailBridge.gasSteps q h
    (StaggerCoreModel.paired q.memory (initial h)) off limit rho (by omega) hr hcode hfork hnp
  have hrest : StaggerPersistentPackBridge.suffix (initial h) off limit rho = coreRest h off limit rho := by
    change StaggerPersistentPackBridge.suffix (StaggerPersistentBootstrapBridge.initial h) off limit rho = _
    rw [StaggerPersistentBootstrapBridge.initial_eq]
    rfl
  have he : (initial h).e = Word.ofUInt32 h.h4 := by
    change (StaggerPersistentBootstrapBridge.initial h).e = _
    rw [StaggerPersistentBootstrapBridge.initial_eq]
  rw [he, hrest] at gt
  exact gp.trans (gb.trans gt)
#print axioms gasSteps
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PersistentStaggerBlock
