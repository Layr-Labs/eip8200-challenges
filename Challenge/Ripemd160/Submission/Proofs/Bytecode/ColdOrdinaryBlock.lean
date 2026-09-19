import Challenge.Ripemd160.Submission.Proofs.Bytecode.ColdOrdinaryPrepare
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PersistentStaggerTailBridge
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.ColdOrdinaryBlock
open Challenge.Ripemd160 EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open PersistentStaggerTable PersistentStaggerFunctional StaggerPersistentFrame

def gasSteps (s : State) (input : ByteArray) (i : Nat) (h : Compression.HashState)
    (limit : UInt256) (rho : List UInt256) (hs : rho.length ≤ 880)
    (tail : List UInt256) (hrho : rho = DenseScheduleTemplate.mask8 :: DenseScheduleTemplate.mask16 :: tail)
    (hfit : CalldataFits input) (hi : i < DriverTrace.blockCount input) (ctx : Context s input i)
    (hordinary : input.size = DriverTrace.blockOffset i → input.size < 5234)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hr : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := LoopCompletionControl.blockPC input i, stack := frame h (DriverTrace.blockOffsetWord i) limit rho}
      {scheduledState s i with pc := UInt256.ofNat 4648, stack := frame (result (scheduledState s i).memory h) (DriverTrace.blockOffsetWord i) limit rho} := by
  let q := scheduledState s i
  let off := DriverTrace.blockOffsetWord i
  have gp := ColdOrdinaryPrepare.gasSteps_prepare s input i h limit rho hs tail hrho hfit hi ctx hordinary hcode hfork hr hnp
  have henv : q.executionEnv = s.executionEnv := scheduled_env s i
  have hrq : q.halt = .Running := (scheduled_halt s i).trans hr
  have hcq : q.executionEnv.code = Artifact.submissionArtifact.code := by rw [henv]; exact hcode
  have hfq : q.fork = .Osaka := by change q.executionEnv.fork = _; rw [henv]; exact hfork
  have hnq : Precompile.isPrecompileWithConfig q.executionEnv.precompileConfig
      q.executionEnv.fork q.executionEnv.codeAddr = false := by rw [henv]; exact hnp
  have gb := StaggerPersistentBootstrapBridge.gasSteps_body q h off limit rho (by omega) hrq
    (by change 35 ≤ (scheduledState s i).activeWords.toNat
        have ha := scheduled_active s input i hfit hi ctx
        omega) hcq hfq hnq
  have gt := PersistentStaggerTailBridge.gasSteps q h
    (StaggerCoreModel.paired q.memory (initial h)) off limit rho (by omega) hrq hcq hfq hnq
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
end Challenge.Ripemd160.Submission.Proofs.Bytecode.ColdOrdinaryBlock
