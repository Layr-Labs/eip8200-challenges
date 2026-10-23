import Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.ColdOrdinaryPrepare
import Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.PersistentStaggerTailBridge
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.ColdOrdinaryBlock
open Challenge.Ripemd160 EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open HoistedInherited.PersistentStaggerTable PersistentStaggerFunctional StaggerPersistentFrame

def gasSteps (s : State) (input : ByteArray) (i : Nat) (h : Compression.HashState)
    (limit : UInt256) (rho : List UInt256) (hs : rho.length ≤ 880)
    (tail : List UInt256) (hrho : rho = DenseScheduleTemplate.mask8 :: DenseScheduleTemplate.mask16 :: tail)
    (hfit : CalldataFits input) (hi : i < DriverTrace.blockCount input) (ctx : Context s input i)
    (hcode : s.executionEnv.code = HoistedInherited.Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hr : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with
        pc := LoopCompletionControl.blockPC input i
        stack := frame h (DriverTrace.messageOffsetWord (LoopCompletionControl.offIndex input i)) limit rho}
      {scheduledState s i with
        pc := UInt256.ofNat 4581
        stack := Word.ofUInt32 h.h2 :: frame (result (scheduledState s i).memory h)
          (DriverTrace.messageOffsetWord (LoopCompletionControl.offIndex input i))
          (StaggerPersistentLoopRaw.blockCont input i limit) rho} := by
  let q := scheduledState s i
  let off := DriverTrace.messageOffsetWord (LoopCompletionControl.offIndex input i)
  let cont := StaggerPersistentLoopRaw.blockCont input i limit
  have gp := HoistedInherited.ColdOrdinaryPrepare.gasSteps_prepare s input i h limit rho hs tail hrho hfit hi ctx hcode hfork hr hnp
  have henv : q.executionEnv = s.executionEnv := scheduled_env s i
  have hrq : q.halt = .Running := (scheduled_halt s i).trans hr
  have hcq : q.executionEnv.code = HoistedInherited.Artifact.submissionArtifact.code := by rw [henv]; exact hcode
  have hfq : q.fork = .Osaka := by change q.executionEnv.fork = _; rw [henv]; exact hfork
  have hnq : Precompile.isPrecompileWithConfig q.executionEnv.precompileConfig
      q.executionEnv.fork q.executionEnv.codeAddr = false := by rw [henv]; exact hnp
  have gb := HoistedInherited.StaggerPersistentBootstrapBridge.gasSteps_body q h off cont rho (by omega) hrq
    (by change 35 ≤ (scheduledState s i).activeWords.toNat
        have ha := scheduled_active s input i hfit hi ctx
        omega) hcq hfq hnq
  have gt := HoistedInherited.PersistentStaggerTailBridge.gasSteps q h
    (StaggerCoreModel.paired q.memory (initial h)) off cont rho (by omega) hrq hcq hfq hnq
  have hrest : HoistedInherited.StaggerPersistentPackBridge.suffix (initial h) off cont rho = coreRest h off cont rho := by
    change HoistedInherited.StaggerPersistentPackBridge.suffix (HoistedInherited.StaggerPersistentBootstrapBridge.initial h) off cont rho = _
    rw [HoistedInherited.StaggerPersistentBootstrapBridge.initial_eq]
    rfl
  have he : (initial h).e = Word.ofUInt32 h.h4 := by
    change (HoistedInherited.StaggerPersistentBootstrapBridge.initial h).e = _
    rw [HoistedInherited.StaggerPersistentBootstrapBridge.initial_eq]
  rw [he, hrest] at gt
  exact gp.trans (gb.trans gt)
#print axioms gasSteps
end Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.ColdOrdinaryBlock
