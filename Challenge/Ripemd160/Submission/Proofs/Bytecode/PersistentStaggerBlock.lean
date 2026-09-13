import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadPrefixPersistentBootstrapBridge
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PersistentStaggerPrepare
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PersistentStaggerTailBridge
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PersistentStaggerBlock
open Challenge.Ripemd160 EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open PersistentStaggerTable PersistentStaggerFunctional StaggerPersistentFrame

def gasSteps (s : State) (input : ByteArray) (i : Nat) (h : Compression.HashState)
    (limit : UInt256) (rho : List UInt256) (hs : rho.length ≤ 880)
    (hfit : CalldataFits input) (hi : i < DriverTrace.blockCount input) (ctx : Context s input)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hr : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := LoopCompletionControl.blockPC input i, stack := frame h (DriverTrace.blockOffsetWord i) limit rho}
      {scheduledState s i with pc := UInt256.ofNat 4631, stack := frame (result (scheduledState s i).memory h) (DriverTrace.blockOffsetWord i) limit rho} := by
  let q := scheduledState s i
  let off := DriverTrace.blockOffsetWord i
  have gp := PersistentStaggerPrepare.gasSteps_prepare s input i h limit rho hs hfit hi ctx hcode hfork hr hnp
  have henv : q.executionEnv = s.executionEnv := scheduled_env s i
  have hrq : q.halt = .Running := (scheduled_halt s i).trans hr
  have hcq : q.executionEnv.code = Artifact.submissionArtifact.code := by rw [henv]; exact hcode
  have hfq : q.fork = .Osaka := by change q.executionEnv.fork = _; rw [henv]; exact hfork
  have hnq : Precompile.isPrecompileWithConfig q.executionEnv.precompileConfig
      q.executionEnv.fork q.executionEnv.codeAddr = false := by rw [henv]; exact hnp
  have ha : 35 ≤ q.activeWords.toNat := by
    have ha := scheduled_active s input i hfit hi ctx
    change 35 ≤ (scheduledState s i).activeWords.toNat
    omega
  have gb : GasSteps
      {q with pc := UInt256.ofNat (if input.size = DriverTrace.blockOffset i then 4977 else 925),
        stack := frame h off limit rho}
      (StaggerCore.suffixState q (Word.ofUInt32 h.h4)
        (StaggerCoreModel.paired q.memory (initial h)) (coreRest h off limit rho)) := by
    by_cases hh : input.size = DriverTrace.blockOffset i
    · have hhs : s.executionEnv.calldata.size = DriverTrace.blockOffset i := by
        rw [ctx.calldata]; exact hh
      have hz : PadPrefixContract.ZeroLoads q := by
        dsimp only [q]
        rw [scheduledState_hit s i hhs]
        apply PadPrefixContract.from_pad s (UInt256.ofNat s.executionEnv.calldata.size)
        rw [Word.word_toNat_ofNat, Nat.mod_eq_of_lt]
        · rw [ctx.calldata]; exact hfit
        · rw [ctx.calldata]; exact calldata_lt_uint256 input hfit
      simpa only [if_pos hh] using
        PadPrefixPersistentBootstrapBridge.gasSteps_body q h off limit rho
          (by omega) hrq ha hz hcq hfq hnq
    · simpa only [if_neg hh] using
        StaggerPersistentBootstrapBridge.gasSteps_body q h off limit rho
          (by omega) hrq ha hcq hfq hnq
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
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PersistentStaggerBlock
