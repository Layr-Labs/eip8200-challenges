import Challenge.Ripemd160.Submission.Proofs.Bytecode.Table144PrepareModel
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Table144PadJump
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Table144BootstrapSite
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Table144Prepare
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof

def hashRest (h : Compression.HashState) (input : ByteArray) (i : Nat)
    (rho : List UInt256) : List UInt256 :=
  [Word.ofUInt32 h.h1, Word.ofUInt32 h.h2, Word.ofUInt32 h.h3, Word.ofUInt32 h.h4] ++ driverRest input i rho

opaque gasSteps_prepare_hit (s : State) (input : ByteArray) (i : Nat)
    (h : Compression.HashState) (rho : List UInt256) (hstack : rho.length ≤ 980)
    (hfit : input.size < 2^64) (hi : i < DriverTrace.blockCount input)
    (ctx : Context s input i)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hhit : input.size = DriverTrace.blockOffset i) :
    GasSteps (entryState s input i h rho)
      {scheduledState s i with
        pc := UInt256.ofNat 1043
        stack := PersistentFrame.frame h (DriverTrace.blockOffsetWord i) (Padding.paddedWord input) rho} := by
  let q := scheduledState s i
  let frame := PersistentFrame.frame h (DriverTrace.blockOffsetWord i) (Padding.paddedWord input) rho
  have hfit256 : s.executionEnv.calldata.size < 2^256 := by rw [ctx.calldata]; omega
  have heq : s.executionEnv.calldata.size = (DriverTrace.blockOffsetWord i).toNat := by
    rw [ctx.calldata, blockOffsetWord_toNat input hfit i hi]
    exact hhit
  have ghit := Table144Dispatch.gasSteps_hit s (UInt256.ofNat (messagePointer i))
    (Word.ofUInt32 h.h0) (Word.ofUInt32 h.h1) (Word.ofUInt32 h.h2)
    (Word.ofUInt32 h.h3) (Word.ofUInt32 h.h4) (DriverTrace.blockOffsetWord i)
    (Padding.paddedWord input :: rho) (by simp; omega) hrun hfit256 heq hcode hfork hnp
  have gtouch := Table144Dispatch.gasSteps_prefix s (Word.ofUInt32 h.h0) (messagePointer i)
    (hashRest h input i rho) (by simp [hashRest, driverRest]; omega) hrun
    (messagePointer_bound input hfit i hi) (messagePointer_aligned i) hcode hfork hnp
  let a : State := {s with activeWords := DenseScheduleTemplate.loadedActiveWords s (UInt256.ofNat (messagePointer i))}
  have ga : GasSteps (entryState s input i h rho)
      {a with pc := UInt256.ofNat 398, stack := frame} := by
    simpa only [entryState, PersistentFrame.frame, frame, hashRest, driverRest,
      List.cons_append, List.nil_append, List.append_assoc] using ghit.trans gtouch
  have gbody := Table144SetupSites.gasSteps_pad a (Word.ofUInt32 h.h0) (hashRest h input i rho)
    (by simp [hashRest, driverRest]; omega) hrun (scheduled_active s input i hfit hi)
    hfit256 hcode hfork hnp
  have hmem : PairTable144Pad.resultMemory a.memory
      (UInt256.ofNat a.executionEnv.calldata.size) = q.memory :=
    scheduled_memory_calldata s input i hfit hi ctx hhit
  have gb : GasSteps {a with pc := UInt256.ofNat 398, stack := frame}
      {q with pc := UInt256.ofNat 486, stack := frame} := by
    apply gbody.cast rfl
    rw [hmem]
    rfl
  have gjump := Table144PadJump.gasSteps_jump q frame
    (by simp [frame, PersistentFrame.frame]; omega) hrun hcode hfork hnp
  exact ga.trans (gb.trans gjump)

opaque gasSteps_prepare_miss (s : State) (input : ByteArray) (i : Nat)
    (h : Compression.HashState) (rho : List UInt256) (hstack : rho.length ≤ 980)
    (hfit : input.size < 2^64) (hi : i < DriverTrace.blockCount input)
    (ctx : Context s input i)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hmiss : input.size ≠ DriverTrace.blockOffset i) :
    GasSteps (entryState s input i h rho)
      {scheduledState s i with
        pc := UInt256.ofNat 1043
        stack := PersistentFrame.frame h (DriverTrace.blockOffsetWord i) (Padding.paddedWord input) rho} := by
  have hfit256 : s.executionEnv.calldata.size < 2^256 := by rw [ctx.calldata]; omega
  have hne : s.executionEnv.calldata.size ≠ (DriverTrace.blockOffsetWord i).toNat := by
    rw [ctx.calldata, blockOffsetWord_toNat input hfit i hi]
    exact hmiss
  have gmiss := Table144Dispatch.gasSteps_miss s (UInt256.ofNat (messagePointer i))
    (Word.ofUInt32 h.h0) (Word.ofUInt32 h.h1) (Word.ofUInt32 h.h2)
    (Word.ofUInt32 h.h3) (Word.ofUInt32 h.h4) (DriverTrace.blockOffsetWord i)
    (Padding.paddedWord input :: rho) (by simp; omega) hrun hfit256 hne hcode hfork hnp
  have gnormal := Table144SetupSites.gasSteps_normal s (Word.ofUInt32 h.h0)
    (messagePointer i) (hashRest h input i rho) (by simp [hashRest, driverRest]; omega) hrun
    (messagePointer_lower i) (messagePointer_bound input hfit i hi) hcode hfork hnp
  exact gmiss.trans gnormal

opaque gasSteps_prepare_schedule (s : State) (input : ByteArray) (i : Nat)
    (h : Compression.HashState) (rho : List UInt256) (hstack : rho.length ≤ 980)
    (hfit : input.size < 2^64) (hi : i < DriverTrace.blockCount input)
    (ctx : Context s input i)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (entryState s input i h rho)
      {scheduledState s i with
        pc := UInt256.ofNat 1043
        stack := PersistentFrame.frame h (DriverTrace.blockOffsetWord i) (Padding.paddedWord input) rho} := by
  by_cases hhit : input.size = DriverTrace.blockOffset i
  · exact gasSteps_prepare_hit s input i h rho hstack hfit hi ctx hcode hfork hrun hnp hhit
  · exact gasSteps_prepare_miss s input i h rho hstack hfit hi ctx hcode hfork hrun hnp hhit

opaque gasSteps_prepare (s : State) (input : ByteArray) (i : Nat)
    (h : Compression.HashState) (rho : List UInt256) (hstack : rho.length ≤ 980)
    (hfit : input.size < 2^64) (hi : i < DriverTrace.blockCount input)
    (ctx : Context s input i)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (entryState s input i h rho) (readyState s input i h rho) := by
  have gs := gasSteps_prepare_schedule s input i h rho hstack hfit hi ctx hcode hfork hrun hnp
  have gb := Table144BootstrapSite.gasSteps (scheduledState s i)
    (Word.ofUInt32 h.h0) (Word.ofUInt32 h.h1) (Word.ofUInt32 h.h2)
    (Word.ofUInt32 h.h3) (Word.ofUInt32 h.h4) (driverRest input i rho)
    (by simp [driverRest]; omega) hrun hcode hfork hnp
  exact gs.trans gb

#print axioms gasSteps_prepare_hit
#print axioms gasSteps_prepare_miss
#print axioms gasSteps_prepare
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Table144Prepare
