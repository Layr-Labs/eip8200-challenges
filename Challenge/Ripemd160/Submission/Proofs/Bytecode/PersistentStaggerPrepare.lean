import Challenge.Ripemd160.Submission.Proofs.Bytecode.PersistentStaggerTable
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentEntrySites
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerSetupSites
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPadJump
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PersistentStaggerPrepare
open Challenge.Ripemd160 EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open PersistentStaggerTable StaggerPersistentFrame

def rest (h : Compression.HashState) (off limit : UInt256) (rho : List UInt256) : List UInt256 :=
  [Word.ofUInt32 h.h1, Word.ofUInt32 h.h2, Word.ofUInt32 h.h3, Word.ofUInt32 h.h4, off, limit] ++ rho

theorem pointer_eq (input : ByteArray) (i : Nat) (hfit : CalldataFits input)
    (hi : i < DriverTrace.blockCount input) :
    StaggerPersistentEntryRaw.pointer (DriverTrace.blockOffsetWord i) = UInt256.ofNat (messagePointer i) := by
  have hb := messagePointer_bound input hfit i hi
  change UInt256.ofNat 1152 + UInt256.ofNat (DriverTrace.blockOffset i) = _
  rw [Word.ofNat_add_ofNat (by unfold messagePointer Padding.messageOffset at hb; omega)]
  rfl

def gasSteps_prepare (s : State) (input : ByteArray) (i : Nat) (h : Compression.HashState)
    (limit : UInt256) (rho : List UInt256) (hs : rho.length ≤ 890)
    (hfit : CalldataFits input) (hi : i < DriverTrace.blockCount input) (ctx : Context s input)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hr : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 466, stack := frame h (DriverTrace.blockOffsetWord i) limit rho}
      {scheduledState s i with pc := UInt256.ofNat 969, stack := frame h (DriverTrace.blockOffsetWord i) limit rho} := by
  let off := DriverTrace.blockOffsetWord i
  let q := scheduledState s i
  let r := rest h off limit rho
  have hrs : r.length ≤ 896 := by simp only [r, rest, List.length_append, List.length_cons, List.length_nil]; omega
  have hf : s.executionEnv.calldata.size < 2^256 := by
    rw [ctx.calldata]; exact calldata_lt_uint256 input hfit
  have gc := StaggerPersistentEntrySites.gasSteps_call s off limit h rho (by omega) hr hcode hfork hnp
  rw [show StaggerPersistentEntryRaw.pointer off = UInt256.ofNat (messagePointer i) from pointer_eq input i hfit hi] at gc
  by_cases hh : input.size = DriverTrace.blockOffset i
  · have he : s.executionEnv.calldata.size = off.toNat := by
      rw [ctx.calldata, blockOffsetWord_toNat input hfit i hi]; exact hh
    have gd := StaggerPersistentEntrySites.gasSteps_hit s (UInt256.ofNat (messagePointer i)) off limit h rho
      (by omega) hr hf he hcode hfork hnp
    have gp := StaggerPersistentPadPrefix.gasSteps_prefix s (Word.ofUInt32 h.h0) (messagePointer i) r
      (by omega) hr hcode hfork hnp
    have ha : 38 ≤ s.activeWords.toNat := by
      have hq := scheduled_active s input i hfit hi
      change 38 ≤ (DenseScheduleTemplate.loadedActiveWords s (UInt256.ofNat (messagePointer i))).toNat at hq
      rw [scheduled_active_eq s input i hfit hi ctx] at hq
      exact hq
    have gb := StaggerSetupSites.gasSteps_pad s (Word.ofUInt32 h.h0) r hrs hr (by omega) hf hcode hfork hnp
    have hm := scheduled_memory_calldata s input i hfit hi ctx hh
    have gj := StaggerPadJump.gasSteps_jump q (frame h off limit rho)
      (by simp only [frame, List.length_append, List.length_cons, List.length_nil]; omega)
      hr hcode hfork hnp
    have gb' : GasSteps {s with pc := UInt256.ofNat 388, stack := frame h off limit rho}
        {q with pc := UInt256.ofNat 461, stack := frame h off limit rho} := by
      apply gb.cast rfl
      dsimp only [q, scheduledState]
      rw [scheduled_active_eq s input i hfit hi ctx]
      rw [hm]
      rfl
    exact gc.trans (gd.trans (gp.trans (gb'.trans gj)))
  · have he : s.executionEnv.calldata.size ≠ off.toNat := by
      rw [ctx.calldata, blockOffsetWord_toNat input hfit i hi]; exact hh
    have gd := StaggerPersistentEntrySites.gasSteps_miss s (UInt256.ofNat (messagePointer i)) off limit h rho
      (by omega) hr hf he hcode hfork hnp
    have gn := StaggerSetupSites.gasSteps_normal s (Word.ofUInt32 h.h0) (messagePointer i) r hrs hr
      (messagePointer_lower i) (messagePointer_bound input hfit i hi) hcode hfork hnp
    exact gc.trans (gd.trans gn)

#print axioms gasSteps_prepare
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PersistentStaggerPrepare
