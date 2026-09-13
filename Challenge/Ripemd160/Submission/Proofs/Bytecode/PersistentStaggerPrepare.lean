import Challenge.Ripemd160.Submission.Proofs.Bytecode.LoopCompletionControl
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

/-- The persistent frame below its top word (the resident factor constant). -/
def rest (h : Compression.HashState) (off limit : UInt256) (rho : List UInt256) : List UInt256 :=
  [UInt256.ofNat 4294967295, Paired144WordRound.compactMaskWord,
   Paired144WordRound.coefficientWord 3 0, Paired144WordRound.coefficientWord 0 3,
   Paired144WordRound.coefficientWord 0 2,
   Word.ofUInt32 h.h4, Word.ofUInt32 h.h1, Word.ofUInt32 h.h2, Word.ofUInt32 h.h3,
   Word.ofUInt32 h.h0, off, limit] ++ rho

theorem pointer_eq (input : ByteArray) (i : Nat) (hfit : CalldataFits input)
    (hi : i < DriverTrace.blockCount input) :
    StaggerPersistentEntryRaw.pointer (DriverTrace.blockOffsetWord i) = UInt256.ofNat (messagePointer i) := by
  have hb := messagePointer_bound input hfit i hi
  change UInt256.ofNat 1120 + UInt256.ofNat (DriverTrace.blockOffset i) = _
  rw [Word.ofNat_add_ofNat (by unfold messagePointer Padding.messageOffset at hb; omega)]
  rfl

def gasSteps_prepare (s : State) (input : ByteArray) (i : Nat) (h : Compression.HashState)
    (limit : UInt256) (rho : List UInt256) (hs : rho.length ≤ 880)
    (hfit : CalldataFits input) (hi : i < DriverTrace.blockCount input) (ctx : Context s input)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hr : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := LoopCompletionControl.blockPC input i, stack := frame h (DriverTrace.blockOffsetWord i) limit rho}
      {scheduledState s i with pc := UInt256.ofNat 920, stack := frame h (DriverTrace.blockOffsetWord i) limit rho} := by
  let off := DriverTrace.blockOffsetWord i
  let r := rest h off limit rho
  have hrs : r.length ≤ 896 := by simp only [r, rest, List.length_append, List.length_cons, List.length_nil]; omega
  by_cases hh : input.size = DriverTrace.blockOffset i
  · change input.size = i * 64 at hh
    have hf : s.executionEnv.calldata.size < 2^256 := by
      rw [ctx.calldata]; exact calldata_lt_uint256 input hfit
    have gp := StaggerPersistentPadPrefix.gasSteps_prefix s (frame h off limit rho)
      (by simp only [frame, List.length_append, List.length_cons, List.length_nil]; omega)
      hr hcode hfork hnp
    have ha : 37 ≤ s.activeWords.toNat := ctx.active
    have gb := StaggerSetupSites.gasSteps_pad s Paired144WordRound.factorWord r hrs hr (by omega) hf hcode hfork hnp
    have hhs : s.executionEnv.calldata.size = DriverTrace.blockOffset i := by rw [ctx.calldata]; exact hh
    rw [scheduledState_hit s i hhs]
    let qh : State :=
      {s with memory := StaggerTablePad.resultMemory s.memory (UInt256.ofNat s.executionEnv.calldata.size)}
    have gj := StaggerPadJump.gasSteps_jump qh (frame h off limit rho)
      (by simp only [frame, List.length_append, List.length_cons, List.length_nil]; omega)
      hr hcode hfork hnp
    have gb' : GasSteps {s with pc := UInt256.ofNat 4780, stack := frame h off limit rho}
        {qh with pc := UInt256.ofNat 4850, stack := frame h off limit rho} := by
      apply gb.cast rfl
      rfl
    simpa only [LoopCompletionControl.blockPC, DriverTrace.blockOffset, if_pos hh] using gp.trans (gb'.trans gj)
  · change input.size ≠ i * 64 at hh
    have hhs : ¬ s.executionEnv.calldata.size = DriverTrace.blockOffset i := by
      rw [ctx.calldata]; exact hh
    rw [scheduledState_miss s i hhs]
    have gc := StaggerPersistentEntrySites.gasSteps_call s off limit h rho (by omega) hr hcode hfork hnp
    rw [show StaggerPersistentEntryRaw.pointer off = UInt256.ofNat (messagePointer i) from pointer_eq input i hfit hi] at gc
    have gn := StaggerSetupSites.gasSteps_normal s Paired144WordRound.factorWord (messagePointer i) r (by rfl) hrs hr
      (messagePointer_lower i) (messagePointer_bound input hfit i hi) ctx.lowClear hcode hfork hnp
    simpa only [LoopCompletionControl.blockPC, DriverTrace.blockOffset, if_neg hh, off, r, rest, frame, selectedWords, List.cons_append] using gc.trans gn

#print axioms gasSteps_prepare
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PersistentStaggerPrepare
