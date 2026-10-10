import Challenge.Ripemd160.Submission.Proofs.Bytecode.LoopCompletionControl
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PersistentStaggerTable
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentEntrySites
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ColdOrdinarySites
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentPadPrefix
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.ColdOrdinaryPrepare
open Challenge.Ripemd160 EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open PersistentStaggerTable StaggerPersistentFrame

/-- The persistent frame below its top word (the resident factor constant). -/
def rest (h : Compression.HashState) (off limit : UInt256) (rho : List UInt256) : List UInt256 :=
  [UInt256.ofNat 4294967295, Paired144WordRound.fusedModulusWord 5 7,
   Paired144WordRound.fusedModulusWord 8 5, Paired144WordRound.fusedCoefficientWord 0 3,
   Paired144WordRound.fusedCoefficientWord 0 2,
   Word.ofUInt32 h.h4, Word.ofUInt32 h.h3, Word.ofUInt32 h.h2, Word.ofUInt32 h.h1,
   Word.ofUInt32 h.h0, off, limit] ++ rho

/-- The pad-only block: the low block (copying zeros from past the calldata at the advanced
offset the exit left on top), then `SWAP11` parks the CODESIZE exit sentinel in slot 12 and `JUMP` goes
straight to the rounds.  Only the fast entry (lengths below 256) reaches it, so the high length
words are zero and the table is complete. -/
def gasSteps_padAll (s : State) (h : Compression.HashState) (off limit : UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 880) (hrun : s.halt = .Running)
    (hsmall : s.executionEnv.calldata.size < 5248)
    (hactive : 35 ≤ s.activeWords.toNat)
    (hfit : s.executionEnv.calldata.size < 2 ^ 256)
    (hoff : s.executionEnv.calldata.size ≤ off.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 130, stack := exitFrame h off limit rho}
      {s with
        pc := UInt256.ofNat 808
        stack := frame h StaggerPersistentLoopRaw.padMark limit rho
        memory := StaggerTablePad.padRealResult s.memory
          (UInt256.ofNat s.executionEnv.calldata.size)} := by
  have g1 := ColdOrdinarySites.gasSteps_low s off (rest h Paired144WordRound.factorPlusWord limit rho)
    (by rfl) (by simp only [rest, List.length_append, List.length_cons, List.length_nil]; omega)
    hrun hactive hfit hoff hcode hfork hnp
  have hz : UInt256.isTrue (StaggerPad.highZero (UInt256.ofNat s.executionEnv.calldata.size)) := by
    apply (StaggerPad.highZero_true_iff _).mpr
    rw [Word.word_toNat_ofNat, Nat.mod_eq_of_lt hfit]
    exact hsmall
  have g2 := ColdOrdinarySites.gasSteps_branch_taken
    {s with memory := (StaggerTablePad.padRealChain s.memory
      (UInt256.ofNat s.executionEnv.calldata.size))}
    (UInt256.ofNat 5248) (UInt256.ofNat 4294967295)
    (Paired144WordRound.fusedModulusWord 5 7) (Paired144WordRound.fusedModulusWord 8 5)
    (Paired144WordRound.fusedCoefficientWord 0 3) (Paired144WordRound.fusedCoefficientWord 0 2)
    (Word.ofUInt32 h.h4) (Word.ofUInt32 h.h3) (Word.ofUInt32 h.h2) (Word.ofUInt32 h.h1)
    (Word.ofUInt32 h.h0) Paired144WordRound.factorPlusWord (limit :: rho) (by simp only [List.length_cons]; omega)
    hrun hcode hfork hnp
  -- `n < 5248` bounds `highDirty n = 0`, which is what `padRealChain_eq` consumes.
  have heq : StaggerTablePad.padRealChain s.memory (UInt256.ofNat s.executionEnv.calldata.size)
      = StaggerTablePad.padRealResult s.memory (UInt256.ofNat s.executionEnv.calldata.size) :=
    StaggerTablePad.padRealChain_eq s.memory _ (StaggerPad.highZero_true_imp _ hz)
  exact (g1.trans g2).cast rfl (by rw [heq]; rfl)

def gasSteps_prepare (s : State) (input : ByteArray) (i : Nat) (h : Compression.HashState)
    (limit : UInt256) (rho : List UInt256) (hs : rho.length ≤ 880)
    (tail : List UInt256) (hrho : rho = DenseScheduleTemplate.mask8 :: DenseScheduleTemplate.mask16 :: tail)
    (hfit : CalldataFits input) (hi : i < DriverTrace.blockCount input) (ctx : Context s input i)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hr : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with
        pc := LoopCompletionControl.blockPC input i
        stack := StaggerPersistentLoopRaw.entryStack input i h (DriverTrace.messageOffsetWord i) limit rho}
      {scheduledState s i with
        pc := UInt256.ofNat 808
        stack := frame h (StaggerPersistentLoopRaw.blockMark input i (DriverTrace.messageOffsetWord i)) limit rho} := by
  let off := DriverTrace.messageOffsetWord i
  let r := rest h off limit rho
  have hrs : r.length ≤ 896 := by simp only [r, rest, List.length_append, List.length_cons, List.length_nil]; omega
  by_cases hh : input.size = DriverTrace.blockOffset i ∧ input.size < 256
  · change input.size = i * 64 ∧ input.size < 256 at hh
    have hf : s.executionEnv.calldata.size < 2^256 := by
      rw [ctx.calldata]; exact calldata_lt_uint256 input hfit
    have gp := StaggerPersistentPadPrefix.gasSteps_prefix s (exitFrame h off limit rho)
      (by simp only [exitFrame, List.length_append, List.length_cons, List.length_nil]; omega)
      hr hcode hfork hnp
    have ha : 35 ≤ s.activeWords.toNat := ctx.active
    have hoff : s.executionEnv.calldata.size ≤ off.toNat := by
      have hb := messagePointer_bound input hfit i hi
      have ho : off.toNat = 1056 + i * 64 := by
        change (1056 + i * 64) % 2^256 = 1056 + i * 64
        exact Nat.mod_eq_of_lt (by unfold messagePointer Padding.messageOffset DriverTrace.blockOffset at hb; omega)
      rw [ho, ctx.calldata]; omega
    have gb := gasSteps_padAll s h off limit rho hs hr (by rw [ctx.calldata]; omega) (by omega) hf hoff hcode hfork hnp
    have hhs : s.executionEnv.calldata.size = DriverTrace.blockOffset i ∧
        s.executionEnv.calldata.size < 256 := by rw [ctx.calldata]; exact hh
    rw [scheduledState_hit s i hhs]
    let qh : State :=
      {s with memory := StaggerTablePad.padRealResult s.memory (UInt256.ofNat s.executionEnv.calldata.size)}
    have gb' : GasSteps {s with pc := UInt256.ofNat 130, stack := exitFrame h off limit rho}
        {qh with pc := UInt256.ofNat 808, stack := frame h StaggerPersistentLoopRaw.padMark limit rho} := by
      apply gb.cast rfl
      rfl
    simpa only [LoopCompletionControl.blockPC, DriverTrace.blockOffset, if_pos hh,
      StaggerPersistentLoopRaw.entryStack, StaggerPersistentLoopRaw.blockMark] using gp.trans gb'
  · change ¬ (input.size = i * 64 ∧ input.size < 256) at hh
    have hhs : ¬ (s.executionEnv.calldata.size = DriverTrace.blockOffset i ∧
        s.executionEnv.calldata.size < 256) := by
      rw [ctx.calldata]; exact hh
    rw [scheduledState_miss s i hhs]
    subst hrho
    have hb := messagePointer_bound input hfit i hi
    have hq0 : off = UInt256.ofNat (messagePointer i) := rfl
    have hq1 : off + UInt256.ofNat 32 = UInt256.ofNat (messagePointer i + 32) := by
      change UInt256.ofNat (messagePointer i) + UInt256.ofNat 32 = _
      rw [Word.ofNat_add_ofNat (by omega)]
    have gn := ColdOrdinarySites.gasSteps_normal s Paired144WordRound.factorPlusWord
      (Paired144WordRound.fusedModulusWord 5 7) (Paired144WordRound.fusedModulusWord 8 5)
      (Paired144WordRound.fusedCoefficientWord 0 3) (Paired144WordRound.fusedCoefficientWord 0 2)
      (Word.ofUInt32 h.h4) (Word.ofUInt32 h.h3) (Word.ofUInt32 h.h2) (Word.ofUInt32 h.h1)
      (Word.ofUInt32 h.h0) off limit tail (messagePointer i)
      (by simp only [List.length_cons] at hs; omega) hr
      (messagePointer_lower i) hb hq1 hq0 hcode hfork hnp
    simpa only [LoopCompletionControl.blockPC, DriverTrace.blockOffset, if_neg hh, off, frame, selectedWords,
      StaggerPersistentLoopRaw.entryStack, StaggerPersistentLoopRaw.blockMark,
      PersistentMaskEndian.stk, Pair13Endian.stk, List.cons_append, List.nil_append] using gn

#print axioms gasSteps_padAll
#print axioms gasSteps_prepare
end Challenge.Ripemd160.Submission.Proofs.Bytecode.ColdOrdinaryPrepare
