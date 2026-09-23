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

theorem pointer_eq (input : ByteArray) (i : Nat) (hfit : CalldataFits input)
    (hi : i < DriverTrace.blockCount input) :
    StaggerPersistentEntryRaw.pointer (DriverTrace.blockOffsetWord i) = UInt256.ofNat (messagePointer i) := by
  have hb := messagePointer_bound input hfit i hi
  change UInt256.ofNat 1056 + UInt256.ofNat (DriverTrace.blockOffset i) = _
  rw [Word.ofNat_add_ofNat (by unfold messagePointer Padding.messageOffset at hb; omega)]
  rfl

/-- The pad-only block (M3b): the low block, then `JUMPI` straight to the rounds when
`n >>> 29 = 0`, otherwise the high block and the jump. Both paths leave the pad table. -/
def gasSteps_padAll (s : State) (ret : UInt256) (rest : List UInt256)
    (hmask : rest.head? = some (UInt256.ofNat 4294967295))
    (hstack : rest.length ≤ 896) (hrun : s.halt = .Running)
    (hsmall : s.executionEnv.calldata.size < 5211)
    (hactive : 35 ≤ s.activeWords.toNat)
    (hfit : s.executionEnv.calldata.size < 2 ^ 256)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 4701, stack := ret :: rest}
      {s with
        pc := UInt256.ofNat 863
        stack := ret :: rest
        memory := StaggerTablePad.padRealResult s.memory
          (UInt256.ofNat s.executionEnv.calldata.size)} := by
  have g1 := ColdOrdinarySites.gasSteps_low s ret rest hmask hstack hrun hactive hfit hcode hfork hnp
  have hz : UInt256.isTrue (StaggerPad.highZero (UInt256.ofNat s.executionEnv.calldata.size)) := by
    apply (StaggerPad.highZero_true_iff _).mpr
    rw [Word.word_toNat_ofNat, Nat.mod_eq_of_lt hfit]
    exact hsmall
  have g2 := ColdOrdinarySites.gasSteps_branch_taken
    {s with memory := (StaggerTablePad.padRealChain s.memory
      (UInt256.ofNat s.executionEnv.calldata.size))}
    _ (ret :: rest) (by simp only [List.length_cons]; omega) hrun hz hcode hfork hnp
  -- The branch is taken exactly when `n < 5211`, which is the conservative proxy for
  -- `highDirty n = 0`; that hypothesis is what `padRealChain_eq` consumes.  Above `2 ^ 29`
  -- this block runs the high stores as well and never reaches here.
  have heq : StaggerTablePad.padRealChain s.memory (UInt256.ofNat s.executionEnv.calldata.size)
      = StaggerTablePad.padRealResult s.memory (UInt256.ofNat s.executionEnv.calldata.size) :=
    StaggerTablePad.padRealChain_eq s.memory _ (StaggerPad.highZero_true_imp _ hz)
  exact (g1.trans g2).cast rfl (by rw [heq])

def gasSteps_prepare (s : State) (input : ByteArray) (i : Nat) (h : Compression.HashState)
    (limit : UInt256) (rho : List UInt256) (hs : rho.length ≤ 880)
    (tail : List UInt256) (hrho : rho = DenseScheduleTemplate.mask8 :: DenseScheduleTemplate.mask16 :: tail)
    (hfit : CalldataFits input) (hi : i < DriverTrace.blockCount input) (ctx : Context s input i)
    (hordinary : input.size = DriverTrace.blockOffset i → input.size < 5211)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hr : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := LoopCompletionControl.blockPC input i, stack := frame h (DriverTrace.blockOffsetWord i) limit rho}
      {scheduledState s i with pc := UInt256.ofNat 863, stack := frame h (DriverTrace.blockOffsetWord i) limit rho} := by
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
    have ha : 35 ≤ s.activeWords.toNat := ctx.active
    have gb := gasSteps_padAll s Paired144WordRound.factorPlusWord r (by rfl) hrs hr (by rw [ctx.calldata]; exact hordinary hh) (by omega) hf hcode hfork hnp
    have hhs : s.executionEnv.calldata.size = DriverTrace.blockOffset i := by rw [ctx.calldata]; exact hh
    rw [scheduledState_hit s i hhs]
    let qh : State :=
      {s with memory := StaggerTablePad.padRealResult s.memory (UInt256.ofNat s.executionEnv.calldata.size)}
    have gb' : GasSteps {s with pc := UInt256.ofNat 4701, stack := frame h off limit rho}
        {qh with pc := UInt256.ofNat 863, stack := frame h off limit rho} := by
      apply gb.cast rfl
      rfl
    simpa only [LoopCompletionControl.blockPC, DriverTrace.blockOffset, if_pos hh] using gp.trans gb'
  · change input.size ≠ i * 64 at hh
    have hhs : ¬ s.executionEnv.calldata.size = DriverTrace.blockOffset i := by
      rw [ctx.calldata]; exact hh
    rw [scheduledState_miss s i hhs]
    subst hrho
    have hb := messagePointer_bound input hfit i hi
    have hq0 : off + UInt256.ofNat 1056 = UInt256.ofNat (messagePointer i) := by
      change UInt256.ofNat (DriverTrace.blockOffset i) + UInt256.ofNat 1056 = _
      rw [Word.ofNat_add_ofNat (by unfold messagePointer Padding.messageOffset at hb; omega)]
      unfold messagePointer Padding.messageOffset
      congr 1
      omega
    have hq1 : off + UInt256.ofNat 1088 = UInt256.ofNat (messagePointer i + 32) := by
      change UInt256.ofNat (DriverTrace.blockOffset i) + UInt256.ofNat 1088 = _
      rw [Word.ofNat_add_ofNat (by unfold messagePointer Padding.messageOffset at hb; omega)]
      unfold messagePointer Padding.messageOffset
      congr 1
      omega
    have gn := ColdOrdinarySites.gasSteps_normal s Paired144WordRound.factorPlusWord
      (Paired144WordRound.fusedModulusWord 5 7) (Paired144WordRound.fusedModulusWord 8 5)
      (Paired144WordRound.fusedCoefficientWord 0 3) (Paired144WordRound.fusedCoefficientWord 0 2)
      (Word.ofUInt32 h.h4) (Word.ofUInt32 h.h3) (Word.ofUInt32 h.h2) (Word.ofUInt32 h.h1)
      (Word.ofUInt32 h.h0) off limit tail (messagePointer i)
      (by simp only [List.length_cons] at hs; omega) hr
      (messagePointer_lower i) hb hq1 hq0 hcode hfork hnp
    simpa only [LoopCompletionControl.blockPC, DriverTrace.blockOffset, if_neg hh, off, frame, selectedWords,
      PersistentMaskEndian.stk, Pair13Endian.stk, List.cons_append, List.nil_append] using gn

#print axioms gasSteps_padAll
#print axioms gasSteps_prepare
end Challenge.Ripemd160.Submission.Proofs.Bytecode.ColdOrdinaryPrepare
