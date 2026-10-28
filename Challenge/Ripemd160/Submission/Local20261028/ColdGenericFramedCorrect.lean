import Challenge.Ripemd160.Submission.Local20261028.AlignedLoop
import Challenge.Ripemd160.Submission.Local20261028.ColdPaddingTail
import Challenge.Ripemd160.Submission.Local20261028.ColdFramed32
import Challenge.Ripemd160.Submission.Local20261028.ColdStaggerPersistentSerializeMath
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.Control.GenericFramedCorrect
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof

private theorem env (input : ByteArray) (i : Nat) : FirstEntry.Env (Iteration.states input i) := by
  refine ⟨?_,?_,?_,?_⟩
  · rw [NormalIteration.executionEnv]; exact PadSkipEntry.entryState_code input
  · change (Iteration.states input i).executionEnv.fork = .Osaka
    rw [NormalIteration.executionEnv]; exact PadSkipEntry.entryState_fork input
  · rw [NormalIteration.halt]; exact PadSkipEntry.entryState_halt input
  · rw [NormalIteration.executionEnv]; exact PadSkipEntry.entryState_noPrecompile input

private noncomputable def gasSteps_pad (input : ByteArray) (hfit : CalldataFits input)
    (hn32 : input.size ≠ 32) (rho : List UInt256) (hs : rho.length ≤ 20) :
    GasSteps (StackTail.append (PaddingTrace.padFramed input) rho)
      (StackTail.append (PaddingTrace.entryState input) rho) := by
  by_cases hz : input.size % 64=0 ∧ input.size<256
  · rw [PaddingTrace.entryState_skip input hz]
    exact PaddingTrace.tail_guardSkip input hfit hz rho hs
  · rw [PaddingTrace.entryState_miss input hz]
    exact (PaddingTail.gasSteps_guardMiss input hfit hn32 hz rho hs).trans
      ((PaddingTail.gasSteps_setup input hfit rho hs).trans (PaddingTail.gasSteps_loop input hfit rho hs))

private theorem correct_cold (input : ByteArray) (hfit : CalldataFits input)
    (hn32 : input.size ≠ 32) (hcold : ¬ (input.size % 64=0 ∧ input.size<256))
    (rho : List UInt256) (hs : rho.length ≤ 20)
    (prefixTrace : GasSteps (initialState submissionBytecode input 0)
      (StackTail.append (PaddingTrace.padFramed input) rho)) :
    ∃ g₀ : Nat, ∀ gas : Nat, g₀ ≤ gas → Eval (initialState submissionBytecode input gas) (.returned (Challenge.Ripemd160.spec input)) := by
  let count := DriverTrace.blockCount input
  have gp := gasSteps_pad input hfit hn32 rho hs
  have ge : StackTail.append (PaddingTrace.entryState input) rho =
      Loop.entry (Iteration.states input) (Iteration.hashes input) 0 (NormalPrepare.masks rho) := by
    simp only [Loop.entry,Iteration.states,Iteration.hashes,NormalIteration.states,NormalIteration.hashes,
      Iteration.entry,PadSkipEntry.entryState,PaddingTrace.entryState_miss input hcold,StackTail.append,
      NormalPrepare.masks,PaddingTrace.padReturned,PaddingTrace.glFrame,StaggerPersistentFrame.frame,
      Nat.mul_zero,Nat.add_zero,List.cons_append,List.nil_append]
  have gb := Loop.gasSteps input hfit hcold rho (by omega)
  have e := env input count
  have go := StaggerPersistentSerialize.gasSteps (Iteration.states input count)
    (UInt256.ofNat (1056+64*(count-1))) (Word.ofUInt32 (Iteration.hashes input (count-1)).h2)
    (Iteration.hashes input count) rho (by omega) e.running e.code e.fork e.noPrecompile
  have trace := prefixTrace.trans ((gp.cast rfl ge).trans (gb.trans go))
  apply FirstComplete.eval_of_returned_trace _ _ _ trace rfl
  · exact (NormalIteration.callStack _ _ _).trans (PadSkipEntry.entryState_callStack input)
  · apply StaggerPersistentSerialize.returned_spec_of_hashArray
    apply Iteration.hash_spec input hfit count (by rfl)
    intro i _ hi
    apply hcold
    unfold DriverTrace.blockOffset at hi
    exact ⟨by omega,hi.2⟩

private theorem correct_aligned (input : ByteArray) (hfit : CalldataFits input) (n : Fin 3)
    (hsize : input.size=64*(n.val+1)) (rho : List UInt256) (hs : rho.length ≤ 20)
    (prefixTrace : GasSteps (initialState submissionBytecode input 0)
      (StackTail.append (PaddingTrace.padFramed input) rho)) :
    ∃ g₀ : Nat, ∀ gas : Nat, g₀ ≤ gas → Eval (initialState submissionBytecode input gas) (.returned (Challenge.Ripemd160.spec input)) := by
  have hn32 : input.size ≠ 32 := by omega
  have hz : input.size % 64=0 ∧ input.size<256 := by have := n.isLt; omega
  have hc : n.val+1 ≤ DriverTrace.blockCount input := by
    unfold DriverTrace.blockCount Padding.paddedLength; omega
  have hnp : ∀ i, i<n.val+1 → ¬ (input.size=DriverTrace.blockOffset i ∧ input.size<256) := by
    intro i hi hj; unfold DriverTrace.blockOffset at hj; omega
  have gp := gasSteps_pad input hfit hn32 rho hs
  have ge : StackTail.append (PaddingTrace.entryState input) rho =
      AlignedLoop.entry (Iteration.states input) (Iteration.hashes input) (n.val+1) 0 (NormalPrepare.masks rho) := by
    simp only [AlignedLoop.entry,Iteration.states,Iteration.hashes,NormalIteration.states,NormalIteration.hashes,
      Iteration.entry,PadSkipEntry.entryState,PaddingTrace.entryState_skip input hz,StackTail.append,
      NormalPrepare.masks,PaddingTrace.padSkip,PaddingTrace.initialFrame,PaddingTrace.copiedLimit,
      hsize,StaggerPersistentFrame.frame,Nat.mul_zero,Nat.add_zero,Nat.sub_zero,List.cons_append,List.nil_append]
  have gb := AlignedLoop.gasSteps_data input n hsize rho (by omega)
  have e := env input (n.val+1)
  have ha : 34 ≤ (Iteration.states input (n.val+1)).activeWords.toNat := by
    rw [Iteration.active input hfit _ hc hnp]
    have hactive := PadSkipEntry.entryState_active input hfit (by omega)
    change 35 ≤ (Iteration.entry input).activeWords.toNat at hactive
    omega
  have gc := PadGas.gasSteps (Iteration.states input (n.val+1)) (PadMemory.length n)
    (Iteration.hashes input (n.val+1)) (UInt256.ofNat (1056+64*n.val))
    (Word.ofUInt32 (Iteration.hashes input n.val).h2) rho (by omega) e.running ha
    (by rw [NormalIteration.executionEnv,PadSkipEntry.entryState_calldata,hsize]; rfl)
    e.code e.fork e.noPrecompile
  have trace := prefixTrace.trans ((gp.cast rfl ge).trans (gb.trans gc))
  apply FirstComplete.eval_of_returned_trace _ _ _ trace rfl
  · exact (NormalIteration.callStack _ _ _).trans (PadSkipEntry.entryState_callStack input)
  · exact PadContract.returned_spec _ input n hsize _ (Iteration.hash_spec input hfit _ hc hnp) _ _ _

theorem correct (input : ByteArray) (hfit : CalldataFits input) (hpositive : 0 < input.size)
    (rho : List UInt256) (hs : rho.length ≤ 20)
    (prefixTrace : GasSteps (initialState submissionBytecode input 0)
      (StackTail.append (PaddingTrace.padFramed input) rho)) :
    ∃ g₀ : Nat, ∀ gas : Nat, g₀ ≤ gas → Eval (initialState submissionBytecode input gas) (.returned (Challenge.Ripemd160.spec input)) := by
  by_cases h32 : input.size=32
  · exact Framed32.correct input h32 rho hs prefixTrace
  by_cases hz : input.size % 64=0 ∧ input.size<256
  · let n : Fin 3 := ⟨input.size/64-1,by omega⟩
    have hn : input.size=64*(n.val+1) := by dsimp [n]; omega
    exact correct_aligned input hfit n hn rho hs prefixTrace
  · exact correct_cold input hfit h32 hz rho hs prefixTrace
#print axioms correct
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.Control.GenericFramedCorrect
