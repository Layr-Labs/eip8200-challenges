import Challenge.Ripemd160.Submission.Proofs.Bytecode.PaddingTail
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Shared32Correct
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Shared32TailCorrect
open Challenge.Ripemd160 EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open Shared32Scratch Shared32Sites Paired144WordRound Shared32Start

def gasSteps_start (input : ByteArray) (h32 : input.size = 32)
    (rho : List UInt256) (hcap : rho.length ≤ 20) :
    GasSteps (StackTail.append (Execution.atPC input 342) rho)
      (atState (tableState input) 858 (frame ++ rho)) := by
  have hfit : CalldataFits input := by change input.size < 2 ^ 64; rw [h32]; decide
  let s := PaddingTrace.padCopied input
  have e : Env s := ⟨rfl, rfl, rfl, deployAddress_not_precompile⟩
  have hframe : PaddingTrace.initialFrame input ++ rho = entryFrame ++ rho := by rw [entry_frame_eq input h32]
  have hactive : s.activeWords = UInt256.ofNat 34 := copied_active input h32
  have hsize : (frame ++ rho).length ≤ 900 := by simp only [List.length_append]; change 15 + rho.length ≤ 900; omega
  have g0 := PaddingTail.gasSteps_prefix input hfit rho hcap
  have g1 : GasSteps (StackTail.append (PaddingTrace.padFramed input) rho)
      (atState s 4761 (entryFrame ++ rho)) := by
    have ga := Shared32Alignment.gasSteps s e (PaddingTrace.initialFrame input ++ rho)
      (by rw [List.length_append, PaddingTrace.initialFrame_length]; omega) h32
    simpa only [PaddingTrace.padFramed, StackTail.append, hframe, atState, s] using ga
  have g2 : GasSteps (atState s 4761 (entryFrame ++ rho)) (atState s 4762 (frame ++ rho)) := by
    exact StaggerPersistentStart.gasSteps_entry s (entryFrame ++ rho)
      (by simp only [entryFrame, StaggerPersistentFrame.frame, maskRho, List.length_append,
        List.length_cons, List.length_nil]; omega) e.run e.code e.fork e.np
  have g3 := Shared32Trace.gasSteps_guard s e (frame ++ rho) hsize h32
  have g4 := Shared32Trace.gasSteps_sparse s e factorPlusWord (UInt256.ofNat 4294967295)
    (fusedModulusWord 5 7) (fusedModulusWord 8 5) (fusedCoefficientWord 0 3)
    (fusedCoefficientWord 0 2)
    (Word.ofUInt32 StackRunBridge.initialHashState.h4) (Word.ofUInt32 StackRunBridge.initialHashState.h3)
    (Word.ofUInt32 StackRunBridge.initialHashState.h2) (Word.ofUInt32 StackRunBridge.initialHashState.h1)
    (Word.ofUInt32 StackRunBridge.initialHashState.h0) (UInt256.ofNat 32) rho (by omega) hactive (by decide)
  have g5 := Shared32Trace.gasSteps_table s e factorPlusWord
    (fusedModulusWord 5 7) (fusedModulusWord 8 5) (fusedCoefficientWord 0 3)
    (fusedCoefficientWord 0 2)
    (Word.ofUInt32 StackRunBridge.initialHashState.h4) (Word.ofUInt32 StackRunBridge.initialHashState.h3)
    (Word.ofUInt32 StackRunBridge.initialHashState.h2) (Word.ofUInt32 StackRunBridge.initialHashState.h1)
    (Word.ofUInt32 StackRunBridge.initialHashState.h0) (UInt256.ofNat 32) rho (by omega) hactive
  have hm : sparseMemory s.memory = PairedScheduleMemory.writeWord s.memory 162 highWord := by
    rw [show s.memory = copiedMemory input from copied_memory input]
    exact copiedMemory_sparse input (by omega)
  rw [hm] at g4
  have g := g0.trans (g1.trans (g2.trans (g3.trans (g4.trans g5))))
  simpa only [atState, tableState, s, copied_memory, frame, maskRho,
    StaggerPersistentFrame.frame, Pair13Endian.stk, List.append_assoc, List.cons_append, List.nil_append] using g



private theorem serialize_append (s : State) (h : Compression.HashState)
    (off limit : UInt256) (headWords tailWords : List UInt256) :
    StackTail.append (StaggerPersistentSerialize.result s h off limit headWords) tailWords =
      StaggerPersistentSerialize.result s h off limit (headWords ++ tailWords) := by
  rfl


def gasSteps_core (s : State) (e : Env s) (input : ByteArray)
    (hcal : s.executionEnv.calldata = input) (h32 : input.size = 32)
    (hactive : s.activeWords = UInt256.ofNat 35)
    (rho : List UInt256) (hcap : rho.length ≤ 20) :
    GasSteps (StackTail.append (Shared32Core.entryState s) rho)
      (StackTail.append (Shared32Core.resultState s) rho) := by
  let masks := Shared32Core.maskRho ++ rho
  have hm : masks.length ≤ 880 := by simp only [masks, Shared32Core.maskRho, List.length_append, List.length_cons, List.length_nil]; omega
  have gb := Shared32Core.gasSteps_body s e StackRunBridge.initialHashState
    (UInt256.ofNat 0) (UInt256.ofNat 32) masks (by omega)
    (by rw [hactive]; decide)
  have ge := StaggerPersistentLoopSites.gasSteps_exit s (Shared32Core.resultHash s)
    (UInt256.ofNat 0) (UInt256.ofNat 32) masks (by omega) e.run
    (by decide) (by rw [hcal, h32]; decide) (by rw [hcal, h32]; decide)
    e.code e.fork e.np
  have go := StaggerPersistentSerialize.gasSteps s (UInt256.ofNat 64) (UInt256.ofNat 32)
    (Shared32Core.resultHash s) rho (by omega) e.run e.code e.fork e.np
  have hoff : StaggerPersistentLoopRaw.nextOffset (UInt256.ofNat 0) = UInt256.ofNat 64 := by decide
  rw [hoff] at ge
  have hresult : StackTail.append (Shared32Core.resultState s) rho =
      StaggerPersistentSerialize.result s (Shared32Core.resultHash s)
        (UInt256.ofNat 64) (UInt256.ofNat 32) masks :=
    serialize_append s (Shared32Core.resultHash s) (UInt256.ofNat 64)
      (UInt256.ofNat 32) Shared32Core.maskRho rho
  rw [hresult]
  simpa only [StackTail.append, Shared32Core.entryState,
    StaggerPersistentFrame.frame, Shared32Core.maskRho, masks,
    List.append_assoc, List.cons_append, List.nil_append] using gb.trans (ge.trans go)

theorem correct (input : ByteArray) (h32 : input.size = 32)
    (rho : List UInt256) (hcap : rho.length ≤ 20)
    (entryPrefix : GasSteps (initialState submissionBytecode input 0)
      (StackTail.append (Execution.atPC input 342) rho)) :
    ∃ g₀ : Nat, ∀ gas : Nat, g₀ ≤ gas →
      Eval (initialState submissionBytecode input gas) (.returned (spec input)) := by
  let s := Shared32Start.tableState input
  have e : Shared32Sites.Env s := ⟨rfl, rfl, rfl, deployAddress_not_precompile⟩
  have gs := gasSteps_start input h32 rho hcap
  have gc := gasSteps_core s e input rfl h32 (Shared32Start.table_active input) rho hcap
  have trace := entryPrefix.trans (gs.trans gc)
  apply Shared32Correct.eval_of_initial_returned input _ trace rfl rfl
  exact Shared32Core.returned_spec s input h32 (Shared32Start.table_ready input h32)

#print axioms gasSteps_start
#print axioms gasSteps_core
#print axioms correct
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Shared32TailCorrect
