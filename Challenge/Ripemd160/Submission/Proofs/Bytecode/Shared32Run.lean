import Challenge.Ripemd160.Submission.Proofs.Bytecode.Shared32SparseRun

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Shared32Run
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace DenseScheduleTemplate PairedScheduleMemory Pair13Endian
open Shared32Scratch

def template : List Instr :=
  (Shared32Lower.lowerTemplate ++ Pair13PoolRaw.template) ++ Pair13WriterRaw.writerTemplate

theorem run_table (s : State) (pc ret a2 a3 a4 a5 a6 a7 a8 a9 a10 lim : UInt256)
    (rho : List UInt256) (hstack : rho.length ≤ 880) (hrun : s.halt = .Running)
    (hactive : s.activeWords = UInt256.ofNat 36)
    (hlow : (MachineState.readWord s.memory 0).toNat < 2 ^ 32)
    (hgap : PairStoreGap.GapClear s.memory) :
    runInstrSeq template
      {s with
        pc := pc
        stack := stk ret (UInt256.ofNat 4294967295) a2 a3 a4 a5 a6 a7 a8 a9 a10
          (UInt256.ofNat 0) lim rho
        memory := writeWord s.memory 60 highWord} =
      some {s with
        pc := pcAfter pc template
        stack := stk ret (UInt256.ofNat 4294967295) a2 a3 a4 a5 a6 a7 a8 a9 a10
          (UInt256.ofNat 0) lim rho
        memory := StaggerTableLayout.resultMemory s.memory (Shared32Table.words s.memory)} := by
  let F := stk ret (UInt256.ofNat 4294967295) a2 a3 a4 a5 a6 a7 a8 a9 a10
    (UInt256.ofNat 0) lim rho
  let words := Shared32Table.words s.memory
  let scratch := StaggerScratch.scratchMemory s.memory
    (PairedScheduleData.reversedWord (MachineState.readWord s.memory 1120)) highWord
  let s1 : State := {s with memory := writeWord s.memory 60 highWord}
  let s2 : State := {s with memory := scratch}
  have ha : 35 ≤ s2.activeWords.toNat := by change 35 ≤ s.activeWords.toNat; rw [hactive]; decide
  have hF : F.length ≤ 900 := by simp only [F, stk, List.length_cons]; omega
  have h1 := Shared32Lower.run_lower s1 pc ret (UInt256.ofNat 4294967295)
    a2 a3 a4 a5 a6 a7 a8 a9 a10 lim rho hstack hrun hactive
  have hread : MachineState.readWord s1.memory 1120 = MachineState.readWord s.memory 1120 :=
    read_writeWord_disjoint _ _ _ _ (Or.inr (by decide))
  rw [hread] at h1
  have h2 := Pair13PoolRaw.run_actual s2 (pcAfter pc Shared32Lower.lowerTemplate)
    (UInt256.ofNat 4294967295) F hF hrun ha
  have hpool : Pair13PoolRaw.poolStack
      (Pair13PoolRaw.poolWord scratch (UInt256.ofNat 4294967295)) F =
      Pair13PoolRaw.poolStack words F := by
    have hD : ∀ i, i < 16 → Pair13PoolRaw.poolWord scratch (UInt256.ofNat 4294967295) i = words i := by
      intro i hi
      rw [Pair13NormalTrace.poolWord_eq_poolWordD]
      exact Shared32Table.pool_words s.memory i hi hlow
    simp (discharger := decide) only [Pair13PoolRaw.poolStack, hD]
  rw [show s2.memory = scratch by rfl, hpool] at h2
  have h12 := DenseScheduleTrace.runInstrSeq_append_running h1 (by exact hrun) h2
  have h3 := Pair13WriterRaw.run_writer s2
    (pcAfter (pcAfter pc Shared32Lower.lowerTemplate) Pair13PoolRaw.template)
    words F hF hrun ha
  have h := DenseScheduleTrace.runInstrSeq_append_running h12 (by exact hrun) h3
  have hmem : Pair13WriterRaw.writerMemory scratch words =
      StaggerTableLayout.resultMemory s.memory words := Shared32Table.writer_memory s.memory hgap
  rw [show s2.memory = scratch by rfl, hmem] at h
  simpa only [template, DenseScheduleTrace.pcAfter_append, s2, s1, scratch, words] using h

theorem end_pc : pcAfter (UInt256.ofNat 532) template = UInt256.ofNat 899 := by decide

#print axioms run_table
#print axioms end_pc
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Shared32Run
