import Challenge.Ripemd160.Submission.Proofs.Bytecode.Shared32SparseRun
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Shared32Table
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Pair13NormalTrace

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
    (hactive : s.activeWords = UInt256.ofNat 35)
    (hlow : (MachineState.readWord s.memory 0).toNat % 2 ^ 144 < 2 ^ 32)
    (hgap : PairStoreGap.GapClear s.memory) :
    runInstrSeq template
      {s with
        pc := pc
        stack := stk ret (UInt256.ofNat 4294967295) a2 a3 a4 a5 a6 a7 a8 a9 a10
          (UInt256.ofNat 0) lim rho
        memory := writeWord s.memory 96 highWord} =
      some {s with
        pc := pcAfter pc template
        stack := stk ret (UInt256.ofNat 4294967295) a2 a3 a4 a5 a6 a7 a8 a9 a10
          (UInt256.ofNat 0) lim rho
        memory := StaggerTableLayout.resultMemory0 s.memory (Shared32Table.words s.memory)} := by
  let rest : List UInt256 :=
    a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: a8 :: a9 :: a10 :: UInt256.ofNat 0 :: lim :: mask8 :: mask16 :: rho
  let F := stk ret (UInt256.ofNat 4294967295) a2 a3 a4 a5 a6 a7 a8 a9 a10
    (UInt256.ofNat 0) lim rho
  let words := Shared32Table.words s.memory
  let scratch := Pair13Endian.scratch3 s.memory
    (PairedScheduleData.reversedWord (MachineState.readWord s.memory 1087)) highWord
  let s1 : State := {s with memory := writeWord s.memory 96 highWord}
  let s2 : State := {s with memory := scratch}
  let s3 : State := {s with memory := Pair13PoolRaw.copied scratch}
  have ha : 35 ≤ s2.activeWords.toNat := by change 35 ≤ s.activeWords.toNat; rw [hactive]; decide
  have ha3 : 35 ≤ s3.activeWords.toNat := by change 35 ≤ s.activeWords.toNat; rw [hactive]; decide
  have hF : F.length ≤ 900 := by simp only [F, stk, List.length_cons]; omega
  have hrest : rest.length ≤ 898 := by simp only [rest, List.length_cons]; omega
  have h1 := Shared32Lower.run_lower s1 pc ret (UInt256.ofNat 4294967295)
    a2 a3 a4 a5 a6 a7 a8 a9 a10 lim rho hstack hrun hactive
  have hread : MachineState.readWord s1.memory 1087 = MachineState.readWord s.memory 1087 :=
    read_writeWord_disjoint _ _ _ _ (Or.inr (by decide))
  rw [hread] at h1
  have h2 := Pair13PoolRaw.run_actual s2 (pcAfter pc Shared32Lower.lowerTemplate) F hF hrun ha
  have hclean : ∀ i, 3 ≤ i → i < 16 → (Shared32Table.wordsRaw s.memory i).toNat < 2 ^ 32 :=
    fun i h0 h1 => Shared32Table.wordsRaw_clean s.memory i h0 h1
  have hpool : Pair13PoolRaw.poolStack
      (Pair13PoolRaw.poolWord (Pair13PoolRaw.copied scratch)) F =
      Pair13PoolRaw.poolStack (Pair13WriterRaw.dualW (Shared32Table.wordsRaw s.memory)) F := by
    have hD : ∀ i, i < 16 → Pair13PoolRaw.poolWord (Pair13PoolRaw.copied scratch) i =
        Pair13WriterRaw.dualW (Shared32Table.wordsRaw s.memory) i := by
      intro i hi
      have h := Shared32Scratch.fan_poolWord s.memory
        (PairedScheduleData.reversedWord (MachineState.readWord s.memory 1087)) highWord hlow i hi
      simp only [Shared32Scratch.dualOf, Shared32Table.pool_wordsRaw s.memory i] at h
      show Pair13PoolRaw.poolWord (Shared32Scratch.fanMemory s.memory
          (PairedScheduleData.reversedWord (MachineState.readWord s.memory 1087)) highWord) i =
        Pair13WriterRaw.dualW (Shared32Table.wordsRaw s.memory) i
      rw [Pair13WriterRaw.dualW]
      exact h
    simp (discharger := decide) only [Pair13PoolRaw.poolStack, hD]
  rw [show s2.memory = scratch by rfl, hpool] at h2
  have h12 := DenseScheduleTrace.runInstrSeq_append_running h1 (by exact hrun) h2
  have h3 := Pair13WriterRaw.run_writer s3
    (pcAfter (pcAfter pc Shared32Lower.lowerTemplate) Pair13PoolRaw.template)
    ret (Shared32Table.wordsRaw s.memory) rest hrest hrun ha3 hclean
  have h := DenseScheduleTrace.runInstrSeq_append_running h12 (by exact hrun) h3
  have hmem : Pair13WriterRaw.writerMemory (Pair13PoolRaw.copied scratch)
      (Shared32Table.wordsRaw s.memory) =
      StaggerTableLayout.resultMemory0 s.memory words :=
    Shared32Table.writer_memory s.memory hgap hlow
  simpa only [template, DenseScheduleTrace.pcAfter_append, s3, s2, s1, hmem, scratch, words,
    rest, stk] using h

theorem end_pc : pcAfter (UInt256.ofNat 503) template = UInt256.ofNat 868 := by decide

#print axioms run_table
#print axioms end_pc
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Shared32Run
