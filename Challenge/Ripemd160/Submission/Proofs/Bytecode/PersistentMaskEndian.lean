import Challenge.Ripemd160.Submission.Proofs.Bytecode.Pair13NormalTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Pair13Memory
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PersistentMaskEndian
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace DenseScheduleTemplate PairedMask32Cache PairedScheduleMemory

abbrev stk := Pair13Endian.stk
abbrev template := Pair13Endian.template
abbrev run_template := Pair13Endian.run_template
abbrev normalTemplate := Pair13NormalTrace.normalTemplate

theorem run_normal (s : State) (pc ret a2 a3 a4 a5 a6 a7 a8 a9 a10 off lim : UInt256)
    (rho : List UInt256) (p : Nat) (hstack : rho.length ≤ 880) (hrun : s.halt = .Running)
    (hp : 1087 ≤ p) (hbound : p + 64 < 2 ^ 256)
    (hq1 : off + UInt256.ofNat 1119 = UInt256.ofNat (p + 32))
    (hq0 : off + UInt256.ofNat 1087 = UInt256.ofNat p)
    (hlow : (MachineState.readWord s.memory 0).toNat % 2 ^ 144 < 2 ^ 32)
    (hgap : PairStoreGap.GapClear s.memory) :
    runInstrSeq normalTemplate {s with pc := pc, stack := stk ret (UInt256.ofNat 4294967295) a2 a3 a4 a5 a6 a7 a8 a9 a10 off lim rho} =
      some {s with
        pc := pcAfter pc normalTemplate
        stack := stk ret (UInt256.ofNat 4294967295) a2 a3 a4 a5 a6 a7 a8 a9 a10 off lim rho
        memory := StaggerTableLayout.resultMemory0 s.memory (StaggerScratch.dirtyWord s.memory p)
        activeWords := loadedActiveWords s (UInt256.ofNat p)} := by
  let words := StaggerScratch.dirtyWord s.memory p
  let wordsR := StaggerScratch.poolWordD (StaggerScratch.scratchMemory s.memory
    (PairedScheduleData.reversedWord (MachineState.readWord s.memory p))
    (PairedScheduleData.reversedWord (MachineState.readWord s.memory (p + 32))))
  let scratch := Shared32Scratch.fanMemory s.memory
    (PairedScheduleData.reversedWord (MachineState.readWord s.memory p))
    (PairedScheduleData.reversedWord (MachineState.readWord s.memory (p + 32)))
  have h := Pair13NormalTrace.run_normal s pc ret a2 a3 a4 a5 a6 a7 a8 a9 a10 off lim rho p
    hstack hrun hp hbound hq1 hq0 hlow
  have hclean : ∀ i, 3 ≤ i → i < 16 → (words i).toNat < 2 ^ 32 := by
    intro i hi _
    have hnot : ¬ (i = 1 ∨ i = 2) := by omega
    simp only [words, StaggerScratch.dirtyWord, if_neg hnot]
    exact PairedScheduleData.extractedWord_bound s.memory p i
  have hscratchgap : PairStoreGap.GapClear scratch :=
    Shared32Scratch.fanMemory_gapClear s.memory _ _ hgap
  have hcleanR : ∀ i, 3 ≤ i → i < 16 → (wordsR i).toNat < 2 ^ 32 := by
    intro i hi hi16
    have hnot : ¬ (i = 1 ∨ i = 2) := by omega
    show (StaggerScratch.poolWordD (StaggerScratch.scratchMemory s.memory _ _) i).toNat < _
    rw [StaggerScratch.poolWordD_eq_dirty_high s.memory p i hi16 (by omega),
      StaggerScratch.dirtyWord, if_neg hnot]
    exact PairedScheduleData.extractedWord_bound s.memory p i
  have hm : Pair13WriterRaw.writerMemory scratch wordsR
      = StaggerTableLayout.resultMemory0 scratch words := by
    rw [Pair13Memory.writerMemory_eq_resultMemoryD scratch wordsR hcleanR hscratchgap,
      Pair13Memory.resultMemoryD_congr_mod _ wordsR words
        (by simp only [Pair13WriterRaw.dualW]
            rw [show wordsR 6 = words 6 from
              StaggerScratch.poolWordD_eq_dirty_high s.memory p 6 (by decide) (by decide)])
        (fun j _ hj => by
          simp only [StaggerTableLayout.tableWords]
          exact StaggerScratch.poolWordD_eq_dirty s.memory p _
            (StaggerTableLayout.slots_lt j hj) hlow),
      Pair13Memory.resultMemoryD_eq _ _ (hclean 6 (by decide) (by decide))]
  have herase : StaggerTableLayout.resultMemory0 scratch words = StaggerTableLayout.resultMemory0 s.memory words :=
    congrArg
      (fun m => PairedScheduleMemory.writeWord m 0
        (StaggerTableLayout.dualLane (words 6)))
      (Shared32Scratch.erase_fan s.memory (StaggerTableLayout.tableWords words) _ _)
  change runInstrSeq normalTemplate {s with pc := pc, stack := stk ret (UInt256.ofNat 4294967295) a2 a3 a4 a5 a6 a7 a8 a9 a10 off lim rho} =
    some {s with pc := pcAfter pc normalTemplate, stack := stk ret (UInt256.ofNat 4294967295) a2 a3 a4 a5 a6 a7 a8 a9 a10 off lim rho, memory := StaggerTableLayout.resultMemory0 s.memory words, activeWords := loadedActiveWords s (UInt256.ofNat p)}
  rw [← herase, ← hm]
  exact h

#print axioms run_normal
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PersistentMaskEndian
