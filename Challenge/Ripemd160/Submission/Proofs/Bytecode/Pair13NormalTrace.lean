import Challenge.Ripemd160.Submission.Proofs.Bytecode.Pair13Endian
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Pair13WriterRaw
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Pair13NormalTrace
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace DenseScheduleTemplate PairedMask32Cache PairedScheduleMemory
open Pair13Endian

theorem poolWord_eq_poolWordD (memory : ByteArray) (i : Nat) :
    Pair13PoolRaw.poolWord memory (UInt256.ofNat 4294967295) i = StaggerScratch.poolWordD memory i := by
  by_cases hsmall : i ≤ 2
  · have hcases : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    simp only [Pair13PoolRaw.poolWord, StaggerScratch.poolWordD, if_pos hsmall, if_pos hcases]
  · have hcases : ¬ (i = 0 ∨ i = 1 ∨ i = 2) := by omega
    simp only [Pair13PoolRaw.poolWord, StaggerScratch.poolWordD, if_neg hsmall, if_neg hcases,
      StaggerScratch.poolWord, Word.mask32, RawExpressionAC.land_comm]
    rfl

def normalTemplate : List Instr := (template ++ Pair13PoolRaw.template) ++ Pair13WriterRaw.writerTemplate

theorem run_normal (s : State) (pc ret a2 a3 a4 a5 a6 a7 a8 a9 a10 off lim : UInt256)
    (rho : List UInt256) (p : Nat) (hstack : rho.length ≤ 880) (hrun : s.halt = .Running)
    (hp : 1120 ≤ p) (hbound : p + 64 < 2 ^ 256)
    (hq1 : off + UInt256.ofNat 1152 = UInt256.ofNat (p + 32))
    (hq0 : off + UInt256.ofNat 1120 = UInt256.ofNat p)
    (hlow : (MachineState.readWord s.memory 0).toNat < 2 ^ 32) :
    runInstrSeq normalTemplate {s with pc := pc, stack := stk ret (UInt256.ofNat 4294967295) a2 a3 a4 a5 a6 a7 a8 a9 a10 off lim rho} =
      some {s with
        pc := pcAfter pc normalTemplate
        stack := stk ret (UInt256.ofNat 4294967295) a2 a3 a4 a5 a6 a7 a8 a9 a10 off lim rho
        memory := Pair13WriterRaw.writerMemory
          (StaggerScratch.scratchMemory s.memory
            (PairedScheduleData.reversedWord (MachineState.readWord s.memory p))
            (PairedScheduleData.reversedWord (MachineState.readWord s.memory (p + 32))))
          (StaggerScratch.dirtyWord s.memory p)
        activeWords := loadedActiveWords s (UInt256.ofNat p)} := by
  let F := stk ret (UInt256.ofNat 4294967295) a2 a3 a4 a5 a6 a7 a8 a9 a10 off lim rho
  let words := StaggerScratch.dirtyWord s.memory p
  let scratch := StaggerScratch.scratchMemory s.memory
    (PairedScheduleData.reversedWord (MachineState.readWord s.memory p))
    (PairedScheduleData.reversedWord (MachineState.readWord s.memory (p + 32)))
  let s1 : State := {s with activeWords := loadedActiveWords s (UInt256.ofNat p)}
  let s2 : State := {s1 with memory := scratch}
  have ha : 37 ≤ s1.activeWords.toNat := Stagger144Active.loaded_active_ge37 s p hp hbound
  have ha2 : 37 ≤ s2.activeWords.toNat := ha
  have hF : F.length ≤ 900 := by simp [F, stk]; omega
  have h1 := run_template s pc ret (UInt256.ofNat 4294967295) a2 a3 a4 a5 a6 a7 a8 a9 a10 off lim rho p
    (by omega) hrun hp hbound hq1 hq0
  have h3 := Pair13PoolRaw.run_actual s2 (pcAfter pc template) (UInt256.ofNat 4294967295) F hF hrun (by omega)
  have hpool : Pair13PoolRaw.poolStack (Pair13PoolRaw.poolWord scratch (UInt256.ofNat 4294967295)) F = Pair13PoolRaw.poolStack words F := by
    have hD : ∀ i, i < 16 → Pair13PoolRaw.poolWord scratch (UInt256.ofNat 4294967295) i = words i := by
      intro i hi
      rw [poolWord_eq_poolWordD]
      exact StaggerScratch.poolWordD_eq_dirty s.memory p i hi hlow
    simp (discharger := decide) only [Pair13PoolRaw.poolStack, hD]
  rw [show s2.memory = scratch by rfl, hpool] at h3
  have h13 := DenseScheduleTrace.runInstrSeq_append_running h1 (by exact hrun) h3
  have h4 := Pair13WriterRaw.run_writer s2 (pcAfter (pcAfter pc template) Pair13PoolRaw.template)
    words F hF hrun (by omega)
  have h := DenseScheduleTrace.runInstrSeq_append_running h13 (by exact hrun) h4
  simpa only [normalTemplate, DenseScheduleTrace.pcAfter_append, s2, s1, scratch, words] using h

theorem exact_bytes : assembleBytes normalTemplate = [97, 4, 128, 140, 1, 81, 128, 96, 8, 28, 129, 24, 143, 22, 97, 1, 1, 2, 24, 143, 129, 128, 96, 16, 28, 24, 22, 98, 1, 0, 1, 2, 24, 96, 60, 82, 97, 4, 96, 140, 1, 81, 128, 96, 8, 28, 129, 24, 143, 22, 97, 1, 1, 2, 24, 143, 129, 128, 96, 16, 28, 24, 22, 98, 1, 0, 1, 2, 24, 96, 28, 82, 129, 96, 24, 81, 129, 22, 95, 81, 96, 48, 81, 131, 22, 131, 96, 20, 81, 22, 96, 44, 81, 133, 22, 114, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 96, 56, 81, 135, 22, 96, 52, 81, 136, 22, 136, 96, 40, 81, 22, 96, 28, 81, 138, 22, 138, 96, 60, 81, 22, 96, 8, 81, 96, 4, 81, 96, 32, 81, 142, 22, 96, 36, 81, 143, 22, 143, 96, 16, 81, 22, 159, 96, 12, 81, 22, 140, 97, 4, 56, 82, 136, 97, 4, 38, 82, 143, 139, 2, 97, 4, 20, 82, 133, 139, 2, 97, 3, 240, 82, 128, 139, 2, 97, 3, 204, 82, 130, 139, 2, 97, 3, 168, 82, 129, 97, 3, 132, 82, 128, 97, 3, 114, 82, 139, 97, 3, 96, 82, 97, 3, 78, 82, 128, 138, 2, 97, 3, 60, 82, 130, 97, 3, 24, 82, 130, 97, 3, 6, 82, 97, 2, 244, 82, 128, 97, 2, 226, 82, 138, 137, 2, 97, 2, 208, 82, 141, 97, 2, 172, 82, 135, 97, 2, 154, 82, 131, 97, 2, 136, 82, 133, 97, 2, 118, 82, 131, 97, 2, 100, 82, 137, 137, 2, 97, 2, 82, 82, 97, 2, 46, 82, 128, 97, 2, 28, 82, 139, 97, 2, 10, 82, 128, 97, 1, 248, 82, 137, 97, 1, 230, 82, 97, 1, 212, 82, 137, 135, 2, 97, 1, 194, 82, 139, 97, 1, 158, 82, 140, 135, 2, 97, 1, 140, 82, 128, 97, 1, 104, 82, 97, 1, 86, 82, 130, 134, 2, 97, 1, 68, 82, 129, 97, 1, 32, 82, 97, 1, 14, 82, 132, 2, 96, 252, 82, 96, 216, 82, 130, 2, 96, 198, 82, 2, 96, 162, 82, 96, 126, 82, 96, 108, 82, 96, 90, 82, 130, 96, 72, 82, 128, 96, 54, 82, 96, 36, 82, 144, 96, 18, 82, 95, 82] := by decide
theorem end_pc : pcAfter (UInt256.ofNat 487) normalTemplate = UInt256.ofNat 890 := by decide
#print axioms run_normal
#print axioms exact_bytes
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Pair13NormalTrace
