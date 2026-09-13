import Challenge.Ripemd160.Submission.Proofs.Bytecode.Stagger144Active
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DeferredNormalEndian
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DeferredNormalInitial
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DeferredNormalInterleaved
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerNormal
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.DeferredNormalSchedule
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Table80Setup
open StackRoundTrace DenseScheduleTemplate PairedMask32Cache PairedScheduleMemory
open StaggerTableMemory PairTableActive
open StaggerScratch StaggerNormal


def normalTemplate : List Instr := (DeferredNormalInterleaved.template ++ StaggerRawNormalPool.template) ++ StaggerNormal.storesTemplate

theorem run_normal (s : State) (pc returnPC : UInt256) (p : Nat) (rest : List UInt256)
    (hstack : rest.length ≤ 896) (hrun : s.halt = .Running)
    (hp : 1120 ≤ p) (hbound : p + 64 < 2 ^ 256)
    (hlow : (MachineState.readWord s.memory 0).toNat < 2 ^ 32)
    (hoff : rest[9]? = some (UInt256.ofNat (p - 1120))) :
    runInstrSeq normalTemplate {s with pc := pc, stack := UInt256.ofNat p :: mask8 :: mask16 :: returnPC :: maskWord :: rest} =
      some {s with pc := pcAfter pc normalTemplate, stack := returnPC :: maskWord :: rest, memory := StaggerTableLayout.resultMemory s.memory (StaggerScratch.dirtyWord s.memory p), activeWords := loadedActiveWords s (UInt256.ofNat p)} := by
  let words := StaggerScratch.dirtyWord s.memory p
  let scratch := StaggerScratch.scratchMemory s.memory
    (PairedScheduleData.reversedWord (MachineState.readWord s.memory p))
    (PairedScheduleData.reversedWord (MachineState.readWord s.memory (p + 32)))
  let s1 : State := {s with activeWords := loadedActiveWords s (UInt256.ofNat p)}
  let s2 : State := {s1 with memory := scratch}
  have ha : 37 ≤ s1.activeWords.toNat := Stagger144Active.loaded_active_ge37 s p hp hbound
  have ha2 : 37 ≤ s2.activeWords.toNat := ha
  have hptr : (UInt256.ofNat p).toNat = p := by
    rw [Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h12 := DeferredNormalInterleaved.run_template s pc returnPC p rest hstack hrun hp hbound hoff
  have h3 := StaggerNormal.run_pool s2 (pcAfter pc DeferredNormalInterleaved.template) (returnPC :: maskWord :: rest) (by simp; omega) hrun (by omega)
  have hpool : StaggerNormal.poolStack (StaggerScratch.poolWordD scratch) = StaggerNormal.poolStack words := by
    have hD : ∀ i, i < 16 → StaggerScratch.poolWordD scratch i = words i :=
      fun i hi => StaggerScratch.poolWordD_eq_dirty s.memory p i hi hlow
    simp (discharger := decide) only [StaggerNormal.poolStack, hD]
  rw [show s2.memory = scratch by rfl, hpool] at h3
  have h123 := DenseScheduleTrace.runInstrSeq_append_running h12 (by exact hrun) h3
  have h4 := StaggerNormal.run_stores s2
    (pcAfter (pcAfter pc DeferredNormalInterleaved.template) StaggerRawNormalPool.template)
    words (returnPC :: maskWord :: rest) (by simp; omega) hrun (by omega)
  have h := DenseScheduleTrace.runInstrSeq_append_running h123 (by exact hrun) h4
  have hm : StaggerTableLayout.resultMemory scratch words = StaggerTableLayout.resultMemory s.memory words :=
    StaggerScratch.erase_scratch s.memory (StaggerTableLayout.tableWords words) _ _
  simpa only [normalTemplate, DenseScheduleTrace.pcAfter_append, s2, s1, hm, words] using h
#print axioms run_normal
end Challenge.Ripemd160.Submission.Proofs.Bytecode.DeferredNormalSchedule
