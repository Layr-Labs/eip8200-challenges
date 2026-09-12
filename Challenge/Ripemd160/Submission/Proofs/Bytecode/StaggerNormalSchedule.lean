import Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80ScratchZeroEndian
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerNormal
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerNormal
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Table80Setup
open StackRoundTrace DenseScheduleTemplate PairedMask32Cache PairedScheduleMemory
open StaggerTableMemory PairTableActive
open StaggerScratch


def normalTemplate : List Instr := ((Table80Setup.initialTemplate ++ Table80ScratchZero.endianTemplate) ++ StaggerRawNormalPool.template) ++ storesTemplate

theorem run_normal (s : State) (pc returnPC : UInt256) (p : Nat) (rest : List UInt256)
    (hstack : rest.length ≤ 896) (hrun : s.halt = .Running)
    (hp : 1024 ≤ p) (hbound : p + 64 < 2 ^ 256) :
    runInstrSeq normalTemplate (scheduleEntry s pc (UInt256.ofNat p) returnPC rest) =
      some {s with pc := pcAfter pc normalTemplate, stack := returnPC :: rest, memory := StaggerTableLayout.resultMemory s.memory (PairedScheduleData.extractedWord s.memory p), activeWords := loadedActiveWords s (UInt256.ofNat p)} := by
  let words := PairedScheduleData.extractedWord s.memory p
  let scratch := StaggerScratch.scratchMemory s.memory
    (PairedScheduleData.reversedWord (MachineState.readWord s.memory p))
    (PairedScheduleData.reversedWord (MachineState.readWord s.memory (p + 32)))
  let s1 : State := {s with activeWords := loadedActiveWords s (UInt256.ofNat p)}
  let s2 : State := {s1 with memory := scratch}
  have ha : 34 ≤ s1.activeWords.toNat := loaded_active_ge34 s p hp hbound
  have hptr : (UInt256.ofNat p).toNat = p := by
    rw [Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h1 := PairedDivMaskCache.run_cachedInitial s pc (UInt256.ofNat p) returnPC rest (by omega) hrun
  rw [← initial_eq_cached] at h1
  simp only [inputWord0, inputWord1, hptr, PairedScheduleContract.pointer_add32_toNat p hbound] at h1
  have h2 := Table80ScratchZero.run_endian s1 (pcAfter pc Table80Setup.initialTemplate)
    (MachineState.readWord s.memory p) (MachineState.readWord s.memory (p + 32)) returnPC rest (by omega) hrun ha
  have h12 := DenseScheduleTrace.runInstrSeq_append_running h1 (by exact hrun) h2
  have h3 := run_pool s2 (pcAfter (pcAfter pc Table80Setup.initialTemplate) Table80ScratchZero.endianTemplate) (returnPC :: rest) (by simp; omega) hrun ha
  have hpool : poolStack (StaggerScratch.poolWord scratch) = poolStack words := by
    simp (discharger := decide) only [poolStack, scratch, words, StaggerScratch.poolWord_eq_extracted]
  rw [show s2.memory = scratch by rfl, hpool] at h3
  have h123 := DenseScheduleTrace.runInstrSeq_append_running h12 (by exact hrun) h3
  have h4 := run_stores s2
    (pcAfter (pcAfter (pcAfter pc Table80Setup.initialTemplate) Table80ScratchZero.endianTemplate) StaggerRawNormalPool.template)
    words (returnPC :: rest) (by simp; omega) hrun ha
  have h := DenseScheduleTrace.runInstrSeq_append_running h123 (by exact hrun) h4
  have hm : StaggerTableLayout.resultMemory scratch words = StaggerTableLayout.resultMemory s.memory words :=
    StaggerScratch.erase_scratch s.memory (StaggerTableLayout.tableWords words) _ _
  simpa only [normalTemplate, DenseScheduleTrace.pcAfter_append, s2, s1, hm, words] using h
#print axioms run_normal
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerNormal
