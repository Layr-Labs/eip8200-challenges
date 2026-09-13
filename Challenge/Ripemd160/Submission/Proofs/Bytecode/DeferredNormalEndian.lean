import Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80EndianSetup
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80ScratchZeroEndian

set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.DeferredNormalEndian

open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace DenseScheduleTemplate PairedMask32Cache PairedScheduleMemory
open PairTableMemory PairTableActive Table80ScratchZero

def reverseTemplate : List Instr := endianStage8 ++ endianStage16

private theorem run_reverse (s : State) (pc value : UInt256) (rest : List UInt256)
    (hstack : rest.length < 1020) (hrun : s.halt = .Running) :
    runInstrSeq reverseTemplate {s with pc := pc, stack := value :: rest} =
      some {{s with pc := pcAfter pc reverseTemplate} with
        stack := PairedScheduleData.reversedWord value :: rest} := by
  have h1 := DenseScheduleTrace.runInstrSeq_endianStage s pc value 8 mask8 rest
    hstack (Or.inl ⟨rfl, rfl⟩) hrun
  dsimp only [DenseScheduleTrace.stageState] at h1
  have h2 := DenseScheduleTrace.runInstrSeq_endianStage s
    (pcAfter pc endianStage8) (packedStage value 8 mask8) 16 mask16 rest
    hstack (Or.inr ⟨rfl, rfl⟩) hrun
  dsimp only [DenseScheduleTrace.stageState] at h2
  have h := DenseScheduleTrace.runInstrSeq_append_running h1 (by exact hrun) h2
  rw [← PairedScheduleContract.packedWord_eq_reversedWord]
  simpa only [reverseTemplate, DenseScheduleTrace.pcAfter_append, packedWord,
    endianStage8, endianStage16] using h

def upperReverse : List Instr := reverseTemplate
def lowerReverse : List Instr := reverseTemplate
def upperStore : List Instr := PairedSchedulePrimitives.storeTemplate 60
def lowerStore : List Instr := PairedSchedulePrimitives.storeTemplate 28
def duplicateMask : List Instr := [.op (.Dup ⟨1, by decide⟩)]
def template : List Instr :=
  (((upperReverse ++ upperStore) ++ lowerReverse) ++ lowerStore) ++ duplicateMask

private theorem run_duplicateMask (s : State) (pc returnPC : UInt256)
    (rest : List UInt256) (hstack : rest.length ≤ 996) (hrun : s.halt = .Running) :
    runInstrSeq duplicateMask {s with pc := pc, stack := returnPC :: maskWord :: rest} =
      some {{s with pc := pcAfter pc duplicateMask} with
        stack := maskWord :: returnPC :: maskWord :: rest} := by
  have hcap : rest.length + 2 < 1024 := by omega
  simp [duplicateMask, runInstrSeq, Stepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, hrun, hcap, List.getElem?_cons_zero]
  change pc + UInt256.ofNat 1 = pc + UInt256.ofNat 1
  rfl

theorem run_endian (s : State) (pc low high returnPC : UInt256) (rest : List UInt256)
    (hstack : rest.length ≤ 996) (hrun : s.halt = .Running)
    (hactive : 34 ≤ s.activeWords.toNat) :
    runInstrSeq template
      {s with pc := pc, stack := high :: low :: returnPC :: maskWord :: rest} =
      some {{{s with pc := pcAfter pc template} with
        stack := maskWord :: returnPC :: maskWord :: rest} with
        memory := (Table80ScratchZero.scratchMemory s.memory
          (PairedScheduleData.reversedWord low)
          (PairedScheduleData.reversedWord high))} := by
  have h1 := run_reverse s pc high
    (low :: returnPC :: maskWord :: rest) (by simp; omega) hrun
  change runInstrSeq upperReverse _ = some _ at h1
  have h2 := PairedSchedulePrimitives.run_storeTemplate s (pcAfter pc upperReverse)
    (PairedScheduleData.reversedWord high) 60
    (low :: returnPC :: maskWord :: rest)
    (by simp; omega) (by decide) hrun
  rw [word_active_preserved _ _ hactive (by decide)] at h2
  change runInstrSeq upperStore _ = some _ at h2
  have h12 := DenseScheduleTrace.runInstrSeq_append_running h1 (by exact hrun) h2
  have h3 := run_reverse
    {s with memory := writeWord s.memory 60 (PairedScheduleData.reversedWord high)}
    (pcAfter (pcAfter pc upperReverse) upperStore) low
    (returnPC :: maskWord :: rest) (by simp; omega) hrun
  change runInstrSeq lowerReverse _ = some _ at h3
  have h123 := DenseScheduleTrace.runInstrSeq_append_running h12 (by exact hrun) h3
  have h4 := PairedSchedulePrimitives.run_storeTemplate
    {s with memory := writeWord s.memory 60 (PairedScheduleData.reversedWord high)}
    (pcAfter (pcAfter (pcAfter pc upperReverse) upperStore) lowerReverse)
    (PairedScheduleData.reversedWord low) 28 (returnPC :: maskWord :: rest)
    (by simp; omega) (by decide) hrun
  rw [word_active_preserved _ _ hactive (by decide)] at h4
  change runInstrSeq lowerStore _ = some _ at h4
  have h1234 := DenseScheduleTrace.runInstrSeq_append_running h123 (by exact hrun) h4
  have h5 := run_duplicateMask
    {s with memory := (Table80ScratchZero.scratchMemory s.memory
      (PairedScheduleData.reversedWord low) (PairedScheduleData.reversedWord high))}
    (pcAfter (pcAfter (pcAfter (pcAfter pc upperReverse) upperStore) lowerReverse) lowerStore)
    returnPC rest hstack hrun
  have h := DenseScheduleTrace.runInstrSeq_append_running h1234 (by exact hrun) h5
  simpa only [template, DenseScheduleTrace.pcAfter_append, lowerStore,
    Table80ScratchZero.scratchMemory] using h

#print axioms run_endian
end Challenge.Ripemd160.Submission.Proofs.Bytecode.DeferredNormalEndian
