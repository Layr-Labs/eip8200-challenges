import Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80Setup
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80Setup
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace DenseScheduleTemplate PairedMask32Cache PairedScheduleMemory
open PairTableMemory PairTableActive

theorem initial_eq_cached : initialTemplate = PairedMask32Cache.cachedInitial := by rfl

def reverseTemplate (slot8 slot16 : Fin 16) : List Instr :=
  cachedStage 8 slot8 ++ cachedStage 16 slot16

theorem run_reverse (s : State) (pc value : UInt256) (slot8 slot16 : Fin 16) (rest : List UInt256)
    (hstack : rest.length < 1020) (hrun : s.halt = .Running)
    (hlookup8 : ∀ a b : UInt256, (a :: b :: rest)[slot8.val]? = some mask8)
    (hlookup16 : ∀ a b : UInt256, (a :: b :: rest)[slot16.val]? = some mask16) :
    runInstrSeq (reverseTemplate slot8 slot16) {s with pc := pc, stack := value :: rest} =
      some {s with pc := pcAfter pc (reverseTemplate slot8 slot16), stack := PairedScheduleData.reversedWord value :: rest} := by
  have h1 := run_cachedStage s pc value 8 mask8 slot8 rest hstack
    (Or.inl ⟨rfl, rfl⟩) hlookup8 hrun
  dsimp only [DenseScheduleTrace.stageState] at h1
  have h2 := run_cachedStage s (pcAfter pc (cachedStage 8 slot8))
    (packedStage value 8 mask8) 16 mask16 slot16 rest hstack
    (Or.inr ⟨rfl, rfl⟩) hlookup16 hrun
  dsimp only [DenseScheduleTrace.stageState] at h2
  have h := DenseScheduleTrace.runInstrSeq_append_running h1 (by exact hrun) h2
  rw [← PairedScheduleContract.packedWord_eq_reversedWord]
  simpa only [reverseTemplate, DenseScheduleTrace.pcAfter_append, packedWord] using h

def upperReverse : List Instr := reverseTemplate ⟨3, by decide⟩ ⟨5, by decide⟩
def lowerReverse : List Instr := reverseTemplate ⟨2, by decide⟩ ⟨4, by decide⟩
def upperStore : List Instr := PairedSchedulePrimitives.storeTemplate 64
def lowerStore : List Instr := PairedSchedulePrimitives.storeTemplate 32
def maskCleanup : List Instr := [.op .POP, .op (.Swap ⟨0, by decide⟩), .op .POP]

theorem endianTemplate_eq : endianTemplate =
    (((upperReverse ++ upperStore) ++ lowerReverse) ++ lowerStore) ++ maskCleanup := by rfl

theorem run_cleanup (s : State) (pc a b c returnPC : UInt256) (rest : List UInt256)
    (hstack : rest.length ≤ 996) (hrun : s.halt = .Running) :
    runInstrSeq maskCleanup {s with pc := pc, stack := a :: b :: c :: returnPC :: rest} =
      some {s with pc := pcAfter pc maskCleanup, stack := b :: returnPC :: rest} := by
  have hcap (n : Nat) (hn : n ≤ 27) : rest.length + n < 1024 := by omega
  simp [maskCleanup, runInstrSeq, Stepper.runInstr, pcAfter, hrun, hcap,
    List.exchange, List.getElem?_cons_zero, UInt256.succ, Instr.size, Nat.add_assoc]
  all_goals repeat first | apply And.intro | rfl

theorem run_endian (s : State) (pc low high returnPC : UInt256) (rest : List UInt256)
    (hstack : rest.length ≤ 996) (hrun : s.halt = .Running) (hactive : 34 ≤ s.activeWords.toNat) :
    runInstrSeq endianTemplate {s with pc := pc, stack := high :: low :: mask8 :: maskWord :: mask16 :: returnPC :: rest} =
      some {s with pc := pcAfter pc endianTemplate, stack := maskWord :: returnPC :: rest, memory := scratchMemory s.memory (PairedScheduleData.reversedWord low) (PairedScheduleData.reversedWord high)} := by
  have h1 := run_reverse s pc high ⟨3, by decide⟩ ⟨5, by decide⟩
    (low :: mask8 :: maskWord :: mask16 :: returnPC :: rest)
    (by simp; omega) hrun (by intros; rfl) (by intros; rfl)
  change runInstrSeq upperReverse _ = some _ at h1
  have h2 := PairedSchedulePrimitives.run_storeTemplate s (pcAfter pc upperReverse)
    (PairedScheduleData.reversedWord high) 64
    (low :: mask8 :: maskWord :: mask16 :: returnPC :: rest)
    (by simp; omega) (by decide) hrun
  rw [word_active_preserved _ _ hactive (by decide)] at h2
  change runInstrSeq upperStore _ = some _ at h2
  have h12 := DenseScheduleTrace.runInstrSeq_append_running h1 (by exact hrun) h2
  have h3 := run_reverse {s with memory := writeWord s.memory 64 (PairedScheduleData.reversedWord high)}
    (pcAfter (pcAfter pc upperReverse) upperStore) low ⟨2, by decide⟩ ⟨4, by decide⟩
    (mask8 :: maskWord :: mask16 :: returnPC :: rest)
    (by simp; omega) hrun (by intros; rfl) (by intros; rfl)
  change runInstrSeq lowerReverse _ = some _ at h3
  have h123 := DenseScheduleTrace.runInstrSeq_append_running h12 (by exact hrun) h3
  have h4 := PairedSchedulePrimitives.run_storeTemplate
    {s with memory := writeWord s.memory 64 (PairedScheduleData.reversedWord high)}
    (pcAfter (pcAfter (pcAfter pc upperReverse) upperStore) lowerReverse)
    (PairedScheduleData.reversedWord low) 32 (mask8 :: maskWord :: mask16 :: returnPC :: rest)
    (by simp; omega) (by decide) hrun
  rw [word_active_preserved _ _ hactive (by decide)] at h4
  change runInstrSeq lowerStore _ = some _ at h4
  have h1234 := DenseScheduleTrace.runInstrSeq_append_running h123 (by exact hrun) h4
  have h5 := run_cleanup {s with memory := scratchMemory s.memory (PairedScheduleData.reversedWord low) (PairedScheduleData.reversedWord high)}
    (pcAfter (pcAfter (pcAfter (pcAfter pc upperReverse) upperStore) lowerReverse) lowerStore)
    mask8 maskWord mask16 returnPC rest hstack hrun
  have h := DenseScheduleTrace.runInstrSeq_append_running h1234 (by exact hrun) h5
  simpa only [endianTemplate_eq, DenseScheduleTrace.pcAfter_append, scratchMemory] using h
#print axioms run_endian
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80Setup
