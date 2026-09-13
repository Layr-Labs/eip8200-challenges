import Challenge.Ripemd160.Submission.Proofs.Bytecode.PersistentMaskEndian

set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Source32Lower
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace DenseScheduleTemplate PairedMask32Cache PairedScheduleMemory
open PersistentMaskEndian

def lowerTemplate : List Instr :=
  [.op .JUMPDEST] ++ loadTemplate 1120 ++ (stage8 false ++ stage16) ++
    lowStore ++ [.op (.Dup ⟨1, by decide⟩)]

def lowerScratch (memory : ByteArray) (p : Nat) : ByteArray :=
  writeWord memory 28 (PairedScheduleData.reversedWord (MachineState.readWord memory p))

theorem run_lower (s : State) (pc ret mw a2 a3 a4 a5 a6 a7 a8 a9 a10 off lim : UInt256)
    (rho : List UInt256) (p : Nat) (hstack : rho.length ≤ 990) (hrun : s.halt = .Running)
    (ha : 35 ≤ s.activeWords.toNat)
    (hq : off + UInt256.ofNat 1120 = UInt256.ofNat p) (hpb : p < 2 ^ 256)
    (hactive : activeAfterWord s.activeWords (UInt256.ofNat p) = s.activeWords) :
    runInstrSeq lowerTemplate {s with pc := pc, stack := stk ret mw a2 a3 a4 a5 a6 a7 a8 a9 a10 off lim rho} =
      some {s with
        pc := pcAfter pc lowerTemplate
        stack := mw :: stk ret mw a2 a3 a4 a5 a6 a7 a8 a9 a10 off lim rho
        memory := lowerScratch s.memory p} := by
  let F := stk ret mw a2 a3 a4 a5 a6 a7 a8 a9 a10 off lim rho
  have hF : F.length ≤ 1005 := by simp [F, stk]; omega
  let pc1 := pcAfter pc [.op .JUMPDEST]
  have h0 : runInstrSeq [.op .JUMPDEST] {s with pc := pc, stack := F} =
      some {s with pc := pc1, stack := F} := by
    have hcapF : F.length < 1024 := by omega
    simp [runInstrSeq, DataStepper.runInstr, pc1, pcAfter, Instr.size, UInt256.succ, hrun, hcapF]
    rfl
  have h1 := run_load s pc1 ret mw a2 a3 a4 a5 a6 a7 a8 a9 a10 off lim rho
    1120 p hstack hrun hq hpb
  rw [hactive] at h1
  have h01 := DenseScheduleTrace.runInstrSeq_append_running h0 (by exact hrun) h1
  let pc2 := pcAfter pc1 (loadTemplate 1120)
  have h2 := run_reverse s pc2 (MachineState.readWord s.memory p)
    ret mw a2 a3 a4 a5 a6 a7 a8 a9 a10 off lim rho false hstack hrun
  have h012 := DenseScheduleTrace.runInstrSeq_append_running h01 (by exact hrun) h2
  let pc3 := pcAfter (pcAfter pc2 (stage8 false)) stage16
  have h3 := run_lowStore s pc3 (PairedScheduleData.reversedWord (MachineState.readWord s.memory p))
    F (by omega) hrun
  rw [Stagger144Active.word_active_preserved _ _ ha (by decide)] at h3
  have h0123 := DenseScheduleTrace.runInstrSeq_append_running h012 (by exact hrun) h3
  let s1 : State := {s with memory := lowerScratch s.memory p}
  let pc4 := pcAfter pc3 lowStore
  have h4 : runInstrSeq [.op (.Dup ⟨1, by decide⟩)] {s1 with pc := pc4, stack := F} =
      some {s1 with pc := pcAfter pc4 [.op (.Dup ⟨1, by decide⟩)], stack := mw :: F} := by
    have hcap (n : Nat) (hn : n ≤ 27) : rho.length + n < 1024 := by omega
    simp (discharger := omega) [F, stk, runInstrSeq, DataStepper.runInstr, pcAfter,
      hrun, hcap, Instr.size, UInt256.succ, s1, Nat.add_assoc, List.getElem?_cons_zero]
    rfl
  have h := DenseScheduleTrace.runInstrSeq_append_running h0123 (by exact hrun) h4
  simp only [lowerTemplate, DenseScheduleTrace.pcAfter_append, List.append_assoc] at h ⊢
  exact h

def sourceTemplate : List Instr :=
  (lowerTemplate ++ StaggerRawNormalPool.template) ++ StaggerNormal.storesTemplate

theorem run_source (s : State) (pc ret a2 a3 a4 a5 a6 a7 a8 a9 a10 off lim : UInt256)
    (rho : List UInt256) (p : Nat) (hstack : rho.length ≤ 880) (hrun : s.halt = .Running)
    (ha : 35 ≤ s.activeWords.toNat)
    (hq : off + UInt256.ofNat 1120 = UInt256.ofNat p) (hpb : p < 2 ^ 256)
    (hactive : activeAfterWord s.activeWords (UInt256.ofNat p) = s.activeWords) :
    runInstrSeq sourceTemplate {s with pc := pc, stack := stk ret (UInt256.ofNat 4294967295) a2 a3 a4 a5 a6 a7 a8 a9 a10 off lim rho} =
      some {s with
        pc := pcAfter pc sourceTemplate
        stack := stk ret (UInt256.ofNat 4294967295) a2 a3 a4 a5 a6 a7 a8 a9 a10 off lim rho
        memory := StaggerTableLayout.resultMemory (lowerScratch s.memory p)
          (StaggerScratch.poolWordD (lowerScratch s.memory p))} := by
  let F := stk ret (UInt256.ofNat 4294967295) a2 a3 a4 a5 a6 a7 a8 a9 a10 off lim rho
  let scratch := lowerScratch s.memory p
  let s1 : State := {s with memory := scratch}
  have hF : F.length ≤ 900 := by simp [F, stk]; omega
  have h0 := run_lower s pc ret (UInt256.ofNat 4294967295) a2 a3 a4 a5 a6 a7 a8 a9 a10 off lim rho p
    (by omega) hrun ha hq hpb hactive
  have h1 := StaggerNormal.run_pool s1 (pcAfter pc lowerTemplate) F hF (by rfl) hrun ha
  have h01 := DenseScheduleTrace.runInstrSeq_append_running h0 (by exact hrun) h1
  have h2 := StaggerNormal.run_stores s1 (pcAfter (pcAfter pc lowerTemplate) StaggerRawNormalPool.template)
    (StaggerScratch.poolWordD scratch) F hF hrun ha
  have h := DenseScheduleTrace.runInstrSeq_append_running h01 (by exact hrun) h2
  simpa only [sourceTemplate, DenseScheduleTrace.pcAfter_append, s1, scratch] using h

def ordinaryEndianTemplate : List Instr :=
  loadTemplate 1152 ++ (stage8 false ++ stage16) ++ highStore ++ lowerTemplate

theorem run_ordinaryEndian (s : State) (pc ret mw a2 a3 a4 a5 a6 a7 a8 a9 a10 off lim : UInt256)
    (rho : List UInt256) (p : Nat) (hstack : rho.length ≤ 990) (hrun : s.halt = .Running)
    (hp : 1120 ≤ p) (hbound : p + 64 < 2 ^ 256)
    (hq1 : off + UInt256.ofNat 1152 = UInt256.ofNat (p + 32))
    (hq0 : off + UInt256.ofNat 1120 = UInt256.ofNat p) :
    runInstrSeq ordinaryEndianTemplate {s with pc := pc, stack := stk ret mw a2 a3 a4 a5 a6 a7 a8 a9 a10 off lim rho} =
      some {s with
        pc := pcAfter pc ordinaryEndianTemplate
        stack := mw :: stk ret mw a2 a3 a4 a5 a6 a7 a8 a9 a10 off lim rho
        memory := StaggerScratch.scratchMemory s.memory
          (PairedScheduleData.reversedWord (MachineState.readWord s.memory p))
          (PairedScheduleData.reversedWord (MachineState.readWord s.memory (p + 32)))
        activeWords := loadedActiveWords s (UInt256.ofNat p)} := by
  let high := PairedScheduleData.reversedWord (MachineState.readWord s.memory (p + 32))
  let low := PairedScheduleData.reversedWord (MachineState.readWord s.memory p)
  let a1 := activeAfterWord s.activeWords (UInt256.ofNat (p + 32))
  have ha1 : 37 ≤ a1.toNat := active_ge37 s.activeWords p hp hbound
  let s1 : State := {s with activeWords := a1}
  let s2 : State := {s1 with memory := writeWord s.memory 60 high}
  let F := stk ret mw a2 a3 a4 a5 a6 a7 a8 a9 a10 off lim rho
  have hF : F.length ≤ 1005 := by simp [F, stk]; omega
  have h1 := run_load s pc ret mw a2 a3 a4 a5 a6 a7 a8 a9 a10 off lim rho 1152 (p + 32) hstack hrun hq1 (by omega)
  have h2 := run_reverse s1 (pcAfter pc (loadTemplate 1152)) (MachineState.readWord s.memory (p + 32))
    ret mw a2 a3 a4 a5 a6 a7 a8 a9 a10 off lim rho false hstack hrun
  have h12 := DenseScheduleTrace.runInstrSeq_append_running h1 (by exact hrun) h2
  have h3 := run_highStore s1 (pcAfter (pcAfter (pcAfter pc (loadTemplate 1152)) (stage8 false)) stage16) high F
    (by omega) hrun
  rw [Stagger144Active.word_active_preserved _ _ (by change 35 ≤ a1.toNat; omega) (by decide)] at h3
  have h123 := DenseScheduleTrace.runInstrSeq_append_running h12 (by exact hrun) h3
  let pc3 := pcAfter (pcAfter (pcAfter (pcAfter pc (loadTemplate 1152)) (stage8 false)) stage16) highStore
  have hact : activeAfterWord s2.activeWords (UInt256.ofNat p) = s2.activeWords :=
    active_reload s.activeWords p hbound
  have h4 := run_lower s2 pc3 ret mw a2 a3 a4 a5 a6 a7 a8 a9 a10 off lim rho p
    hstack hrun (by change 35 ≤ a1.toNat; omega) hq0 (by omega) hact
  have hread : MachineState.readWord s2.memory p = MachineState.readWord s.memory p :=
    read_writeWord_disjoint _ _ _ _ (Or.inr (by omega))
  have hscratch : lowerScratch s2.memory p = StaggerScratch.scratchMemory s.memory low high := by
    unfold lowerScratch
    rw [hread]
    rfl
  rw [hscratch] at h4
  have h := DenseScheduleTrace.runInstrSeq_append_running h123 (by exact hrun) h4
  have hloaded : loadedActiveWords s (UInt256.ofNat p) = a1 := active_swap s.activeWords p hbound
  simp only [ordinaryEndianTemplate, DenseScheduleTrace.pcAfter_append, List.append_assoc] at h ⊢
  rw [hloaded]
  exact h

def ordinaryTemplate : List Instr :=
  (ordinaryEndianTemplate ++ StaggerRawNormalPool.template) ++ StaggerNormal.storesTemplate

theorem ordinaryTemplate_eq :
    ordinaryTemplate = (loadTemplate 1152 ++ (stage8 false ++ stage16) ++ highStore) ++ sourceTemplate := by
  simp only [ordinaryTemplate, ordinaryEndianTemplate, sourceTemplate, List.append_assoc]

theorem run_ordinary (s : State) (pc ret a2 a3 a4 a5 a6 a7 a8 a9 a10 off lim : UInt256)
    (rho : List UInt256) (p : Nat) (hstack : rho.length ≤ 880) (hrun : s.halt = .Running)
    (hp : 1120 ≤ p) (hbound : p + 64 < 2 ^ 256)
    (hq1 : off + UInt256.ofNat 1152 = UInt256.ofNat (p + 32))
    (hq0 : off + UInt256.ofNat 1120 = UInt256.ofNat p)
    (hlow : (MachineState.readWord s.memory 0).toNat < 2 ^ 32) :
    runInstrSeq ordinaryTemplate {s with pc := pc, stack := stk ret (UInt256.ofNat 4294967295) a2 a3 a4 a5 a6 a7 a8 a9 a10 off lim rho} =
      some {s with
        pc := pcAfter pc ordinaryTemplate
        stack := stk ret (UInt256.ofNat 4294967295) a2 a3 a4 a5 a6 a7 a8 a9 a10 off lim rho
        memory := StaggerTableLayout.resultMemory s.memory (StaggerScratch.dirtyWord s.memory p)
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
  have h1 := run_ordinaryEndian s pc ret (UInt256.ofNat 4294967295) a2 a3 a4 a5 a6 a7 a8 a9 a10 off lim rho p
    (by omega) hrun hp hbound hq1 hq0
  have h3 := StaggerNormal.run_pool s2 (pcAfter pc ordinaryEndianTemplate) F hF (by rfl) hrun (by omega)
  have hpool : StaggerNormal.poolStack (StaggerScratch.poolWordD scratch) = StaggerNormal.poolStack words := by
    have hD : ∀ i, i < 16 → StaggerScratch.poolWordD scratch i = words i :=
      fun i hi => StaggerScratch.poolWordD_eq_dirty s.memory p i hi hlow
    simp (discharger := decide) only [StaggerNormal.poolStack, hD]
  rw [show s2.memory = scratch by rfl, hpool] at h3
  have h13 := DenseScheduleTrace.runInstrSeq_append_running h1 (by exact hrun) h3
  have h4 := StaggerNormal.run_stores s2 (pcAfter (pcAfter pc ordinaryEndianTemplate) StaggerRawNormalPool.template)
    words F hF hrun (by omega)
  have h := DenseScheduleTrace.runInstrSeq_append_running h13 (by exact hrun) h4
  have hm : StaggerTableLayout.resultMemory scratch words = StaggerTableLayout.resultMemory s.memory words :=
    StaggerScratch.erase_scratch s.memory (StaggerTableLayout.tableWords words) _ _
  simpa only [ordinaryTemplate, DenseScheduleTrace.pcAfter_append, s2, s1, hm, words] using h

#print axioms run_ordinaryEndian
#print axioms ordinaryTemplate_eq
#print axioms run_ordinary

#print axioms run_lower
#print axioms run_source
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Source32Lower
