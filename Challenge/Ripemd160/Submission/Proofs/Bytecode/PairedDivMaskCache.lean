import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedMask32Cache

set_option warningAsError true

/-! Replace the two cached literal masks by closed, input-independent quotients.
No schedule-memory or public input precondition changes; the old rest < 1015
bound remains explicit. This module is private source until ordinary checking. -/
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedDivMaskCache

open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace DenseScheduleTemplate PairedScheduleMemory PairedMask32Cache

theorem mask8_div :
    UInt256.lnot (UInt256.ofNat 0) / UInt256.ofNat 257 = mask8 := by decide

#print axioms mask8_div

theorem mask16_div :
    UInt256.lnot (UInt256.ofNat 0) / UInt256.ofNat 65537 = mask16 := by decide

#print axioms mask16_div

private theorem word_add_assoc (u v w : UInt256) :
    (u + v) + w = u + (v + w) := by
  apply Word.word_ext
  change ((u.val + v.val) + w.val).val = (u.val + (v.val + w.val)).val
  simp [Fin.add_def, Nat.add_assoc]

private theorem word_add_ofNat_assoc (u : UInt256) (a b : Nat) :
    (u + UInt256.ofNat a) + UInt256.ofNat b = u + UInt256.ofNat (a + b) := by
  rw [word_add_assoc, Word.ofNat_add_mod]

private theorem add_ofNat_assoc (u : UInt256) (a b : Nat) :
    UInt256.add (UInt256.add u (UInt256.ofNat a)) (UInt256.ofNat b) =
      UInt256.add u (UInt256.ofNat (a + b)) := by
  exact word_add_ofNat_assoc u a b

private theorem add_ofNat_assoc_hAdd (u : UInt256) (a b : Nat) :
    (UInt256.add u (UInt256.ofNat a)) + UInt256.ofNat b =
      u + UInt256.ofNat (a + b) := by
  exact word_add_ofNat_assoc u a b

private theorem add_ofNat_assoc_add (u : UInt256) (a b : Nat) :
    UInt256.add (u + UInt256.ofNat a) (UInt256.ofNat b) =
      u + UInt256.ofNat (a + b) := by
  exact word_add_ofNat_assoc u a b

def cachedInitial : List Instr :=
  [op .JUMPDEST, .push ⟨4, by decide⟩ maskWord,
    .push ⟨31, by decide⟩ mask8, .push ⟨30, by decide⟩ mask16,
    .op (.Swap ⟨2, by decide⟩), dup1, op .MLOAD, swap1,
    push1 (UInt256.ofNat 32), op .ADD, op .MLOAD]

theorem run_cachedInitial (s : State) (pc messageOffset returnPC : UInt256)
    (rest : List UInt256) (hstack : rest.length < 1015) (hrun : s.halt = .Running) :
    runInstrSeq cachedInitial (scheduleEntry s pc messageOffset returnPC rest) =
      some {s with
        pc := pcAfter pc cachedInitial
        stack := inputWord1 s messageOffset :: inputWord0 s messageOffset ::
          mask8 :: maskWord :: mask16 :: returnPC :: rest
        activeWords := loadedActiveWords s messageOffset} := by
  have hcap (m : Nat) (hm : m ≤ 9) : rest.length + m < 1024 := by omega
  have hswap1 (u v : UInt256) (rho : List UInt256) :
      (u :: v :: rho).exchange 0 1 = some (v :: u :: rho) := by
    simpa using YulEvmCompiler.exchange_swap u v ([] : List UInt256) rho
  have hswap3 (u v w z : UInt256) (rho : List UInt256) :
      (u :: v :: w :: z :: rho).exchange 0 3 = some (z :: v :: w :: u :: rho) := by
    simpa using YulEvmCompiler.exchange_swap u z [v,w] rho
  have hzero : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have h32 : UInt256.ofNat 32 + messageOffset = messageOffset + UInt256.ofNat 32 :=
    Word.word_add_comm _ _
  simp [cachedInitial, scheduleEntry, inputWord0, inputWord1,
    loadedActiveWords, activeAfterWord, op, push1, dup1, swap1,
    runInstrSeq, Stepper.runInstr, pcAfter, hrun, hcap, hswap1, hswap3, h32,
    word_add_assoc, Nat.add_assoc, State.activeWordsAfterUInt256,
    Word.word_toNat_ofNat, Word.ofNat_add_mod, UInt256.succ, Instr.size]
  repeat first
    | rw [add_ofNat_assoc_hAdd]
    | rw [add_ofNat_assoc_add]
    | rw [add_ofNat_assoc]
  simp only [word_add_ofNat_assoc]

#print axioms run_cachedInitial


open PairedScheduleHalves PairedScheduleCombined PairedScheduleContract

/-- Schedule cleanup that keeps the 32-bit mask instead of dropping and
re-pushing it: `POP SWAP1 POP` discards the two wide masks and leaves the
middle word, which the multiply startup consumes in place of its own `PUSH4`.
Three stack operations either way; the preserved word is `maskWord` by the
schedule's own reasoning, not by observation. -/
def keepCleanupTemplate : List Instr := [op .POP, swap1, op .POP]

theorem run_keepCleanupTemplate (s : State) (pc a b c : UInt256) (rest : List UInt256)
    (hstack : rest.length < 1021) (hrun : s.halt = .Running) :
    runInstrSeq keepCleanupTemplate {s with pc := pc, stack := a :: b :: c :: rest} =
      some {s with pc := pcAfter pc keepCleanupTemplate, stack := b :: rest} := by
  have hcap2 : rest.length + 1 + 1 < 1024 := by omega
  have hcap3 : rest.length + 1 + 1 + 1 < 1024 := by omega
  have hswap1 (u v : UInt256) (rho : List UInt256) :
      (u :: v :: rho).exchange 0 1 = some (v :: u :: rho) := by
    simpa using YulEvmCompiler.exchange_swap u v ([] : List UInt256) rho
  simp [keepCleanupTemplate, op, swap1, runInstrSeq, Stepper.runInstr, pcAfter, hrun,
    hcap2, hcap3, hswap1, UInt256.succ, Instr.size]
  rfl

#print axioms run_keepCleanupTemplate

def fullTemplate : List Instr :=
  (((cachedInitial ++ upperTemplate) ++ lowerTemplate) ++ sentinelTemplate) ++
    keepCleanupTemplate

theorem run_fullTemplate (s : State) (pc messageOffset returnPC : UInt256)
    (rest : List UInt256) (hstack : rest.length < 1015) (hrun : s.halt = .Running)
    (hactive : 23 ≤ (loadedActiveWords s messageOffset).toNat) :
    runInstrSeq fullTemplate (scheduleEntry s pc messageOffset returnPC rest) =
      some {s with
        pc := pcAfter pc fullTemplate
        stack := maskWord :: returnPC :: rest
        memory := normalizedMemory s.memory (scheduleWords s messageOffset)
        activeWords := loadedActiveWords s messageOffset} := by
  have h1 := run_cachedInitial s pc messageOffset returnPC rest hstack hrun
  have h2 := run_cachedReversedHalf
    {s with activeWords := loadedActiveWords s messageOffset}
    (pcAfter pc cachedInitial) (inputWord1 s messageOffset) 8
    ⟨3, by decide⟩ ⟨5, by decide⟩ ⟨2, by decide⟩
    (inputWord0 s messageOffset :: mask8 :: maskWord :: mask16 :: returnPC :: rest)
    (by simp only [List.length_cons]; omega) hrun hactive (by decide)
    (by intros; rfl) (by intros; rfl) rfl
  have h12 := DenseScheduleTrace.runInstrSeq_append_running h1 (by exact hrun) h2
  have h3 := run_cachedReversedHalf
    {s with
      activeWords := loadedActiveWords s messageOffset
      memory := storeCells s.memory (halfWords (packedInput1 s messageOffset) 8) 8 8}
    (pcAfter (pcAfter pc cachedInitial) upperTemplate)
    (inputWord0 s messageOffset) 0 ⟨2, by decide⟩ ⟨4, by decide⟩ ⟨1, by decide⟩
    (mask8 :: maskWord :: mask16 :: returnPC :: rest)
    (by simp only [List.length_cons]; omega) hrun hactive (by decide)
    (by intros; rfl) (by intros; rfl) rfl
  have h123 := DenseScheduleTrace.runInstrSeq_append_running h12 (by exact hrun) h3
  have h4 := run_sentinelTemplate
    {s with
      activeWords := loadedActiveWords s messageOffset
      memory := storeCells
        (storeCells s.memory (halfWords (packedInput1 s messageOffset) 8) 8 8)
        (halfWords (packedInput0 s messageOffset) 0) 0 8}
    (pcAfter (pcAfter (pcAfter pc cachedInitial) upperTemplate) lowerTemplate)
    (mask8 :: maskWord :: mask16 :: returnPC :: rest)
    (by simp only [List.length_cons]; omega) hrun hactive
  have h1234 := DenseScheduleTrace.runInstrSeq_append_running h123 (by exact hrun) h4
  have h5 := run_keepCleanupTemplate
    {s with
      activeWords := loadedActiveWords s messageOffset
      memory := writeWord
        (storeCells (storeCells s.memory (halfWords (packedInput1 s messageOffset) 8) 8 8)
          (halfWords (packedInput0 s messageOffset) 0) 0 8)
        (cell 16) (UInt256.ofNat 0)}
    (pcAfter (pcAfter (pcAfter (pcAfter pc cachedInitial) upperTemplate) lowerTemplate)
      sentinelTemplate) mask8 maskWord mask16 (returnPC :: rest)
    (by simp only [List.length_cons]; omega) hrun
  have hjoin := DenseScheduleTrace.runInstrSeq_append_running h1234 (by exact hrun) h5
  rw [store_upper_schedule, store_lower_schedule] at hjoin
  simpa only [fullTemplate, upperTemplate, lowerTemplate,
    DenseScheduleTrace.pcAfter_append, normalizedMemory] using hjoin

#print axioms run_fullTemplate

theorem run_fullTemplate_natural (s : State) (pc returnPC : UInt256)
    (p : Nat) (rest : List UInt256)
    (hstack : rest.length < 1015) (hrun : s.halt = .Running)
    (hp : 736 ≤ p) (hbound : p + 64 < 2 ^ 256) :
    runInstrSeq fullTemplate (scheduleEntry s pc (UInt256.ofNat p) returnPC rest) =
      some {s with
        pc := pcAfter pc fullTemplate
        stack := maskWord :: returnPC :: rest
        memory := normalizedMemory s.memory (PairedScheduleData.extractedWord s.memory p)
        activeWords := loadedActiveWords s (UInt256.ofNat p)} := by
  have h := run_fullTemplate s pc (UInt256.ofNat p) returnPC rest hstack hrun
    (loaded_active_ge23 s p hp hbound)
  rw [normalizedMemory_congr s.memory (scheduleWords s (UInt256.ofNat p))
    (PairedScheduleData.extractedWord s.memory p)
    (fun i hi => scheduleWords_eq_extracted s p i hi hbound)] at h
  exact h

#print axioms run_fullTemplate_natural


theorem fullTemplate_length : fullTemplate.length = 159 := by
  have hold := PairedMask32Cache.fullTemplate_length
  have hi : PairedMask32Cache.cachedInitial.length = 11 := rfl
  have hc0 : PairedMask32Cache.cleanupTemplate.length = 3 := rfl
  have hn : cachedInitial.length = 11 := rfl
  have hc1 : keepCleanupTemplate.length = 3 := rfl
  simp only [PairedMask32Cache.fullTemplate, List.length_append, hi, hc0] at hold
  simp only [fullTemplate, List.length_append, hn, hc1]
  omega

#print axioms fullTemplate_length

theorem fullTemplate_byteLength : (assembleBytes fullTemplate).length = 285 := by
  rw [DenseScheduleTemplate.assembleBytes_length]
  norm_num [fullTemplate, cachedInitial, upperTemplate, lowerTemplate, cachedReversedHalf,
    cachedStage, endianFactorPush, endianFactor, PairedMask32Cache.halfTemplate,
    PairedMask32Cache.prefixTemplate, PairedMask32Cache.keepTemplate,
    PairedScheduleStores.firstTemplate, PairedMask32Cache.middleTemplate,
    PairedMask32Cache.lastTemplate, maskTemplate,
    PairedSchedulePrimitives.duplicateShiftTemplate, PairedSchedulePrimitives.storeTemplate,
    PairedSchedulePrimitives.storeTemplateW, PairedSchedulePrimitives.storeWidth,
    sentinelTemplate, keepCleanupTemplate, cell, op, push1, push2, push3, dup1, swap1]

#print axioms fullTemplate_byteLength

theorem fullTemplate_staticGas : staticGas fullTemplate = 480 := by
  have happend (xs ys : List Instr) : staticGas (xs ++ ys) = staticGas xs + staticGas ys := by
    simp only [staticGas, List.map_append, List.sum_append]
  have hold := PairedMask32Cache.fullTemplate_staticGas
  have hi : staticGas PairedMask32Cache.cachedInitial = 31 := by decide
  have hc0 : staticGas PairedMask32Cache.cleanupTemplate = 6 := by decide
  have hn : staticGas cachedInitial = 31 := by decide
  have hc1 : staticGas keepCleanupTemplate = 7 := by decide
  simp only [PairedMask32Cache.fullTemplate, happend, hi, hc0] at hold
  simp only [fullTemplate, happend, hn, hc1]
  omega

#print axioms fullTemplate_staticGas


open StackRoundTemplate

theorem runInstr_pc_div {s t : State}
    (hresult : Stepper.runInstr (.op .DIV) s = some t) :
    t.pc = s.pc + UInt256.ofNat (Instr.op .DIV).size := by
  by_cases hcap : s.stack.length < 1024
  · rw [Stepper.runInstr, if_pos hcap] at hresult
    cases hs : s.stack with
    | nil => simp [hs] at hresult
    | cons a tail =>
        cases ht : tail with
        | nil => simp [hs, ht] at hresult
        | cons b rest =>
            simp [hs, ht] at hresult
            subst t
            rfl
  · simp [Stepper.runInstr, hcap] at hresult

#print axioms runInstr_pc_div

private theorem cachedInitial_advances :
    ∀ instruction ∈ cachedInitial,
      DenseScheduleLift.Advances instruction ∨ instruction = .op .DIV := by
  intro instruction hmem
  simp only [cachedInitial, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  all_goals first
    | exact Or.inr rfl
    | exact Or.inl (Or.inl (Or.inl (StraightLine.push _ _)))
    | exact Or.inl (Or.inl (Or.inl (StraightLine.dup _)))
    | exact Or.inl (Or.inl (Or.inl (StraightLine.swap _)))
    | exact Or.inl (Or.inl (Or.inl StraightLine.add))
    | exact Or.inl (Or.inl (Or.inl StraightLine.mload))
    | exact Or.inl (Or.inl (Or.inl StraightLine.not))
    | exact Or.inl (Or.inl (Or.inr (Or.inr rfl)))

theorem fullTemplate_advances :
    ∀ instruction ∈ fullTemplate,
      DenseScheduleLift.Advances instruction ∨ instruction = .op .DIV := by
  intro instruction hmem
  simp only [fullTemplate, List.mem_append] at hmem
  rcases hmem with (((hi | hu) | hl) | hs) | hc
  · exact cachedInitial_advances instruction hi
  · apply Or.inl
    apply PairedMask32Cache.fullTemplate_advances instruction
    simp only [PairedMask32Cache.fullTemplate, List.mem_append]
    exact Or.inl (Or.inl (Or.inl (Or.inr hu)))
  · apply Or.inl
    apply PairedMask32Cache.fullTemplate_advances instruction
    simp only [PairedMask32Cache.fullTemplate, List.mem_append]
    exact Or.inl (Or.inl (Or.inr hl))
  · apply Or.inl
    apply PairedMask32Cache.fullTemplate_advances instruction
    simp only [PairedMask32Cache.fullTemplate, List.mem_append]
    exact Or.inl (Or.inr hs)
  · simp only [keepCleanupTemplate, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    all_goals first
      | exact Or.inl (Or.inl (Or.inl StraightLine.pop))
      | exact Or.inl (Or.inl (Or.inl (StraightLine.swap _)))

#print axioms fullTemplate_advances

theorem advances {instruction : Instr} {s t : State}
    (hmem : instruction ∈ fullTemplate) (hresult : Stepper.runInstr instruction s = some t) :
    t.pc = s.pc + UInt256.ofNat instruction.size := by
  rcases fullTemplate_advances instruction hmem with hnormal | hdiv
  · exact DenseScheduleLift.runInstr_pc_of_advances hnormal hresult
  · subst instruction
    exact runInstr_pc_div hresult

#print axioms advances

theorem runLocatedBlock_fullTemplate {artifact : ProgramArtifact} {fork : Fork}
    (site : GenericRoundSite artifact fork fullTemplate)
    (s : State) (returnPC : UInt256) (p : Nat) (rest : List UInt256)
    (hstack : rest.length < 1015) (hrun : s.halt = .Running)
    (hp : 736 ≤ p) (hbound : p + 64 < 2 ^ 256) :
    Stepper.runLocatedBlock site.path
      (scheduleEntry s site.startPC (UInt256.ofNat p) returnPC rest) =
      some {s with
        pc := site.endPC
        stack := maskWord :: returnPC :: rest
        memory := normalizedMemory s.memory (PairedScheduleData.extractedWord s.memory p)
        activeWords := loadedActiveWords s (UInt256.ofNat p)} := by
  have hend : site.endPC = pcAfter site.startPC fullTemplate := by
    have h := endPC_eq_pcAfter_sites site.sites site.startPC site.endPC
      site.head_eq site.end_eq site.contiguous
    rwa [site.instruction_eq] at h
  have hraw : Stepper.runLocatedBlock site.path
      (scheduleEntry s site.startPC (UInt256.ofNat p) returnPC rest) =
      runInstrSeq fullTemplate
        (scheduleEntry s site.startPC (UInt256.ofNat p) returnPC rest) := by
    apply runLocatedBlock_eq_runInstrSeq_site site _ rfl
    intro located hmem u v hresult
    apply advances ?_ hresult
    rw [← site.instruction_eq]
    exact List.mem_map_of_mem hmem
  rw [hraw]
  have h := run_fullTemplate_natural s site.startPC returnPC p rest hstack hrun hp hbound
  rw [← hend] at h
  exact h

def gasSteps_fullTemplate {artifact : ProgramArtifact} {fork : Fork}
    (site : GenericRoundSite artifact fork fullTemplate)
    (s : State) (returnPC : UInt256) (p : Nat) (rest : List UInt256)
    (hstack : rest.length < 1015) (hrun : s.halt = .Running)
    (hp : 736 ≤ p) (hbound : p + 64 < 2 ^ 256)
    (hcode : s.executionEnv.code = artifact.code) (hfork : s.fork = fork)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (scheduleEntry s site.startPC (UInt256.ofNat p) returnPC rest)
      {s with
        pc := site.endPC
        stack := maskWord :: returnPC :: rest
        memory := normalizedMemory s.memory (PairedScheduleData.extractedWord s.memory p)
        activeWords := loadedActiveWords s (UInt256.ofNat p)} := by
  apply Stepper.runLocatedBlock_sound artifact fork site.path
  · exact hcode
  · exact hfork
  · exact runLocatedBlock_fullTemplate site s returnPC p rest hstack hrun hp hbound
  · exact hrun
  · exact hnp


#print axioms runLocatedBlock_fullTemplate
#print axioms gasSteps_fullTemplate

theorem fullTemplate_exactBytes : assembleBytes fullTemplate =
  (((([
    0x5b, 0x63, 0xff, 0xff, 0xff, 0xff, 0x7e, 0xff, 0x00, 0xff, 0x00, 0xff, 0x00, 0xff, 0x00, 0xff,
    0x00, 0xff, 0x00, 0xff, 0x00, 0xff, 0x00, 0xff, 0x00, 0xff, 0x00, 0xff, 0x00, 0xff, 0x00, 0xff,
    0x00, 0xff, 0x00, 0xff, 0x00, 0xff, 0x7d, 0xff, 0xff, 0x00, 0x00, 0xff, 0xff, 0x00, 0x00, 0xff,
    0xff, 0x00, 0x00, 0xff, 0xff, 0x00, 0x00, 0xff, 0xff, 0x00, 0x00, 0xff, 0xff, 0x00, 0x00, 0xff,
    0xff, 0x00, 0x00, 0xff, 0xff, 0x92, 0x80, 0x51, 0x90, 0x60, 0x20, 0x01, 0x51] ++ [
    0x80, 0x80, 0x60, 0x08, 0x1c, 0x18, 0x83, 0x16, 0x61, 0x01, 0x01, 0x02, 0x18, 0x80, 0x80, 0x60,
    0x10, 0x1c, 0x18, 0x85, 0x16, 0x62, 0x01, 0x00, 0x01, 0x02, 0x18, 0x80, 0x60, 0xe0, 0x1c, 0x61,
    0x01, 0xc0, 0x52, 0x80, 0x60, 0xc0, 0x1c, 0x84, 0x16, 0x61, 0x01, 0xe0, 0x52, 0x80, 0x60, 0xa0,
    0x1c, 0x84, 0x16, 0x61, 0x02, 0x00, 0x52, 0x80, 0x60, 0x80, 0x1c, 0x84, 0x16, 0x61, 0x02, 0x20,
    0x52, 0x80, 0x60, 0x60, 0x1c, 0x84, 0x16, 0x61, 0x02, 0x40, 0x52, 0x80, 0x60, 0x40, 0x1c, 0x84,
    0x16, 0x61, 0x02, 0x60, 0x52, 0x80, 0x60, 0x20, 0x1c, 0x84, 0x16, 0x61, 0x02, 0x80, 0x52, 0x83,
    0x16, 0x61, 0x02, 0xa0, 0x52]) ++ [
    0x80, 0x80, 0x60, 0x08, 0x1c, 0x18, 0x82, 0x16, 0x61, 0x01, 0x01, 0x02, 0x18, 0x80, 0x80, 0x60,
    0x10, 0x1c, 0x18, 0x84, 0x16, 0x62, 0x01, 0x00, 0x01, 0x02, 0x18, 0x80, 0x60, 0xe0, 0x1c, 0x60, 0xc0, 0x52, 0x80, 0x60, 0xc0, 0x1c, 0x83, 0x16, 0x60, 0xe0, 0x52, 0x80, 0x60, 0xa0,
    0x1c, 0x83, 0x16, 0x61, 0x01, 0x00, 0x52, 0x80, 0x60, 0x80, 0x1c, 0x83, 0x16, 0x61, 0x01, 0x20,
    0x52, 0x80, 0x60, 0x60, 0x1c, 0x83, 0x16, 0x61, 0x01, 0x40, 0x52, 0x80, 0x60, 0x40, 0x1c, 0x83,
    0x16, 0x61, 0x01, 0x60, 0x52, 0x80, 0x60, 0x20, 0x1c, 0x83, 0x16, 0x61, 0x01, 0x80, 0x52, 0x82,
    0x16, 0x61, 0x01, 0xa0, 0x52]) ++ [
    0x5f, 0x61, 0x02, 0xc0, 0x52]) ++ [
    0x50, 0x90, 0x50]) := by
  have h0 : assembleBytes cachedInitial = [
    0x5b, 0x63, 0xff, 0xff, 0xff, 0xff, 0x7e, 0xff, 0x00, 0xff, 0x00, 0xff, 0x00, 0xff, 0x00, 0xff,
    0x00, 0xff, 0x00, 0xff, 0x00, 0xff, 0x00, 0xff, 0x00, 0xff, 0x00, 0xff, 0x00, 0xff, 0x00, 0xff,
    0x00, 0xff, 0x00, 0xff, 0x00, 0xff, 0x7d, 0xff, 0xff, 0x00, 0x00, 0xff, 0xff, 0x00, 0x00, 0xff,
    0xff, 0x00, 0x00, 0xff, 0xff, 0x00, 0x00, 0xff, 0xff, 0x00, 0x00, 0xff, 0xff, 0x00, 0x00, 0xff,
    0xff, 0x00, 0x00, 0xff, 0xff, 0x92, 0x80, 0x51, 0x90, 0x60, 0x20, 0x01, 0x51] := by decide
  have h1 : assembleBytes upperTemplate = [
    0x80, 0x80, 0x60, 0x08, 0x1c, 0x18, 0x83, 0x16, 0x61, 0x01, 0x01, 0x02, 0x18, 0x80, 0x80, 0x60,
    0x10, 0x1c, 0x18, 0x85, 0x16, 0x62, 0x01, 0x00, 0x01, 0x02, 0x18, 0x80, 0x60, 0xe0, 0x1c, 0x61,
    0x01, 0xc0, 0x52, 0x80, 0x60, 0xc0, 0x1c, 0x84, 0x16, 0x61, 0x01, 0xe0, 0x52, 0x80, 0x60, 0xa0,
    0x1c, 0x84, 0x16, 0x61, 0x02, 0x00, 0x52, 0x80, 0x60, 0x80, 0x1c, 0x84, 0x16, 0x61, 0x02, 0x20,
    0x52, 0x80, 0x60, 0x60, 0x1c, 0x84, 0x16, 0x61, 0x02, 0x40, 0x52, 0x80, 0x60, 0x40, 0x1c, 0x84,
    0x16, 0x61, 0x02, 0x60, 0x52, 0x80, 0x60, 0x20, 0x1c, 0x84, 0x16, 0x61, 0x02, 0x80, 0x52, 0x83,
    0x16, 0x61, 0x02, 0xa0, 0x52] := by decide
  have h2 : assembleBytes lowerTemplate = [
    0x80, 0x80, 0x60, 0x08, 0x1c, 0x18, 0x82, 0x16, 0x61, 0x01, 0x01, 0x02, 0x18, 0x80, 0x80, 0x60,
    0x10, 0x1c, 0x18, 0x84, 0x16, 0x62, 0x01, 0x00, 0x01, 0x02, 0x18, 0x80, 0x60, 0xe0, 0x1c, 0x60, 0xc0, 0x52, 0x80, 0x60, 0xc0, 0x1c, 0x83, 0x16, 0x60, 0xe0, 0x52, 0x80, 0x60, 0xa0,
    0x1c, 0x83, 0x16, 0x61, 0x01, 0x00, 0x52, 0x80, 0x60, 0x80, 0x1c, 0x83, 0x16, 0x61, 0x01, 0x20,
    0x52, 0x80, 0x60, 0x60, 0x1c, 0x83, 0x16, 0x61, 0x01, 0x40, 0x52, 0x80, 0x60, 0x40, 0x1c, 0x83,
    0x16, 0x61, 0x01, 0x60, 0x52, 0x80, 0x60, 0x20, 0x1c, 0x83, 0x16, 0x61, 0x01, 0x80, 0x52, 0x82,
    0x16, 0x61, 0x01, 0xa0, 0x52] := by decide
  have h3 : assembleBytes sentinelTemplate = [
    0x5f, 0x61, 0x02, 0xc0, 0x52] := by decide
  have h4 : assembleBytes keepCleanupTemplate = [
    0x50, 0x90, 0x50] := by decide
  have h01 := (assembleBytes_append cachedInitial upperTemplate).trans
    (congrArg₂ List.append h0 h1)
  have h012 := (assembleBytes_append (cachedInitial ++ upperTemplate) lowerTemplate).trans
    (congrArg₂ List.append h01 h2)
  have h0123 := (assembleBytes_append ((cachedInitial ++ upperTemplate) ++ lowerTemplate)
    sentinelTemplate).trans (congrArg₂ List.append h012 h3)
  exact (assembleBytes_append (((cachedInitial ++ upperTemplate) ++ lowerTemplate) ++
    sentinelTemplate) keepCleanupTemplate).trans (congrArg₂ List.append h0123 h4)

#print axioms fullTemplate_exactBytes

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedDivMaskCache
