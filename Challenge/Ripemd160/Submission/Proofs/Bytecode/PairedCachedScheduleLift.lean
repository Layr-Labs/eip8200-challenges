import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedScheduleLift

set_option warningAsError true

/-! Cached endian masks for the generic paired schedule. The two cached words
increase the internal stack peak, so the complete schedule requires rest < 1016.
Memory and input words remain arbitrary; the public calldata domain is unchanged. -/
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedCachedSchedule

open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Challenge.EvmProof.Word
open StackRoundTrace DenseScheduleTemplate

private theorem word_add_assoc (u v w : UInt256) :
    (u + v) + w = u + (v + w) := by
  apply word_ext
  change ((u.val + v.val) + w.val).val = (u.val + (v.val + w.val)).val
  simp [Fin.add_def, Nat.add_assoc]

private theorem word_add_ofNat_assoc (u : UInt256) (a b : Nat) :
    (u + UInt256.ofNat a) + UInt256.ofNat b = u + UInt256.ofNat (a + b) := by
  rw [word_add_assoc, Challenge.EvmProof.Word.ofNat_add_mod]

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

private theorem add_assoc_explicit (u v w : UInt256) :
    UInt256.add (UInt256.add u v) w = UInt256.add u (UInt256.add v w) := by
  exact word_add_assoc u v w

private theorem add_assoc_explicit_hAdd (u v w : UInt256) :
    (UInt256.add u v) + w = u + (v + w) := by
  exact word_add_assoc u v w

private theorem add_assoc_hAdd_explicit (u v w : UInt256) :
    UInt256.add (u + v) w = u + (v + w) := by
  exact word_add_assoc u v w

def cachedStage (shift : Nat) (slot : Fin 16) : List Instr :=
  [dup1, dup1, push1 (UInt256.ofNat shift), op .SHR, op .XOR,
    .op (.Dup ⟨slot⟩), op .AND, endianFactorPush shift, op .MUL, op .XOR]

theorem run_cachedStage (s : State) (pc value : UInt256)
    (shift : Nat) (mask : UInt256) (slot : Fin 16) (rest : List UInt256)
    (hstack : rest.length < 1020)
    (hcase : (shift = 8 ∧ mask = mask8) ∨ (shift = 16 ∧ mask = mask16))
    (hlookup : ∀ a b : UInt256, (a :: b :: rest)[slot.val]? = some mask)
    (hrun : s.halt = .Running) :
    runInstrSeq (cachedStage shift slot) {s with pc := pc, stack := value :: rest} =
      some (DenseScheduleTrace.stageState s (pcAfter pc (cachedStage shift slot))
        value shift mask rest) := by
  have hcap (m : Nat) (hm : m ≤ 4) : rest.length + m < 1024 := by omega
  have hcap2 : rest.length + 1 + 1 < 1024 := by omega
  have hcap3 : rest.length + 1 + 1 + 1 < 1024 := by omega
  have hcap4 : rest.length + 1 + 1 + 1 + 1 < 1024 := by omega
  have hsemantic :
      UInt256.xor (UInt256.mul (endianFactor shift)
        (UInt256.land mask (UInt256.xor
          (UInt256.shiftRight value (UInt256.ofNat shift)) value))) value =
        packedStage value shift mask := by
    rw [Word.land_comm mask]
    rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simpa only [multipliedStage, endianDelta, endianFactor] using
        DenseEndianMultiply.multipliedStage8_eq_packedStage value
    · simpa only [multipliedStage, endianDelta, endianFactor] using
        DenseEndianMultiply.multipliedStage16_eq_packedStage value
  rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals simp only [endianFactor] at hsemantic
  all_goals norm_num at hsemantic
  all_goals
    simp [cachedStage, endianFactorPush, endianFactor, op, push1, push2, push3,
      dup1, DenseScheduleTrace.stageState, runInstrSeq, Stepper.runInstr,
      pcAfter, hrun, hcap, hcap2, hcap3, hcap4, hlookup, UInt256.succ, Instr.size,
      Challenge.EvmProof.Word.ofNat_add_mod, word_add_assoc]
    rw [add_ofNat_assoc pc 1 1]
    repeat first
      | rw [add_ofNat_assoc_hAdd]
      | rw [add_ofNat_assoc_add]
      | rw [add_ofNat_assoc]
    simp only [word_add_assoc]
    simp [Challenge.EvmProof.Word.ofNat_add_mod]
    exact hsemantic

def cachedInitial : List Instr :=
  [op .JUMPDEST, .push ⟨31, by decide⟩ mask8, .push ⟨30, by decide⟩ mask16,
    .op (.Swap ⟨1, by decide⟩), dup1, op .MLOAD, swap1,
    push1 (UInt256.ofNat 32), op .ADD, op .MLOAD]

theorem run_cachedInitial (s : State) (pc messageOffset returnPC : UInt256)
    (rest : List UInt256) (hstack : rest.length < 1016) (hrun : s.halt = .Running) :
    runInstrSeq cachedInitial (scheduleEntry s pc messageOffset returnPC rest) =
      some {s with
        pc := pcAfter pc cachedInitial
        stack := inputWord1 s messageOffset :: inputWord0 s messageOffset ::
          mask8 :: mask16 :: returnPC :: rest
        activeWords := loadedActiveWords s messageOffset} := by
  have hcap (m : Nat) (hm : m ≤ 8) : rest.length + m < 1024 := by omega
  have hswap1 (u v : UInt256) (rho : List UInt256) :
      (u :: v :: rho).exchange 0 1 = some (v :: u :: rho) := by
    simpa using YulEvmCompiler.exchange_swap u v ([] : List UInt256) rho
  have hswap2 (u v w : UInt256) (rho : List UInt256) :
      (u :: v :: w :: rho).exchange 0 2 = some (w :: v :: u :: rho) := by
    simpa using YulEvmCompiler.exchange_swap u w [v] rho
  have h32 : UInt256.ofNat 32 + messageOffset = messageOffset + UInt256.ofNat 32 :=
    word_add_comm _ _
  simp [cachedInitial, scheduleEntry, inputWord0, inputWord1,
    loadedActiveWords, activeAfterWord, op, push1, dup1, swap1,
    runInstrSeq, Stepper.runInstr, pcAfter, hrun, hcap, hswap1, hswap2, h32,
    word_add_assoc, Nat.add_assoc,
    State.activeWordsAfterUInt256, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod,
    UInt256.succ, Instr.size]
  repeat first
    | rw [add_ofNat_assoc_hAdd]
    | rw [add_ofNat_assoc_add]
    | rw [add_ofNat_assoc]
  rw [word_add_ofNat_assoc]

open PairedScheduleMemory PairedScheduleHalves
open PairedScheduleCombined PairedScheduleContract

def cachedReversedHalf (first : Nat) (slot8 slot16 : Fin 16) : List Instr :=
  (cachedStage 8 slot8 ++ cachedStage 16 slot16) ++ halfTemplate first

theorem run_cachedReversedHalf (s : State) (pc value : UInt256)
    (first : Nat) (slot8 slot16 : Fin 16) (rest : List UInt256)
    (hstack : rest.length < 1020) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) (hfirst : first + 8 ≤ 16)
    (hlookup8 : ∀ a b : UInt256, (a :: b :: rest)[slot8.val]? = some mask8)
    (hlookup16 : ∀ a b : UInt256, (a :: b :: rest)[slot16.val]? = some mask16) :
    runInstrSeq (cachedReversedHalf first slot8 slot16)
        {s with pc := pc, stack := value :: rest} =
      some {s with
        pc := pcAfter pc (cachedReversedHalf first slot8 slot16)
        stack := rest
        memory := storeCells s.memory (halfWords (packedWord value) first) first 8} := by
  have h1 := run_cachedStage s pc value 8 mask8 slot8 rest hstack
    (Or.inl ⟨rfl, rfl⟩) hlookup8 hrun
  dsimp only [DenseScheduleTrace.stageState] at h1
  have h2 := run_cachedStage s (pcAfter pc (cachedStage 8 slot8))
    (packedStage value 8 mask8) 16 mask16 slot16 rest hstack
    (Or.inr ⟨rfl, rfl⟩) hlookup16 hrun
  dsimp only [DenseScheduleTrace.stageState] at h2
  have h12 := DenseScheduleTrace.runInstrSeq_append_running h1 (by exact hrun) h2
  have h3 := run_halfTemplate s
    (pcAfter (pcAfter pc (cachedStage 8 slot8)) (cachedStage 16 slot16))
    (packedWord value) first rest hstack hrun hactive hfirst
  have hjoin := DenseScheduleTrace.runInstrSeq_append_running h12 (by exact hrun) h3
  simpa only [cachedReversedHalf, DenseScheduleTrace.pcAfter_append] using hjoin

def upperTemplate : List Instr := cachedReversedHalf 8 ⟨3, by decide⟩ ⟨4, by decide⟩
def lowerTemplate : List Instr := cachedReversedHalf 0 ⟨2, by decide⟩ ⟨3, by decide⟩
def cleanupTemplate : List Instr := [op .POP, op .POP]

theorem run_cleanupTemplate (s : State) (pc a b : UInt256) (rest : List UInt256)
    (hstack : rest.length < 1022) (hrun : s.halt = .Running) :
    runInstrSeq cleanupTemplate {s with pc := pc, stack := a :: b :: rest} =
      some {s with pc := pcAfter pc cleanupTemplate, stack := rest} := by
  have hcap1 : rest.length + 1 < 1024 := by omega
  have hcap2 : rest.length + 1 + 1 < 1024 := by omega
  simp [cleanupTemplate, op, runInstrSeq, Stepper.runInstr, pcAfter, hrun,
    hcap1, hcap2, UInt256.succ, Instr.size]
  rfl

def fullTemplate : List Instr :=
  (((cachedInitial ++ upperTemplate) ++ lowerTemplate) ++ sentinelTemplate) ++ cleanupTemplate

theorem run_fullTemplate (s : State) (pc messageOffset returnPC : UInt256)
    (rest : List UInt256) (hstack : rest.length < 1016) (hrun : s.halt = .Running)
    (hactive : 23 ≤ (loadedActiveWords s messageOffset).toNat) :
    runInstrSeq fullTemplate (scheduleEntry s pc messageOffset returnPC rest) =
      some {s with
        pc := pcAfter pc fullTemplate
        stack := returnPC :: rest
        memory := normalizedMemory s.memory (scheduleWords s messageOffset)
        activeWords := loadedActiveWords s messageOffset} := by
  have h1 := run_cachedInitial s pc messageOffset returnPC rest hstack hrun
  have h2 := run_cachedReversedHalf
    {s with activeWords := loadedActiveWords s messageOffset}
    (pcAfter pc cachedInitial) (inputWord1 s messageOffset) 8 ⟨3, by decide⟩ ⟨4, by decide⟩
    (inputWord0 s messageOffset :: mask8 :: mask16 :: returnPC :: rest)
    (by simp only [List.length_cons]; omega) hrun hactive (by decide)
    (by intros; rfl) (by intros; rfl)
  have h12 := DenseScheduleTrace.runInstrSeq_append_running h1 (by exact hrun) h2
  have h3 := run_cachedReversedHalf
    {s with
      activeWords := loadedActiveWords s messageOffset
      memory := storeCells s.memory (halfWords (packedInput1 s messageOffset) 8) 8 8}
    (pcAfter (pcAfter pc cachedInitial) upperTemplate)
    (inputWord0 s messageOffset) 0 ⟨2, by decide⟩ ⟨3, by decide⟩
    (mask8 :: mask16 :: returnPC :: rest)
    (by simp only [List.length_cons]; omega) hrun hactive (by decide)
    (by intros; rfl) (by intros; rfl)
  have h123 := DenseScheduleTrace.runInstrSeq_append_running h12 (by exact hrun) h3
  have h4 := run_sentinelTemplate
    {s with
      activeWords := loadedActiveWords s messageOffset
      memory := storeCells
        (storeCells s.memory (halfWords (packedInput1 s messageOffset) 8) 8 8)
        (halfWords (packedInput0 s messageOffset) 0) 0 8}
    (pcAfter (pcAfter (pcAfter pc cachedInitial) upperTemplate) lowerTemplate)
    (mask8 :: mask16 :: returnPC :: rest)
    (by simp only [List.length_cons]; omega) hrun hactive
  have h1234 := DenseScheduleTrace.runInstrSeq_append_running h123 (by exact hrun) h4
  have h5 := run_cleanupTemplate
    {s with
      activeWords := loadedActiveWords s messageOffset
      memory := writeWord
        (storeCells (storeCells s.memory (halfWords (packedInput1 s messageOffset) 8) 8 8)
          (halfWords (packedInput0 s messageOffset) 0) 0 8)
        (cell 16) (UInt256.ofNat 0)}
    (pcAfter (pcAfter (pcAfter (pcAfter pc cachedInitial) upperTemplate) lowerTemplate)
      sentinelTemplate) mask8 mask16 (returnPC :: rest)
    (by simp only [List.length_cons]; omega) hrun
  have hjoin := DenseScheduleTrace.runInstrSeq_append_running h1234 (by exact hrun) h5
  rw [store_upper_schedule, store_lower_schedule] at hjoin
  simpa only [fullTemplate, upperTemplate, lowerTemplate,
    DenseScheduleTrace.pcAfter_append, normalizedMemory] using hjoin

theorem run_fullTemplate_natural (s : State) (pc returnPC : UInt256)
    (p : Nat) (rest : List UInt256)
    (hstack : rest.length < 1016) (hrun : s.halt = .Running)
    (hp : 736 ≤ p) (hbound : p + 64 < 2 ^ 256) :
    runInstrSeq fullTemplate (scheduleEntry s pc (UInt256.ofNat p) returnPC rest) =
      some {s with
        pc := pcAfter pc fullTemplate
        stack := returnPC :: rest
        memory := normalizedMemory s.memory (PairedScheduleData.extractedWord s.memory p)
        activeWords := loadedActiveWords s (UInt256.ofNat p)} := by
  have h := run_fullTemplate s pc (UInt256.ofNat p) returnPC rest hstack hrun
    (loaded_active_ge23 s p hp hbound)
  rw [normalizedMemory_congr s.memory (scheduleWords s (UInt256.ofNat p))
    (PairedScheduleData.extractedWord s.memory p)
    (fun i hi => scheduleWords_eq_extracted s p i hi hbound)] at h
  exact h

theorem fullTemplate_length : fullTemplate.length = 157 := by
  norm_num [fullTemplate, cachedInitial, upperTemplate, lowerTemplate, cachedReversedHalf,
    cachedStage, halfTemplate, prefixTemplate, keepTemplate, PairedScheduleStores.firstTemplate,
    PairedScheduleStores.middleTemplate, PairedScheduleStores.lastTemplate,
    PairedSchedulePrimitives.duplicateShiftTemplate, PairedSchedulePrimitives.maskTemplate,
    PairedSchedulePrimitives.storeTemplate, sentinelTemplate, cleanupTemplate]

theorem fullTemplate_byteLength : (assembleBytes fullTemplate).length = 337 := by
  rw [DenseScheduleTemplate.assembleBytes_length]
  norm_num [fullTemplate, cachedInitial, upperTemplate, lowerTemplate, cachedReversedHalf,
    cachedStage, endianFactorPush, endianFactor, halfTemplate, prefixTemplate, keepTemplate,
    PairedScheduleStores.firstTemplate, PairedScheduleStores.middleTemplate,
    PairedScheduleStores.lastTemplate, PairedSchedulePrimitives.duplicateShiftTemplate,
    PairedSchedulePrimitives.maskTemplate, PairedSchedulePrimitives.storeTemplate,
    sentinelTemplate, cleanupTemplate, cell, op, push1, push2, push3, dup1, swap1]

theorem fullTemplate_staticGas : staticGas fullTemplate = 474 := by
  norm_num [staticGas, fullTemplate, cachedInitial, upperTemplate, lowerTemplate, cachedReversedHalf,
    cachedStage, endianFactorPush, endianFactor, halfTemplate, prefixTemplate, keepTemplate,
    PairedScheduleStores.firstTemplate, PairedScheduleStores.middleTemplate,
    PairedScheduleStores.lastTemplate, PairedSchedulePrimitives.duplicateShiftTemplate,
    PairedSchedulePrimitives.maskTemplate, PairedSchedulePrimitives.storeTemplate,
    sentinelTemplate, cleanupTemplate, cell, op, push1, push2, push3, dup1, swap1,
    Challenge.EvmProof.Meter.instrStaticCost, Gas.baseCost]

open StackRoundTemplate

private theorem cachedStage_advances (shift : Nat) (slot : Fin 16) :
    ∀ instruction ∈ cachedStage shift slot, DenseScheduleLift.Advances instruction := by
  intro instruction hmem
  simp only [cachedStage, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact Or.inl (Or.inl (StraightLine.push _ _))
    | exact Or.inl (Or.inl (StraightLine.dup _))
    | exact Or.inl (Or.inl StraightLine.shr)
    | exact Or.inl (Or.inl StraightLine.xor)
    | exact Or.inl (Or.inl StraightLine.and)
    | exact Or.inr (Or.inr rfl)
    | (unfold endianFactorPush; split <;> exact Or.inl (Or.inl (StraightLine.push _ _)))

private theorem cachedInitial_advances :
    ∀ instruction ∈ cachedInitial, DenseScheduleLift.Advances instruction := by
  intro instruction hmem
  simp only [cachedInitial, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact Or.inl (Or.inl (StraightLine.push _ _))
    | exact Or.inl (Or.inl (StraightLine.dup _))
    | exact Or.inl (Or.inl (StraightLine.swap _))
    | exact Or.inl (Or.inl StraightLine.add)
    | exact Or.inl (Or.inl StraightLine.mload)
    | exact Or.inl (Or.inr (Or.inr rfl))

private theorem cachedReversedHalf_advances (first : Nat) (slot8 slot16 : Fin 16)
    (hfirst : first = 0 ∨ first = 8) :
    ∀ instruction ∈ cachedReversedHalf first slot8 slot16,
      DenseScheduleLift.Advances instruction := by
  intro instruction hmem
  simp only [cachedReversedHalf, List.mem_append] at hmem
  rcases hmem with (h8 | h16) | hhalf
  · exact cachedStage_advances 8 slot8 instruction h8
  · exact cachedStage_advances 16 slot16 instruction h16
  · apply PairedScheduleLift.fullTemplate_advances instruction
    simp only [PairedScheduleCombined.fullTemplate, reversedHalfTemplate, List.mem_append]
    rcases hfirst with rfl | rfl
    · exact Or.inl (Or.inr (Or.inr hhalf))
    · exact Or.inl (Or.inl (Or.inr (Or.inr hhalf)))

theorem fullTemplate_advances :
    ∀ instruction ∈ fullTemplate, DenseScheduleLift.Advances instruction := by
  intro instruction hmem
  simp only [fullTemplate, List.mem_append] at hmem
  rcases hmem with (((hi | hu) | hl) | hs) | hc
  · exact cachedInitial_advances instruction hi
  · exact cachedReversedHalf_advances 8 _ _ (Or.inr rfl) instruction hu
  · exact cachedReversedHalf_advances 0 _ _ (Or.inl rfl) instruction hl
  · apply PairedScheduleLift.fullTemplate_advances instruction
    exact List.mem_append_right _ hs
  · simp only [cleanupTemplate, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    all_goals exact Or.inl (Or.inl StraightLine.pop)

theorem runLocatedBlock_fullTemplate {artifact : ProgramArtifact} {fork : Fork}
    (site : GenericRoundSite artifact fork fullTemplate)
    (s : State) (returnPC : UInt256) (p : Nat) (rest : List UInt256)
    (hstack : rest.length < 1016) (hrun : s.halt = .Running)
    (hp : 736 ≤ p) (hbound : p + 64 < 2 ^ 256) :
    Stepper.runLocatedBlock site.path
      (scheduleEntry s site.startPC (UInt256.ofNat p) returnPC rest) =
      some {s with
        pc := site.endPC
        stack := returnPC :: rest
        memory := normalizedMemory s.memory (PairedScheduleData.extractedWord s.memory p)
        activeWords := loadedActiveWords s (UInt256.ofNat p)} := by
  have hend : site.endPC = pcAfter site.startPC fullTemplate := by
    have h := endPC_eq_pcAfter_sites site.sites site.startPC site.endPC
      site.head_eq site.end_eq site.contiguous
    rwa [site.instruction_eq] at h
  rw [DenseScheduleLift.runLocatedBlock_eq_raw site fullTemplate_advances
    (scheduleEntry s site.startPC (UInt256.ofNat p) returnPC rest) rfl]
  have h := run_fullTemplate_natural s site.startPC returnPC p rest hstack hrun hp hbound
  rw [← hend] at h
  exact h

def gasSteps_fullTemplate {artifact : ProgramArtifact} {fork : Fork}
    (site : GenericRoundSite artifact fork fullTemplate)
    (s : State) (returnPC : UInt256) (p : Nat) (rest : List UInt256)
    (hstack : rest.length < 1016) (hrun : s.halt = .Running)
    (hp : 736 ≤ p) (hbound : p + 64 < 2 ^ 256)
    (hcode : s.executionEnv.code = artifact.code) (hfork : s.fork = fork)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (scheduleEntry s site.startPC (UInt256.ofNat p) returnPC rest)
      {s with
        pc := site.endPC
        stack := returnPC :: rest
        memory := normalizedMemory s.memory (PairedScheduleData.extractedWord s.memory p)
        activeWords := loadedActiveWords s (UInt256.ofNat p)} := by
  apply Stepper.runLocatedBlock_sound artifact fork site.path
  · exact hcode
  · exact hfork
  · exact runLocatedBlock_fullTemplate site s returnPC p rest hstack hrun hp hbound
  · exact hrun
  · exact hnp

theorem fullTemplate_exactBytes : assembleBytes fullTemplate =
  (((([
      0x5b, 0x7e, 0xff, 0x00, 0xff, 0x00, 0xff, 0x00, 0xff, 0x00, 0xff, 0x00, 0xff, 0x00, 0xff, 0x00,
      0xff, 0x00, 0xff, 0x00, 0xff, 0x00, 0xff, 0x00, 0xff, 0x00, 0xff, 0x00, 0xff, 0x00, 0xff, 0x00,
      0xff, 0x7d, 0xff, 0xff, 0x00, 0x00, 0xff, 0xff, 0x00, 0x00, 0xff, 0xff, 0x00, 0x00, 0xff, 0xff,
      0x00, 0x00, 0xff, 0xff, 0x00, 0x00, 0xff, 0xff, 0x00, 0x00, 0xff, 0xff, 0x00, 0x00, 0xff, 0xff,
      0x91, 0x80, 0x51, 0x90, 0x60, 0x20, 0x01, 0x51] ++ [
      0x80, 0x80, 0x60, 0x08, 0x1c, 0x18, 0x83, 0x16, 0x61, 0x01, 0x01, 0x02, 0x18, 0x80, 0x80, 0x60,
      0x10, 0x1c, 0x18, 0x84, 0x16, 0x62, 0x01, 0x00, 0x01, 0x02, 0x18, 0x80, 0x60, 0xe0, 0x1c, 0x61,
      0x01, 0xc0, 0x52, 0x80, 0x60, 0xc0, 0x1c, 0x63, 0xff, 0xff, 0xff, 0xff, 0x16, 0x61, 0x01, 0xe0,
      0x52, 0x80, 0x60, 0xa0, 0x1c, 0x63, 0xff, 0xff, 0xff, 0xff, 0x16, 0x61, 0x02, 0x00, 0x52, 0x80,
      0x60, 0x80, 0x1c, 0x63, 0xff, 0xff, 0xff, 0xff, 0x16, 0x61, 0x02, 0x20, 0x52, 0x80, 0x60, 0x60,
      0x1c, 0x63, 0xff, 0xff, 0xff, 0xff, 0x16, 0x61, 0x02, 0x40, 0x52, 0x80, 0x60, 0x40, 0x1c, 0x63,
      0xff, 0xff, 0xff, 0xff, 0x16, 0x61, 0x02, 0x60, 0x52, 0x80, 0x60, 0x20, 0x1c, 0x63, 0xff, 0xff,
      0xff, 0xff, 0x16, 0x61, 0x02, 0x80, 0x52, 0x63, 0xff, 0xff, 0xff, 0xff, 0x16, 0x61, 0x02, 0xa0,
      0x52]) ++ [
      0x80, 0x80, 0x60, 0x08, 0x1c, 0x18, 0x82, 0x16, 0x61, 0x01, 0x01, 0x02, 0x18, 0x80, 0x80, 0x60,
      0x10, 0x1c, 0x18, 0x83, 0x16, 0x62, 0x01, 0x00, 0x01, 0x02, 0x18, 0x80, 0x60, 0xe0, 0x1c, 0x61,
      0x00, 0xc0, 0x52, 0x80, 0x60, 0xc0, 0x1c, 0x63, 0xff, 0xff, 0xff, 0xff, 0x16, 0x61, 0x00, 0xe0,
      0x52, 0x80, 0x60, 0xa0, 0x1c, 0x63, 0xff, 0xff, 0xff, 0xff, 0x16, 0x61, 0x01, 0x00, 0x52, 0x80,
      0x60, 0x80, 0x1c, 0x63, 0xff, 0xff, 0xff, 0xff, 0x16, 0x61, 0x01, 0x20, 0x52, 0x80, 0x60, 0x60,
      0x1c, 0x63, 0xff, 0xff, 0xff, 0xff, 0x16, 0x61, 0x01, 0x40, 0x52, 0x80, 0x60, 0x40, 0x1c, 0x63,
      0xff, 0xff, 0xff, 0xff, 0x16, 0x61, 0x01, 0x60, 0x52, 0x80, 0x60, 0x20, 0x1c, 0x63, 0xff, 0xff,
      0xff, 0xff, 0x16, 0x61, 0x01, 0x80, 0x52, 0x63, 0xff, 0xff, 0xff, 0xff, 0x16, 0x61, 0x01, 0xa0,
      0x52]) ++ [
      0x5f, 0x61, 0x02, 0xc0, 0x52]) ++ [
      0x50, 0x50]) := by
  have hi : assembleBytes cachedInitial =
    [
      0x5b, 0x7e, 0xff, 0x00, 0xff, 0x00, 0xff, 0x00, 0xff, 0x00, 0xff, 0x00, 0xff, 0x00, 0xff, 0x00,
      0xff, 0x00, 0xff, 0x00, 0xff, 0x00, 0xff, 0x00, 0xff, 0x00, 0xff, 0x00, 0xff, 0x00, 0xff, 0x00,
      0xff, 0x7d, 0xff, 0xff, 0x00, 0x00, 0xff, 0xff, 0x00, 0x00, 0xff, 0xff, 0x00, 0x00, 0xff, 0xff,
      0x00, 0x00, 0xff, 0xff, 0x00, 0x00, 0xff, 0xff, 0x00, 0x00, 0xff, 0xff, 0x00, 0x00, 0xff, 0xff,
      0x91, 0x80, 0x51, 0x90, 0x60, 0x20, 0x01, 0x51] := by decide
  have hu : assembleBytes upperTemplate =
    [
      0x80, 0x80, 0x60, 0x08, 0x1c, 0x18, 0x83, 0x16, 0x61, 0x01, 0x01, 0x02, 0x18, 0x80, 0x80, 0x60,
      0x10, 0x1c, 0x18, 0x84, 0x16, 0x62, 0x01, 0x00, 0x01, 0x02, 0x18, 0x80, 0x60, 0xe0, 0x1c, 0x61,
      0x01, 0xc0, 0x52, 0x80, 0x60, 0xc0, 0x1c, 0x63, 0xff, 0xff, 0xff, 0xff, 0x16, 0x61, 0x01, 0xe0,
      0x52, 0x80, 0x60, 0xa0, 0x1c, 0x63, 0xff, 0xff, 0xff, 0xff, 0x16, 0x61, 0x02, 0x00, 0x52, 0x80,
      0x60, 0x80, 0x1c, 0x63, 0xff, 0xff, 0xff, 0xff, 0x16, 0x61, 0x02, 0x20, 0x52, 0x80, 0x60, 0x60,
      0x1c, 0x63, 0xff, 0xff, 0xff, 0xff, 0x16, 0x61, 0x02, 0x40, 0x52, 0x80, 0x60, 0x40, 0x1c, 0x63,
      0xff, 0xff, 0xff, 0xff, 0x16, 0x61, 0x02, 0x60, 0x52, 0x80, 0x60, 0x20, 0x1c, 0x63, 0xff, 0xff,
      0xff, 0xff, 0x16, 0x61, 0x02, 0x80, 0x52, 0x63, 0xff, 0xff, 0xff, 0xff, 0x16, 0x61, 0x02, 0xa0,
      0x52] := by decide
  have hl : assembleBytes lowerTemplate =
    [
      0x80, 0x80, 0x60, 0x08, 0x1c, 0x18, 0x82, 0x16, 0x61, 0x01, 0x01, 0x02, 0x18, 0x80, 0x80, 0x60,
      0x10, 0x1c, 0x18, 0x83, 0x16, 0x62, 0x01, 0x00, 0x01, 0x02, 0x18, 0x80, 0x60, 0xe0, 0x1c, 0x61,
      0x00, 0xc0, 0x52, 0x80, 0x60, 0xc0, 0x1c, 0x63, 0xff, 0xff, 0xff, 0xff, 0x16, 0x61, 0x00, 0xe0,
      0x52, 0x80, 0x60, 0xa0, 0x1c, 0x63, 0xff, 0xff, 0xff, 0xff, 0x16, 0x61, 0x01, 0x00, 0x52, 0x80,
      0x60, 0x80, 0x1c, 0x63, 0xff, 0xff, 0xff, 0xff, 0x16, 0x61, 0x01, 0x20, 0x52, 0x80, 0x60, 0x60,
      0x1c, 0x63, 0xff, 0xff, 0xff, 0xff, 0x16, 0x61, 0x01, 0x40, 0x52, 0x80, 0x60, 0x40, 0x1c, 0x63,
      0xff, 0xff, 0xff, 0xff, 0x16, 0x61, 0x01, 0x60, 0x52, 0x80, 0x60, 0x20, 0x1c, 0x63, 0xff, 0xff,
      0xff, 0xff, 0x16, 0x61, 0x01, 0x80, 0x52, 0x63, 0xff, 0xff, 0xff, 0xff, 0x16, 0x61, 0x01, 0xa0,
      0x52] := by decide
  have hs : assembleBytes sentinelTemplate =
    [
      0x5f, 0x61, 0x02, 0xc0, 0x52] := by decide
  have hc : assembleBytes cleanupTemplate =
    [
      0x50, 0x50] := by decide
  have h12 := (assembleBytes_append cachedInitial upperTemplate).trans
    (congrArg₂ List.append hi hu)
  have h123 := (assembleBytes_append (cachedInitial ++ upperTemplate) lowerTemplate).trans
    (congrArg₂ List.append h12 hl)
  have h1234 := (assembleBytes_append ((cachedInitial ++ upperTemplate) ++ lowerTemplate)
    sentinelTemplate).trans (congrArg₂ List.append h123 hs)
  exact (assembleBytes_append (((cachedInitial ++ upperTemplate) ++ lowerTemplate) ++
    sentinelTemplate) cleanupTemplate).trans (congrArg₂ List.append h1234 hc)

#print axioms run_cachedStage
#print axioms run_cachedInitial
#print axioms run_cachedReversedHalf
#print axioms run_cleanupTemplate
#print axioms run_fullTemplate
#print axioms run_fullTemplate_natural
#print axioms fullTemplate_length
#print axioms fullTemplate_byteLength
#print axioms fullTemplate_staticGas
#print axioms fullTemplate_advances
#print axioms runLocatedBlock_fullTemplate
#print axioms gasSteps_fullTemplate
#print axioms fullTemplate_exactBytes

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedCachedSchedule
