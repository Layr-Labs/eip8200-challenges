import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedScheduleLift

set_option warningAsError true

/-! Cache MASK32 on an explicit stack slot; arbitrary input words and memory.
The full schedule will require rest < 1015, discharged by the actual rest of length2. -/
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedMask32Cache

open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace DenseScheduleTemplate PairedScheduleMemory

def maskWord : UInt256 := UInt256.ofNat 0xffffffff

def maskTemplate (slot : Fin 16) : List Instr :=
  [.op (.Dup ⟨slot⟩), op .AND]

theorem run_maskTemplate (s : State) (pc value : UInt256) (slot : Fin 16)
    (rest : List UInt256) (hstack : rest.length < 1022)
    (hlookup : (value :: rest)[slot.val]? = some maskWord)
    (hrun : s.halt = .Running) :
    runInstrSeq (maskTemplate slot) {s with pc := pc, stack := value :: rest} =
      some {s with
        pc := pcAfter pc (maskTemplate slot)
        stack := Word.mask32 value :: rest} := by
  have hcap1 : rest.length + 1 < 1024 := by omega
  have hcap2 : rest.length + 1 + 1 < 1024 := by omega
  simp [maskTemplate, op, runInstrSeq, Stepper.runInstr,
    pcAfter, hrun, hcap1, hcap2, hlookup, UInt256.succ, Instr.size,
    maskWord, Word.mask32, Word.land_comm]
  exact ⟨rfl, rfl⟩

#print axioms run_maskTemplate

def middleTemplate (shift address : Nat) (slot : Fin 16) : List Instr :=
  PairedSchedulePrimitives.duplicateShiftTemplate shift ++
    (maskTemplate slot ++ PairedSchedulePrimitives.storeTemplate address)

theorem run_middleTemplate (s : State) (pc value : UInt256)
    (shift address : Nat) (slot : Fin 16)
    (rest : List UInt256) (hstack : rest.length < 1020)
    (hlookup : ∀ a b : UInt256, (a :: b :: rest)[slot.val]? = some maskWord)
    (haddress : address < 2 ^ 256) (hrun : s.halt = .Running) :
    runInstrSeq (middleTemplate shift address slot) {s with pc := pc, stack := value :: rest} =
      some {s with
        pc := pcAfter pc (middleTemplate shift address slot)
        stack := value :: rest
        memory := writeWord s.memory address (Word.mask32
          (UInt256.shiftRight value (UInt256.ofNat shift)))
        activeWords := UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32)} := by
  have h1 := PairedSchedulePrimitives.run_duplicateShiftTemplate s pc value shift rest hstack hrun
  have h2 := run_maskTemplate s
    (pcAfter pc (PairedSchedulePrimitives.duplicateShiftTemplate shift))
    (UInt256.shiftRight value (UInt256.ofNat shift)) slot (value :: rest)
    (by simp only [List.length_cons]; omega) (hlookup _ _) hrun
  have h3 := PairedSchedulePrimitives.run_storeTemplate s
    (pcAfter (pcAfter pc (PairedSchedulePrimitives.duplicateShiftTemplate shift)) (maskTemplate slot))
    (Word.mask32 (UInt256.shiftRight value (UInt256.ofNat shift)))
    address (value :: rest) (by simp only [List.length_cons]; omega) haddress hrun
  have h23 := DenseScheduleTrace.runInstrSeq_append_running h2 (by exact hrun) h3
  unfold middleTemplate
  rw [DenseScheduleTrace.pcAfter_append, DenseScheduleTrace.pcAfter_append]
  exact DenseScheduleTrace.runInstrSeq_append_running h1 (by exact hrun) h23

#print axioms run_middleTemplate

def lastTemplate (address : Nat) (slot : Fin 16) : List Instr :=
  maskTemplate slot ++ PairedSchedulePrimitives.storeTemplate address

theorem run_lastTemplate (s : State) (pc value : UInt256) (address : Nat)
    (slot : Fin 16) (rest : List UInt256) (hstack : rest.length < 1022)
    (hlookup : (value :: rest)[slot.val]? = some maskWord)
    (haddress : address < 2 ^ 256) (hrun : s.halt = .Running) :
    runInstrSeq (lastTemplate address slot) {s with pc := pc, stack := value :: rest} =
      some {s with
        pc := pcAfter pc (lastTemplate address slot)
        stack := rest
        memory := writeWord s.memory address (Word.mask32 value)
        activeWords := UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32)} := by
  have h1 := run_maskTemplate s pc value slot rest hstack hlookup hrun
  have h2 := PairedSchedulePrimitives.run_storeTemplate s (pcAfter pc (maskTemplate slot))
    (Word.mask32 value) address rest hstack haddress hrun
  unfold lastTemplate
  rw [DenseScheduleTrace.pcAfter_append]
  exact DenseScheduleTrace.runInstrSeq_append_running h1 (by exact hrun) h2

#print axioms run_lastTemplate


open PairedScheduleHalves

def keepTemplate (first j : Nat) (slot : Fin 14) : List Instr :=
  if j = 0 then PairedScheduleStores.firstTemplate (cell (first + j))
  else middleTemplate (32 * (7 - j)) (cell (first + j)) ⟨slot.val + 2, by omega⟩

def prefixTemplate (first : Nat) (slot : Fin 14) : Nat → List Instr
  | 0 => []
  | n + 1 => prefixTemplate first slot n ++ keepTemplate first n slot

def halfTemplate (first : Nat) (slot : Fin 14) : List Instr :=
  prefixTemplate first slot 7 ++ lastTemplate (cell (first + 7)) ⟨slot.val + 1, by omega⟩

theorem run_keepTemplate (s : State) (pc value : UInt256)
    (first j : Nat) (slot : Fin 14) (rest : List UInt256)
    (hstack : rest.length < 1020) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) (hslot : first + j ≤ 16) (hj : j < 7)
    (hlookup : rest[slot.val]? = some maskWord) :
    runInstrSeq (keepTemplate first j slot) {s with pc := pc, stack := value :: rest} =
      some {s with
        pc := pcAfter pc (keepTemplate first j slot)
        stack := value :: rest
        memory := writeWord s.memory (cell (first + j)) (chunkValue value j)} := by
  by_cases hzero : j = 0
  · have h := PairedScheduleStores.run_firstTemplate s pc value (cell (first + j)) rest hstack
      (schedule_cell_lt (first + j) hslot) hrun
    rw [active_wrapped_cell_preserved s.activeWords (first + j) hactive hslot] at h
    simpa only [keepTemplate, chunkValue, if_pos hzero] using h
  · have hseven : j ≠ 7 := by omega
    have h := run_middleTemplate s pc value (32 * (7 - j)) (cell (first + j))
      ⟨slot.val + 2, by omega⟩ rest hstack
      (by intros; simpa only [List.getElem?_cons_succ] using hlookup)
      (schedule_cell_lt (first + j) hslot) hrun
    rw [active_wrapped_cell_preserved s.activeWords (first + j) hactive hslot] at h
    simpa only [keepTemplate, chunkValue, if_neg hzero, if_neg hseven] using h

#print axioms run_keepTemplate

theorem run_prefixTemplate (s : State) (pc value : UInt256)
    (first n : Nat) (slot : Fin 14) (rest : List UInt256)
    (hstack : rest.length < 1020) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) (hfirst : first + 8 ≤ 16) (hn : n ≤ 7)
    (hlookup : rest[slot.val]? = some maskWord) :
    runInstrSeq (prefixTemplate first slot n) {s with pc := pc, stack := value :: rest} =
      some {s with
        pc := pcAfter pc (prefixTemplate first slot n)
        stack := value :: rest
        memory := storeCells s.memory (halfWords value first) first n} := by
  induction n with
  | zero =>
    simp only [prefixTemplate, runInstrSeq, pcAfter, storeCells]
  | succ n ih =>
    have h1 := ih (by omega)
    have h2 := run_keepTemplate
      {s with memory := storeCells s.memory (halfWords value first) first n}
      (pcAfter pc (prefixTemplate first slot n)) value first n slot rest
      hstack hrun hactive (by omega) (by omega) hlookup
    have hjoin := DenseScheduleTrace.runInstrSeq_append_running h1 (by exact hrun) h2
    simpa only [prefixTemplate, DenseScheduleTrace.pcAfter_append, storeCells,
      halfWords, Nat.add_sub_cancel_left] using hjoin

#print axioms run_prefixTemplate

theorem run_halfTemplate (s : State) (pc value : UInt256)
    (first : Nat) (slot : Fin 14) (rest : List UInt256)
    (hstack : rest.length < 1020) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) (hfirst : first + 8 ≤ 16)
    (hlookup : rest[slot.val]? = some maskWord) :
    runInstrSeq (halfTemplate first slot) {s with pc := pc, stack := value :: rest} =
      some {s with
        pc := pcAfter pc (halfTemplate first slot)
        stack := rest
        memory := storeCells s.memory (halfWords value first) first 8} := by
  have h1 := run_prefixTemplate s pc value first 7 slot rest hstack hrun hactive hfirst
    (by decide) hlookup
  have h2 := run_lastTemplate
    {s with memory := storeCells s.memory (halfWords value first) first 7}
    (pcAfter pc (prefixTemplate first slot 7)) value (cell (first + 7))
    ⟨slot.val + 1, by omega⟩ rest (by omega)
    (by simpa only [List.getElem?_cons_succ] using hlookup)
    (schedule_cell_lt (first + 7) (by omega)) hrun
  rw [active_wrapped_cell_preserved s.activeWords (first + 7) hactive (by omega)] at h2
  have hjoin := DenseScheduleTrace.runInstrSeq_append_running h1 (by exact hrun) h2
  simpa only [halfTemplate, DenseScheduleTrace.pcAfter_append, storeCells,
    halfWords, Nat.add_sub_cancel_left, chunkValue, show ¬(7 = 0) by decide,
    if_false, if_true] using hjoin

#print axioms run_halfTemplate


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
  rw [word_add_ofNat_assoc]

#print axioms run_cachedInitial

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


#print axioms run_cachedStage


open PairedScheduleCombined PairedScheduleContract

def cachedReversedHalf (first : Nat) (slot8 slot16 : Fin 16) (slot32 : Fin 14) : List Instr :=
  (cachedStage 8 slot8 ++ cachedStage 16 slot16) ++ halfTemplate first slot32

theorem run_cachedReversedHalf (s : State) (pc value : UInt256)
    (first : Nat) (slot8 slot16 : Fin 16) (slot32 : Fin 14) (rest : List UInt256)
    (hstack : rest.length < 1020) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) (hfirst : first + 8 ≤ 16)
    (hlookup8 : ∀ a b : UInt256, (a :: b :: rest)[slot8.val]? = some mask8)
    (hlookup16 : ∀ a b : UInt256, (a :: b :: rest)[slot16.val]? = some mask16)
    (hlookup32 : rest[slot32.val]? = some maskWord) :
    runInstrSeq (cachedReversedHalf first slot8 slot16 slot32)
        {s with pc := pc, stack := value :: rest} =
      some {s with
        pc := pcAfter pc (cachedReversedHalf first slot8 slot16 slot32)
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
    (packedWord value) first slot32 rest hstack hrun hactive hfirst hlookup32
  have hjoin := DenseScheduleTrace.runInstrSeq_append_running h12 (by exact hrun) h3
  simpa only [cachedReversedHalf, DenseScheduleTrace.pcAfter_append] using hjoin

#print axioms run_cachedReversedHalf

def upperTemplate : List Instr :=
  cachedReversedHalf 8 ⟨3, by decide⟩ ⟨5, by decide⟩ ⟨2, by decide⟩
def lowerTemplate : List Instr :=
  cachedReversedHalf 0 ⟨2, by decide⟩ ⟨4, by decide⟩ ⟨1, by decide⟩
def cleanupTemplate : List Instr := [op .POP, op .POP, op .POP]

theorem run_cleanupTemplate (s : State) (pc a b c : UInt256) (rest : List UInt256)
    (hstack : rest.length < 1021) (hrun : s.halt = .Running) :
    runInstrSeq cleanupTemplate {s with pc := pc, stack := a :: b :: c :: rest} =
      some {s with pc := pcAfter pc cleanupTemplate, stack := rest} := by
  have hcap1 : rest.length + 1 < 1024 := by omega
  have hcap2 : rest.length + 1 + 1 < 1024 := by omega
  have hcap3 : rest.length + 1 + 1 + 1 < 1024 := by omega
  simp [cleanupTemplate, op, runInstrSeq, Stepper.runInstr, pcAfter, hrun,
    hcap1, hcap2, hcap3, UInt256.succ, Instr.size]
  rfl

#print axioms run_cleanupTemplate

def fullTemplate : List Instr :=
  (((cachedInitial ++ upperTemplate) ++ lowerTemplate) ++ sentinelTemplate) ++ cleanupTemplate

theorem run_fullTemplate (s : State) (pc messageOffset returnPC : UInt256)
    (rest : List UInt256) (hstack : rest.length < 1015) (hrun : s.halt = .Running)
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
  have h5 := run_cleanupTemplate
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
        stack := returnPC :: rest
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
  norm_num [fullTemplate, cachedInitial, upperTemplate, lowerTemplate, cachedReversedHalf,
    cachedStage, halfTemplate, prefixTemplate, keepTemplate, PairedScheduleStores.firstTemplate,
    middleTemplate, lastTemplate, maskTemplate,
    PairedSchedulePrimitives.duplicateShiftTemplate, PairedSchedulePrimitives.storeTemplate,
    sentinelTemplate, cleanupTemplate]

#print axioms fullTemplate_length

theorem fullTemplate_byteLength : (assembleBytes fullTemplate).length = 285 := by
  rw [DenseScheduleTemplate.assembleBytes_length]
  norm_num [fullTemplate, cachedInitial, upperTemplate, lowerTemplate, cachedReversedHalf,
    cachedStage, endianFactorPush, endianFactor, halfTemplate, prefixTemplate, keepTemplate,
    PairedScheduleStores.firstTemplate, middleTemplate, lastTemplate, maskTemplate,
    PairedSchedulePrimitives.duplicateShiftTemplate, PairedSchedulePrimitives.storeTemplate,
    sentinelTemplate, cleanupTemplate, cell, op, push1, push2, push3, dup1, swap1]

#print axioms fullTemplate_byteLength

theorem fullTemplate_staticGas : staticGas fullTemplate = 479 := by
  norm_num [staticGas, fullTemplate, cachedInitial, upperTemplate, lowerTemplate, cachedReversedHalf,
    cachedStage, endianFactorPush, endianFactor, halfTemplate, prefixTemplate, keepTemplate,
    PairedScheduleStores.firstTemplate, middleTemplate, lastTemplate, maskTemplate,
    PairedSchedulePrimitives.duplicateShiftTemplate, PairedSchedulePrimitives.storeTemplate,
    sentinelTemplate, cleanupTemplate, cell, op, push1, push2, push3, dup1, swap1,
    Meter.instrStaticCost, Gas.baseCost]

#print axioms fullTemplate_staticGas


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
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact Or.inl (Or.inl (StraightLine.push _ _))
    | exact Or.inl (Or.inl (StraightLine.dup _))
    | exact Or.inl (Or.inl (StraightLine.swap _))
    | exact Or.inl (Or.inl StraightLine.add)
    | exact Or.inl (Or.inl StraightLine.mload)
    | exact Or.inl (Or.inr (Or.inr rfl))


private theorem storeAddress_advances (address : Nat) :
    DenseScheduleLift.Advances
      (if address = 192 ∨ address = 224 then
        DenseScheduleTemplate.push1 (UInt256.ofNat address)
       else DenseScheduleTemplate.push2 (UInt256.ofNat address)) := by
  split <;> exact Or.inl (Or.inl (StraightLine.push _ _))

private theorem keepTemplate_advances (first j : Nat) (slot : Fin 14) :
    ∀ instruction ∈ keepTemplate first j slot, DenseScheduleLift.Advances instruction := by
  intro instruction hmem
  unfold keepTemplate at hmem
  split at hmem
  · simp only [PairedScheduleStores.firstTemplate,
      PairedSchedulePrimitives.duplicateShiftTemplate, PairedSchedulePrimitives.storeTemplate,
      List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with (rfl | rfl | rfl) | (rfl | rfl)
    all_goals first
      | exact storeAddress_advances _
      | exact Or.inl (Or.inl (StraightLine.push _ _))
      | exact Or.inl (Or.inl (StraightLine.dup _))
      | exact Or.inl (Or.inl StraightLine.shr)
      | exact Or.inr (Or.inl rfl)
  · simp only [middleTemplate, maskTemplate,
      PairedSchedulePrimitives.duplicateShiftTemplate, PairedSchedulePrimitives.storeTemplate,
      List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with (rfl | rfl | rfl) | ((rfl | rfl) | (rfl | rfl))
    all_goals first
      | exact storeAddress_advances _
      | exact Or.inl (Or.inl (StraightLine.push _ _))
      | exact Or.inl (Or.inl (StraightLine.dup _))
      | exact Or.inl (Or.inl StraightLine.shr)
      | exact Or.inl (Or.inl StraightLine.and)
      | exact Or.inr (Or.inl rfl)

private theorem prefixTemplate_advances (first : Nat) (slot : Fin 14) (n : Nat) :
    ∀ instruction ∈ prefixTemplate first slot n, DenseScheduleLift.Advances instruction := by
  induction n with
  | zero => simp [prefixTemplate]
  | succ n ih =>
    intro instruction hmem
    rcases List.mem_append.mp hmem with hp | hk
    · exact ih instruction hp
    · exact keepTemplate_advances first n slot instruction hk

private theorem halfTemplate_advances (first : Nat) (slot : Fin 14) :
    ∀ instruction ∈ halfTemplate first slot, DenseScheduleLift.Advances instruction := by
  intro instruction hmem
  rcases List.mem_append.mp hmem with hp | hl
  · exact prefixTemplate_advances first slot 7 instruction hp
  · simp only [lastTemplate, maskTemplate, PairedSchedulePrimitives.storeTemplate,
      List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with (rfl | rfl) | (rfl | rfl)
    all_goals first
      | exact storeAddress_advances _
      | exact Or.inl (Or.inl (StraightLine.push _ _))
      | exact Or.inl (Or.inl (StraightLine.dup _))
      | exact Or.inl (Or.inl StraightLine.and)
      | exact Or.inr (Or.inl rfl)

private theorem cachedReversedHalf_advances (first : Nat) (slot8 slot16 : Fin 16)
    (slot32 : Fin 14) :
    ∀ instruction ∈ cachedReversedHalf first slot8 slot16 slot32,
      DenseScheduleLift.Advances instruction := by
  intro instruction hmem
  simp only [cachedReversedHalf, List.mem_append] at hmem
  rcases hmem with (h8 | h16) | hhalf
  · exact cachedStage_advances 8 slot8 instruction h8
  · exact cachedStage_advances 16 slot16 instruction h16
  · exact halfTemplate_advances first slot32 instruction hhalf

theorem fullTemplate_advances :
    ∀ instruction ∈ fullTemplate, DenseScheduleLift.Advances instruction := by
  intro instruction hmem
  simp only [fullTemplate, List.mem_append] at hmem
  rcases hmem with (((hi | hu) | hl) | hs) | hc
  · exact cachedInitial_advances instruction hi
  · exact cachedReversedHalf_advances 8 _ _ _ instruction hu
  · exact cachedReversedHalf_advances 0 _ _ _ instruction hl
  · apply PairedScheduleLift.fullTemplate_advances instruction
    exact List.mem_append_right _ hs
  · simp only [cleanupTemplate, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    all_goals exact Or.inl (Or.inl StraightLine.pop)

#print axioms fullTemplate_advances

theorem runLocatedBlock_fullTemplate {artifact : ProgramArtifact} {fork : Fork}
    (site : GenericRoundSite artifact fork fullTemplate)
    (s : State) (returnPC : UInt256) (p : Nat) (rest : List UInt256)
    (hstack : rest.length < 1015) (hrun : s.halt = .Running)
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
    (hstack : rest.length < 1015) (hrun : s.halt = .Running)
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
    0x50, 0x50, 0x50]) := by
  have h0 : assembleBytes cachedInitial =
    [
      0x5b, 0x63, 0xff, 0xff, 0xff, 0xff, 0x7e, 0xff, 0x00, 0xff, 0x00, 0xff, 0x00, 0xff, 0x00, 0xff,
      0x00, 0xff, 0x00, 0xff, 0x00, 0xff, 0x00, 0xff, 0x00, 0xff, 0x00, 0xff, 0x00, 0xff, 0x00, 0xff,
      0x00, 0xff, 0x00, 0xff, 0x00, 0xff, 0x7d, 0xff, 0xff, 0x00, 0x00, 0xff, 0xff, 0x00, 0x00, 0xff,
      0xff, 0x00, 0x00, 0xff, 0xff, 0x00, 0x00, 0xff, 0xff, 0x00, 0x00, 0xff, 0xff, 0x00, 0x00, 0xff,
      0xff, 0x00, 0x00, 0xff, 0xff, 0x92, 0x80, 0x51, 0x90, 0x60, 0x20, 0x01, 0x51] := by decide
  have h1 : assembleBytes upperTemplate =
    [
      0x80, 0x80, 0x60, 0x08, 0x1c, 0x18, 0x83, 0x16, 0x61, 0x01, 0x01, 0x02, 0x18, 0x80, 0x80, 0x60,
      0x10, 0x1c, 0x18, 0x85, 0x16, 0x62, 0x01, 0x00, 0x01, 0x02, 0x18, 0x80, 0x60, 0xe0, 0x1c, 0x61,
      0x01, 0xc0, 0x52, 0x80, 0x60, 0xc0, 0x1c, 0x84, 0x16, 0x61, 0x01, 0xe0, 0x52, 0x80, 0x60, 0xa0,
      0x1c, 0x84, 0x16, 0x61, 0x02, 0x00, 0x52, 0x80, 0x60, 0x80, 0x1c, 0x84, 0x16, 0x61, 0x02, 0x20,
      0x52, 0x80, 0x60, 0x60, 0x1c, 0x84, 0x16, 0x61, 0x02, 0x40, 0x52, 0x80, 0x60, 0x40, 0x1c, 0x84,
      0x16, 0x61, 0x02, 0x60, 0x52, 0x80, 0x60, 0x20, 0x1c, 0x84, 0x16, 0x61, 0x02, 0x80, 0x52, 0x83,
      0x16, 0x61, 0x02, 0xa0, 0x52] := by decide
  have h2 : assembleBytes lowerTemplate =
    [
      0x80, 0x80, 0x60, 0x08, 0x1c, 0x18, 0x82, 0x16, 0x61, 0x01, 0x01, 0x02, 0x18, 0x80, 0x80, 0x60,
      0x10, 0x1c, 0x18, 0x84, 0x16, 0x62, 0x01, 0x00, 0x01, 0x02, 0x18, 0x80, 0x60, 0xe0, 0x1c, 0x60, 0xc0, 0x52, 0x80, 0x60, 0xc0, 0x1c, 0x83, 0x16, 0x60, 0xe0, 0x52, 0x80, 0x60, 0xa0,
      0x1c, 0x83, 0x16, 0x61, 0x01, 0x00, 0x52, 0x80, 0x60, 0x80, 0x1c, 0x83, 0x16, 0x61, 0x01, 0x20,
      0x52, 0x80, 0x60, 0x60, 0x1c, 0x83, 0x16, 0x61, 0x01, 0x40, 0x52, 0x80, 0x60, 0x40, 0x1c, 0x83,
      0x16, 0x61, 0x01, 0x60, 0x52, 0x80, 0x60, 0x20, 0x1c, 0x83, 0x16, 0x61, 0x01, 0x80, 0x52, 0x82,
      0x16, 0x61, 0x01, 0xa0, 0x52] := by decide
  have h3 : assembleBytes sentinelTemplate =
    [
      0x5f, 0x61, 0x02, 0xc0, 0x52] := by decide
  have h4 : assembleBytes cleanupTemplate =
    [
      0x50, 0x50, 0x50] := by decide
  have h01 := (assembleBytes_append cachedInitial upperTemplate).trans
    (congrArg₂ List.append h0 h1)
  have h012 := (assembleBytes_append (cachedInitial ++ upperTemplate) lowerTemplate).trans
    (congrArg₂ List.append h01 h2)
  have h0123 := (assembleBytes_append ((cachedInitial ++ upperTemplate) ++ lowerTemplate)
    sentinelTemplate).trans (congrArg₂ List.append h012 h3)
  exact (assembleBytes_append (((cachedInitial ++ upperTemplate) ++ lowerTemplate) ++
    sentinelTemplate) cleanupTemplate).trans (congrArg₂ List.append h0123 h4)

#print axioms fullTemplate_exactBytes

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedMask32Cache
