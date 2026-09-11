import Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedCoreCommon
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedDivMaskCache
/-!
The decoder retains six schedule words below the core's working registers.
`originalLower` is a virtual execution model: its PC 599 is used only to
identify written memory with the established store contract. The actual
lower sequence starts at PC 584, and the complete physical decoder at 429.
The located-site certificate is supplied by PairedAllInlineBoundarySites.
-/
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedSchedule
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace StackRoundTemplate PairedHelperBooleanTrace
open DenseScheduleTemplate PairedScheduleMemory PairedScheduleHalves PairedScheduleCombined
open PairedMask32Cache PairedScheduleContract CachedCoreCommon
def originalLower : List Instr :=
  [ .op (.Dup ⟨0, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 224),
    .op .SHR,
    .push ⟨1, by decide⟩ (UInt256.ofNat 192),
    .op .MSTORE,
    .op (.Dup ⟨0, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 192),
    .op .SHR,
    .op (.Dup ⟨3, by decide⟩),
    .op .AND,
    .push ⟨1, by decide⟩ (UInt256.ofNat 224),
    .op .MSTORE,
    .op (.Dup ⟨0, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 160),
    .op .SHR,
    .op (.Dup ⟨3, by decide⟩),
    .op .AND,
    .push ⟨2, by decide⟩ (UInt256.ofNat 256),
    .op .MSTORE,
    .op (.Dup ⟨0, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 128),
    .op .SHR,
    .op (.Dup ⟨3, by decide⟩),
    .op .AND,
    .push ⟨2, by decide⟩ (UInt256.ofNat 288),
    .op .MSTORE,
    .op (.Dup ⟨0, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 96),
    .op .SHR,
    .op (.Dup ⟨3, by decide⟩),
    .op .AND,
    .push ⟨2, by decide⟩ (UInt256.ofNat 320),
    .op .MSTORE,
    .op (.Dup ⟨0, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 64),
    .op .SHR,
    .op (.Dup ⟨3, by decide⟩),
    .op .AND,
    .push ⟨2, by decide⟩ (UInt256.ofNat 352),
    .op .MSTORE,
    .op (.Dup ⟨0, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 32),
    .op .SHR,
    .op (.Dup ⟨3, by decide⟩),
    .op .AND,
    .push ⟨2, by decide⟩ (UInt256.ofNat 384),
    .op .MSTORE,
    .op (.Dup ⟨2, by decide⟩),
    .op .AND,
    .push ⟨2, by decide⟩ (UInt256.ofNat 416),
    .op .MSTORE,
    .push ⟨0, by decide⟩ (UInt256.ofNat 0),
    .push ⟨2, by decide⟩ (UInt256.ofNat 704),
    .op .MSTORE,
    .op .POP,
    .op .POP,
    .op .POP ]
def actualLower : List Instr :=
  [ .op (.Dup ⟨0, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 224),
    .op .SHR,
    .push ⟨1, by decide⟩ (UInt256.ofNat 192),
    .op .MSTORE,
    .op (.Dup ⟨0, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 192),
    .op .SHR,
    .op (.Dup ⟨3, by decide⟩),
    .op .AND,
    .push ⟨1, by decide⟩ (UInt256.ofNat 224),
    .op .MSTORE,
    .op (.Dup ⟨0, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 160),
    .op .SHR,
    .op (.Dup ⟨3, by decide⟩),
    .op .AND,
    .op (.Dup ⟨0, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 256),
    .op .MSTORE,
    .op (.Dup ⟨1, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 128),
    .op .SHR,
    .op (.Dup ⟨4, by decide⟩),
    .op .AND,
    .op (.Dup ⟨0, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 288),
    .op .MSTORE,
    .op (.Dup ⟨2, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 96),
    .op .SHR,
    .op (.Dup ⟨5, by decide⟩),
    .op .AND,
    .op (.Dup ⟨0, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 320),
    .op .MSTORE,
    .op (.Dup ⟨3, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 64),
    .op .SHR,
    .op (.Dup ⟨6, by decide⟩),
    .op .AND,
    .op (.Dup ⟨0, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 352),
    .op .MSTORE,
    .op (.Dup ⟨4, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 32),
    .op .SHR,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND,
    .op (.Dup ⟨0, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 384),
    .op .MSTORE,
    .op (.Swap ⟨4, by decide⟩),
    .op (.Dup ⟨7, by decide⟩),
    .op .AND,
    .op (.Dup ⟨0, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 416),
    .op .MSTORE,
    .push ⟨0, by decide⟩ (UInt256.ofNat 0),
    .push ⟨2, by decide⟩ (UInt256.ofNat 704),
    .op .MSTORE,
    .op (.Swap ⟨5, by decide⟩),
    .op .POP,
    .op (.Swap ⟨5, by decide⟩),
    .op .POP,
    .op (.Swap ⟨5, by decide⟩),
    .op .POP ]
def rawMemory (memory : ByteArray) (value : UInt256) : ByteArray :=
  (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord (writeWord memory 192 (UInt256.shiftRight value (UInt256.ofNat 224))) 224 (UInt256.land maskWord (UInt256.shiftRight value (UInt256.ofNat 192)))) 256 (UInt256.land maskWord (UInt256.shiftRight value (UInt256.ofNat 160)))) 288 (UInt256.land maskWord (UInt256.shiftRight value (UInt256.ofNat 128)))) 320 (UInt256.land maskWord (UInt256.shiftRight value (UInt256.ofNat 96)))) 352 (UInt256.land maskWord (UInt256.shiftRight value (UInt256.ofNat 64)))) 384 (UInt256.land maskWord (UInt256.shiftRight value (UInt256.ofNat 32)))) 416 (UInt256.land maskWord value)) 704 (UInt256.ofNat 0))
def rawCache (value : UInt256) : List UInt256 :=
  [(UInt256.land maskWord (UInt256.shiftRight value (UInt256.ofNat 128))),
   (UInt256.land maskWord (UInt256.shiftRight value (UInt256.ofNat 160))),
   (UInt256.land maskWord (UInt256.shiftRight value (UInt256.ofNat 32))),
   (UInt256.land maskWord value),
   (UInt256.land maskWord (UInt256.shiftRight value (UInt256.ofNat 64))),
   (UInt256.land maskWord (UInt256.shiftRight value (UInt256.ofNat 96)))]
theorem cache_rawMemory (memory : ByteArray) (value : UInt256) :
    cache (rawMemory memory value) = rawCache value := by
  simp (discharger := omega) [cache, rawCache, rawMemory, read_writeWord, read_writeWord_disjoint]

theorem run_original_raw (s : State) (value returnPC : UInt256) (rest : List UInt256)
    (hstack : rest.length ≤ 996) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq originalLower {s with pc := (UInt256.ofNat 599), stack := value :: mask8 :: maskWord :: mask16 :: returnPC :: rest} =
      some {s with pc := pcAfter (UInt256.ofNat 599) originalLower, stack := (returnPC :: rest), memory := rawMemory s.memory value} := by
  have hcap (n : Nat) (hn : n ≤ 26) : rest.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) = s.activeWords :=
    active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [originalLower, rawMemory, rawCache, writeWord,
    runInstrSeq, Stepper.runInstr, pcAfter, UInt256.succ, Instr.size,
    List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hcap,
    State.activeWordsAfterUInt256, hactiveAt, Challenge.EvmProof.Word.word_toNat_ofNat]
  all_goals repeat first | apply And.intro | rfl
theorem run_actual_raw (s : State) (value returnPC : UInt256) (rest : List UInt256)
    (hstack : rest.length ≤ 996) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq actualLower {s with pc := (UInt256.ofNat 584), stack := value :: mask8 :: maskWord :: mask16 :: returnPC :: rest} =
      some {s with pc := pcAfter (UInt256.ofNat 584) actualLower, stack := rawCache value ++ (returnPC :: rest), memory := rawMemory s.memory value} := by
  have hcap (n : Nat) (hn : n ≤ 26) : rest.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) = s.activeWords :=
    active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [actualLower, rawMemory, rawCache, writeWord,
    runInstrSeq, Stepper.runInstr, pcAfter, UInt256.succ, Instr.size,
    List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hcap,
    State.activeWordsAfterUInt256, hactiveAt, Challenge.EvmProof.Word.word_toNat_ofNat]
  all_goals repeat first | apply And.intro | rfl
def modelMemory (memory : ByteArray) (value : UInt256) : ByteArray :=
  writeWord (storeCells memory (halfWords value 0) 0 8) (cell 16) (UInt256.ofNat 0)

theorem run_original_model (s : State) (pc value returnPC : UInt256) (rest : List UInt256)
    (hstack : rest.length ≤ 996) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq originalLower {s with pc := pc, stack := value :: mask8 :: maskWord :: mask16 :: returnPC :: rest} =
      some {s with pc := pcAfter pc originalLower, stack := returnPC :: rest, memory := modelMemory s.memory value} := by
  have h1 := run_halfTemplate s pc value 0 ⟨1, by decide⟩
    (mask8 :: maskWord :: mask16 :: returnPC :: rest)
    (by simp only [List.length_cons]; omega) hrun hactive (by decide) rfl
  have h2 := run_sentinelTemplate
    {s with memory := storeCells s.memory (halfWords value 0) 0 8}
    (pcAfter pc (halfTemplate 0 ⟨1, by decide⟩)) (mask8 :: maskWord :: mask16 :: returnPC :: rest)
    (by simp only [List.length_cons]; omega) hrun hactive
  have h3 := run_cleanupTemplate {s with memory := modelMemory s.memory value}
    (pcAfter (pcAfter pc (halfTemplate 0 ⟨1, by decide⟩)) sentinelTemplate)
    mask8 maskWord mask16 (returnPC :: rest)
    (by simp only [List.length_cons]; omega) hrun
  have h := DenseScheduleTrace.runInstrSeq_append_running
    (DenseScheduleTrace.runInstrSeq_append_running h1 hrun h2) hrun h3
  have heq : originalLower = (halfTemplate 0 ⟨1, by decide⟩ ++ sentinelTemplate) ++ cleanupTemplate := by rfl
  simpa only [heq, DenseScheduleTrace.pcAfter_append] using h

theorem run_actual_lower (s : State) (value returnPC : UInt256) (rest : List UInt256)
    (hstack : rest.length ≤ 996) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq actualLower {s with pc := UInt256.ofNat 584, stack := value :: mask8 :: maskWord :: mask16 :: returnPC :: rest} =
      some {s with pc := pcAfter (UInt256.ofNat 584) actualLower, stack := cache (modelMemory s.memory value) ++ (returnPC :: rest), memory := modelMemory s.memory value} := by
  have hmem : rawMemory s.memory value = modelMemory s.memory value :=
    congrArg (fun t : State => t.memory) (Option.some.inj
      ((run_original_raw s value returnPC rest hstack hrun hactive).symm.trans
        (run_original_model s (UInt256.ofNat 599) value returnPC rest hstack hrun hactive)))
  have h := run_actual_raw s value returnPC rest hstack hrun hactive
  rw [← cache_rawMemory s.memory value, hmem] at h
  exact h

def lowerEndian : List Instr := cachedStage 8 ⟨2, by decide⟩ ++ cachedStage 16 ⟨4, by decide⟩

theorem run_lowerEndian (s : State) (pc value returnPC : UInt256) (rest : List UInt256)
    (hstack : rest.length ≤ 996) (hrun : s.halt = .Running) :
    runInstrSeq lowerEndian {s with pc := pc, stack := value :: mask8 :: maskWord :: mask16 :: returnPC :: rest} =
      some {s with pc := pcAfter pc lowerEndian, stack := packedWord value :: mask8 :: maskWord :: mask16 :: returnPC :: rest} := by
  have h1 := run_cachedStage s pc value 8 mask8 ⟨2, by decide⟩
    (mask8 :: maskWord :: mask16 :: returnPC :: rest)
    (by simp only [List.length_cons]; omega) (Or.inl ⟨rfl, rfl⟩) (by intros; rfl) hrun
  dsimp only [DenseScheduleTrace.stageState] at h1
  have h2 := run_cachedStage s (pcAfter pc (cachedStage 8 ⟨2, by decide⟩))
    (packedStage value 8 mask8) 16 mask16 ⟨4, by decide⟩
    (mask8 :: maskWord :: mask16 :: returnPC :: rest)
    (by simp only [List.length_cons]; omega) (Or.inr ⟨rfl, rfl⟩) (by intros; rfl) hrun
  dsimp only [DenseScheduleTrace.stageState] at h2
  have h := DenseScheduleTrace.runInstrSeq_append_running h1 hrun h2
  simpa only [lowerEndian, DenseScheduleTrace.pcAfter_append, DenseScheduleTemplate.packedWord] using h

def fullTemplate : List Instr :=
  ((PairedDivMaskCache.cachedInitial ++ upperTemplate) ++ lowerEndian) ++ actualLower

theorem run_fullTemplate (s : State) (messageOffset returnPC : UInt256)
    (rest : List UInt256) (hstack : rest.length ≤ 996) (hrun : s.halt = .Running)
    (hactive : 23 ≤ (loadedActiveWords s messageOffset).toNat) :
    runInstrSeq fullTemplate (scheduleEntry s (UInt256.ofNat 429) messageOffset returnPC rest) =
      some {s with pc := pcAfter (UInt256.ofNat 429) fullTemplate, stack := cache (normalizedMemory s.memory (scheduleWords s messageOffset)) ++ (returnPC :: rest), memory := normalizedMemory s.memory (scheduleWords s messageOffset), activeWords := loadedActiveWords s messageOffset} := by
  have h1 := PairedDivMaskCache.run_cachedInitial s (UInt256.ofNat 429) messageOffset returnPC rest (by omega) hrun
  have h2 := run_cachedReversedHalf
    {s with activeWords := loadedActiveWords s messageOffset}
    (pcAfter (UInt256.ofNat 429) PairedDivMaskCache.cachedInitial) (inputWord1 s messageOffset) 8
    ⟨3, by decide⟩ ⟨5, by decide⟩ ⟨2, by decide⟩
    (inputWord0 s messageOffset :: mask8 :: maskWord :: mask16 :: returnPC :: rest)
    (by simp only [List.length_cons]; omega) hrun hactive (by decide)
    (by intros; rfl) (by intros; rfl) rfl
  have h12 := DenseScheduleTrace.runInstrSeq_append_running h1 hrun h2
  have he := run_lowerEndian
    {s with activeWords := loadedActiveWords s messageOffset, memory := storeCells s.memory (halfWords (packedInput1 s messageOffset) 8) 8 8}
    (pcAfter (pcAfter (UInt256.ofNat 429) PairedDivMaskCache.cachedInitial) upperTemplate)
    (inputWord0 s messageOffset) returnPC rest hstack hrun
  have h12e := DenseScheduleTrace.runInstrSeq_append_running h12 hrun he
  have h3 := run_actual_lower
    {s with activeWords := loadedActiveWords s messageOffset, memory := storeCells s.memory (halfWords (packedInput1 s messageOffset) 8) 8 8}
    (packedInput0 s messageOffset) returnPC rest hstack hrun hactive
  have h := DenseScheduleTrace.runInstrSeq_append_running h12e hrun h3
  unfold modelMemory at h
  rw [store_upper_schedule, store_lower_schedule] at h
  have hpc : pcAfter (UInt256.ofNat 429)
      ((PairedDivMaskCache.cachedInitial ++ upperTemplate) ++ lowerEndian) = UInt256.ofNat 584 := by decide
  rw [fullTemplate, DenseScheduleTrace.pcAfter_append, hpc]
  simpa only [upperTemplate, normalizedMemory] using h

theorem run_fullTemplate_natural (s : State) (returnPC : UInt256)
    (p : Nat) (rest : List UInt256) (hstack : rest.length ≤ 996) (hrun : s.halt = .Running)
    (hp : 736 ≤ p) (hbound : p + 64 < 2 ^ 256) :
    runInstrSeq fullTemplate (scheduleEntry s (UInt256.ofNat 429) (UInt256.ofNat p) returnPC rest) =
      some {s with pc := pcAfter (UInt256.ofNat 429) fullTemplate, stack := cache (normalizedMemory s.memory (PairedScheduleData.extractedWord s.memory p)) ++ (returnPC :: rest), memory := normalizedMemory s.memory (PairedScheduleData.extractedWord s.memory p), activeWords := loadedActiveWords s (UInt256.ofNat p)} := by
  have h := run_fullTemplate s (UInt256.ofNat p) returnPC rest hstack hrun
    (loaded_active_ge23 s p hp hbound)
  rw [normalizedMemory_congr s.memory (scheduleWords s (UInt256.ofNat p))
    (PairedScheduleData.extractedWord s.memory p)
    (fun i hi => scheduleWords_eq_extracted s p i hi hbound)] at h
  exact h
#print axioms run_fullTemplate_natural
end Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedSchedule
