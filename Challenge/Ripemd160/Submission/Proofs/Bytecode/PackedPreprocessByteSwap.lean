import Challenge.Ripemd160.Submission.Proofs.Bytecode.ClosedEndianMultiply
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DenseScheduleLift
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedPreprocessLayout
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundData
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackSiteBuilder
import Challenge.Ripemd160.Submission.Proofs.Bytecode.newArtifactByteLength

set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

/-!
# Located two-word byte-swap preprocessing

This is the exact straight-line trace at instruction indices `300 .. 361`
(PCs `544 .. 634`) in the frozen packed artifact.  It reads two adjacent
message words, byte-swaps each four-byte lane with the already-proved compact
endian stages, and stores the second word at `320` followed by the first word
at `288`.

The trace is parametric in the incoming memory and source pointer.  The two
loads perform the ordinary EVM active-memory expansion; the low stores are
then already covered because the source is at least byte `512`.  The theorem
also records pointwise preservation of the message region beginning at byte
`512`.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedPreprocessByteSwap

open Challenge.Ripemd160 Challenge.EvmProof
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open StackRoundTemplate StackRoundTrace

def loadTemplate : List Instr :=
  [DenseScheduleTemplate.dup1, DenseScheduleTemplate.op .MLOAD,
    DenseScheduleTemplate.swap1,
    DenseScheduleTemplate.push1 (UInt256.ofNat 32),
    DenseScheduleTemplate.op .ADD, DenseScheduleTemplate.op .MLOAD]

def storeTemplate (address : Nat) : List Instr :=
  [DenseScheduleTemplate.push2 (UInt256.ofNat address),
    DenseScheduleTemplate.op .MSTORE]

def halfTemplate (address : Nat) : List Instr :=
  ClosedEndianMultiply.code 8 ++ ClosedEndianMultiply.code 16 ++
    storeTemplate address

def byteSwapTemplate : List Instr :=
  loadTemplate ++ halfTemplate 320 ++ halfTemplate 288

@[simp] theorem loadTemplate_length : loadTemplate.length = 6 := by rfl

@[simp] theorem storeTemplate_length (address : Nat) :
    (storeTemplate address).length = 2 := by
  rfl

@[simp] theorem halfTemplate_length (address : Nat) :
    (halfTemplate address).length = 28 := by
  rfl

@[simp] theorem byteSwapTemplate_length : byteSwapTemplate.length = 62 := by
  rfl

theorem artifact_byteSwap_slice :
    (Artifact.submissionArtifact.instructions.drop 300).take 62 =
      byteSwapTemplate := by
  rfl

def inputWord0 (memory : ByteArray) (source : Nat) : UInt256 :=
  MachineState.readWord memory source

def inputWord1 (memory : ByteArray) (source : Nat) : UInt256 :=
  MachineState.readWord memory (source + 32)

def byteSwapEntry (s : State) (startPC : UInt256) (source : Nat)
    (rest : List UInt256) : State :=
  { s with pc := startPC, stack := UInt256.ofNat source :: rest }

/-- Active memory after the two adjacent 32-byte source loads. -/
def loadedActiveWords (s : State) (source : Nat) : UInt256 :=
  s.activeWordsAfterUInt256_2 source 32 (source + 32) 32

def afterLoads (s : State) (startPC : UInt256) (source : Nat)
    (rest : List UInt256) : State :=
  { s with
    pc := pcAfter startPC loadTemplate
    stack := inputWord1 s.memory source :: inputWord0 s.memory source :: rest
    activeWords := loadedActiveWords s source }

def byteSwapReturned (s : State) (endPC : UInt256) (source : Nat)
    (rest : List UInt256) : State :=
  { s with
    pc := endPC
    stack := rest
    memory := PackedPreprocessLayout.packedBaseMemory s.memory
      (inputWord0 s.memory source) (inputWord1 s.memory source)
    activeWords := loadedActiveWords s source }

@[simp] theorem byteSwapReturned_executionEnv (s : State) (endPC : UInt256)
    (source : Nat) (rest : List UInt256) :
    (byteSwapReturned s endPC source rest).executionEnv = s.executionEnv := by
  rfl

@[simp] theorem byteSwapReturned_halt (s : State) (endPC : UInt256)
    (source : Nat) (rest : List UInt256) :
    (byteSwapReturned s endPC source rest).halt = s.halt := by
  rfl

@[simp] theorem byteSwapReturned_callStack (s : State) (endPC : UInt256)
    (source : Nat) (rest : List UInt256) :
    (byteSwapReturned s endPC source rest).callStack = s.callStack := by
  rfl

@[simp] theorem byteSwapReturned_activeWords (s : State) (endPC : UInt256)
    (source : Nat) (rest : List UInt256) :
    (byteSwapReturned s endPC source rest).activeWords =
      loadedActiveWords s source := by
  rfl

private theorem activeWordsAfter_eq_of_end_le (curr offset size : Nat)
    (hend : offset + size ≤ curr * 32) :
    MachineState.activeWordsAfter curr offset size = curr := by
  unfold MachineState.activeWordsAfter
  split
  · rfl
  · dsimp only
    apply Nat.max_eq_left
    have hq : (offset + size - 1) / 32 < curr :=
      (Nat.div_lt_iff_lt_mul (by omega)).2 (by omega)
    omega

private theorem activeWordsAfterUInt256_eq (s : State) (offset size : Nat)
    (hend : offset + size ≤ s.activeWords.toNat * 32) :
    s.activeWordsAfterUInt256 offset size = s.activeWords := by
  have hofNat (w : UInt256) : UInt256.ofNat w.toNat = w := by
    cases w with
    | mk value => simp [UInt256.ofNat, UInt256.toNat, UInt256.size]
  rw [State.activeWordsAfterUInt256,
    activeWordsAfter_eq_of_end_le _ _ _ hend, hofNat]

private theorem activeWordsAfter_lt_of_end_lt (curr offset size : Nat)
    (hcurr : curr < 2 ^ 256) (hend : offset + size < 2 ^ 256) :
    MachineState.activeWordsAfter curr offset size < 2 ^ 256 := by
  unfold MachineState.activeWordsAfter
  split
  · exact hcurr
  · rw [Nat.max_lt]
    constructor
    · exact hcurr
    · have hdiv := Nat.div_le_self (offset + size - 1) 32
      omega

private theorem activeWordsAfter_lastWord_le (curr offset size : Nat)
    (hsize : size ≠ 0) :
    (offset + size - 1) / 32 + 1 ≤
      MachineState.activeWordsAfter curr offset size := by
  unfold MachineState.activeWordsAfter
  rw [if_neg hsize]
  exact Nat.le_max_right _ _

theorem loadedActiveWords_toNat (s : State) (source : Nat)
    (hnowrap : source + 64 < 2 ^ 256) :
    (loadedActiveWords s source).toNat =
      MachineState.activeWordsAfter
        (MachineState.activeWordsAfter s.activeWords.toNat source 32)
        (source + 32) 32 := by
  have hfirstLt :
      MachineState.activeWordsAfter s.activeWords.toNat source 32 <
        2 ^ 256 := by
    apply activeWordsAfter_lt_of_end_lt
    · exact s.activeWords.val.isLt
    · omega
  have hsecondLt :
      MachineState.activeWordsAfter
          (MachineState.activeWordsAfter s.activeWords.toNat source 32)
          (source + 32) 32 < 2 ^ 256 := by
    apply activeWordsAfter_lt_of_end_lt
    · exact hfirstLt
    · omega
  unfold loadedActiveWords State.activeWordsAfterUInt256_2
  rw [Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt hsecondLt]

theorem loadedActiveWords_ge_11 (s : State) (source : Nat)
    (hsource : 512 ≤ source) (hnowrap : source + 64 < 2 ^ 256) :
    11 ≤ (loadedActiveWords s source).toNat := by
  rw [loadedActiveWords_toNat s source hnowrap]
  have hlast := activeWordsAfter_lastWord_le
    (MachineState.activeWordsAfter s.activeWords.toNat source 32)
    (source + 32) 32 (by norm_num)
  have hdiv : 10 ≤ (source + 32 + 32 - 1) / 32 := by
    apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 32)).2
    omega
  omega

theorem loadedActiveWords_eq_of_end_le (s : State) (source : Nat)
    (hactive : source + 64 ≤ s.activeWords.toNat * 32) :
    loadedActiveWords s source = s.activeWords := by
  unfold loadedActiveWords State.activeWordsAfterUInt256_2
  rw [activeWordsAfter_eq_of_end_le s.activeWords.toNat source 32 (by omega),
    activeWordsAfter_eq_of_end_le s.activeWords.toNat (source + 32) 32 hactive]
  cases s.activeWords with
  | mk value => simp [UInt256.ofNat, UInt256.toNat, UInt256.size]

private theorem word_add_assoc (u v w : UInt256) :
    (u + v) + w = u + (v + w) := by
  apply Challenge.EvmProof.Word.word_ext
  change ((u.val + v.val) + w.val).val =
    (u.val + (v.val + w.val)).val
  simp [Fin.add_def, Nat.add_assoc]

private theorem word_add_ofNat_assoc (u : UInt256) (a b : Nat) :
    (u + UInt256.ofNat a) + UInt256.ofNat b =
      u + UInt256.ofNat (a + b) := by
  rw [word_add_assoc, Challenge.EvmProof.Word.ofNat_add_mod]

private theorem add_ofNat_assoc_hAdd (u : UInt256) (a b : Nat) :
    UInt256.add u (UInt256.ofNat a) + UInt256.ofNat b =
      u + UInt256.ofNat (a + b) := by
  change (u + UInt256.ofNat a) + UInt256.ofNat b =
    u + UInt256.ofNat (a + b)
  exact word_add_ofNat_assoc u a b

private theorem packedStage_eq_math (value : UInt256) (shift : Nat)
    (mask : UInt256) :
    DenseScheduleTemplate.packedStage value shift mask =
      UInt256.lor
        (UInt256.land (PackedScheduleMath.shr value shift) mask)
        (PackedScheduleMath.shl (UInt256.land value mask) shift) := by
  unfold DenseScheduleTemplate.packedStage PackedScheduleMath.shr
    PackedScheduleMath.shl
  exact Word.lor_comm _ _

theorem packedWord_eq_math (value : UInt256) :
    DenseScheduleTemplate.packedWord value = PackedScheduleMath.packed value := by
  unfold DenseScheduleTemplate.packedWord PackedScheduleMath.packed
  rw [packedStage_eq_math, packedStage_eq_math]
  simp only [DenseScheduleTemplate.mask8, DenseScheduleTemplate.mask16,
    PackedScheduleMath.mask8, PackedScheduleMath.mask16]
  rfl

set_option linter.unusedSimpArgs false in
theorem runInstrSeq_load (s : State) (startPC : UInt256) (source : Nat)
    (rest : List UInt256) (hstack : rest.length < 1021)
    (hrun : s.halt = .Running) (hnowrap : source + 64 < 2 ^ 256) :
    runInstrSeq loadTemplate (byteSwapEntry s startPC source rest) =
      some (afterLoads s startPC source rest) := by
  have hcap (n : Nat) (hn : n ≤ 3) : rest.length + n < 1024 := by omega
  have hsource : (UInt256.ofNat source).toNat = source := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt]
    omega
  have hsource32 :
      (UInt256.ofNat source + UInt256.ofNat 32).toNat = source + 32 := by
    rw [Challenge.EvmProof.Word.ofNat_add_ofNat (by omega),
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt]
    omega
  have hsource32rev :
      (UInt256.ofNat 32 + UInt256.ofNat source).toNat = source + 32 := by
    have hsum : 32 + source < 2 ^ 256 := by omega
    rw [Challenge.EvmProof.Word.ofNat_add_ofNat hsum,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hsum]
    omega
  have hfirstLt :
      MachineState.activeWordsAfter s.activeWords.toNat source 32 <
        2 ^ 256 := by
    apply activeWordsAfter_lt_of_end_lt
    · exact s.activeWords.val.isLt
    · omega
  have hfirstMod :
      MachineState.activeWordsAfter s.activeWords.toNat source 32 %
          2 ^ 256 =
        MachineState.activeWordsAfter s.activeWords.toNat source 32 :=
    Nat.mod_eq_of_lt hfirstLt
  have hsource32Mod : (32 + source) % 2 ^ 256 = source + 32 := by
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  have hpc :
      ((startPC + UInt256.ofNat 5).add (UInt256.ofNat 1)).add
          (UInt256.ofNat 1) =
        startPC + UInt256.ofNat 7 := by
    change ((startPC + UInt256.ofNat 5) + UInt256.ofNat 1) +
        UInt256.ofNat 1 = startPC + UInt256.ofNat 7
    rw [word_add_ofNat_assoc startPC 5 1,
      word_add_ofNat_assoc startPC 6 1]
  norm_num only [Nat.reducePow] at hfirstMod hsource32Mod
  have hswap1 (u v : UInt256) (rho : List UInt256) :
      (u :: v :: rho).exchange 0 1 = some (v :: u :: rho) := by
    simpa using YulEvmCompiler.exchange_swap u v ([] : List UInt256) rho
  simp (config := { maxSteps := 1000000 })
    [loadTemplate, byteSwapEntry, afterLoads, inputWord0, inputWord1,
      runInstrSeq, Stepper.runInstr, pcAfter, DenseScheduleTemplate.dup1,
      DenseScheduleTemplate.swap1, DenseScheduleTemplate.push1,
      DenseScheduleTemplate.op, hrun, hcap, hsource, hsource32,
      hsource32rev, loadedActiveWords, State.activeWordsAfterUInt256,
      State.activeWordsAfterUInt256_2,
      hswap1, UInt256.succ, Instr.size_push, Instr.size_op,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.ofNat_add_mod, word_add_assoc,
      word_add_ofNat_assoc, add_ofNat_assoc_hAdd, Nat.add_assoc]
  constructor
  · rw [hfirstMod, hsource32Mod]
  · constructor
    · exact hpc
    · rw [hsource32Mod]

set_option linter.unusedSimpArgs false in
theorem runInstrSeq_store (s : State) (startPC value : UInt256)
    (address : Nat) (rest : List UInt256) (hstack : rest.length < 1022)
    (hrun : s.halt = .Running) (haddress : address < 2 ^ 16)
    (hactive : address + 32 ≤ s.activeWords.toNat * 32) :
    runInstrSeq (storeTemplate address)
      { s with pc := startPC, stack := value :: rest } =
      some { s with
        pc := pcAfter startPC (storeTemplate address)
        stack := rest
        memory := PackedGapInvariant.storeWord s.memory address value } := by
  have hcap (n : Nat) (hn : n ≤ 2) : rest.length + n < 1024 := by omega
  have hcap2 : rest.length + 1 + 1 < 1024 := by omega
  have haddressNat : (UInt256.ofNat address).toNat = address := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt]
    omega
  have hwords : s.activeWordsAfterUInt256 address 32 = s.activeWords := by
    apply activeWordsAfterUInt256_eq
    exact hactive
  have hwords' (pc : UInt256) (stack : List UInt256) :
      ({s with pc := pc, stack := stack} : State).activeWordsAfterUInt256
          address 32 = s.activeWords := by
    change s.activeWordsAfterUInt256 address 32 = s.activeWords
    exact hwords
  have hwordsRunning (pc : UInt256) (stack : List UInt256) :
      State.activeWordsAfterUInt256
          ({s with pc := pc, stack := stack, halt := .Running} : State)
          address 32 = s.activeWords := by
    rw [← hrun]
    exact hwords' pc stack
  simp [storeTemplate, DenseScheduleTemplate.push2, DenseScheduleTemplate.op,
    PackedGapInvariant.storeWord,
    runInstrSeq, Stepper.runInstr, pcAfter, hrun, hcap, hcap2, haddressNat,
    hwords, hwords',
    UInt256.succ, Instr.size_push, Instr.size_op,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod, add_ofNat_assoc_hAdd]
  constructor
  · exact hwordsRunning _ _
  · rfl

theorem runInstrSeq_half (s : State) (startPC value : UInt256)
    (address : Nat) (rest : List UInt256) (hstack : rest.length < 1020)
    (hrun : s.halt = .Running) (haddress : address < 2 ^ 16)
    (hactive : address + 32 ≤ s.activeWords.toNat * 32) :
    runInstrSeq (halfTemplate address)
      { s with pc := startPC, stack := value :: rest } =
      some { s with
        pc := pcAfter startPC (halfTemplate address)
        stack := rest
        memory := PackedGapInvariant.storeWord s.memory address
          (PackedScheduleMath.packed value) } := by
  have h8 := ClosedEndianMultiply.run_endian s startPC value 8
    DenseScheduleTemplate.mask8 rest hstack
    (Or.inl ⟨rfl, rfl⟩) hrun
  have h16 := ClosedEndianMultiply.run_endian s
    (pcAfter startPC (ClosedEndianMultiply.code 8))
    (DenseScheduleTemplate.packedStage value 8 DenseScheduleTemplate.mask8)
    16 DenseScheduleTemplate.mask16 rest hstack
    (Or.inr ⟨rfl, rfl⟩) hrun
  have hstore := runInstrSeq_store s
    (pcAfter (pcAfter startPC (ClosedEndianMultiply.code 8))
      (ClosedEndianMultiply.code 16))
    (DenseScheduleTemplate.packedWord value) address rest (by omega) hrun
      haddress hactive
  have h16store := DenseScheduleTrace.runInstrSeq_append_running h16
    (by simpa using hrun)
    (by simpa only [DenseScheduleTemplate.packedWord] using hstore)
  have hfull := DenseScheduleTrace.runInstrSeq_append_running h8
    (by simpa using hrun) h16store
  rw [halfTemplate, DenseScheduleTrace.pcAfter_append,
    DenseScheduleTrace.pcAfter_append]
  have hpacked := packedWord_eq_math value
  unfold DenseScheduleTemplate.packedWord at hpacked
  rw [hpacked] at hfull
  simpa only [List.append_assoc] using hfull

theorem runInstrSeq_byteSwap (s : State) (startPC : UInt256) (source : Nat)
    (rest : List UInt256) (hsource : 512 ≤ source)
    (hnowrap : source + 64 < 2 ^ 256)
    (hstack : rest.length < 1019) (hrun : s.halt = .Running) :
    runInstrSeq byteSwapTemplate (byteSwapEntry s startPC source rest) =
      some (byteSwapReturned s (pcAfter startPC byteSwapTemplate) source rest) := by
  have hload := runInstrSeq_load s startPC source rest (by omega) hrun hnowrap
  let loaded := afterLoads s startPC source rest
  have hloaded11 : 11 ≤ loaded.activeWords.toNat := by
    simpa [loaded, afterLoads] using
      loadedActiveWords_ge_11 s source hsource hnowrap
  have hhalf1 := runInstrSeq_half loaded loaded.pc
    (inputWord1 s.memory source) 320 (inputWord0 s.memory source :: rest)
    (by simp; omega) (by simpa [loaded, afterLoads] using hrun)
    (by norm_num) (by omega)
  let first :=
    { loaded with
      pc := pcAfter loaded.pc (halfTemplate 320)
      stack := inputWord0 s.memory source :: rest
      memory := PackedGapInvariant.storeWord loaded.memory 320
        (PackedScheduleMath.packed (inputWord1 s.memory source)) }
  have hhalf1' : runInstrSeq (halfTemplate 320) loaded = some first := by
    simpa [first, loaded, afterLoads] using hhalf1
  have hhalf2 := runInstrSeq_half first first.pc
    (inputWord0 s.memory source) 288 rest (by omega)
    (by simpa [first, loaded, afterLoads] using hrun) (by norm_num)
    (by simp only [first]; omega)
  have hload1 := DenseScheduleTrace.runInstrSeq_append_running hload
    (by simpa [loaded, afterLoads] using hrun) hhalf1'
  have hall := DenseScheduleTrace.runInstrSeq_append_running hload1
    (by simpa [first, loaded, afterLoads] using hrun) hhalf2
  rw [byteSwapTemplate, DenseScheduleTrace.pcAfter_append,
    DenseScheduleTrace.pcAfter_append]
  simpa [byteSwapReturned, PackedPreprocessLayout.packedBaseMemory, first,
    loaded, afterLoads]
    using hall

theorem packedBaseMemory_preserves_high (memory : ByteArray)
    (word0 word1 : UInt256) (i : Nat) (hi : 512 ≤ i) :
    (PackedPreprocessLayout.packedBaseMemory memory word0 word1)[i]?.getD 0 =
      memory[i]?.getD 0 := by
  unfold PackedPreprocessLayout.packedBaseMemory PackedGapInvariant.storeWord
  rw [MachineState.writeBytes_getElem?_getD,
    MachineState.writeBytes_getElem?_getD]
  simp only [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  rw [if_neg (by omega), if_neg (by omega)]

theorem packedBaseMemory_read0 (memory : ByteArray) (word0 word1 : UInt256) :
    MachineState.readWord
        (PackedPreprocessLayout.packedBaseMemory memory word0 word1) 288 =
      PackedScheduleMath.packed word0 := by
  unfold PackedPreprocessLayout.packedBaseMemory PackedGapInvariant.storeWord
  exact Challenge.EvmProof.Memory.readWord_writeWord _ _ _

theorem packedBaseMemory_read1 (memory : ByteArray) (word0 word1 : UInt256) :
    MachineState.readWord
        (PackedPreprocessLayout.packedBaseMemory memory word0 word1) 320 =
      PackedScheduleMath.packed word1 := by
  unfold PackedPreprocessLayout.packedBaseMemory PackedGapInvariant.storeWord
  rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint]
  · exact Challenge.EvmProof.Memory.readWord_writeWord _ _ _
  · simp only [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
    exact Or.inr (by omega)

private theorem inputTemplate_advances :
    ∀ instruction ∈ loadTemplate, DenseScheduleLift.Advances instruction := by
  intro instruction hmem
  simp only [loadTemplate, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals exact Or.inl (Or.inl (by constructor))

private theorem storeTemplate_advances (address : Nat) :
    ∀ instruction ∈ storeTemplate address,
      DenseScheduleLift.Advances instruction := by
  intro instruction hmem
  simp only [storeTemplate, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl
  · exact Or.inl (Or.inl (by constructor))
  · exact Or.inr (Or.inl rfl)

private theorem byteSwapTemplate_runInstr_pc :
    ∀ instruction ∈ byteSwapTemplate, ∀ {s t : State},
      Stepper.runInstr instruction s = some t →
      t.pc = s.pc + UInt256.ofNat instruction.size := by
  intro instruction hmem s t hresult
  have htop :
      (instruction ∈ loadTemplate ∨ instruction ∈ halfTemplate 320) ∨
        instruction ∈ halfTemplate 288 := by
    simpa only [byteSwapTemplate, List.mem_append] using hmem
  rcases htop with (hload | hhalf320) | hhalf288
  · exact DenseScheduleLift.runInstr_pc_of_advances
      (inputTemplate_advances instruction hload) hresult
  · have hhalf :
        (instruction ∈ ClosedEndianMultiply.code 8 ∨
          instruction ∈ ClosedEndianMultiply.code 16) ∨
            instruction ∈ storeTemplate 320 := by
      simpa only [halfTemplate, List.mem_append] using hhalf320
    rcases hhalf with (h8 | h16) | hstore
    · exact ClosedEndianMultiply.advances 8 h8 hresult
    · exact ClosedEndianMultiply.advances 16 h16 hresult
    · exact DenseScheduleLift.runInstr_pc_of_advances
        (storeTemplate_advances 320 instruction hstore) hresult
  · have hhalf :
        (instruction ∈ ClosedEndianMultiply.code 8 ∨
          instruction ∈ ClosedEndianMultiply.code 16) ∨
            instruction ∈ storeTemplate 288 := by
      simpa only [halfTemplate, List.mem_append] using hhalf288
    rcases hhalf with (h8 | h16) | hstore
    · exact ClosedEndianMultiply.advances 8 h8 hresult
    · exact ClosedEndianMultiply.advances 16 h16 hresult
    · exact DenseScheduleLift.runInstr_pc_of_advances
        (storeTemplate_advances 288 instruction hstore) hresult

private theorem artifact_code_bound :
    Artifact.submissionArtifact.code.size < UInt256.size := by
  change submissionBytecode.size < UInt256.size
  rw [referenceBytecode_size]
  decide

def byteSwapSite :
    GenericRoundSite Artifact.submissionArtifact .Osaka byteSwapTemplate :=
  StackSiteBuilder.ofSlice
    (artifact := Artifact.submissionArtifact) (fork := .Osaka)
    byteSwapTemplate 300 artifact_byteSwap_slice
    (by
      change 300 + byteSwapTemplate.length ≤ Artifact.submissionInstructions.length
      rw [byteSwapTemplate_length, Artifact.referenceInstructions_count]
      decide)
    artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := byteSwapTemplate)
      (by decide))
    (by decide)

private theorem byteSwap_start_instructionPC :
    Artifact.submissionArtifact.instructionPC 300 = 544 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

private theorem byteSwap_end_instructionPC :
    Artifact.submissionArtifact.instructionPC 362 = 635 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem byteSwapSite_startPC :
    byteSwapSite.startPC = UInt256.ofNat 544 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 300) =
    UInt256.ofNat 544
  rw [byteSwap_start_instructionPC]

@[simp] theorem byteSwapSite_endPC :
    byteSwapSite.endPC = UInt256.ofNat 635 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 362) =
    UInt256.ofNat 635
  rw [byteSwap_end_instructionPC]

theorem byteSwapSite_end_eq_pcAfter :
    byteSwapSite.endPC = pcAfter byteSwapSite.startPC byteSwapTemplate := by
  have h := endPC_eq_pcAfter_sites byteSwapSite.sites byteSwapSite.startPC
    byteSwapSite.endPC byteSwapSite.head_eq byteSwapSite.end_eq
    byteSwapSite.contiguous
  rwa [byteSwapSite.instruction_eq] at h

theorem runLocatedBlock_byteSwap (s : State) (source : Nat)
    (rest : List UInt256) (hsource : 512 ≤ source)
    (hnowrap : source + 64 < 2 ^ 256)
    (hstack : rest.length < 1019) (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock byteSwapSite.path
      (byteSwapEntry s byteSwapSite.startPC source rest) =
      some (byteSwapReturned s byteSwapSite.endPC source rest) := by
  have hraw : Stepper.runLocatedBlock byteSwapSite.path
      (byteSwapEntry s byteSwapSite.startPC source rest) =
      runInstrSeq byteSwapTemplate
        (byteSwapEntry s byteSwapSite.startPC source rest) := by
    apply runLocatedBlock_eq_runInstrSeq_site byteSwapSite _ rfl
    intro located hmem u v hresult
    apply byteSwapTemplate_runInstr_pc located.located.instruction ?_ hresult
    rw [← byteSwapSite.instruction_eq]
    exact List.mem_map_of_mem hmem
  rw [hraw, runInstrSeq_byteSwap s byteSwapSite.startPC source rest hsource
    hnowrap hstack hrun, ← byteSwapSite_end_eq_pcAfter]

def gasSteps_byteSwap (s : State) (source : Nat) (rest : List UInt256)
    (hsource : 512 ≤ source) (hnowrap : source + 64 < 2 ^ 256)
    (hstack : rest.length < 1019)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (byteSwapEntry s byteSwapSite.startPC source rest)
      (byteSwapReturned s byteSwapSite.endPC source rest) := by
  apply Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka
    byteSwapSite.path
  · exact hcode
  · exact hfork
  · exact runLocatedBlock_byteSwap s source rest hsource hnowrap
      hstack hrun
  · exact hrun
  · exact hnp

#print axioms packedWord_eq_math
#print axioms runInstrSeq_byteSwap
#print axioms packedBaseMemory_preserves_high
#print axioms packedBaseMemory_read0
#print axioms packedBaseMemory_read1
#print axioms runLocatedBlock_byteSwap
#print axioms gasSteps_byteSwap

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedPreprocessByteSwap
