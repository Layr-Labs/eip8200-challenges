import Challenge.Blake2f.Reference.Proofs.Bytecode.RoundGas

set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false

/-! Memory invariants connecting compiled rounds to the pure BLAKE2f model. -/

namespace Challenge.Blake2f.Reference.Proofs.Bytecode.RoundCorrectness

open Challenge.Blake2f
open Challenge.Blake2f.ProofSupport
open EvmSemantics

def sigmaPacked : Nat → Nat
  | 0 => 0x000102030405060708090a0b0c0d0e0f
  | 1 => 0x0e0a0408090f0d06010c00020b070503
  | 2 => 0x0b080c0005020f0d0a0e030607010904
  | 3 => 0x070903010d0c0b0e0206050a04000f08
  | 4 => 0x0900050702040a0f0e010b0c0608030d
  | 5 => 0x020c060a000b0803040d07050f0e0109
  | 6 => 0x0c05010f0e0d040a000706030902080b
  | 7 => 0x0d0b070e0c01030905000f040806020a
  | 8 => 0x060f0e090b0300080c020d0701040a05
  | _ => 0x0a020804070601050f0b090e030c0d00

def ScheduleRows (memory : ByteArray) : Prop :=
  ∀ round : UInt256, MixG.rowWord memory round =
    UInt256.ofNat (sigmaPacked (round.toNat % 10))

theorem rowOffset_toNat_word (round : UInt256) :
    (MixG.rowOffset round).toNat = 1536 + 32 * (round.toNat % 10) := by
  have hmod : round.toNat % 10 < 10 := Nat.mod_lt _ (by omega)
  have hwordMod : round % UInt256.ofNat 10 =
      UInt256.ofNat (round.toNat % 10) := by
    apply Challenge.EvmProof.Word.word_ext
    change (UInt256.mod round (UInt256.ofNat 10)).toNat =
      (UInt256.ofNat (round.toNat % 10)).toNat
    unfold UInt256.mod
    rw [if_neg (by decide)]
    change round.toNat % (10 % 2 ^ 256) =
      (round.toNat % 10) % 2 ^ 256
    rw [Nat.mod_eq_of_lt (by norm_num : 10 < 2 ^ 256),
      Nat.mod_eq_of_lt (Nat.lt_trans hmod (by norm_num))]
  have hshift : UInt256.shiftLeft (UInt256.ofNat (round.toNat % 10))
      (UInt256.ofNat 5) = UInt256.ofNat ((round.toNat % 10) * 2 ^ 5) :=
    Challenge.EvmProof.Word.shiftLeft_ofNat (by omega) (by omega) (by omega)
  have hadd : UInt256.ofNat 1536 + UInt256.ofNat ((round.toNat % 10) * 2 ^ 5) =
      UInt256.ofNat (1536 + (round.toNat % 10) * 2 ^ 5) :=
    Challenge.EvmProof.Word.ofNat_add_ofNat (by omega)
  rw [MixG.rowOffset, hwordMod, hshift, hadd,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  omega

theorem rowOffset_toNat (round : Nat) (hround : round < 2 ^ 256) :
    (MixG.rowOffset (UInt256.ofNat round)).toNat =
      1536 + 32 * (round % 10) := by
  rw [rowOffset_toNat_word, Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt hround]

theorem accessSafe_of_schedule {memory : ByteArray} (round : Nat)
    (hround : round < 2 ^ 256) (schedule : ScheduleRows memory) :
    Round.AccessSafe memory round := by
  constructor
  · rw [rowOffset_toNat round hround]
    have hm : round % 10 < 10 := Nat.mod_lt _ (by omega)
    omega
  · intro column hcolumn
    have hrow := schedule (UInt256.ofNat round)
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hround] at hrow
    rw [hrow]
    have hm : round % 10 < 10 := Nat.mod_lt _ (by omega)
    interval_cases hr : round % 10 <;>
      interval_cases hc : column <;>
      subst_vars <;>
      norm_num [MixG.messageOffset, sigmaPacked, UInt256.byteAt,
        UInt256.shiftLeft, UInt256.add,
        Challenge.EvmProof.Word.ofNat_add_ofNat,
        Challenge.EvmProof.Word.word_toNat_ofNat] at * <;>
      decide

/-- A compiled quarter-round cannot modify the sigma table when all four of
its scratch lanes end before the table begins. -/
theorem schedule_transition {memory : ByteArray}
    (a b c d round xColumn yColumn : UInt256)
    (schedule : ScheduleRows memory)
    (ha : a.toNat + 32 ≤ 1536) (hb : b.toNat + 32 ≤ 1536)
    (hc : c.toNat + 32 ≤ 1536) (hd : d.toNat + 32 ≤ 1536) :
    ScheduleRows (MixG.transition memory a b c d round xColumn yColumn) := by
  intro selectedRound
  unfold MixG.rowWord
  rw [MixGCorrectness.readWord_transition_disjoint]
  · exact schedule selectedRound
  all_goals
    rw [rowOffset_toNat_word]
    exact Or.inr (by omega)

theorem schedule_memory1 {memory : ByteArray} (round : Nat)
    (schedule : ScheduleRows memory) :
    ScheduleRows (Round.memory1 memory round) := by
  apply schedule_transition
  · exact schedule
  all_goals decide

theorem schedule_memory2 {memory : ByteArray} (round : Nat)
    (schedule : ScheduleRows memory) :
    ScheduleRows (Round.memory2 memory round) := by
  apply schedule_transition
  · exact schedule_memory1 round schedule
  all_goals decide

theorem schedule_memory3 {memory : ByteArray} (round : Nat)
    (schedule : ScheduleRows memory) :
    ScheduleRows (Round.memory3 memory round) := by
  apply schedule_transition
  · exact schedule_memory2 round schedule
  all_goals decide

theorem schedule_memory4 {memory : ByteArray} (round : Nat)
    (schedule : ScheduleRows memory) :
    ScheduleRows (Round.memory4 memory round) := by
  apply schedule_transition
  · exact schedule_memory3 round schedule
  all_goals decide

theorem schedule_memory5 {memory : ByteArray} (round : Nat)
    (schedule : ScheduleRows memory) :
    ScheduleRows (Round.memory5 memory round) := by
  apply schedule_transition
  · exact schedule_memory4 round schedule
  all_goals decide

theorem schedule_memory6 {memory : ByteArray} (round : Nat)
    (schedule : ScheduleRows memory) :
    ScheduleRows (Round.memory6 memory round) := by
  apply schedule_transition
  · exact schedule_memory5 round schedule
  all_goals decide

theorem schedule_memory7 {memory : ByteArray} (round : Nat)
    (schedule : ScheduleRows memory) :
    ScheduleRows (Round.memory7 memory round) := by
  apply schedule_transition
  · exact schedule_memory6 round schedule
  all_goals decide

theorem schedule_transition_round {memory : ByteArray} (round : Nat)
    (schedule : ScheduleRows memory) :
    ScheduleRows (Round.transition memory round) := by
  apply schedule_transition
  · exact schedule_memory7 round schedule
  all_goals decide

theorem iterationSafe_of_schedule {memory : ByteArray} (round : Nat)
    (hround : round < 2 ^ 256) (schedule : ScheduleRows memory) :
    Round.IterationSafe memory round := by
  exact ⟨accessSafe_of_schedule round hround schedule,
    accessSafe_of_schedule round hround (schedule_memory1 round schedule),
    accessSafe_of_schedule round hround (schedule_memory2 round schedule),
    accessSafe_of_schedule round hround (schedule_memory3 round schedule),
    accessSafe_of_schedule round hround (schedule_memory4 round schedule),
    accessSafe_of_schedule round hround (schedule_memory5 round schedule),
    accessSafe_of_schedule round hround (schedule_memory6 round schedule),
    accessSafe_of_schedule round hround (schedule_memory7 round schedule)⟩

@[simp] theorem readWord_initialization_storeWord_same (memory : ByteArray)
    (offset : Nat) (value : UInt256) :
    MachineState.readWord (Initialization.storeWord memory offset value) offset =
      value := by
  exact Challenge.EvmProof.Memory.readWord_writeWord memory offset value

theorem readWord_initialization_storeWord_disjoint (memory : ByteArray)
    (readStart writeStart : Nat) (value : UInt256)
    (h : Memory.WordDisjoint readStart writeStart) :
    MachineState.readWord
        (Initialization.storeWord memory writeStart value) readStart =
      MachineState.readWord memory readStart := by
  apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
  simpa [Memory.WordDisjoint, Data.Bytes.natToBytesPadded, ByteArray.size] using h

theorem schedule_constantsMemory (input : ByteArray) :
    ScheduleRows (Initialization.constantsMemory input) := by
  intro round
  unfold MixG.rowWord
  rw [rowOffset_toNat_word]
  have hm : round.toNat % 10 < 10 := Nat.mod_lt _ (by omega)
  interval_cases hr : round.toNat % 10 <;>
    simp only [hr, Initialization.constantsMemory, Initialization.fixedStores,
      Initialization.applyFixedStore, List.foldl_cons, List.foldl_nil,
      Prod.fst, Prod.snd, sigmaPacked] <;>
    norm_num at * <;>
    repeat first
      | rw [readWord_initialization_storeWord_same]
      | rw [readWord_initialization_storeWord_disjoint
          (h := Or.inl (by omega))]
      | rw [readWord_initialization_storeWord_disjoint
          (h := Or.inr (by omega))]

theorem schedule_storeWord {memory : ByteArray} (offset : Nat) (value : UInt256)
    (schedule : ScheduleRows memory) (hoffset : offset + 32 ≤ 1536) :
    ScheduleRows (Initialization.storeWord memory offset value) := by
  intro round
  change MachineState.readWord
      (Memory.storeWord memory offset value) (MixG.rowOffset round).toNat = _
  rw [Memory.readWord_storeWord_disjoint]
  · exact schedule round
  · rw [rowOffset_toNat_word]
    exact Or.inr (by omega)

theorem schedule_t0Memory (input : ByteArray) :
    ScheduleRows (ScalarInitialization.t0Memory input) := by
  apply schedule_storeWord
  · exact schedule_constantsMemory input
  · omega

theorem schedule_t1Memory (input : ByteArray) :
    ScheduleRows (ScalarInitialization.t1Memory input) := by
  apply schedule_storeWord
  · exact schedule_t0Memory input
  · omega

theorem schedule_flaggedMemory (input : ByteArray) :
    ScheduleRows (ScalarInitialization.flaggedMemory input) := by
  apply schedule_storeWord
  · exact schedule_t1Memory input
  · omega

theorem schedule_finalMemory (input : ByteArray) :
    ScheduleRows (ScalarInitialization.finalMemory input) := by
  unfold ScalarInitialization.finalMemory
  split
  · exact schedule_t1Memory input
  · exact schedule_flaggedMemory input

end Challenge.Blake2f.Reference.Proofs.Bytecode.RoundCorrectness
