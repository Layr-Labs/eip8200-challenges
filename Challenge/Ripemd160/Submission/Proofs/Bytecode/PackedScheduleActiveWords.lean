import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedScheduleTemplate
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ScheduleActiveWords
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DriverTrace

set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedScheduleActiveWords

open Challenge.Ripemd160
open Challenge.EvmProof
open EvmSemantics
open EvmSemantics.EVM

private theorem activeAfterWord_toNat (current offset : UInt256)
    (hlt : MachineState.activeWordsAfter current.toNat offset.toNat 32 <
      2 ^ 256) :
    (PackedScheduleTemplate.activeAfterWord current offset).toNat =
      MachineState.activeWordsAfter current.toNat offset.toNat 32 := by
  unfold PackedScheduleTemplate.activeAfterWord
  rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hlt]

private theorem activeAfterWord_eq (s : State) (current offset : UInt256)
    (hend : offset.toNat + 32 ≤ current.toNat * 32) :
    PackedScheduleTemplate.activeAfterWord current offset = current := by
  have h := ScheduleActiveWords.activeWordsAfterUInt256_eq
    ({s with activeWords := current}) offset.toNat 32 hend
  simpa [PackedScheduleTemplate.activeAfterWord, State.activeWordsAfterUInt256]
    using h

private theorem storeActiveWords_eq_of_end_le (s : State) (current : UInt256)
    (addresses : List Nat)
    (hend : ∀ address ∈ addresses, address + 32 ≤ current.toNat * 32)
    (haddr : ∀ address ∈ addresses, address < 2 ^ 256) :
    PackedScheduleTemplate.storeActiveWords current addresses = current := by
  induction addresses with
  | nil => rfl
  | cons address addresses ih =>
      have hendAddress : address + 32 ≤ current.toNat * 32 :=
        hend address (by simp)
      have haddrAddress : address < 2 ^ 256 := haddr address (by simp)
      have hoff : (UInt256.ofNat address).toNat + 32 ≤ current.toNat * 32 := by
        rw [Challenge.EvmProof.Word.word_toNat_ofNat,
          Nat.mod_eq_of_lt haddrAddress]
        exact hendAddress
      have htail : ∀ address ∈ addresses,
          address + 32 ≤ current.toNat * 32 := by
        intro address hmem
        exact hend address (by simp [hmem])
      have htailAddr : ∀ address ∈ addresses, address < 2 ^ 256 := by
        intro address hmem
        exact haddr address (by simp [hmem])
      simp only [PackedScheduleTemplate.storeActiveWords, List.foldl]
      rw [activeAfterWord_eq s current (UInt256.ofNat address) hoff]
      exact ih htail htailAddr

private theorem storeActiveWords_stores (s : State) (current : UInt256)
    (half : Nat) (hhalf : half ≤ 1) (hcurrent : 66 ≤ current.toNat) :
    PackedScheduleTemplate.storeActiveWords current
      (PackedScheduleTemplate.storeAddresses half) = current := by
  apply storeActiveWords_eq_of_end_le s current
  · intro address haddress
    obtain ⟨index, hindex, rfl⟩ := List.mem_map.1 haddress
    have hindex' : index < 8 := by simpa using hindex
    simp [PackedScheduleTemplate.storeAddress]
    omega
  · intro address haddress
    obtain ⟨index, hindex, rfl⟩ := List.mem_map.1 haddress
    have hindex' : index < 8 := by simpa using hindex
    simp [PackedScheduleTemplate.storeAddress]
    omega

private theorem message_bounds (input : ByteArray) (hfit : CalldataFits input)
    (i : Nat) (hi : i < DriverTrace.blockCount input) :
    Padding.messageOffset + 64 * i < 2 ^ 256 ∧
    Padding.messageOffset + 64 * i + 32 < 2 ^ 256 ∧
    66 + 2 * i < 2 ^ 256 ∧
    (Padding.messageOffset + 64 * i + 32 + 32 - 1) / 32 + 1 =
      66 + 2 * i ∧
    Padding.messageOffset + 64 * i + 32 ≤ (66 + 2 * i) * 32 ∧
    Padding.messageOffset + 64 * i + 64 ≤ (66 + 2 * i) * 32 := by
  have hpadded := Padding.paddedLength_lt input.size
  have hoff : 64 * i < Padding.paddedLength input.size := by
    rw [DriverTrace.paddedLength_eq_blockCount input]
    omega
  have hsize : input.size < 2 ^ 64 := by
    simpa [CalldataFits] using hfit
  have hp : Padding.messageOffset + 64 * i < 2 ^ 256 := by
    norm_num [Padding.messageOffset] at hsize ⊢
    omega
  have hp32 : Padding.messageOffset + 64 * i + 32 < 2 ^ 256 := by
    change 2048 + 64 * i + 32 < 2 ^ 256
    omega
  have htarget : 66 + 2 * i < 2 ^ 256 := by
    norm_num [Padding.messageOffset] at hsize ⊢
    omega
  have hlast :
      (Padding.messageOffset + 64 * i + 32 + 32 - 1) / 32 + 1 =
        66 + 2 * i := by
    norm_num [Padding.messageOffset]
    omega
  have hread0 : Padding.messageOffset + 64 * i + 32 ≤
      (66 + 2 * i) * 32 := by
    norm_num [Padding.messageOffset]
    omega
  have hread1 : Padding.messageOffset + 64 * i + 64 ≤
      (66 + 2 * i) * 32 := by
    norm_num [Padding.messageOffset]
    omega
  exact ⟨hp, hp32, htarget, hlast, hread0, hread1⟩

private theorem message_words (i : Nat)
    (hp : Padding.messageOffset + 64 * i < 2 ^ 256)
    (hp32 : Padding.messageOffset + 64 * i + 32 < 2 ^ 256) :
    DriverTrace.messageOffsetWord i =
        UInt256.ofNat (Padding.messageOffset + 64 * i) ∧
    (DriverTrace.messageOffsetWord i).toNat =
        Padding.messageOffset + 64 * i ∧
    (DriverTrace.messageOffsetWord i + UInt256.ofNat 32).toNat =
        Padding.messageOffset + 64 * i + 32 := by
  have hmsgWord : DriverTrace.messageOffsetWord i =
      UInt256.ofNat (Padding.messageOffset + 64 * i) := by
    simp [DriverTrace.messageOffsetWord, DriverTrace.blockOffset, Nat.mul_comm]
  have hmsg : (DriverTrace.messageOffsetWord i).toNat =
      Padding.messageOffset + 64 * i := by
    rw [hmsgWord, Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt hp]
  have hmsg32 :
      (DriverTrace.messageOffsetWord i + UInt256.ofNat 32).toNat =
        Padding.messageOffset + 64 * i + 32 := by
    rw [hmsgWord, Challenge.EvmProof.Word.ofNat_add_ofNat hp32,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hp32]
  exact ⟨hmsgWord, hmsg, hmsg32⟩

private theorem warmupActiveWords_toNat_of_bounds (s : State)
    (messageOffset : UInt256) (p target : Nat)
    (hmessage : messageOffset.toNat = p)
    (hmessage32 : (messageOffset + UInt256.ofNat 32).toNat = p + 32)
    (htarget : target < 2 ^ 256)
    (hhigh : (p + 32 + 32 - 1) / 32 + 1 = target)
    (hread0 : p + 32 ≤ target * 32)
    (hread1 : p + 64 ≤ target * 32) :
    (PackedScheduleTemplate.warmupActiveWords s messageOffset).toNat =
      max s.activeWords.toNat target := by
  have hnz : (32 : Nat) ≠ 0 := by omega
  have hlo : (p + 31) / 32 + 1 ≤ target := by
    have : p + 31 ≤ p + 63 := by omega
    exact (Nat.add_le_add_right (Nat.div_le_div_right this) 1).trans (le_of_eq hhigh)
  have hfirstEq :
      MachineState.activeWordsAfter s.activeWords.toNat p 32 =
        max s.activeWords.toNat ((p + 31) / 32 + 1) := by
    simp only [MachineState.activeWordsAfter, if_neg hnz]
  have hfirstLt :
      MachineState.activeWordsAfter s.activeWords.toNat p 32 < 2 ^ 256 := by
    rw [hfirstEq]
    exact (Nat.max_lt).2 ⟨s.activeWords.val.isLt, Nat.lt_of_le_of_lt hlo htarget⟩
  let a0 := PackedScheduleTemplate.activeAfterWord s.activeWords messageOffset
  have ha0 :
      a0.toNat = max s.activeWords.toNat ((p + 31) / 32 + 1) := by
    dsimp [a0]
    have hlt : MachineState.activeWordsAfter s.activeWords.toNat
        messageOffset.toNat 32 < 2 ^ 256 := by
      rw [hmessage]; exact hfirstLt
    rw [activeAfterWord_toNat _ _ hlt, hmessage, hfirstEq]
  have hsecondEq :
      MachineState.activeWordsAfter a0.toNat (p + 32) 32 =
        max a0.toNat target := by
    simp only [MachineState.activeWordsAfter, if_neg hnz]
    rw [hhigh]
  have hsecondLt :
      MachineState.activeWordsAfter a0.toNat (p + 32) 32 < 2 ^ 256 := by
    rw [hsecondEq, ha0]
    exact (Nat.max_lt).2 ⟨(Nat.max_lt).2 ⟨s.activeWords.val.isLt,
      Nat.lt_of_le_of_lt hlo htarget⟩, htarget⟩
  have hsecond := activeAfterWord_toNat a0 (messageOffset + UInt256.ofNat 32)
    (by rw [hmessage32]; exact hsecondLt)
  let _ := hread0
  let _ := hread1
  simp only [PackedScheduleTemplate.warmupActiveWords]
  change (PackedScheduleTemplate.activeAfterWord a0
      (messageOffset + UInt256.ofNat 32)).toNat = _
  rw [hsecond, hmessage32, hsecondEq, ha0, Nat.max_assoc, Nat.max_eq_left hlo]

private theorem warmupActiveWords_toNat (s : State) (input : ByteArray)
    (hfit : CalldataFits input) (i : Nat)
    (hi : i < DriverTrace.blockCount input) :
    (PackedScheduleTemplate.warmupActiveWords s
        (DriverTrace.messageOffsetWord i)).toNat =
      max s.activeWords.toNat (66 + 2 * i) := by
  rcases message_bounds input hfit i hi with
    ⟨hp, hp32, htarget, hhigh, hread0, hread1⟩
  rcases message_words i hp hp32 with
    ⟨_, hmsg, hmsg32⟩
  exact warmupActiveWords_toNat_of_bounds s
    (DriverTrace.messageOffsetWord i) (Padding.messageOffset + 64 * i)
    (66 + 2 * i) hmsg hmsg32 htarget hhigh hread0 hread1

private theorem expectedActiveWords_toNat (s : State) (input : ByteArray)
    (hfit : CalldataFits input) (i : Nat)
    (hi : i < DriverTrace.blockCount input) :
    (PackedScheduleTemplate.expectedActiveWords s
        (DriverTrace.messageOffsetWord i)).toNat =
      max s.activeWords.toNat (66 + 2 * i) := by
  have hwarm := warmupActiveWords_toNat s input hfit i hi
  have hwarm66 : 66 ≤
      (PackedScheduleTemplate.warmupActiveWords s
          (DriverTrace.messageOffsetWord i)).toNat := by
    rw [hwarm]
    exact (by omega : 66 ≤ 66 + 2 * i).trans (Nat.le_max_right _ _)
  have hstore0 := storeActiveWords_stores s
    (PackedScheduleTemplate.warmupActiveWords s
      (DriverTrace.messageOffsetWord i)) 0 (by norm_num) hwarm66
  have hstore1 := storeActiveWords_stores s
    (PackedScheduleTemplate.warmupActiveWords s
      (DriverTrace.messageOffsetWord i)) 1 (by norm_num) hwarm66
  unfold PackedScheduleTemplate.expectedActiveWords
  rw [hstore0, hstore1, hwarm]

theorem expectedActiveWords_eq_schedule (s : State) (input : ByteArray)
    (hfit : CalldataFits input) (i : Nat)
    (hi : i < DriverTrace.blockCount input) (ret : UInt256)
    (rest : List UInt256) :
    PackedScheduleTemplate.expectedActiveWords s
        (DriverTrace.messageOffsetWord i) =
      (Schedule.loopState s (DriverTrace.messageOffsetWord i) ret rest 16).activeWords := by
  apply Challenge.EvmProof.Word.word_ext
  rw [expectedActiveWords_toNat s input hfit i hi]
  exact (ScheduleActiveWords.scheduledState_activeWords s input hfit i hi ret rest).symm

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedScheduleActiveWords
