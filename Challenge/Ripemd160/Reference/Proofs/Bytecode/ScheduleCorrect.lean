import Challenge.Ripemd160.Reference.Proofs.Bytecode.Schedule
import Challenge.EvmProof.Memory

set_option warningAsError true
set_option maxRecDepth 10000

/-!
# Memory postcondition of the RIPEMD-160 schedule

This layer describes the `X[0..15]` image independently of control flow.  The
only caller seam is preservation of the message reads while the disjoint X
area is populated; the padding/driver proof can discharge it from its concrete
`msgOff >= 0x800` layout.
-/

namespace Challenge.Ripemd160.Reference.Proofs.Bytecode.ScheduleCorrect

open EvmSemantics
open EvmSemantics.EVM

def xValue (s : State) (i : Nat) : UInt256 :=
  MachineState.readWord s.memory (Schedule.xSlotWord i).toNat

def expectedWord (memory : ByteArray) (msgOff : UInt256) (i : Nat) : UInt256 :=
  UInt256.land (Schedule.readLEWord memory (Schedule.loadOffsetWord msgOff i))
    (UInt256.ofNat 0xffffffff)

def SlotsCorrect (s : State) (expected : Nat → UInt256) (upto : Nat) : Prop :=
  ∀ i, i < upto → xValue s i = expected i

theorem xSlotWord_eq (i : Nat) (hi : i < 16) :
    Schedule.xSlotWord i = UInt256.ofNat (0x2a0 + i * 32) := by
  unfold Schedule.xSlotWord
  calc
    UInt256.shiftLeft (UInt256.ofNat i) (UInt256.ofNat 5) +
        UInt256.ofNat 0x2a0 =
      UInt256.ofNat (i * 2 ^ 5) + UInt256.ofNat 0x2a0 := by
        rw [Challenge.EvmProof.Word.shiftLeft_ofNat (by omega)
          (by decide) (by omega)]
    _ = UInt256.ofNat (i * 2 ^ 5 + 0x2a0) :=
      Challenge.EvmProof.Word.ofNat_add_ofNat (by omega)
    _ = UInt256.ofNat (0x2a0 + i * 32) := by
      congr 1
      omega

theorem xSlotWord_toNat (i : Nat) (hi : i < 16) :
    (Schedule.xSlotWord i).toNat = 0x2a0 + i * 32 := by
  rw [xSlotWord_eq i hi, Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt (by omega)]

@[simp] theorem afterIteration_memory (s : State)
    (msgOff returnDest : UInt256) (rest : List UInt256) (i : Nat) :
    (Schedule.afterIteration s msgOff returnDest rest i).memory =
      MachineState.writeBytes s.memory
        (Data.Bytes.natToBytesPadded
          (expectedWord s.memory msgOff i).toNat 32)
        (Schedule.xSlotWord i).toNat := by
  rfl

/-- Writes to `X[0..15]` cannot disturb a message word at or above `0x4a0`. -/
theorem loopState_readLEWord (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j k : Nat) (hj : j ≤ 16) (_hk : k < 16)
    (hseparated : 0x4a0 ≤ (Schedule.loadOffsetWord msgOff k).toNat) :
    Schedule.readLEWord
        (Schedule.loopState s msgOff returnDest rest j).memory
        (Schedule.loadOffsetWord msgOff k) =
      Schedule.readLEWord s.memory (Schedule.loadOffsetWord msgOff k) := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [Schedule.loopState]
      unfold Schedule.readLEWord
      simp only [afterIteration_memory]
      rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint]
      · exact ih (by omega)
      · right
        have hsize : (Data.Bytes.natToBytesPadded
            (expectedWord (Schedule.loopState s msgOff returnDest rest j).memory
              msgOff j).toNat 32).size = 32 := by
          simp [Data.Bytes.natToBytesPadded, ByteArray.size]
        rw [hsize]
        rw [xSlotWord_toNat j (by omega)]
        omega

/-- The exact X-array invariant after `n` schedule iterations. -/
theorem loopState_slots (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (n : Nat) (hn : n ≤ 16)
    (hread : ∀ (j k : Nat), j ≤ 16 → k < 16 →
      Schedule.readLEWord
          (Schedule.loopState s msgOff returnDest rest j).memory
          (Schedule.loadOffsetWord msgOff k) =
        Schedule.readLEWord s.memory (Schedule.loadOffsetWord msgOff k)) :
    SlotsCorrect (Schedule.loopState s msgOff returnDest rest n)
      (expectedWord s.memory msgOff) n := by
  induction n with
  | zero =>
      intro i hi
      omega
  | succ n ih =>
      intro i hi
      rw [Schedule.loopState]
      simp only [xValue, afterIteration_memory]
      by_cases hin : i = n
      · subst i
        rw [Challenge.EvmProof.Memory.readWord_writeWord]
        unfold expectedWord
        rw [hread n n (by omega) (by omega)]
      · rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint]
        · exact ih (by omega) i (by omega)
        · simp only [Data.Bytes.natToBytesPadded, ByteArray.size]
          rw [xSlotWord_toNat i (by omega), xSlotWord_toNat n (by omega)]
          omega

/-- Caller-facing postcondition for all sixteen little-endian message words. -/
theorem loopState_sixteen_slots (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256)
    (hread : ∀ (j k : Nat), j ≤ 16 → k < 16 →
      Schedule.readLEWord
          (Schedule.loopState s msgOff returnDest rest j).memory
          (Schedule.loadOffsetWord msgOff k) =
        Schedule.readLEWord s.memory (Schedule.loadOffsetWord msgOff k)) :
    SlotsCorrect (Schedule.loopState s msgOff returnDest rest 16)
      (expectedWord s.memory msgOff) 16 :=
  loopState_slots s msgOff returnDest rest 16 (by omega) hread

/-- The concrete reference layout (`msgOff >= 0x800`) discharges the
read-preservation seam and yields the complete X-array image. -/
theorem loopState_sixteen_slots_of_separated (s : State)
    (msgOff returnDest : UInt256) (rest : List UInt256)
    (hseparated : ∀ k, k < 16 →
      0x4a0 ≤ (Schedule.loadOffsetWord msgOff k).toNat) :
    SlotsCorrect (Schedule.loopState s msgOff returnDest rest 16)
      (expectedWord s.memory msgOff) 16 := by
  apply loopState_sixteen_slots
  intro j k hj hk
  exact loopState_readLEWord s msgOff returnDest rest j k hj hk
    (hseparated k hk)

/-- Initial-memory bridge to the mathematical RIPEMD-160 message words. -/
def MessageBlockAt (memory : ByteArray) (msgOff : UInt256)
    (padded : ByteArray) (blockOff : Nat) : Prop :=
  ∀ k, k < 16 → expectedWord memory msgOff k =
    Challenge.EvmProof.Word.ofUInt32
      (Crypto.Ripemd160.readLE32 padded (blockOff + k * 4))

/-- All sixteen stored X words agree with `Crypto.Ripemd160.readLE32`. -/
theorem loopState_sixteen_cryptoWords (s : State)
    (msgOff returnDest : UInt256) (rest : List UInt256)
    (padded : ByteArray) (blockOff : Nat)
    (hseparated : ∀ k, k < 16 →
      0x4a0 ≤ (Schedule.loadOffsetWord msgOff k).toNat)
    (hblock : MessageBlockAt s.memory msgOff padded blockOff) :
    ∀ k, k < 16 →
      xValue (Schedule.loopState s msgOff returnDest rest 16) k =
        Challenge.EvmProof.Word.ofUInt32
          (Crypto.Ripemd160.readLE32 padded (blockOff + k * 4)) := by
  have hslots := loopState_sixteen_slots_of_separated
    s msgOff returnDest rest hseparated
  intro k hk
  rw [hslots k hk]
  exact hblock k hk

end Challenge.Ripemd160.Reference.Proofs.Bytecode.ScheduleCorrect
