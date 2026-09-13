import Challenge.Ripemd160.Submission.Proofs.Bytecode.Source32CallerFacts
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Source32Ghost
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Source32Words
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PersistentStaggerIteration
set_option warningAsError true
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Source32Ready
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof Challenge.Ripemd160
open Source32CallerFacts

def low (input : ByteArray) : UInt256 :=
  PairedScheduleData.reversedWord (MachineState.readWord (constructedMemory input) 1120)
def scratch (input : ByteArray) : ByteArray :=
  Source32Memory.writeWord (constructedMemory input) 28 (low input)
def table (input : ByteArray) : ByteArray :=
  StaggerTableLayout.resultMemory (scratch input) (StaggerScratch.poolWordD (scratch input))

theorem ordinary_eq_entry (input : ByteArray) :
    ordinaryMemory input = (PadSkipEntry.entryState input).memory := by
  unfold ordinaryMemory PadSkipEntry.entryState PaddingTrace.entryState
  split <;> rfl

theorem constructed_lower (input : ByteArray) :
    MachineState.readWord (constructedMemory input) 1120 =
      MachineState.readWord (constructorBase input) 1120 := by
  have hr : MachineState.readPadded (constructedMemory input) 1120 32 =
      MachineState.readPadded (constructorBase input) 1120 32 := by
    apply Memory.readPadded_congr
    intro i hi
    exact constructed_frame88 input _ (by omega)
  unfold MachineState.readWord
  rw [hr]

theorem constructor_lower (input : ByteArray) (hsize : input.size = 32) :
    MachineState.readWord (constructorBase input) 1120 = MachineState.readWord input 0 := by
  have hr : MachineState.readPadded (constructorBase input) 1120 32 =
      MachineState.readPadded input 0 32 := by
    apply ByteArray.ext_getElem
    · simp
    · intro i hi₁ hi₂
      rw [← Memory.getD0_eq_getElem _ _ hi₁,
        ← Memory.getD0_eq_getElem _ _ hi₂,
        Memory.readPadded_getElem?_getD, Memory.readPadded_getElem?_getD]
      have hi : i < 32 := by simpa using hi₁
      rw [if_pos hi, if_pos hi]
      simpa only [Padding.messageOffset, Nat.zero_add] using
        constructorBase_input_byte input i (by omega)
  unfold MachineState.readWord
  rw [hr]

theorem ordinary_read (input : ByteArray) (hfit : CalldataFits input)
    (hsize : input.size = 32) (off : Nat) (hoff : off ≤ 32) :
    MachineState.readWord (ordinaryMemory input) (1120+off) =
      MachineState.readWord (Padding.paddedMessage input) off := by
  have hn : input.size % 64 ≠ 0 := by rw [hsize]; decide
  unfold ordinaryMemory
  rw [if_neg hn, PaddingTrace.padReturned_readWord input hfit _ (by
    simp only [Padding.messageOffset, hsize, Padding.paddedLength]; omega)]
  exact PaddedBlockBridge.readWord_paddedMemory_shift _ input off (by
    change (ByteArray.empty).size ≤ 1120
    decide)

theorem ordinary_lower (input : ByteArray) (hfit : CalldataFits input) (hsize : input.size = 32) :
    MachineState.readWord (ordinaryMemory input) 1120 = MachineState.readWord input 0 := by
  rw [show 1120 = 1120+0 by rfl, ordinary_read input hfit hsize 0 (by decide)]
  have hr : MachineState.readPadded (Padding.paddedMessage input) 0 32 =
      MachineState.readPadded input 0 32 := by
    apply Memory.readPadded_congr
    intro i hi
    rw [Source32Words.padded_eq input hsize, Memory.getElem?_getD_append, if_pos (by omega)]
  unfold MachineState.readWord
  rw [hr]

theorem ordinary_upper (input : ByteArray) (hfit : CalldataFits input) (hsize : input.size = 32) :
    PairedScheduleData.reversedWord (MachineState.readWord (ordinaryMemory input) (1120+32)) =
      Source32Memory.source32Word := by
  rw [ordinary_read input hfit hsize 32 (by decide), Source32Words.reversed_upper input hsize]
  rfl

theorem low_eq_ghost (input : ByteArray) (hfit : CalldataFits input) (hsize : input.size = 32) :
    low input = PairedScheduleData.reversedWord (MachineState.readWord (ordinaryMemory input) 1120) := by
  rw [low, constructed_lower, constructor_lower input hsize, ordinary_lower input hfit hsize]

theorem pool_eq_ghost (input : ByteArray) (hfit : CalldataFits input) (hsize : input.size = 32)
    (k : Nat) (hk : k < 16) :
    StaggerScratch.poolWordD (scratch input) k = StaggerScratch.dirtyWord (ordinaryMemory input) 1120 k := by
  have hp : ∀ a, a < 28 → (constructorBase input)[a]?.getD 0 = (ordinaryMemory input)[a]?.getD 0 := by
    intro a ha
    rw [constructorBase_low_zero input a (by unfold Padding.messageOffset; omega),
      ordinary_low_zero input hfit a (by unfold Padding.messageOffset; omega)]
  have hclear : (MachineState.readWord (ordinaryMemory input) 0).toNat < 2^32 := by
    rw [ordinary_eq_entry]
    exact PadSkipEntry.entryState_lowClear input hfit
  change StaggerScratch.poolWordD (Source32Ghost.actualMemory (constructorBase input) (low input)) k = _
  rw [Source32Ghost.poolWordD_eq _ _ _ hp (constructorBase_zero_tail input) k hk]
  unfold Source32Ghost.ghostMemory
  rw [low_eq_ghost input hfit hsize, ← ordinary_upper input hfit hsize]
  exact StaggerScratch.poolWordD_eq_dirty (ordinaryMemory input) 1120 k hk hclear

theorem ready (input : ByteArray) (hfit : CalldataFits input) (hsize : input.size = 32) :
    StaggerMessage.Ready (table input) (PersistentStaggerTable.blockWords input 0) := by
  apply Source32Ghost.tableReady (scratch input) (scratch input) (ordinaryMemory input) 1120
    (PersistentStaggerTable.blockWords input 0) (pool_eq_ghost input hfit hsize)
  intro k hk
  rw [ordinary_eq_entry]
  have hi : 0 < DriverTrace.blockCount input := by
    simp only [DriverTrace.blockCount, hsize, Padding.paddedLength]
    decide
  have ctx := PersistentStaggerIteration.initial_context input hfit (by omega)
  exact PersistentStaggerTable.extracted_words (PadSkipEntry.entryState input) input 0 hfit hi ctx
    (by simp only [DriverTrace.blockOffset, Nat.zero_mul]; omega) k hk

#print axioms ordinary_eq_entry
#print axioms constructed_lower
#print axioms constructor_lower
#print axioms ordinary_read
#print axioms ordinary_lower
#print axioms ordinary_upper
#print axioms low_eq_ghost
#print axioms pool_eq_ghost
#print axioms ready
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Source32Ready
