import Challenge.Sha256.Submission.Proofs.Bytecode.Driver
import Challenge.Sha256.Submission.Proofs.Bytecode.CompressionCorrect
import Challenge.Sha256.Submission.Proofs.Bytecode.InitializationCorrect
import Challenge.Sha256.Submission.Proofs.Bytecode.PaddedBlockBridge
import Challenge.Sha256.Submission.Proofs.Bytecode.HashSpecBridge
import Mathlib.Tactic
import YulEvmCompiler.BytesLemmas

set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

/-!
# Functional correctness of the reference SHA-256 driver

This module is the reusable outer-loop layer.  It records only the eight
chaining words carried between blocks; bytecode-specific schedule and round
details are discharged by `CompressionCorrect`.
-/

namespace Challenge.Sha256.Submission.Proofs.Bytecode.DriverCorrect

open EvmSemantics
open EvmSemantics.Crypto
open EvmSemantics.EVM

/-- The reference memory's eight chaining slots represent a SHA-256 state. -/
def ChainRepresents (s : State) (H : Array UInt32) : Prop :=
  ∀ i, i < 8 →
    Compression.hValue s i = Challenge.EvmProof.Word.ofUInt32 H[i]!

/-- The packed SHA round-constant table is intact. -/
def KCorrect (s : State) : Prop :=
  ∀ j, j < 64 →
    Compression.kValue s j =
      Challenge.EvmProof.Word.ofUInt32 Sha256.K[j]!

/-- Every padded block remains readable at its concrete bytecode address.
This predicate is stable across the loop even though compression rewrites all
scratch memory below `Padding.messageOffset`. -/
def PaddedBlocksCorrect (s : State) (input : ByteArray) : Prop :=
  ∀ i, i < Driver.blockCount input →
    ScheduleCorrect.PaddedBlockAt s.memory (Driver.messageOffsetWord i)
      (Padding.paddedMessage input) (Driver.blockOffset i)

/-- Reusable complete outer-loop invariant. -/
def Invariant (s : State) (input : ByteArray) (H : Array UInt32) : Prop :=
  ChainRepresents s H ∧ KCorrect s ∧ PaddedBlocksCorrect s input

private theorem hSlot_eq (i : Nat) (hi : i < 8) :
    Accessors.slotOffset 288 (UInt256.ofNat i) = 288 + 32 * i := by
  unfold Accessors.slotOffset
  rw [Challenge.EvmProof.Word.shiftLeft_ofNat (by omega) (by decide) (by omega)]
  rw [Challenge.EvmProof.Word.ofNat_add_ofNat (by omega),
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  omega

private theorem padBase_memory (input : ByteArray) :
    (PaddingTrace.padLengthReady input).memory =
      (Main.initializedState input).memory := by
  rfl

set_option maxRecDepth 100000 in
private theorem padBase_size (input : ByteArray) :
    (PaddingTrace.padLengthReady input).memory.size ≤ Padding.messageOffset := by
  rw [padBase_memory, InitializationCorrect.initializedState_memory]
  norm_num [InitializationCorrect.initializedMemory, Main.initializedState,
    Main.initStart, Artifact.initStores, Main.applyInitStore,
    Challenge.Sha256.initialState, MachineState.writeBytes_size,
    YulEvmCompiler.BytesLemmas.natToBytesPadded_size,
    Padding.messageOffset]

private theorem padReturned_hValue (input : ByteArray) (hfit : CalldataFits input)
    (i : Nat) (hi : i < 8) :
    Compression.hValue (PaddingTrace.padReturned input) i =
      InitializationCorrect.hWord (Main.initializedState input).memory i := by
  rw [Compression.hValue, hSlot_eq i hi, PaddingTrace.padReturned_memory input hfit,
    Padding.paddedMemory_eq_write _ _ (padBase_size input)]
  rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint]
  · rw [padBase_memory]
    congr 2
  · left
    simp only [Padding.messageOffset]
    omega

private theorem kOffset_eq (j : Nat) (hj : j < 64) :
    (UInt256.shiftLeft (UInt256.ofNat j) (UInt256.ofNat 2) +
      UInt256.ofNat 32).toNat = 32 + 4 * j := by
  rw [Challenge.EvmProof.Word.shiftLeft_ofNat (by omega) (by decide) (by omega),
    Challenge.EvmProof.Word.ofNat_add_ofNat (by omega),
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  omega

private theorem padReturned_kValue (input : ByteArray) (hfit : CalldataFits input)
    (j : Nat) (hj : j < 64) :
    Compression.kValue (PaddingTrace.padReturned input) j =
      InitializationCorrect.kWord (Main.initializedState input).memory j := by
  simp only [Compression.kValue, InitializationCorrect.kWord]
  apply congrArg (fun w => UInt256.shiftRight w (UInt256.ofNat 224))
  rw [PaddingTrace.padReturned_memory input hfit,
    Padding.paddedMemory_eq_write _ _ (padBase_size input)]
  rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint]
  · rw [padBase_memory]
  · left
    rw [kOffset_eq j hj]
    simp only [Padding.messageOffset]
    omega

/-- Initialization and padding establish the outer-loop invariant before the
first block. -/
theorem blockLoopState_zero (input : ByteArray) (hfit : CalldataFits input) :
    ChainRepresents (Driver.blockLoopState input 0) Sha256.H0 := by
  intro i hi
  change Compression.hValue (PaddingTrace.padReturned input) i = _
  rw [padReturned_hValue input hfit i hi]
  exact InitializationCorrect.initializedState_hWord input i hi

private theorem blockOffset_block_fits (input : ByteArray) (i : Nat)
    (hi : i < Driver.blockCount input) :
    Driver.blockOffset i + 64 ≤ Padding.paddedLength input.size := by
  rw [Driver.paddedLength_eq_blockCount input]
  unfold Driver.blockOffset
  omega

/-- Padding establishes all persistent, non-chaining portions of the outer
invariant. -/
theorem blockLoopState_zero_invariant (input : ByteArray)
    (hfit : CalldataFits input) :
    Invariant (Driver.blockLoopState input 0) input Sha256.H0 := by
  refine ⟨blockLoopState_zero input hfit, ?_, ?_⟩
  · intro j hj
    change Compression.kValue (PaddingTrace.padReturned input) j = _
    rw [padReturned_kValue input hfit j hj]
    exact InitializationCorrect.initializedState_kWord input j hj
  · intro i hi
    apply PaddedBlockBridge.paddedBlockAt
      (base := (PaddingTrace.padLengthReady input).memory)
      (input := input)
    · simpa [Driver.blockLoopState, Driver.loopAt] using
        PaddingTrace.padReturned_memory input hfit
    · exact padBase_size input
    · rfl
    · exact hfit
    · exact blockOffset_block_fits input i hi

theorem loopAt_invariant (s : State) (input : ByteArray) (i : Nat)
    (H : Array UInt32) (h : Invariant s input H) :
    Invariant (Driver.loopAt s input i) input H := by
  exact h

/-- The persistent outer invariant supplies the complete schedule expected by
the one-block compression theorem. -/
theorem afterSchedule_slots (s : State) (input : ByteArray) (i : Nat)
    (H : Array UInt32) (returnDest : UInt256) (rest : List UInt256)
    (hfit : CalldataFits input) (hi : i < Driver.blockCount input)
    (hinv : Invariant s input H) :
    ScheduleCorrect.SlotsCorrect
      (Compression.afterSchedule (Driver.loopAt s input i)
        (Driver.messageOffsetWord i) returnDest rest)
      (Padding.paddedMessage input) (Driver.blockOffset i) 64 := by
  unfold Compression.afterSchedule
  apply ScheduleCorrect.scheduleResult_slots_of_paddedBlockAt
  · exact PaddedBlockBridge.scheduleSeparated input
      (Driver.messageOffsetWord i) (Driver.blockOffset i) rfl hfit
      (blockOffset_block_fits input i hi)
  · exact hinv.2.2 i hi

/-- A 32-byte read is outside every scratch write performed by compression. -/
def OutsideScratch (addr : Nat) : Prop :=
  addr + 32 ≤ 288 ∨ Padding.messageOffset ≤ addr

private theorem readWord_writeScratch (memory bytes : ByteArray)
    (addr writeStart writeSize : Nat) (hbytes : bytes.size = writeSize)
    (hstart : 288 ≤ writeStart)
    (hend : writeStart + writeSize ≤ Padding.messageOffset)
    (hout : OutsideScratch addr) :
    MachineState.readWord (MachineState.writeBytes memory bytes writeStart) addr =
      MachineState.readWord memory addr := by
  apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
  rcases hout with hlow | hhigh
  · exact Or.inl (by omega)
  · exact Or.inr (by rw [hbytes]; omega)

private theorem readWord_firstIteration (s : State)
    (msgOff returnDest : UInt256) (rest : List UInt256) (j addr : Nat)
    (hj : j < 64) (hout : OutsideScratch addr) :
    MachineState.readWord
        (Schedule.afterFirstIteration s msgOff returnDest rest j).memory addr =
      MachineState.readWord s.memory addr := by
  rw [ScheduleCorrect.afterFirstIteration_memory]
  apply readWord_writeScratch
  · exact YulEvmCompiler.BytesLemmas.natToBytesPadded_size _ 32
  · rw [ScheduleCorrect.scheduleSlot_eq j hj]
    omega
  · exact ScheduleCorrect.scheduleSlot_end_le_messageOffset j hj
  · exact hout

private theorem readWord_firstLoop (s : State)
    (msgOff returnDest : UInt256) (rest : List UInt256) (n addr : Nat)
    (hn : n ≤ 16) (hout : OutsideScratch addr) :
    MachineState.readWord
        (Schedule.firstLoopState s msgOff returnDest rest n).memory addr =
      MachineState.readWord s.memory addr := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Schedule.firstLoopState]
      exact (readWord_firstIteration
        (Schedule.firstLoopState s msgOff returnDest rest n)
        msgOff returnDest rest n addr (by omega) hout).trans (ih (by omega))

private theorem readWord_secondIteration (s : State)
    (msgOff returnDest : UInt256) (rest : List UInt256) (j addr : Nat)
    (hj : j < 64) (hout : OutsideScratch addr) :
    MachineState.readWord
        (Schedule.afterSecondIteration s msgOff returnDest rest j).memory addr =
      MachineState.readWord s.memory addr := by
  rw [ScheduleCorrect.afterSecondIteration_memory]
  apply readWord_writeScratch
  · exact YulEvmCompiler.BytesLemmas.natToBytesPadded_size _ 32
  · rw [ScheduleCorrect.scheduleSlot_eq j hj]
    omega
  · exact ScheduleCorrect.scheduleSlot_end_le_messageOffset j hj
  · exact hout

private theorem readWord_secondLoop (s : State)
    (msgOff returnDest : UInt256) (rest : List UInt256) (n addr : Nat)
    (hn : n ≤ 48) (hout : OutsideScratch addr) :
    MachineState.readWord
        (Schedule.secondLoopState s msgOff returnDest rest n).memory addr =
      MachineState.readWord s.memory addr := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Schedule.secondLoopState]
      exact (readWord_secondIteration
        (Schedule.secondLoopState s msgOff returnDest rest n)
        msgOff returnDest rest (16 + n) addr (by omega) hout).trans
          (ih (by omega))

private theorem readWord_afterSchedule (s : State)
    (msgOff returnDest : UInt256) (rest : List UInt256) (addr : Nat)
    (hout : OutsideScratch addr) :
    MachineState.readWord
        (Compression.afterSchedule s msgOff returnDest rest).memory addr =
      MachineState.readWord s.memory addr := by
  let q := Schedule.firstLoopState s msgOff (UInt256.ofNat 621)
    (msgOff :: returnDest :: rest) 16
  change MachineState.readWord
      (Schedule.secondLoopState q msgOff (UInt256.ofNat 621)
        (msgOff :: returnDest :: rest) 48).memory addr = _
  exact (readWord_secondLoop q msgOff (UInt256.ofNat 621)
    (msgOff :: returnDest :: rest) 48 addr (by omega) hout).trans
      (readWord_firstLoop s msgOff (UInt256.ofNat 621)
        (msgOff :: returnDest :: rest) 16 addr (by omega) hout)

private theorem readWord_copyHashState (s : State) (addr : Nat)
    (hout : OutsideScratch addr) :
    MachineState.readWord (Compression.copyHashState s).memory addr =
      MachineState.readWord s.memory addr := by
  unfold Compression.copyHashState
  apply readWord_writeScratch (writeSize := 256)
  · exact Challenge.EvmProof.Memory.readPadded_size _ _ _
  · omega
  · norm_num [Padding.messageOffset]
  · exact hout

/- Superseded single-round scratch-memory trace. -/
/-
private theorem readWord_storeReturnedH (q : State) (dest : Nat)
    (value returnDest : UInt256) (context : List UInt256) (addr : Nat)
    (hdest : dest < 8) (hout : OutsideScratch addr) :
    MachineState.readWord
        (Accessors.storeReturned q 288 (UInt256.ofNat dest) value
          returnDest context).memory addr =
      MachineState.readWord q.memory addr := by
  unfold Accessors.storeReturned
  rw [hSlot_eq dest hdest]
  apply readWord_writeScratch (writeSize := 32)
  · exact YulEvmCompiler.BytesLemmas.natToBytesPadded_size _ 32
  · omega
  · norm_num [Padding.messageOffset]
    omega
  · exact hout

private theorem readWord_shiftReturned (q : State) (src dest loadReturn
    storeReturn : Nat) (context : List UInt256) (addr : Nat)
    (hdest : dest < 8) (hout : OutsideScratch addr) :
    MachineState.readWord
        (Compression.shiftReturned q src dest loadReturn storeReturn context).memory
        addr = MachineState.readWord q.memory addr := by
  simpa [Compression.shiftReturned, Compression.shiftLoaded,
    Accessors.loadReturned] using
      readWord_storeReturnedH
        (Compression.shiftLoaded q src loadReturn storeReturn context) dest
        (Compression.hValue q src)
        (UInt256.ofNat storeReturn) context addr hdest hout

private theorem readWord_directStored (q : State) (offset : Nat)
    (value : UInt256) (nextPC : Nat) (context : List UInt256) (addr : Nat)
    (hstart : 288 ≤ offset) (hend : offset + 32 ≤ Padding.messageOffset)
    (hout : OutsideScratch addr) :
    MachineState.readWord
        (Compression.directStored q offset value nextPC context).memory addr =
      MachineState.readWord q.memory addr := by
  unfold Compression.directStored
  apply readWord_writeScratch (writeSize := 32)
  · exact YulEvmCompiler.BytesLemmas.natToBytesPadded_size _ 32
  · exact hstart
  · exact hend
  · exact hout

private theorem readWord_afterSecondIteration (s : State)
    (msgOff returnDest : UInt256) (rest : List UInt256) (j addr : Nat)
    (hout : OutsideScratch addr) :
    MachineState.readWord
        (Compression.afterSecondIteration s msgOff returnDest rest j).memory addr =
      MachineState.readWord s.memory addr := by
  let q7 := Compression.afterShift7 s msgOff returnDest rest j
  let q6 := Compression.afterShift6 s msgOff returnDest rest j
  let q5 := Compression.afterStoreE s msgOff returnDest rest j
  let q4 := Compression.afterStoreH4 s msgOff returnDest rest j
  let q3 := Compression.afterShift3 s msgOff returnDest rest j
  let q2 := Compression.afterShift2 s msgOff returnDest rest j
  let q1 := Compression.afterStoreH1 s msgOff returnDest rest j
  calc
    MachineState.readWord
        (Compression.afterSecondIteration s msgOff returnDest rest j).memory addr =
        MachineState.readWord q1.memory addr := by
      unfold Compression.afterSecondIteration
      apply readWord_writeScratch (writeSize := 32)
      · exact YulEvmCompiler.BytesLemmas.natToBytesPadded_size _ 32
      · omega
      · norm_num [Padding.messageOffset]
      · exact hout
    _ = MachineState.readWord q2.memory addr := by
      exact readWord_directStored q2 320 (Compression.hValue s 0) 906
        (Compression.roundContext s msgOff returnDest rest j) addr
        (by omega) (by norm_num [Padding.messageOffset]) hout
    _ = MachineState.readWord q3.memory addr := by
      exact readWord_shiftReturned q3 1 2 893 900
        (Compression.roundContext s msgOff returnDest rest j) addr
        (by omega) hout
    _ = MachineState.readWord q4.memory addr := by
      exact readWord_shiftReturned q4 2 3 872 879
        (Compression.roundContext s msgOff returnDest rest j) addr
        (by omega) hout
    _ = MachineState.readWord q5.memory addr := by
      simpa [q4, q5, Compression.afterStoreH4, Compression.h4Loaded,
        Accessors.loadReturned] using
        readWord_storeReturnedH
          (Compression.h4Loaded s msgOff returnDest rest j) 4
          (Compression.newH4 s msgOff returnDest rest j) (UInt256.ofNat 858)
          (Compression.roundContext s msgOff returnDest rest j) addr
          (by omega) hout
    _ = MachineState.readWord q6.memory addr := by
      exact readWord_directStored q6 448 (Compression.hValue s 4) 830
        (Compression.roundContext s msgOff returnDest rest j) addr
        (by omega) (by norm_num [Padding.messageOffset]) hout
    _ = MachineState.readWord q7.memory addr := by
      exact readWord_shiftReturned q7 5 6 817 824
        (Compression.roundContext s msgOff returnDest rest j) addr
        (by omega) hout
    _ = MachineState.readWord
        (Compression.afterT2 s msgOff returnDest rest j).memory addr := by
      exact readWord_shiftReturned
        (Compression.afterT2 s msgOff returnDest rest j) 6 7 796 803
        (Compression.roundContext s msgOff returnDest rest j) addr
        (by omega) hout
    _ = MachineState.readWord s.memory addr := by
      rfl

private theorem readWord_roundLoop (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (n addr : Nat) (hout : OutsideScratch addr) :
    MachineState.readWord
        (Compression.roundLoopState s msgOff returnDest rest n).memory addr =
      MachineState.readWord s.memory addr := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Compression.roundLoopState]
      exact (readWord_afterSecondIteration
        (Compression.roundLoopState s msgOff returnDest rest n)
        msgOff returnDest rest n addr hout).trans ih
-/

private theorem readWord_storeReturnedH (q : State) (dest : Nat)
    (value returnDest : UInt256) (context : List UInt256) (addr : Nat)
    (hdest : dest < 8) (hout : OutsideScratch addr) :
    MachineState.readWord
        (Accessors.storeReturned q 288 (UInt256.ofNat dest) value
          returnDest context).memory addr =
      MachineState.readWord q.memory addr := by
  unfold Accessors.storeReturned
  rw [hSlot_eq dest hdest]
  apply readWord_writeScratch (writeSize := 32)
  · exact YulEvmCompiler.BytesLemmas.natToBytesPadded_size _ 32
  · omega
  · norm_num [Padding.messageOffset]
    omega
  · exact hout

private theorem readWord_storedWord (q : State) (offset : Nat)
    (value : UInt256) (addr : Nat)
    (hstart : 288 ≤ offset) (hend : offset + 32 ≤ Padding.messageOffset)
    (hout : OutsideScratch addr) :
    MachineState.readWord (Compression.storedWord q offset value).memory addr =
      MachineState.readWord q.memory addr := by
  unfold Compression.storedWord
  apply readWord_writeScratch (writeSize := 32)
  · exact YulEvmCompiler.BytesLemmas.natToBytesPadded_size _ 32
  · exact hstart
  · exact hend
  · exact hout

private theorem readWord_afterPair (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j addr : Nat) (hout : OutsideScratch addr) :
    MachineState.readWord
        (Compression.afterPair s msgOff returnDest rest j).memory addr =
      MachineState.readWord s.memory addr := by
  let q0 := Compression.afterPairT21 s msgOff returnDest rest j
  let q1 := Compression.storedWord q0 288 (Compression.pairA2 s j)
  let q2 := Compression.storedWord q1 320 (Compression.pairA1 s j)
  let q3 := Compression.storedWord q2 352 (Compression.hValue s 0)
  let q4 := Compression.storedWord q3 384 (Compression.hValue s 1)
  let q5 := Compression.storedWord q4 416 (Compression.pairE2 s j)
  let q6 := Compression.storedWord q5 448 (Compression.pairE1 s j)
  let q7 := Compression.storedWord q6 480 (Compression.hValue s 4)
  let q8 := Compression.storedWord q7 512 (Compression.hValue s 5)
  change MachineState.readWord q8.memory addr = MachineState.readWord s.memory addr
  exact (readWord_storedWord q7 512 (Compression.hValue s 5) addr
    (by omega) (by norm_num [Padding.messageOffset]) hout).trans
    ((readWord_storedWord q6 480 (Compression.hValue s 4) addr
      (by omega) (by norm_num [Padding.messageOffset]) hout).trans
    ((readWord_storedWord q5 448 (Compression.pairE1 s j) addr
      (by omega) (by norm_num [Padding.messageOffset]) hout).trans
    ((readWord_storedWord q4 416 (Compression.pairE2 s j) addr
      (by omega) (by norm_num [Padding.messageOffset]) hout).trans
    ((readWord_storedWord q3 384 (Compression.hValue s 1) addr
      (by omega) (by norm_num [Padding.messageOffset]) hout).trans
    ((readWord_storedWord q2 352 (Compression.hValue s 0) addr
      (by omega) (by norm_num [Padding.messageOffset]) hout).trans
    ((readWord_storedWord q1 320 (Compression.pairA1 s j) addr
      (by omega) (by norm_num [Padding.messageOffset]) hout).trans
    ((readWord_storedWord q0 288 (Compression.pairA2 s j) addr
      (by omega) (by norm_num [Padding.messageOffset]) hout).trans (by rfl))))))))

private theorem readWord_pairLoop (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (n addr : Nat) (hout : OutsideScratch addr) :
    MachineState.readWord
        (PairCompositionTest.pairLoopState s msgOff returnDest rest n).memory addr =
      MachineState.readWord s.memory addr := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [PairCompositionTest.pairLoopState]
      exact (readWord_afterPair
        (PairCompositionTest.pairLoopState s msgOff returnDest rest n)
        msgOff returnDest rest (2 * n) addr hout).trans ih

private theorem readWord_roundLoop (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (n addr : Nat) (hout : OutsideScratch addr) :
    MachineState.readWord
        (Compression.roundLoopState s msgOff returnDest rest n).memory addr =
      MachineState.readWord s.memory addr := by
  simpa [Compression.roundLoopState] using
    readWord_pairLoop s msgOff returnDest rest (n / 2) addr hout

private theorem readWord_afterFoldIteration (s : State)
    (msgOff returnDest : UInt256) (rest : List UInt256) (i addr : Nat)
    (hi : i < 8) (hout : OutsideScratch addr) :
    MachineState.readWord
        (Compression.afterFoldIteration s msgOff returnDest rest i).memory addr =
      MachineState.readWord s.memory addr := by
  simpa [Compression.afterFoldIteration, Compression.foldGotSet,
    Compression.foldGotH, Compression.loadedSaved, Accessors.loadReturned] using
    readWord_storeReturnedH
      (Compression.foldGotH s msgOff returnDest rest i) i
      (Compression.foldedValue s msgOff returnDest rest i)
      (UInt256.ofNat 981) ([UInt256.ofNat i, msgOff, returnDest] ++ rest)
      addr hi hout

private theorem readWord_foldLoop (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (n addr : Nat) (hn : n ≤ 8)
    (hout : OutsideScratch addr) :
    MachineState.readWord
        (Compression.foldLoopState s msgOff returnDest rest n).memory addr =
      MachineState.readWord s.memory addr := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Compression.foldLoopState]
      exact (readWord_afterFoldIteration
        (Compression.foldLoopState s msgOff returnDest rest n)
        msgOff returnDest rest n addr (by omega) hout).trans (ih (by omega))

/-- Compression changes only scratch memory: the constant table below byte
288 and the padded message beginning at `messageOffset` are preserved. -/
theorem compressResult_readWord (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (addr : Nat) (hout : OutsideScratch addr) :
    MachineState.readWord
        (Compression.compressResult s msgOff returnDest rest).memory addr =
      MachineState.readWord s.memory addr := by
  let scheduled := Compression.afterSchedule s msgOff returnDest rest
  let prepared := Compression.copyHashState scheduled
  let rounded := Compression.roundLoopState prepared msgOff returnDest rest 64
  change MachineState.readWord
      (Compression.foldLoopState rounded msgOff returnDest rest 8).memory addr = _
  exact (readWord_foldLoop rounded msgOff returnDest rest 8 addr
    (by omega) hout).trans
      ((readWord_roundLoop prepared msgOff returnDest rest 64 addr hout).trans
        ((readWord_copyHashState scheduled addr hout).trans
          (readWord_afterSchedule s msgOff returnDest rest addr hout)))

theorem compressResult_paddedBlocksCorrect (s : State) (input : ByteArray)
    (msgOff returnDest : UInt256) (rest : List UInt256)
    (hfit : CalldataFits input) (hpadded : PaddedBlocksCorrect s input) :
    PaddedBlocksCorrect (Compression.compressResult s msgOff returnDest rest)
      input := by
  intro i hi k hk
  unfold Schedule.initialWord
  rw [compressResult_readWord]
  · exact hpadded i hi k hk
  · right
    exact PaddedBlockBridge.scheduleSeparated input
      (Driver.messageOffsetWord i) (Driver.blockOffset i) rfl hfit
      (blockOffset_block_fits input i hi) k hk

/-- One outer-loop iteration absorbs exactly the selected padded block and
preserves every persistent input needed by later iterations. -/
theorem afterIteration_invariant (s : State) (input : ByteArray) (i : Nat)
    (H : Array UInt32) (hfit : CalldataFits input)
    (hi : i < Driver.blockCount input) (hinv : Invariant s input H) :
    Invariant (Driver.afterIteration s input i) input
      (Sha256.compressBlock H (Padding.paddedMessage input)
        (Driver.blockOffset i)) := by
  let entered := Driver.loopAt s input i
  have hentered : Invariant entered input H :=
    loopAt_invariant s input i H hinv
  have hslots := afterSchedule_slots s input i H (UInt256.ofNat 1390)
    [Driver.blockOffsetWord i, Padding.paddedWord input] hfit hi hinv
  refine ⟨?_, ?_, ?_⟩
  · intro k hk
    change Compression.hValue
      (Compression.compressResult entered (Driver.messageOffsetWord i)
        (UInt256.ofNat 1390)
        [Driver.blockOffsetWord i, Padding.paddedWord input]) k = _
    exact CompressionCorrect.compressResult_eq_compressBlock entered
      (Driver.messageOffsetWord i) (UInt256.ofNat 1390)
      [Driver.blockOffsetWord i, Padding.paddedWord input]
      (Padding.paddedMessage input) (Driver.blockOffset i) H
      hentered.1 hentered.2.1 hslots k hk
  · intro k hk
    change Compression.kValue
      (Compression.compressResult entered (Driver.messageOffsetWord i)
        (UInt256.ofNat 1390)
        [Driver.blockOffsetWord i, Padding.paddedWord input]) k = _
    exact (CompressionCorrect.compressResult_kValue entered
      (Driver.messageOffsetWord i) (UInt256.ofNat 1390)
      [Driver.blockOffsetWord i, Padding.paddedWord input] k hk).trans
        (hentered.2.1 k hk)
  · change PaddedBlocksCorrect
      (Compression.compressResult entered (Driver.messageOffsetWord i)
        (UInt256.ofNat 1390)
        [Driver.blockOffsetWord i, Padding.paddedWord input]) input
    exact compressResult_paddedBlocksCorrect entered input
      (Driver.messageOffsetWord i) (UInt256.ofNat 1390)
      [Driver.blockOffsetWord i, Padding.paddedWord input]
      hfit hentered.2.2

/-- Complete functional invariant for every prefix of the block loop. -/
theorem blockLoopState_invariant (input : ByteArray) (hfit : CalldataFits input)
    (i : Nat) (hi : i ≤ Driver.blockCount input) :
    Invariant (Driver.blockLoopState input i) input
      (SpecBridge.absorbBlocks Sha256.H0 (Padding.paddedMessage input) 0 i) := by
  induction i with
  | zero => simpa using blockLoopState_zero_invariant input hfit
  | succ i ih =>
      rw [Driver.blockLoopState]
      have hstep := afterIteration_invariant (Driver.blockLoopState input i)
        input i
        (SpecBridge.absorbBlocks Sha256.H0 (Padding.paddedMessage input) 0 i)
        hfit (by omega) (ih (by omega))
      rw [SpecBridge.absorbBlocks_succ]
      simpa [Driver.blockOffset] using hstep

theorem finalBlockLoop_chain (input : ByteArray) (hfit : CalldataFits input) :
    ChainRepresents
      (Driver.blockLoopState input (Driver.blockCount input))
      (SpecBridge.absorbBlocks Sha256.H0 (Padding.paddedMessage input) 0
        (Driver.blockCount input)) :=
  (blockLoopState_invariant input hfit (Driver.blockCount input)
    (by omega)).1

open EvmSemantics

theorem or_ofNat_eq_add {a b : Nat}
    (ha : a < 2 ^ 256) (hb : b < 2 ^ 256)
    (hab : a ||| b < 2 ^ 256) (hdis : a + b = a ||| b) :
    UInt256.lor (UInt256.ofNat a) (UInt256.ofNat b) =
      UInt256.ofNat (a + b) := by
  apply Challenge.EvmProof.Word.word_ext
  unfold UInt256.lor UInt256.toNat
  simp only [Fin.lor]
  simp only [UInt256.ofNat, Fin.ofNat]
  change (a % 2 ^ 256 ||| b % 2 ^ 256) % 2 ^ 256 =
    (a + b) % 2 ^ 256
  rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb, hdis,
    Nat.mod_eq_of_lt hab]

theorem concatWord {a b shift : Nat}
    (ha : a < 2 ^ (256 - shift)) (hshift : shift < 256)
    (hb : b < 2 ^ shift) :
    UInt256.lor
      (UInt256.shiftLeft (UInt256.ofNat a) (UInt256.ofNat shift))
      (UInt256.ofNat b) =
    UInt256.ofNat (a * 2 ^ shift + b) := by
  have ha256 : a < 2 ^ 256 := by
    apply lt_of_lt_of_le ha
    exact pow_le_pow_right₀ (by omega) (by omega)
  have hpow : 2 ^ (256 - shift) * 2 ^ shift = 2 ^ 256 := by
    rw [← Nat.pow_add]
    congr 1
    omega
  have hmul : a * 2 ^ shift < 2 ^ 256 := by
    nlinarith [Nat.mul_lt_mul_of_pos_right ha (Nat.two_pow_pos shift)]
  rw [Challenge.EvmProof.Word.shiftLeft_ofNat ha256 hshift hmul]
  apply or_ofNat_eq_add hmul (lt_trans hb (Nat.pow_lt_pow_right (by omega) hshift))
  · rw [← Nat.shiftLeft_eq, ← Nat.shiftLeft_add_eq_or_of_lt hb,
      Nat.shiftLeft_eq]
    calc
      a * 2 ^ shift + b < a * 2 ^ shift + 2 ^ shift := by omega
      _ = (a + 1) * 2 ^ shift := by ring
      _ ≤ 2 ^ (256 - shift) * 2 ^ shift := by
        exact Nat.mul_le_mul_right _ ha
      _ = 2 ^ 256 := hpow
  · rw [← Nat.shiftLeft_eq]
    exact Nat.shiftLeft_add_eq_or_of_lt hb a


theorem writeBE32_empty (x : UInt32) :
    Sha256.writeBE32 ByteArray.empty x =
      Data.Bytes.natToBytesPadded x.toNat 4 := by
  apply ByteArray.ext
  norm_num [Sha256.writeBE32, Data.Bytes.natToBytesPadded,
    UInt32.toNat_shiftRight, Nat.shiftRight_eq_div_pow,
    List.range', List.range.loop]
  constructor
  · apply UInt8.toNat_inj.mp
    simp [UInt32.toNat_shiftRight, Nat.shiftRight_eq_div_pow,
      Nat.div_div_eq_div_mul]
    rw [show 255 = 2 ^ 8 - 1 by norm_num,
      Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (Nat.mod_lt _ (by omega))]
  constructor
  · apply UInt8.toNat_inj.mp
    simp [UInt32.toNat_shiftRight, Nat.shiftRight_eq_div_pow,
      Nat.div_div_eq_div_mul]
    rw [show 255 = 2 ^ 8 - 1 by norm_num,
      Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (Nat.mod_lt _ (by omega))]
  constructor
  · apply UInt8.toNat_inj.mp
    simp [UInt32.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
    rw [show 255 = 2 ^ 8 - 1 by norm_num,
      Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (Nat.mod_lt _ (by omega))]
  · apply UInt8.toNat_inj.mp
    simp
    rw [show 255 = 2 ^ 8 - 1 by norm_num,
      Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (Nat.mod_lt _ (by omega))]

theorem writeBE32_append (acc : ByteArray) (x : UInt32) :
    Sha256.writeBE32 acc x =
      acc ++ Data.Bytes.natToBytesPadded x.toNat 4 := by
  rw [← writeBE32_empty]
  apply ByteArray.ext
  norm_num [Sha256.writeBE32, List.range', List.range.loop]
  simp only [Array.push_eq_append, Array.append_assoc]
  congr 1

theorem natToBE_concat (a b hi lo : Nat) (hb : b < 256 ^ lo) :
    YulEvmCompiler.natToBE (a * 256 ^ lo + b) (hi + lo) =
      YulEvmCompiler.natToBE a hi ++ YulEvmCompiler.natToBE b lo := by
  induction lo generalizing b with
  | zero =>
      have : b = 0 := by simpa using hb
      subst b
      simp [YulEvmCompiler.natToBE]
  | succ lo ih =>
      have hbdiv : b / 256 < 256 ^ lo := by
        rw [Nat.div_lt_iff_lt_mul (by omega)]
        simpa [Nat.pow_succ] using hb
      have hquot : (a * 256 ^ (lo + 1) + b) / 256 =
          a * 256 ^ lo + b / 256 := by
        rw [Nat.pow_succ]
        rw [show a * (256 ^ lo * 256) = 256 * (a * 256 ^ lo) by ring,
          Nat.mul_add_div (by omega)]
      have hmod : (a * 256 ^ (lo + 1) + b) % 256 = b % 256 := by
        rw [Nat.pow_succ]
        rw [show a * (256 ^ lo * 256) = 256 * (a * 256 ^ lo) by ring,
          Nat.mul_add_mod]
      rw [show hi + (lo + 1) = (hi + lo) + 1 by omega,
        YulEvmCompiler.natToBE, hquot, hmod, ih (b / 256) hbdiv,
        YulEvmCompiler.natToBE, List.append_assoc]

theorem natToBytesPadded_concat (a b hi lo : Nat) (hb : b < 256 ^ lo) :
    Data.Bytes.natToBytesPadded (a * 256 ^ lo + b) (hi + lo) =
      Data.Bytes.natToBytesPadded a hi ++
        Data.Bytes.natToBytesPadded b lo := by
  rw [Challenge.EvmProof.Memory.natToBytesPadded_eq_natToBE,
    Challenge.EvmProof.Memory.natToBytesPadded_eq_natToBE,
    Challenge.EvmProof.Memory.natToBytesPadded_eq_natToBE,
    natToBE_concat a b hi lo hb]
  apply ByteArray.ext
  simp

def packNat (x0 x1 x2 x3 x4 x5 x6 x7 : UInt32) : Nat :=
  (((((((x0.toNat * 2 ^ 32 + x1.toNat) * 2 ^ 32 + x2.toNat) * 2 ^ 32 +
      x3.toNat) * 2 ^ 32 + x4.toNat) * 2 ^ 32 + x5.toNat) * 2 ^ 32 +
      x6.toNat) * 2 ^ 32 + x7.toNat)

theorem packedBytes_eq
    (x0 x1 x2 x3 x4 x5 x6 x7 : UInt32) :
    Data.Bytes.natToBytesPadded (packNat x0 x1 x2 x3 x4 x5 x6 x7) 32 =
      Sha256.writeBE32
        (Sha256.writeBE32
          (Sha256.writeBE32
            (Sha256.writeBE32
              (Sha256.writeBE32
                (Sha256.writeBE32
                  (Sha256.writeBE32
                    (Sha256.writeBE32 ByteArray.empty x0) x1) x2) x3) x4) x5) x6) x7 := by
  rw [writeBE32_append, writeBE32_append, writeBE32_append,
    writeBE32_append, writeBE32_append, writeBE32_append,
    writeBE32_append, writeBE32_empty]
  unfold packNat
  rw [show 2 ^ 32 = 256 ^ 4 by norm_num]
  rw [natToBytesPadded_concat _ x7.toNat 28 4 (by
        exact lt_of_lt_of_le x7.toNat_lt (by norm_num)),
      natToBytesPadded_concat _ x6.toNat 24 4 (by
        exact lt_of_lt_of_le x6.toNat_lt (by norm_num)),
      natToBytesPadded_concat _ x5.toNat 20 4 (by
        exact lt_of_lt_of_le x5.toNat_lt (by norm_num)),
      natToBytesPadded_concat _ x4.toNat 16 4 (by
        exact lt_of_lt_of_le x4.toNat_lt (by norm_num)),
      natToBytesPadded_concat _ x3.toNat 12 4 (by
        exact lt_of_lt_of_le x3.toNat_lt (by norm_num)),
      natToBytesPadded_concat _ x2.toNat 8 4 (by
        exact lt_of_lt_of_le x2.toNat_lt (by norm_num)),
      natToBytesPadded_concat _ x1.toNat 4 4 (by
        exact lt_of_lt_of_le x1.toNat_lt (by norm_num))]

theorem shiftUInt32 (x : UInt32) (shift : Nat) (hs : shift ≤ 224) :
    UInt256.shiftLeft (Challenge.EvmProof.Word.ofUInt32 x) (UInt256.ofNat shift) =
      UInt256.ofNat (x.toNat * 2 ^ shift) := by
  apply Challenge.EvmProof.Word.shiftLeft_ofNat
  · exact Nat.lt_trans x.toNat_lt (by norm_num)
  · omega
  · calc
      x.toNat * 2 ^ shift < 2 ^ 32 * 2 ^ shift :=
        Nat.mul_lt_mul_of_pos_right x.toNat_lt (Nat.two_pow_pos shift)
      _ = 2 ^ (32 + shift) := by rw [Nat.pow_add]
      _ ≤ 2 ^ 256 := pow_le_pow_right₀ (by omega) (by omega)

theorem orShifted (a b width low : Nat) (hb : b < 2 ^ width) :
    a * 2 ^ (width + low) ||| b * 2 ^ low =
      (a * 2 ^ width + b) * 2 ^ low := by
  rw [← Nat.shiftLeft_eq, ← Nat.shiftLeft_eq]
  rw [Nat.shiftLeft_add]
  rw [← Nat.shiftLeft_or_distrib]
  rw [← Nat.shiftLeft_add_eq_or_of_lt hb]
  simp [Nat.shiftLeft_eq]

theorem concatNat_lt {a b wa wb : Nat}
    (ha : a < 2 ^ wa) (hb : b < 2 ^ wb) :
    a * 2 ^ wb + b < 2 ^ (wa + wb) := by
  calc
    a * 2 ^ wb + b < a * 2 ^ wb + 2 ^ wb := by omega
    _ = (a + 1) * 2 ^ wb := by ring
    _ ≤ 2 ^ wa * 2 ^ wb := Nat.mul_le_mul_right _ ha
    _ = 2 ^ (wa + wb) := by rw [Nat.pow_add]

theorem wordOrShifted (a b width low : Nat)
    (ha : a * 2 ^ (width + low) < 2 ^ 256)
    (hbterm : b * 2 ^ low < 2 ^ 256)
    (hout : (a * 2 ^ width + b) * 2 ^ low < 2 ^ 256)
    (hb : b < 2 ^ width) :
    UInt256.lor
      (UInt256.ofNat (a * 2 ^ (width + low)))
      (UInt256.ofNat (b * 2 ^ low)) =
      UInt256.ofNat ((a * 2 ^ width + b) * 2 ^ low) := by
  calc
    _ = UInt256.ofNat
        (a * 2 ^ (width + low) + b * 2 ^ low) := by
      apply or_ofNat_eq_add ha hbterm
      · rw [orShifted a b width low hb]
        exact hout
      · rw [orShifted a b width low hb]
        ring
    _ = _ := by
      apply congrArg UInt256.ofNat
      ring

theorem placed_lt_256 (width shift : Nat) {n : Nat} (hn : n < 2 ^ width)
    (hsum : width + shift ≤ 256) :
    n * 2 ^ shift < 2 ^ 256 := by
  calc
    n * 2 ^ shift < 2 ^ width * 2 ^ shift :=
      Nat.mul_lt_mul_of_pos_right hn (Nat.two_pow_pos shift)
    _ = 2 ^ (width + shift) := by rw [Nat.pow_add]
    _ ≤ 2 ^ 256 := pow_le_pow_right₀ (by omega) hsum

theorem directPackWord (x0 x1 x2 x3 x4 x5 x6 x7 : UInt32) :
    UInt256.lor
      (UInt256.lor
        (UInt256.lor
          (UInt256.shiftLeft (Challenge.EvmProof.Word.ofUInt32 x0) (UInt256.ofNat 224))
          (UInt256.shiftLeft (Challenge.EvmProof.Word.ofUInt32 x1) (UInt256.ofNat 192)))
        (UInt256.lor
          (UInt256.shiftLeft (Challenge.EvmProof.Word.ofUInt32 x2) (UInt256.ofNat 160))
          (UInt256.shiftLeft (Challenge.EvmProof.Word.ofUInt32 x3) (UInt256.ofNat 128))))
      (UInt256.lor
        (UInt256.lor
          (UInt256.shiftLeft (Challenge.EvmProof.Word.ofUInt32 x4) (UInt256.ofNat 96))
          (UInt256.shiftLeft (Challenge.EvmProof.Word.ofUInt32 x5) (UInt256.ofNat 64)))
        (UInt256.lor
          (UInt256.shiftLeft (Challenge.EvmProof.Word.ofUInt32 x6) (UInt256.ofNat 32))
          (Challenge.EvmProof.Word.ofUInt32 x7))) =
    UInt256.ofNat (packNat x0 x1 x2 x3 x4 x5 x6 x7) := by
  let n0 := x0.toNat
  let n1 := x1.toNat
  let n2 := x2.toNat
  let n3 := x3.toNat
  let n4 := x4.toNat
  let n5 := x5.toNat
  let n6 := x6.toNat
  let n7 := x7.toNat
  have h0 : n0 < 2 ^ 32 := x0.toNat_lt
  have h1 : n1 < 2 ^ 32 := x1.toNat_lt
  have h2 : n2 < 2 ^ 32 := x2.toNat_lt
  have h3 : n3 < 2 ^ 32 := x3.toNat_lt
  have h4 : n4 < 2 ^ 32 := x4.toNat_lt
  have h5 : n5 < 2 ^ 32 := x5.toNat_lt
  have h6 : n6 < 2 ^ 32 := x6.toNat_lt
  have h7 : n7 < 2 ^ 32 := x7.toNat_lt
  let n01 := n0 * 2 ^ 32 + n1
  let n23 := n2 * 2 ^ 32 + n3
  let n45 := n4 * 2 ^ 32 + n5
  let n67 := n6 * 2 ^ 32 + n7
  have h01 : n01 < 2 ^ 64 := by
    simpa [n01] using concatNat_lt h0 h1
  have h23 : n23 < 2 ^ 64 := by
    simpa [n23] using concatNat_lt h2 h3
  have h45 : n45 < 2 ^ 64 := by
    simpa [n45] using concatNat_lt h4 h5
  have h67 : n67 < 2 ^ 64 := by
    simpa [n67] using concatNat_lt h6 h7
  let n0123 := n01 * 2 ^ 64 + n23
  let n4567 := n45 * 2 ^ 64 + n67
  have h0123 : n0123 < 2 ^ 128 := by
    simpa [n0123] using concatNat_lt h01 h23
  have h4567 : n4567 < 2 ^ 128 := by
    simpa [n4567] using concatNat_lt h45 h67
  rw [shiftUInt32 x0 224 (by omega), shiftUInt32 x1 192 (by omega),
    shiftUInt32 x2 160 (by omega), shiftUInt32 x3 128 (by omega),
    shiftUInt32 x4 96 (by omega), shiftUInt32 x5 64 (by omega),
    shiftUInt32 x6 32 (by omega)]
  change UInt256.lor
      (UInt256.lor
        (UInt256.lor (UInt256.ofNat (n0 * 2 ^ 224))
          (UInt256.ofNat (n1 * 2 ^ 192)))
        (UInt256.lor (UInt256.ofNat (n2 * 2 ^ 160))
          (UInt256.ofNat (n3 * 2 ^ 128))))
      (UInt256.lor
        (UInt256.lor (UInt256.ofNat (n4 * 2 ^ 96))
          (UInt256.ofNat (n5 * 2 ^ 64)))
        (UInt256.lor (UInt256.ofNat (n6 * 2 ^ 32))
          (UInt256.ofNat n7))) = _
  rw [wordOrShifted n0 n1 32 192 (by
        simpa using placed_lt_256 32 224 h0 (by omega))
      (placed_lt_256 32 192 h1 (by omega))
      (placed_lt_256 64 192 h01 (by omega)) h1]
  -- The remaining six tree nodes have identical power-of-two bounds.
  rw [wordOrShifted n2 n3 32 128 (by
        simpa using placed_lt_256 32 160 h2 (by omega))
      (placed_lt_256 32 128 h3 (by omega))
      (placed_lt_256 64 128 h23 (by omega)) h3]
  rw [wordOrShifted n01 n23 64 128 (by
        simpa using placed_lt_256 64 192 h01 (by omega))
      (placed_lt_256 64 128 h23 (by omega))
      (placed_lt_256 128 128 h0123 (by omega)) h23]
  rw [wordOrShifted n4 n5 32 64 (by
        simpa using placed_lt_256 32 96 h4 (by omega))
      (placed_lt_256 32 64 h5 (by omega))
      (placed_lt_256 64 64 h45 (by omega)) h5]
  rw [show UInt256.lor (UInt256.ofNat (n6 * 2 ^ 32)) (UInt256.ofNat n7) =
      UInt256.ofNat n67 by
    simpa [n67] using wordOrShifted n6 n7 32 0
      (placed_lt_256 32 32 h6 (by omega))
      (by simpa using placed_lt_256 32 0 h7 (by omega))
      (by simpa [n67] using placed_lt_256 64 0 h67 (by omega)) h7]
  rw [show UInt256.lor (UInt256.ofNat (n45 * 2 ^ 64)) (UInt256.ofNat n67) =
      UInt256.ofNat n4567 by
    simpa [n4567] using wordOrShifted n45 n67 64 0
      (placed_lt_256 64 64 h45 (by omega))
      (by simpa using placed_lt_256 64 0 h67 (by omega))
      (by simpa [n4567] using placed_lt_256 128 0 h4567 (by omega)) h67]
  rw [show UInt256.lor (UInt256.ofNat (n0123 * 2 ^ 128))
      (UInt256.ofNat n4567) =
      UInt256.ofNat (n0123 * 2 ^ 128 + n4567) by
    simpa using wordOrShifted n0123 n4567 128 0
      (placed_lt_256 128 128 h0123 (by omega))
      (by simpa using placed_lt_256 128 0 h4567 (by omega))
      (by simpa using concatNat_lt h0123 h4567) h4567]
  unfold packNat
  dsimp [n0, n1, n2, n3, n4, n5, n6, n7,
    n01, n23, n45, n67, n0123, n4567]
  apply congrArg UInt256.ofNat
  ring

theorem packNat_lt (x0 x1 x2 x3 x4 x5 x6 x7 : UInt32) :
    packNat x0 x1 x2 x3 x4 x5 x6 x7 < 2 ^ 256 := by
  have h01 := concatNat_lt x0.toNat_lt x1.toNat_lt
  have h23 := concatNat_lt x2.toNat_lt x3.toNat_lt
  have h45 := concatNat_lt x4.toNat_lt x5.toNat_lt
  have h67 := concatNat_lt x6.toNat_lt x7.toNat_lt
  have h0123 := concatNat_lt h01 h23
  have h4567 := concatNat_lt h45 h67
  have h := concatNat_lt h0123 h4567
  unfold packNat
  calc
    _ = ((x0.toNat * 2 ^ 32 + x1.toNat) * 2 ^ 64 +
          (x2.toNat * 2 ^ 32 + x3.toNat)) * 2 ^ 128 +
        ((x4.toNat * 2 ^ 32 + x5.toNat) * 2 ^ 64 +
          (x6.toNat * 2 ^ 32 + x7.toNat)) := by ring
    _ < 2 ^ 256 := h

open EvmSemantics.EVM

theorem digestBytes_eq_emitDigest (s : State) (H : Array UInt32)
    (h : ∀ i, i < 8 →
      Output.hWord s i = Challenge.EvmProof.Word.ofUInt32 H[i]!) :
    Output.digestBytes s = SpecBridge.emitDigest H := by
  unfold Output.digestBytes Output.digestWord Output.shifted1 Output.pair23
    Output.shifted3 Output.lowHalf Output.pair45 Output.shifted5 Output.pair67
  rw [h 0 (by omega), h 1 (by omega), h 2 (by omega), h 3 (by omega),
    h 4 (by omega), h 5 (by omega), h 6 (by omega), h 7 (by omega)]
  rw [directPackWord, Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt (packNat_lt H[0]! H[1]! H[2]! H[3]!
      H[4]! H[5]! H[6]! H[7]!), packedBytes_eq]
  norm_num [SpecBridge.emitDigest, List.range, List.range.loop]

/-- Once the outer loop has absorbed every padded block, the concrete output
packing is the challenge's canonical SHA-256 specification. -/
theorem digestBytes_eq_spec_of_chain (s : State) (input : ByteArray)
    (hchain : ChainRepresents s
      (SpecBridge.absorbBlocks Sha256.H0 (Padding.paddedMessage input) 0
        (Driver.blockCount input))) :
    Output.digestBytes s = Challenge.Sha256.spec input := by
  calc
    Output.digestBytes s = SpecBridge.emitDigest
        (SpecBridge.absorbBlocks Sha256.H0 (Padding.paddedMessage input) 0
          (Driver.blockCount input)) := by
      apply digestBytes_eq_emitDigest
      intro i hi
      exact hchain i hi
    _ = SpecBridge.paddedHash input := by rfl
    _ = Challenge.Sha256.spec input := HashSpecBridge.paddedHash_eq_spec input

/-- Functional postcondition of the exact terminal state used by
`Driver.gasSteps_reference`. -/
theorem referenceOutput_correct (input : ByteArray) (hfit : CalldataFits input) :
    (Output.outputResult
      (Driver.blockLoopState input (Driver.blockCount input))
      [Padding.paddedWord input]).hReturn = Challenge.Sha256.spec input := by
  rw [Output.outputResult_returnData]
  exact digestBytes_eq_spec_of_chain
    (Driver.blockLoopState input (Driver.blockCount input)) input
    (finalBlockLoop_chain input hfit)

end Challenge.Sha256.Submission.Proofs.Bytecode.DriverCorrect
