import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRunBridge
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackCompression
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackMemory
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ScheduleActiveWords

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 1000000

/-!
# H10 block endpoint model

This names the endpoint used by the round and tail traces. The mathematical
message words are linked to the actual schedule slots below. No machine trace
or unconditional correctness theorem is asserted here.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StackBlockModel

open Challenge.Ripemd160
open EvmSemantics EvmSemantics.EVM

def driverRest (input : ByteArray) (i : Nat) : List UInt256 :=
  [DriverTrace.blockOffsetWord i, Padding.paddedWord input]

def scheduleRest (input : ByteArray) (i : Nat) : List UInt256 :=
  [DriverTrace.messageOffsetWord i, UInt256.ofNat 0x643] ++ driverRest input i

def scheduledState (s : State) (input : ByteArray) (i : Nat) : State :=
  Schedule.loopState s (DriverTrace.messageOffsetWord i) (UInt256.ofNat 0x72f)
    (scheduleRest input i) 16

def blockWords (input : ByteArray) (i : Nat) : Nat → UInt32 :=
  fun k => (CompressionCorrect.schedule (Padding.paddedMessage input)
    (DriverTrace.blockOffset i))[k]!

theorem blockWords_eq_readLE32 (input : ByteArray) (i k : Nat) (hk : k < 16) :
    blockWords input i k = Crypto.Ripemd160.readLE32 (Padding.paddedMessage input)
      (DriverTrace.blockOffset i + k * 4) := by
  interval_cases k <;> simp [blockWords, CompressionCorrect.schedule, List.range']

def resultHash (s : State) (input : ByteArray) (i : Nat) : Compression.EvmHashState :=
  StackCompression.compress (blockWords input i) (StackMemory.hashAt s.memory)

def resultState (s : State) (input : ByteArray) (i : Nat) : State :=
  {scheduledState s input i with
    pc := UInt256.ofNat 0x643
    stack := driverRest input i
    memory := StackMemory.storeHash (scheduledState s input i).memory (resultHash s input i)}

@[simp] theorem resultState_executionEnv (s : State) (input : ByteArray) (i : Nat) :
    (resultState s input i).executionEnv = s.executionEnv := by
  simp only [resultState, scheduledState, Schedule.loopState_executionEnv]

@[simp] theorem resultState_halt (s : State) (input : ByteArray) (i : Nat) :
    (resultState s input i).halt = s.halt := by
  simp only [resultState, scheduledState, Schedule.loopState_halt]

private theorem scheduleLoop_callStack (s : State)
    (messageOffset returnDest : UInt256) (rest : List UInt256) (n : Nat) :
    (Schedule.loopState s messageOffset returnDest rest n).callStack = s.callStack := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [Schedule.loopState, Schedule.afterIteration, Schedule.afterStore,
      Schedule.afterRead, ih]

@[simp] theorem resultState_callStack (s : State) (input : ByteArray) (i : Nat) :
    (resultState s input i).callStack = s.callStack := by
  simp only [resultState, scheduledState, scheduleLoop_callStack]

theorem scheduleLoop_word_outsideX (s : State) (messageOffset returnDest : UInt256)
    (rest : List UInt256) (n address : Nat) (hn : n ≤ 16)
    (houtside : address + 32 ≤ 0x2a0 ∨ 0x4a0 ≤ address) :
    MachineState.readWord (Schedule.loopState s messageOffset returnDest rest n).memory
        address = MachineState.readWord s.memory address := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Schedule.loopState, ScheduleCorrect.afterIteration_memory]
      rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint]
      · exact ih (by omega)
      · simp only [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
        rw [ScheduleCorrect.xSlotWord_toNat n (by omega)]
        rcases houtside with hbefore | hafter
        · left
          omega
        · right
          omega

theorem resultState_word_above (s : State) (input : ByteArray) (i address : Nat)
    (haddress : 0x4a0 ≤ address) :
    StackRunBridge.wordAt (resultState s input i) address =
      StackRunBridge.wordAt s address := by
  unfold StackRunBridge.wordAt resultState
  rw [StackMemory.readWord_storeHash_ge_4a0 _ _ address haddress]
  exact scheduleLoop_word_outsideX s _ _ _ 16 address (by omega) (Or.inr haddress)

theorem scheduledState_hash (s : State) (input : ByteArray) (i : Nat) :
    StackMemory.hashAt (scheduledState s input i).memory = StackMemory.hashAt s.memory := by
  simp only [StackMemory.hashAt, scheduledState]
  rw [scheduleLoop_word_outsideX s _ _ _ 16 32 (by omega) (Or.inl (by omega)),
    scheduleLoop_word_outsideX s _ _ _ 16 64 (by omega) (Or.inl (by omega)),
    scheduleLoop_word_outsideX s _ _ _ 16 96 (by omega) (Or.inl (by omega)),
    scheduleLoop_word_outsideX s _ _ _ 16 128 (by omega) (Or.inl (by omega)),
    scheduleLoop_word_outsideX s _ _ _ 16 160 (by omega) (Or.inl (by omega))]

theorem scheduledState_activeWords (s : State) (input : ByteArray)
    (hfit : CalldataFits input) (i : Nat) (hi : i < DriverTrace.blockCount input) :
    (scheduledState s input i).activeWords.toNat = max s.activeWords.toNat (67 + 2 * i) :=
  ScheduleActiveWords.scheduledState_activeWords s input hfit i hi _ _

theorem scheduledState_words (s : State) (input : ByteArray) (i : Nat)
    (h : Compression.HashState) (ctx : StackRunBridge.BlockContext s input i h)
    (k : Nat) (hk : k < 16) :
    ScheduleCorrect.xValue (scheduledState s input i) k =
      Challenge.EvmProof.Word.ofUInt32 (blockWords input i k) := by
  rw [blockWords_eq_readLE32 input i k hk]
  exact ScheduleCorrect.loopState_sixteen_cryptoWords s _ _ _ _ _
    ctx.separated ctx.messageBlock k hk

theorem resultState_hash (s : State) (input : ByteArray) (i : Nat)
    (h : Compression.HashState) (ctx : StackRunBridge.BlockContext s input i h) :
    StackRunBridge.hashAt32 (resultState s input i) =
      StackRunBridge.embedHashArray
        (Crypto.Ripemd160.compressBlock (CompressionCorrect.hashArray h)
          (Padding.paddedMessage input) (DriverTrace.blockOffset i)) := by
  change StackMemory.hashAt (StackMemory.storeHash (scheduledState s input i).memory
    (resultHash s input i)) = _
  rw [StackMemory.hashAt_storeHash]
  unfold resultHash
  have hhash : StackMemory.hashAt s.memory = Compression.embedHash h := ctx.hash
  rw [hhash, StackCompression.compress_embed]
  rw [← CompressionCorrect.compressModel_eq_compressBlock
    (Padding.paddedMessage input) (DriverTrace.blockOffset i) h]
  rfl

end Challenge.Ripemd160.Submission.Proofs.Bytecode.StackBlockModel
