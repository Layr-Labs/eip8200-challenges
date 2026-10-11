import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerTableLayout
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairTableActive
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackMemory
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRunBridge

set_option warningAsError true

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedBlockModel
open Challenge.Ripemd160 EvmSemantics EvmSemantics.EVM
open Challenge.EvmProof

def messagePointer (i : Nat) : Nat := Padding.messageOffset + DriverTrace.blockOffset i

def blockWords (input : ByteArray) (i : Nat) : Nat → UInt32 :=
  fun k => (CompressionCorrect.schedule (Padding.paddedMessage input)
    (DriverTrace.blockOffset i))[k]!

theorem blockWords_eq_readLE32 (input : ByteArray) (i k : Nat) (hk : k < 16) :
    blockWords input i k = Crypto.Ripemd160.readLE32 (Padding.paddedMessage input)
      (DriverTrace.blockOffset i + k * 4) := by
  interval_cases k <;> simp [blockWords, CompressionCorrect.schedule, List.range']

theorem messagePointer_lower (i : Nat) : 1024 ≤ messagePointer i := by
  simp only [messagePointer, Padding.messageOffset]
  omega

theorem messagePointer_bound (input : ByteArray) (hfit : CalldataFits input)
    (i : Nat) (hi : i < DriverTrace.blockCount input) :
    messagePointer i + 64 < 2 ^ 256 := by
  have hp := Padding.paddedLength_lt input.size
  have heq := DriverTrace.paddedLength_eq_blockCount input
  have hoff : DriverTrace.blockOffset i < Padding.paddedLength input.size := by
    unfold DriverTrace.blockOffset
    omega
  unfold CalldataFits at hfit
  norm_num [messagePointer, Padding.messageOffset] at hfit ⊢
  omega

def selectedWords (s : State) (i : Nat) : Nat → UInt256 :=
  PairedScheduleData.extractedWord s.memory (messagePointer i)

def scheduledState (s : State) (i : Nat) : State :=
  { s with
    memory := StaggerTableLayout.resultMemory s.memory (selectedWords s i)
    activeWords := DenseScheduleTemplate.loadedActiveWords s (UInt256.ofNat (messagePointer i)) }

theorem scheduled_active (s : State) (input : ByteArray) (i : Nat)
    (hfit : CalldataFits input) (hi : i < DriverTrace.blockCount input) :
    34 ≤ (scheduledState s i).activeWords.toNat :=
  PairTableActive.loaded_active_ge34 s (messagePointer i)
    (messagePointer_lower i) (messagePointer_bound input hfit i hi)

theorem extracted_words (s : State) (input : ByteArray) (i : Nat)
    (h : Compression.HashState) (hfit : CalldataFits input)
    (hi : i < DriverTrace.blockCount input) (ctx : StackRunBridge.BlockContext s input i h)
    (k : Nat) (hk : k < 16) :
    PairedScheduleData.extractedWord s.memory (messagePointer i) k =
      Word.ofUInt32 (blockWords input i k) := by
  rw [PairedScheduleData.extractedWord_eq_expectedWord _ _ _ hk
    (messagePointer_bound input hfit i hi)]
  change ScheduleCorrect.expectedWord s.memory (DriverTrace.messageOffsetWord i) k = _
  rw [ctx.messageBlock k hk, blockWords_eq_readLE32 input i k hk]

def stateHash (s : State) : Array UInt32 :=
  let h := StackMemory.hashAt s.memory
  #[Word.toUInt32 h.h0, Word.toUInt32 h.h1, Word.toUInt32 h.h2,
    Word.toUInt32 h.h3, Word.toUInt32 h.h4]

def desiredHash (s : State) (input : ByteArray) (i : Nat) : Compression.EvmHashState :=
  StackRunBridge.embedHashArray (Crypto.Ripemd160.compressBlock
    (stateHash s) (Padding.paddedMessage input) (DriverTrace.blockOffset i))

def resultState (s : State) (input : ByteArray) (i : Nat) : State :=
  { scheduledState s i with
    memory := StackMemory.storeHash (scheduledState s i).memory (desiredHash s input i) }

@[simp] theorem resultState_executionEnv (s : State) (input : ByteArray) (i : Nat) :
    (resultState s input i).executionEnv = s.executionEnv := by rfl
@[simp] theorem resultState_halt (s : State) (input : ByteArray) (i : Nat) :
    (resultState s input i).halt = s.halt := by rfl
@[simp] theorem resultState_callStack (s : State) (input : ByteArray) (i : Nat) :
    (resultState s input i).callStack = s.callStack := by rfl

theorem resultState_word_above (s : State) (input : ByteArray) (i address : Nat)
    (haddress : 1024 ≤ address) :
    StackRunBridge.wordAt (resultState s input i) address = StackRunBridge.wordAt s address := by
  change MachineState.readWord (StackMemory.storeHash _ _) address = _
  rw [StackMemory.readWord_storeHash_ge_120 _ _ _ (by omega)]
  exact StaggerTableLayout.read_resultMemory_outside _ _ _ (by omega)

theorem stateHash_of_context (s : State) (input : ByteArray) (i : Nat)
    (h : Compression.HashState) (ctx : StackRunBridge.BlockContext s input i h) :
    stateHash s = CompressionCorrect.hashArray h := by
  have hh : StackMemory.hashAt s.memory = Compression.embedHash h := ctx.hash
  simp only [stateHash, hh, Compression.embedHash, Word.toUInt32_ofUInt32]
  rfl

theorem resultState_hash (s : State) (input : ByteArray) (i : Nat) (h : Compression.HashState)
    (ctx : StackRunBridge.BlockContext s input i h) :
    StackRunBridge.hashAt32 (resultState s input i) =
      StackRunBridge.embedHashArray
        (Crypto.Ripemd160.compressBlock (CompressionCorrect.hashArray h)
          (Padding.paddedMessage input) (DriverTrace.blockOffset i)) := by
  change StackMemory.hashAt (StackMemory.storeHash _ _) = _
  rw [StackMemory.hashAt_storeHash]
  unfold desiredHash
  rw [stateHash_of_context s input i h ctx]

#print axioms extracted_words
#print axioms resultState_hash
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedBlockModel
