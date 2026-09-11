import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedBlockMath
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedScheduleLift
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedHelperBooleanTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRunBridge

set_option warningAsError true

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedBlockModel

open Challenge.Ripemd160 EvmSemantics EvmSemantics.EVM
open PairedLaneCryptoBridge (CryptoLane)
open PairedHelperBooleanTrace

def messagePointer (i : Nat) : Nat := Padding.messageOffset + DriverTrace.blockOffset i

def blockWords (input : ByteArray) (i : Nat) : Nat → UInt32 :=
  fun k => (CompressionCorrect.schedule (Padding.paddedMessage input)
    (DriverTrace.blockOffset i))[k]!

theorem blockWords_eq_readLE32 (input : ByteArray) (i k : Nat) (hk : k < 16) :
    blockWords input i k = Crypto.Ripemd160.readLE32 (Padding.paddedMessage input)
      (DriverTrace.blockOffset i + k * 4) := by
  interval_cases k <;> simp [blockWords, CompressionCorrect.schedule, List.range']

theorem messagePointer_lower (i : Nat) : 736 ≤ messagePointer i := by
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

def scheduledState (s : State) (i : Nat) : State :=
  { s with
    memory := PairedScheduleMemory.normalizedMemory s.memory
      (PairedScheduleData.extractedWord s.memory (messagePointer i))
    activeWords := DenseScheduleTemplate.loadedActiveWords s (UInt256.ofNat (messagePointer i)) }

theorem scheduled_active (s : State) (input : ByteArray) (i : Nat)
    (hfit : CalldataFits input) (hi : i < DriverTrace.blockCount input) :
    23 ≤ (scheduledState s i).activeWords.toNat :=
  PairedScheduleContract.loaded_active_ge23 s (messagePointer i)
    (messagePointer_lower i) (messagePointer_bound input hfit i hi)

theorem extracted_words (s : State) (input : ByteArray) (i : Nat)
    (h : Compression.HashState) (hfit : CalldataFits input)
    (hi : i < DriverTrace.blockCount input) (ctx : StackRunBridge.BlockContext s input i h)
    (k : Nat) (hk : k < 16) :
    PairedScheduleData.extractedWord s.memory (messagePointer i) k =
      Challenge.EvmProof.Word.ofUInt32 (blockWords input i k) := by
  rw [PairedScheduleData.extractedWord_eq_expectedWord _ _ _ hk
    (messagePointer_bound input hfit i hi)]
  change ScheduleCorrect.expectedWord s.memory (DriverTrace.messageOffsetWord i) k = _
  rw [ctx.messageBlock k hk, blockWords_eq_readLE32 input i k hk]

theorem scheduled_ready (s : State) (input : ByteArray) (i : Nat)
    (h : Compression.HashState) (hfit : CalldataFits input)
    (hi : i < DriverTrace.blockCount input) (ctx : StackRunBridge.BlockContext s input i h) :
    NormalizedScheduleReady (scheduledState s i).memory (blockWords input i) := by
  constructor
  · intro k hk
    change MachineState.readWord
      (PairedScheduleMemory.normalizedMemory s.memory
        (PairedScheduleData.extractedWord s.memory (messagePointer i)))
        (PairedScheduleMemory.cell k) = _
    rw [PairedScheduleMemory.read_normalized_cell _ _ _ (by omega), if_neg (by omega)]
    exact extracted_words s input i h hfit hi ctx k hk
  · intro k hk
    change MachineState.readWord
      (PairedScheduleMemory.normalizedMemory s.memory
        (PairedScheduleData.extractedWord s.memory (messagePointer i)))
        (PairedScheduleMemory.cell k + 16) = _
    rw [PairedScheduleData.read_normalized_extracted_upper _ _ _ hk,
      ← PairedScheduleData.extractedWord_eq_littleWord,
      extracted_words s input i h hfit hi ctx k hk]
    rfl

theorem scheduled_hashWords (s : State) (i : Nat) :
    PairedBlockMath.hashWords (scheduledState s i).memory = PairedBlockMath.hashWords s.memory := by
  -- the chaining state lies above the schedule cells (read_normalized_outside: 544 ≤ address);
  -- stated address-generically so it follows the relocated hashWords literals.
  simp (disch := decide) only [scheduledState, PairedBlockMath.hashWords,
    PairedScheduleMemory.read_normalized_outside]

def leftFold (words : Nat → UInt32) : Nat → CryptoLane → CryptoLane :=
  scalarLeftFold (fun i => i / 16) (fun i => Crypto.Ripemd160.s[i]!)
    (fun i => words Crypto.Ripemd160.r[i]!) (fun i => Crypto.Ripemd160.K[i / 16]!)

def rightFold (words : Nat → UInt32) : Nat → CryptoLane → CryptoLane :=
  scalarRightFold (fun i => i / 16) (fun i => Crypto.Ripemd160.sP[i]!)
    (fun i => words Crypto.Ripemd160.rP[i]!) (fun i => Crypto.Ripemd160.KP[i / 16]!)

def resultFrame (s : State) (input : ByteArray) (i : Nat) : PairedTailTrace.Frame :=
  PairedBlockMath.tailFrame
    (leftFold (blockWords input i) 80 (PairedBlockMath.readLane s.memory))
    (rightFold (blockWords input i) 80 (PairedBlockMath.readLane s.memory))

def resultState (s : State) (input : ByteArray) (i : Nat) : State :=
  { scheduledState s i with
    memory := PairedTailTrace.resultMemory (scheduledState s i).memory (resultFrame s input i) }

@[simp] theorem resultState_executionEnv (s : State) (input : ByteArray) (i : Nat) :
    (resultState s input i).executionEnv = s.executionEnv := by rfl

@[simp] theorem resultState_halt (s : State) (input : ByteArray) (i : Nat) :
    (resultState s input i).halt = s.halt := by rfl

@[simp] theorem resultState_callStack (s : State) (input : ByteArray) (i : Nat) :
    (resultState s input i).callStack = s.callStack := by rfl

theorem resultState_word_above (s : State) (input : ByteArray) (i address : Nat)
    (haddress : 736 ≤ address) :
    StackRunBridge.wordAt (resultState s input i) address = StackRunBridge.wordAt s address := by
  change MachineState.readWord
    (PairedTailTrace.resultMemory (scheduledState s i).memory (resultFrame s input i)) address = _
  unfold MachineState.readWord
  rw [PairedTailTrace.tail_readPadded_outside _ _ _ _ (Or.inr (by omega))]
  change MachineState.readWord (scheduledState s i).memory address = MachineState.readWord s.memory address
  exact PairedScheduleMemory.read_normalized_outside _ _ address (by omega)

theorem resultState_hash (s : State) (input : ByteArray) (i : Nat) (h : Compression.HashState)
    (ctx : StackRunBridge.BlockContext s input i h) :
    StackRunBridge.hashAt32 (resultState s input i) =
      StackRunBridge.embedHashArray
        (Crypto.Ripemd160.compressBlock (CompressionCorrect.hashArray h)
          (Padding.paddedMessage input) (DriverTrace.blockOffset i)) := by
  have hh : PairedBlockMath.hashWords s.memory = Compression.embedHash h := ctx.hash
  have hq : PairedBlockMath.hashWords (scheduledState s i).memory = Compression.embedHash h :=
    (scheduled_hashWords s i).trans hh
  change PairedBlockMath.hashWords
    (PairedTailTrace.resultMemory (scheduledState s i).memory (resultFrame s input i)) = _
  unfold resultFrame
  rw [PairedBlockMath.tail_hash _ h _ _ hq, PairedBlockMath.readLane_of_hash _ h hh]
  have hspec := PairedCompressionBridge.paired_compression_eq_spec
    (Padding.paddedMessage input) (DriverTrace.blockOffset i) h
    (leftFold (blockWords input i)) (rightFold (blockWords input i))
    (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
  exact congrArg StackRunBridge.embedHashArray hspec

#print axioms blockWords_eq_readLE32
#print axioms messagePointer_lower
#print axioms messagePointer_bound
#print axioms scheduled_active
#print axioms extracted_words
#print axioms scheduled_ready
#print axioms scheduled_hashWords
#print axioms resultState_executionEnv
#print axioms resultState_halt
#print axioms resultState_callStack
#print axioms resultState_word_above
#print axioms resultState_hash

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedBlockModel
