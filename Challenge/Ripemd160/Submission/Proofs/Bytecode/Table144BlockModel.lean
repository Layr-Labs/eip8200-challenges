import Challenge.Ripemd160.Submission.Proofs.Bytecode.Table144CallPrepare
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Table144Core
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired144FinalCorrect
set_option warningAsError true
set_option maxRecDepth 10000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Table144BlockBridge
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open PairedLaneUInt256Bridge Paired144Core Paired144WordRound Paired144Algorithm Table144Prepare

def blockWords (input : ByteArray) (i : Nat) : Nat → UInt32 :=
  fun k => (CompressionCorrect.schedule (Padding.paddedMessage input) (DriverTrace.blockOffset i))[k]!

def initialLane (h : Compression.HashState) : WordLane :=
  packCrypto (PairedCompressionBridge.ofWorking (CompressionCorrect.workingOfHash h))
    (PairedCompressionBridge.ofWorking (CompressionCorrect.workingOfHash h))

def nextHash (input : ByteArray) (i : Nat) (h : Compression.HashState) : Compression.HashState :=
  CompressionCorrect.compressModel (blockWords input i) h

def resultState (s : State) (input : ByteArray) (i : Nat) (h : Compression.HashState)
    (rho : List UInt256) : State :=
  {scheduledState s i with
    pc := UInt256.ofNat 490
    stack := PersistentFrame.frame (nextHash input i h) (DriverTrace.blockOffsetWord i) (Padding.paddedWord input) rho}

theorem blockWords_eq_readLE32 (input : ByteArray) (i k : Nat) (hk : k<16) :
    blockWords input i k = Crypto.Ripemd160.readLE32 (Padding.paddedMessage input)
      (DriverTrace.blockOffset i+k*4) := by
  interval_cases k <;> simp [blockWords,CompressionCorrect.schedule,List.range']

theorem extracted_words (s : State) (input : ByteArray) (i : Nat)
    (hfit : input.size<2^64) (hi : i<DriverTrace.blockCount input) (ctx : Context s input i)
    (k : Nat) (hk : k<16) :
    selectedWords s i k = Word.ofUInt32 (blockWords input i k) := by
  unfold selectedWords
  rw [PairedScheduleData.extractedWord_eq_expectedWord _ _ _ hk (messagePointer_bound input hfit i hi),
    ctx.messageBlock k hk, blockWords_eq_readLE32 input i k hk]

theorem scheduled_messageReady (s : State) (input : ByteArray) (i : Nat)
    (hfit : input.size<2^64) (hi : i<DriverTrace.blockCount input) (ctx : Context s input i) :
    MessageReady (Table144Core.message (scheduledState s i).memory) (blockWords input i) 80 := by
  intro r hr
  obtain ⟨hl,hrr⟩ := index_bounds ⟨r,hr⟩
  apply bits_injective
  apply BitVec.eq_of_toNat_eq
  rw [packed32,bits_word,pack_toNat,bits_toNat]
  change (MachineState.readWord (PairTable144Layout.resultMemory s.memory (selectedWords s i))
      (18*PairTable144Layout.pairIndices[r]!)).toNat = _
  rw [PairTable144Layout.read_round s.memory (selectedWords s i) r hr (fun k _ => PairedScheduleData.extractedWord_bound s.memory (messagePointer i) k),
    extracted_words s input i hfit hi ctx _ hl, extracted_words s input i hfit hi ctx _ hrr,
    Word.ofUInt32_toNat,Word.ofUInt32_toNat]
  rfl

theorem final_combine_eq_nextHash (s : State) (input : ByteArray) (i : Nat)
    (h : Compression.HashState) (hfit : input.size<2^64) (hi : i<DriverTrace.blockCount input)
    (ctx : Context s input i) :
    PersistentTailBinding.combine h
      (finalLane (Table144Core.message (scheduledState s i).memory) (initialLane h)) = nextHash input i h := by
  rw [initialLane, Paired144FinalCorrect.final_combine _ (blockWords input i) h _ _
    (scheduled_messageReady s input i hfit hi ctx), PairedCompressionBridge.projected_combination,
    PairedCompressionBridge.projected_left_fold _ (leftFold (blockWords input i))
      (fun _ => rfl) (fun _ _ => rfl),
    PairedCompressionBridge.projected_right_fold _ (rightFold (blockWords input i))
      (fun _ => rfl) (fun _ _ => rfl), PairedCompressionBridge.working_roundtrip]
  rfl

theorem nextHash_compressBlock (input : ByteArray) (i : Nat) (h : Compression.HashState) :
    CompressionCorrect.hashArray (nextHash input i h) =
      Crypto.Ripemd160.compressBlock (CompressionCorrect.hashArray h)
        (Padding.paddedMessage input) (DriverTrace.blockOffset i) :=
  CompressionCorrect.compressModel_eq_compressBlock (Padding.paddedMessage input) (DriverTrace.blockOffset i) h

theorem scheduled_context (s : State) (input : ByteArray) (i j : Nat)
    (hfit : input.size<2^64) (hj : j<DriverTrace.blockCount input) (ctx : Context s input j) :
    Context (scheduledState s i) input j := by
  constructor
  · exact ctx.calldata
  · intro k hk
    have hp := messagePointer_bound input hfit j hj
    have hlo := messagePointer_lower j
    change ScheduleCorrect.expectedWord (PairTable144Layout.resultMemory s.memory (selectedWords s i))
      (UInt256.ofNat (messagePointer j)) k = _
    unfold ScheduleCorrect.expectedWord Schedule.readLEWord
    rw [PairedScheduleData.loadOffsetWord_toNat (messagePointer j) k hk hp,
      PairTable144Layout.read_resultMemory_outside _ _ _ (by omega)]
    have hm := ctx.messageBlock k hk
    unfold ScheduleCorrect.expectedWord Schedule.readLEWord at hm
    rw [PairedScheduleData.loadOffsetWord_toNat (messagePointer j) k hk hp] at hm
    exact hm

#print axioms scheduled_messageReady
#print axioms final_combine_eq_nextHash
#print axioms nextHash_compressBlock
#print axioms scheduled_context
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Table144BlockBridge
