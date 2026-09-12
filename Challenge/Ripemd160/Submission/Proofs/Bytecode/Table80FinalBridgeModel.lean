import Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80FinalBridgeMemory
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80FinalBridgeMessage
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedBlockModel
set_option warningAsError true
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80FinalBridge
open Challenge.Ripemd160 EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open Paired80WordRound Paired80Algorithm PairedBlockModel

def initialLane (h : Compression.HashState) : WordLane :=
  packCrypto (PairedCompressionBridge.ofWorking (CompressionCorrect.workingOfHash h))
    (PairedCompressionBridge.ofWorking (CompressionCorrect.workingOfHash h))

def finalLane (memory : ByteArray) (q : WordLane) : WordLane :=
  Paired80FinalWord.finish (message memory) (fold (message memory) 78 q)

theorem scheduled_hashAt (s : State) (i : Nat) :
    StackMemory.hashAt (scheduledState s i).memory = StackMemory.hashAt s.memory := by
  simp (discharger := omega) only [scheduledState, StackMemory.hashAt,
    PairTableLayout.read_resultMemory_outside]

theorem scheduled_messageReady (s : State) (input : ByteArray) (i : Nat)
    (h : Compression.HashState) (hfit : CalldataFits input)
    (hi : i < DriverTrace.blockCount input) (ctx : StackRunBridge.BlockContext s input i h) :
    MessageReady (message (scheduledState s i).memory) (blockWords input i) 80 := by
  exact messageReady s.memory (selectedWords s i) (blockWords input i)
    (fun k hk => extracted_words s input i h hfit hi ctx k hk)

theorem desiredHash_eq_combine (s : State) (input : ByteArray) (i : Nat)
    (h : Compression.HashState) (hfit : CalldataFits input)
    (hi : i < DriverTrace.blockCount input) (ctx : StackRunBridge.BlockContext s input i h) :
    desiredHash s input i = Compression.embedHash (Paired80Compression.combine h
      (finalLane (scheduledState s i).memory (initialLane h))) := by
  have hm := scheduled_messageReady s input i h hfit hi ctx
  have hc := Paired80FinalWord.finish_compression (Padding.paddedMessage input)
    (DriverTrace.blockOffset i) h (message (scheduledState s i).memory) hm
  unfold desiredHash
  rw [stateHash_of_context s input i h ctx, ← hc]
  rfl

theorem resultMemory_model (s : State) (input : ByteArray) (i : Nat)
    (h : Compression.HashState) (hfit : CalldataFits input)
    (hi : i < DriverTrace.blockCount input) (ctx : StackRunBridge.BlockContext s input i h) :
    Table80Tail.resultMemory (scheduledState s i).memory
      (finalLane (scheduledState s i).memory (initialLane h)) =
      (resultState s input i).memory := by
  have hh : StackMemory.hashAt (scheduledState s i).memory = Compression.embedHash h :=
    (scheduled_hashAt s i).trans ctx.hash
  rw [resultMemory_eq_storeHash _ _ h hh,
    ← desiredHash_eq_combine s input i h hfit hi ctx]
  rfl

theorem resultState_model (s : State) (input : ByteArray) (i : Nat)
    (h : Compression.HashState) (hfit : CalldataFits input)
    (hi : i < DriverTrace.blockCount input) (ctx : StackRunBridge.BlockContext s input i h) :
    {scheduledState s i with
      memory := Table80Tail.resultMemory (scheduledState s i).memory
        (finalLane (scheduledState s i).memory (initialLane h))} = resultState s input i := by
  rw [resultMemory_model s input i h hfit hi ctx]
  rfl

#print axioms scheduled_messageReady
#print axioms desiredHash_eq_combine
#print axioms resultMemory_model
#print axioms resultState_model
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80FinalBridge
