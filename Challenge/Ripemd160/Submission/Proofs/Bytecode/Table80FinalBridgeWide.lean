import Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80FinalBridgeModel
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80WideFinalMemory
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80Core
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80ConsumedTerminalTail
set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80FinalBridge
open Challenge.Ripemd160 EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open Paired80WordRound Paired80Algorithm PairedBlockModel

theorem physical_resultMemory_model (s : State) (input : ByteArray) (i : Nat)
    (h : Compression.HashState) (hfit : CalldataFits input)
    (hi : i < DriverTrace.blockCount input) (ctx : StackRunBridge.BlockContext s input i h) :
    Table80ConsumedTerminalTail.resultMemory (scheduledState s i).memory
      (Table80Core.physicalFinalLane (scheduledState s i).memory (initialLane h)) =
      (resultState s input i).memory := by
  have hm := scheduled_messageReady s input i h hfit hi ctx
  have heq := Table80WideFinalMemory.resultMemory_eq_old
    (scheduledState s i).memory (message (scheduledState s i).memory) (blockWords input i)
    (PairedCompressionBridge.ofWorking (CompressionCorrect.workingOfHash h))
    (PairedCompressionBridge.ofWorking (CompressionCorrect.workingOfHash h)) hm
  exact heq.trans (resultMemory_model s input i h hfit hi ctx)
#print axioms physical_resultMemory_model
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80FinalBridge
