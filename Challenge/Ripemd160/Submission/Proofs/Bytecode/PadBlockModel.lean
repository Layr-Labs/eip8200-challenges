import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadOnlyContract
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedBlockModel
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PadBlockModel
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open PadOnlySchedule

theorem calldata_lt_uint256 (input : ByteArray) (hfit : CalldataFits input) :
    input.size < 2^256 := by
  unfold CalldataFits at hfit
  omega

theorem messagePointer_aligned (i : Nat) : PairedBlockModel.messagePointer i % 32 = 0 := by
  unfold PairedBlockModel.messagePointer Padding.messageOffset DriverTrace.blockOffset
  omega

theorem blockOffsetWord_toNat (input : ByteArray) (hfit : CalldataFits input)
    (i : Nat) (hi : i < DriverTrace.blockCount input) :
    (DriverTrace.blockOffsetWord i).toNat = DriverTrace.blockOffset i := by
  have hb := PairedBlockModel.messagePointer_bound input hfit i hi
  unfold PairedBlockModel.messagePointer at hb
  rw [DriverTrace.blockOffsetWord, Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

theorem hit_aligned (input : ByteArray) (i : Nat)
    (hhit : input.size = DriverTrace.blockOffset i) : input.size % 64 = 0 := by
  rw [hhit, DriverTrace.blockOffset]
  omega

theorem scheduled_memory (s : State) (input : ByteArray) (i : Nat)
    (h : Compression.HashState) (hfit : CalldataFits input)
    (hi : i < DriverTrace.blockCount input) (ctx : StackRunBridge.BlockContext s input i h)
    (hhit : input.size = DriverTrace.blockOffset i) :
    (PairedBlockModel.scheduledState s i).memory =
      resultMemory s.memory (UInt256.ofNat input.size) := by
  apply normalized_memory s.memory input (PairedBlockModel.messagePointer i) hfit
    (hit_aligned input i hhit) (PairedBlockModel.messagePointer_bound input hfit i hi)
  · rw [hhit]
    exact ctx.messageBlock
  · exact ctx.sentinel

theorem scheduled_memory_calldata (s : State) (input : ByteArray) (i : Nat)
    (h : Compression.HashState) (hfit : CalldataFits input)
    (hi : i < DriverTrace.blockCount input) (ctx : StackRunBridge.BlockContext s input i h)
    (hhit : input.size = DriverTrace.blockOffset i) :
    resultMemory s.memory (UInt256.ofNat s.executionEnv.calldata.size) =
      (PairedBlockModel.scheduledState s i).memory := by
  rw [ctx.calldata]
  exact (scheduled_memory s input i h hfit hi ctx hhit).symm

theorem scheduled_cache22 (s : State) (input : ByteArray) (i : Nat)
    (h : Compression.HashState) (hfit : CalldataFits input)
    (hi : i < DriverTrace.blockCount input) (ctx : StackRunBridge.BlockContext s input i h)
    (hhit : input.size = DriverTrace.blockOffset i) :
    [UInt256.ofNat 22,
     MachineState.readWord (PairedBlockModel.scheduledState s i).memory 256,
     MachineState.readWord (PairedBlockModel.scheduledState s i).memory 384,
     MachineState.readWord (PairedBlockModel.scheduledState s i).memory 416,
     MachineState.readWord (PairedBlockModel.scheduledState s i).memory 352,
     MachineState.readWord (PairedBlockModel.scheduledState s i).memory 320] =
      [UInt256.ofNat 22, UInt256.ofNat 0, UInt256.ofNat 0, UInt256.ofNat 0,
       UInt256.ofNat 0, UInt256.ofNat 0] := by
  rw [scheduled_memory s input i h hfit hi ctx hhit]
  exact congrArg (List.cons (UInt256.ofNat 22))
    (resultMemory_cache_tail s.memory (UInt256.ofNat input.size) ctx.sentinel)

#print axioms calldata_lt_uint256
#print axioms messagePointer_aligned
#print axioms blockOffsetWord_toNat
#print axioms scheduled_memory
#print axioms scheduled_memory_calldata
#print axioms scheduled_cache22
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PadBlockModel
