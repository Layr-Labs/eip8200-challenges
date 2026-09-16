import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedBlockModel
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadOnlyContract
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerTableCongruence
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerTablePad
set_option warningAsError true
set_option maxHeartbeats 2000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPrepare
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof

def driverRest (input : ByteArray) (i : Nat) : List UInt256 :=
  [DriverTrace.blockOffsetWord i, Padding.paddedWord input]

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

theorem scheduled_active_eq (s : State) (input : ByteArray) (i : Nat)
    (h : Compression.HashState) (hfit : CalldataFits input)
    (hi : i < DriverTrace.blockCount input) (ctx : StackRunBridge.BlockContext s input i h) :
    DenseScheduleTemplate.loadedActiveWords s
      (UInt256.ofNat (PairedBlockModel.messagePointer i)) = s.activeWords := by
  apply PairTableActive.loaded_active_eq_of_allocated s _
    (PairedBlockModel.messagePointer_bound input hfit i hi) (messagePointer_aligned i)
  have hpad := PaddingTrace.padReturned_allocated input hfit
  have hlength := DriverTrace.paddedLength_eq_blockCount input
  have hctx := ctx.allocated
  unfold PairedBlockModel.messagePointer DriverTrace.blockOffset Padding.messageOffset at *
  omega

theorem scheduled_memory_calldata (s : State) (input : ByteArray) (i : Nat)
    (h : Compression.HashState) (hfit : CalldataFits input)
    (hi : i < DriverTrace.blockCount input) (ctx : StackRunBridge.BlockContext s input i h)
    (hhit : input.size = DriverTrace.blockOffset i) :
    StaggerTablePad.resultMemory s.memory (UInt256.ofNat s.executionEnv.calldata.size) =
      (PairedBlockModel.scheduledState s i).memory := by
  rw [ctx.calldata, StaggerTablePad.resultMemory_eq_table]
  apply StaggerTableLayout.resultMemory_congr
  intro k hk
  symm
  apply PadOnlySchedule.extracted_words s.memory input (PairedBlockModel.messagePointer i)
    hfit (hit_aligned input i hhit) (PairedBlockModel.messagePointer_bound input hfit i hi)
    _ k hk
  rw [hhit]
  exact ctx.messageBlock

#print axioms scheduled_memory_calldata
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPrepare
