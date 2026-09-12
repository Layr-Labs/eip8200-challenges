import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedBlockModel
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadOnlyContract
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairTableCongruence
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairTablePad
set_option warningAsError true
set_option maxHeartbeats 2000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80Prepare
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

theorem scheduled_memory_calldata (s : State) (input : ByteArray) (i : Nat)
    (h : Compression.HashState) (hfit : CalldataFits input)
    (hi : i < DriverTrace.blockCount input) (ctx : StackRunBridge.BlockContext s input i h)
    (hhit : input.size = DriverTrace.blockOffset i) :
    PairTablePad.resultMemory s.memory (UInt256.ofNat s.executionEnv.calldata.size) =
      (PairedBlockModel.scheduledState s i).memory := by
  rw [ctx.calldata, PairTablePad.resultMemory_eq_table]
  apply PairTableLayout.resultMemory_congr
  intro k hk
  symm
  apply PadOnlySchedule.extracted_words s.memory input (PairedBlockModel.messagePointer i)
    hfit (hit_aligned input i hhit) (PairedBlockModel.messagePointer_bound input hfit i hi)
    _ k hk
  rw [hhit]
  exact ctx.messageBlock

#print axioms scheduled_memory_calldata
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80Prepare
