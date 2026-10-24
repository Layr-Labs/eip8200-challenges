import Challenge.Modexp.Submission.Proofs.CRT.LoopInvariant
import Challenge.Modexp.Submission.Proofs.CRT.PureSquareMemory
set_option warningAsError true
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option exponentiation.threshold 4096

namespace HistoricalSearch.EntryInvariant
open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Fast
open HistoricalSearch.CRTLoopArithmetic HistoricalSearch.CRTAdapterMeaning
open HistoricalSearch.LoopInvariant HistoricalSearch.PureLoop

theorem entry_live (mem : ByteArray) (counter : UInt256) :
    Live (entryMemory mem counter) mem := by
  intro addr hd
  unfold MachineState.readWord
  rw [entry_keep mem counter addr 32 (by omega)]

theorem entry (mem : ByteArray) (n : Nat → UInt256) (minv : UInt256)
    (f : CRTLoopFrames.Frame) (N k A : Nat)
    (hs : Static mem n minv f N) (ha : Model.FastRepresents mem 2368 8 A)
    (hk : 1 ≤ k) (hk16 : k ≤ 16) :
    Invariant (entryMemory mem (UInt256.ofNat (k-1))) n minv f N k A where
  toStatic := hs.transport (entry_live mem (UInt256.ofNat (k-1)))
  operand := entry_represents mem (UInt256.ofNat (k-1)) A ha
  counter := by
    rw [entry_counter, Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt]
    exact lt_of_le_of_lt (by omega : k-1 ≤ 16) (by norm_num)
  countPositive := hk
  countBound := hk16

theorem initial (mem : ByteArray) (n : Nat → UInt256) (minv : UInt256)
    (f : CRTLoopFrames.Frame) (N k A : Nat)
    (hs : Static mem n minv f N) (ha : Model.FastRepresents mem 2112 8 A)
    (hk : 1 ≤ k) (hk16 : k ≤ 16) :
    Invariant (PureSquareMemory.initial k mem) n minv f N k A where
  toStatic := hs.transport (PureSquareMemory.initial_live k mem)
  operand := PureSquareMemory.initial_represents k mem A ha
  counter := by
    rw [PureSquareMemory.initial, entry_counter, Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt]
    exact lt_of_le_of_lt (by omega : k-1 ≤ 16) (by norm_num)
  countPositive := hk
  countBound := hk16

#print axioms entry
#print axioms initial
end HistoricalSearch.EntryInvariant
