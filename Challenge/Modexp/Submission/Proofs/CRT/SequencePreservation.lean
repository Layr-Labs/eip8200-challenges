import Challenge.Modexp.Submission.Proofs.CRT.ColumnSequence
set_option warningAsError true
set_option maxHeartbeats 4000000

namespace HistoricalSearch.SequencePreservation
open EvmSemantics EvmSemantics.EVM
open HistoricalSearch.ColumnMemory HistoricalSearch.ColumnSequence
open HistoricalSearch.CRTMemoryCells

theorem memory_live (s : State) (minv : UInt256) (n : Nat → UInt256) (rest : List UInt256)
    (t : Nat) (ht : t ≤ 17) (start count : Nat) (hrange : start+count ≤ 1056 ∨ 1632 ≤ start) :
    MachineState.readPadded (states s minv n rest t).memory start count =
      MachineState.readPadded s.memory start count := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [states_succ, step_memory t (by omega)]
    rw [readPadded_storeCells]
    · exact ih (by omega)
    · intro c hc
      have hb := cell_bounds t (by omega) _ c hc
      omega

theorem word_live (s : State) (minv : UInt256) (n : Nat → UInt256) (rest : List UInt256)
    (t : Nat) (ht : t ≤ 17) (start : Nat) (hrange : start+32 ≤ 1056 ∨ 1632 ≤ start) :
    MachineState.readWord (states s minv n rest t).memory start = MachineState.readWord s.memory start := by
  unfold MachineState.readWord
  rw [memory_live s minv n rest t ht start 32 hrange]

#print axioms memory_live
#print axioms word_live
end HistoricalSearch.SequencePreservation
