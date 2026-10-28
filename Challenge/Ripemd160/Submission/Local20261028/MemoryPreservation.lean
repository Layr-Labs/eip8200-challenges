import Challenge.Ripemd160.Submission.Local20261028.GeneralMemoryExecution
import Challenge.Ripemd160.Submission.Local20261028.FirstMemory

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace RipemdMemoryBridge20261028
open EvmSemantics EvmSemantics.EVM
open Challenge.Ripemd160.Submission.Proofs.Bytecode
open RipemdSubmissionTables20261028

theorem fold_outside (sources m : ByteArray) (ws : List RipemdTableOrder20261027.Write)
    (bound : Nat) (hbound : ∀ w ∈ ws, w.2.1+32 ≤ bound) (a : Nat) (ha : bound ≤ a) :
    (ws.foldl (store sources) m)[a]?.getD 0 = m[a]?.getD 0 := by
  induction ws generalizing m with
  | nil => rfl
  | cons w ws ih =>
    simp only [List.foldl_cons]
    rw [ih _ (by intro w hw; exact hbound w (List.mem_cons_of_mem _ hw))]
    have hw := hbound w (by simp)
    rw [store, write_getD, if_neg (by omega)]

theorem fan_outside (m : ByteArray) (a : Nat) (ha : 318 ≤ a) :
    (fanMemory m)[a]?.getD 0 = m[a]?.getD 0 := by
  simp only [fanMemory, copy, write_getD]
  repeat rw [if_neg (by omega)]

theorem general_outside (s : State) (x : Nat → UInt256) (rho : List UInt256)
    (a : Nat) (ha : 1040 ≤ a) :
    (GeneralTable.result8 s x rho).memory[a]?.getD 0 = s.memory[a]?.getD 0 := by
  rw [actual_memory, resultMemory, fold_outside _ _ _ 1040 (by decide) a ha]
  exact fan_outside _ a (by omega)

theorem first_outside (s : State) (continuation : UInt256) (rho : List UInt256)
    (a : Nat) (ha : 1040 ≤ a) :
    (FirstTable.result7 s (FirstMemory.frame continuation) rho).memory[a]?.getD 0 = s.memory[a]?.getD 0 := by
  rw [FirstMemory.eq7]
  change (FirstMemory.memory33 s)[a]?.getD 0 = s.memory[a]?.getD 0
  simp only [FirstMemory.memory0, FirstMemory.memory1, FirstMemory.memory2, FirstMemory.memory3, FirstMemory.memory4, FirstMemory.memory5, FirstMemory.memory6, FirstMemory.memory7, FirstMemory.memory8, FirstMemory.memory9, FirstMemory.memory10, FirstMemory.memory11, FirstMemory.memory12, FirstMemory.memory13, FirstMemory.memory14, FirstMemory.memory15, FirstMemory.memory16, FirstMemory.memory17, FirstMemory.memory18, FirstMemory.memory19, FirstMemory.memory20, FirstMemory.memory21, FirstMemory.memory22, FirstMemory.memory23, FirstMemory.memory24, FirstMemory.memory25, FirstMemory.memory26, FirstMemory.memory27, FirstMemory.memory28, FirstMemory.memory29, FirstMemory.memory30, FirstMemory.memory31, FirstMemory.memory32, FirstMemory.memory33, write_getD]
  repeat rw [if_neg (by omega)]
#print axioms general_outside
#print axioms first_outside
end RipemdMemoryBridge20261028
