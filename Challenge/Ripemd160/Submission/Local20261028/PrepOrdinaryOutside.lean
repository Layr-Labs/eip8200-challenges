import Challenge.Ripemd160.Submission.Local20261028.PrepOrdinaryBytes
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace RipemdSubmission20261101.OrdinaryOutside
open EvmSemantics EvmSemantics.EVM
open RipemdMemoryBridge20261028 OrdinaryBytes
theorem fold_outside (sources m : ByteArray) (ws : List (Nat × Nat))
    (bound : Nat) (hb : ∀ w ∈ ws, w.1+32 ≤ bound) (a : Nat) (ha : bound ≤ a) :
    (ws.foldl (OrdinaryBytes.store sources) m)[a]?.getD 0 = m[a]?.getD 0 := by
  induction ws generalizing m with
  | nil => rfl
  | cons w ws ih =>
    simp only [List.foldl_cons]
    rw [ih _ (by intro w hw; exact hb w (List.mem_cons_of_mem _ hw))]
    have hw := hb w (by simp)
    rw [OrdinaryBytes.store, write_getD, if_neg (by omega)]
theorem actual_outside (s : State) (x : Nat → UInt256) (rho : List UInt256)
    (a : Nat) (ha : 1040 ≤ a) :
    (OrdinaryTable.result7 s x rho).memory[a]?.getD 0 = s.memory[a]?.getD 0 := by
  rw [OrdinaryMemory.actual_memory, model_exact, OrdinaryBytes.resultMemory,
    fold_outside _ _ _ 1040 (by decide) a ha]
  simp only [fanMemory, copy, write_getD]
  repeat rw [if_neg (by omega)]
#print axioms actual_outside
end RipemdSubmission20261101.OrdinaryOutside
