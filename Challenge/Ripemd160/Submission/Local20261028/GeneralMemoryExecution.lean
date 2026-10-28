import Challenge.Ripemd160.Submission.Local20261028.GeneralCheckpoints

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace RipemdMemoryBridge20261028
open EvmSemantics EvmSemantics.EVM
open RipemdSubmissionTables20261028

/-- Connect the already proved raw EVM trace to the memory-store fold used
    by the byte-source certificate. This is equality of actual ByteArrays. -/
theorem actual_memory (s : State) (x : Nat → UInt256) (rho : List UInt256) :
    (GeneralTable.result8 s x rho).memory =
      resultMemory (fanMemory s.memory) RipemdTableOrder20261027.selected := by
  exact GeneralCheckpoints.actual_memory s x rho

theorem actual_bytes (s : State) (x : Nat → UInt256) (rho : List UInt256)
    (hclear : ∀ a ∈ RipemdTableOrder20261027.clearAddresses, s.memory[a]?.getD 0 = 0)
    (a : Nat) :
    (GeneralTable.result8 s x rho).memory[a]?.getD 0 =
      valuation s.memory (RipemdTableOrder20261027.result RipemdTableOrder20261027.selected a) := by
  rw [actual_memory]
  exact result_matches _ _ (actual_fan_matches _ hclear) (valuation_zero _) _ a

theorem actual_preserves_zeros (s : State) (x : Nat → UInt256) (rho : List UInt256)
    (hclear : ∀ a ∈ RipemdTableOrder20261027.clearAddresses, s.memory[a]?.getD 0 = 0)
    (a : Nat) (ha : a ∈ RipemdTableOrder20261027.clearAddresses) :
    (GeneralTable.result8 s x rho).memory[a]?.getD 0 = 0 := by
  rw [actual_memory]
  exact preserved_zeros _ _ (actual_fan_matches _ hclear) (valuation_zero _) a ha

theorem actual_projected_reads (s : State) (x : Nat → UInt256) (rho : List UInt256)
    (hclear : ∀ a ∈ RipemdTableOrder20261027.clearAddresses, s.memory[a]?.getD 0 = 0)
    (l : RipemdTableOrder20261027.Load) (hl : l ∈ RipemdTableOrder20261027.loads)
    (j : Nat) (hj : j ∈ RipemdTableOrder20261027.offsets l.2.2.2) :
    (resultMemory (fanMemory s.memory) RipemdTableOrder20261027.plan)[l.2.1+j]?.getD 0 =
      (GeneralTable.result8 s x rho).memory[l.2.2.1+j]?.getD 0 := by
  rw [actual_memory]
  exact projected_reads _ _ (actual_fan_matches _ hclear) (valuation_zero _) l hl j hj

#print axioms actual_memory
#print axioms actual_bytes
#print axioms actual_preserves_zeros
#print axioms actual_projected_reads
end RipemdMemoryBridge20261028
