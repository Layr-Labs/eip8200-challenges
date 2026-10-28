import Challenge.Ripemd160.Submission.Local20261028.MemoryBridge

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
namespace RipemdMemoryBridge20261028
open EvmSemantics EvmSemantics.EVM

/-- Interpret input symbols by the actual decoded entry bytes. All other
    old-memory bytes retain their own addresses. No equality between distinct
    symbols is assumed. -/
def valuation (m : ByteArray) (symbol : Nat) : UInt8 :=
  if symbol = 0 then 0
  else if symbol ≤ 32 then m[252+4*((symbol-1)/4)+3-(symbol-1)%4]?.getD 0
  else if symbol ≤ 64 then m[162+4*((symbol-33)/4)+3-(symbol-33)%4]?.getD 0
  else m[symbol-1000]?.getD 0

@[simp] theorem valuation_zero (m : ByteArray) : valuation m 0 = 0 := rfl

theorem initial_matches (m : ByteArray)
    (hclear : ∀ a ∈ RipemdTableOrder20261027.clearAddresses, m[a]?.getD 0 = 0) :
    Matches m RipemdTableOrder20261027.initial (valuation m) := by
  intro a
  by_cases hhi : 162 ≤ a ∧ a < 194
  · obtain ⟨hl,hh⟩ := hhi
    interval_cases a <;> rfl
  by_cases hlo : 252 ≤ a ∧ a < 284
  · obtain ⟨hl,hh⟩ := hlo
    interval_cases a <;> rfl
  by_cases hz : a ∈ RipemdTableOrder20261027.clearAddresses
  · simp only [RipemdTableOrder20261027.initial, if_neg hhi, if_neg hlo, if_pos hz,
      valuation_zero]
    exact hclear a hz
  · simp only [RipemdTableOrder20261027.initial, if_neg hhi, if_neg hlo, if_neg hz,
      valuation, if_neg (by omega : ¬ 1000+a = 0),
      if_neg (by omega : ¬ 1000+a ≤ 32), if_neg (by omega : ¬ 1000+a ≤ 64)]
    congr 2
    omega

theorem actual_fan_matches (m : ByteArray)
    (hclear : ∀ a ∈ RipemdTableOrder20261027.clearAddresses, m[a]?.getD 0 = 0) :
    Matches (fanMemory m) RipemdTableOrder20261027.fan (valuation m) :=
  fan_matches m (valuation m) (initial_matches m hclear)

#print axioms initial_matches
#print axioms actual_fan_matches
end RipemdMemoryBridge20261028
