import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadPrefixCanonicalZeroMload
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerTablePad
set_option warningAsError true
namespace AstraPadPrefixCanonical
open EvmSemantics
open Challenge.Ripemd160.Submission.Proofs.Bytecode

/-- Instantiate the proved uniform pad contract with the canonical pad words. -/
theorem canonical_padWords_zero (n : UInt256) (i : Nat)
    (h0 : i ≠ 0) (h14 : i ≠ 14) (h15 : i ≠ 15) :
    StaggerTablePad.padWordsDirty n i = UInt256.ofNat 0 := by
  simp only [StaggerTablePad.padWordsDirty, PadOnlySchedule.padWords, if_neg h0, if_neg h14, if_neg h15]

/-- Sparse canonical pad preparation has the same certified zero MLOADs as
its full overlapping table; all original memory outside the table is arbitrary. -/
theorem mload_canonical_pad_zero (state : MachineState) (n : UInt256) (hn : n.toNat < 2 ^ 64)
    (j : Fin 61) (hcert : j.val ∈ zeroPairPositions) :
    let afterPad := {state with memory := StaggerTablePad.resultMemory state.memory n}
    MachineState.mload afterPad (UInt256.ofNat (18*j.val)) =
      (UInt256.ofNat 0, afterPad) := by
  dsimp only
  rw [StaggerTablePad.resultMemory_eq_table state.memory n hn]
  exact mload_certified_zero state (StaggerTablePad.padWordsDirty n)
    (canonical_padWords_zero n) j hcert

#print axioms canonical_padWords_zero
#print axioms mload_canonical_pad_zero
end AstraPadPrefixCanonical
