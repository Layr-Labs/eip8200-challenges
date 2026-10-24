import Challenge.EvmProof.Stepper
import Challenge.EvmProof.Word
set_option warningAsError true

/-!
Artifact-independent memory bounds used by generated execution certificates.
These two lemmas are adapted from the Apache-2.0 upstream
Challenge.Modexp.Submission.Proofs.Fast.Monpro active-word lemmas. Keeping this
small dependency separate avoids rebuilding every kernel certificate when only
the surrounding bytecode artifact changes.
-/
namespace HistoricalSearch.CRTMemoryBounds
open EvmSemantics EvmSemantics.EVM

theorem activeWordsAfter_fix (curr off sz : Nat) (hsz : sz ≠ 0)
    (hoff : off + sz ≤ 2816) (hcurr : 88 ≤ curr) :
    MachineState.activeWordsAfter curr off sz = curr := by
  unfold MachineState.activeWordsAfter
  simp only [hsz, if_false]
  have hle : (off + sz - 1) / 32 + 1 ≤ curr := by omega
  exact Nat.max_eq_left hle

theorem activeWords_fix (s : State) (off sz : Nat) (hsz : sz ≠ 0)
    (hoff : off + sz ≤ 2816) (hact : 88 ≤ s.activeWords.toNat) :
    UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat off sz) =
      s.activeWords := by
  rw [activeWordsAfter_fix _ off sz hsz hoff hact]
  exact (Challenge.EvmProof.Word.word_eq_ofNat_toNat _).symm

#print axioms activeWordsAfter_fix
#print axioms activeWords_fix
end HistoricalSearch.CRTMemoryBounds
