import Challenge.Ripemd160.Submission.H39Memo.PatternTerminalInstances

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000

namespace Challenge.Ripemd160.Submission.H39Memo.PatternTerminalCertificates

open EvmSemantics EvmSemantics.EVM Challenge.EvmProof PatternTerminal

def tailCertificate : (p : Fin 14) → (PatternFacts.target p).size % 32 ≠ 0 →
    TailCertificate (entryPC p + 2) (offsetWidth p) (tailOffset p) (PatternFacts.tailWord p)
  | ⟨0, _⟩, _ => by
      simpa [entryPC, offsetWidth, tailOffset, PatternFacts.target_size, PatternFacts.size] using tailP1
  | ⟨1, _⟩, _ => by
      simpa [entryPC, offsetWidth, tailOffset, PatternFacts.target_size, PatternFacts.size] using tailP31
  | ⟨2, _⟩, h => False.elim (h (by rw [PatternFacts.target_size]; norm_num [PatternFacts.size]))
  | ⟨3, _⟩, _ => by
      simpa [entryPC, offsetWidth, tailOffset, PatternFacts.target_size, PatternFacts.size] using tailP55
  | ⟨4, _⟩, _ => by
      simpa [entryPC, offsetWidth, tailOffset, PatternFacts.target_size, PatternFacts.size] using tailP56
  | ⟨5, _⟩, _ => by
      simpa [entryPC, offsetWidth, tailOffset, PatternFacts.target_size, PatternFacts.size] using tailP63
  | ⟨6, _⟩, h => False.elim (h (by rw [PatternFacts.target_size]; norm_num [PatternFacts.size]))
  | ⟨7, _⟩, _ => by
      simpa [entryPC, offsetWidth, tailOffset, PatternFacts.target_size, PatternFacts.size] using tailP65
  | ⟨8, _⟩, _ => by
      simpa [entryPC, offsetWidth, tailOffset, PatternFacts.target_size, PatternFacts.size] using tailP119
  | ⟨9, _⟩, _ => by
      simpa [entryPC, offsetWidth, tailOffset, PatternFacts.target_size, PatternFacts.size] using tailP120
  | ⟨10, _⟩, h => False.elim (h (by rw [PatternFacts.target_size]; norm_num [PatternFacts.size]))
  | ⟨11, _⟩, h => False.elim (h (by rw [PatternFacts.target_size]; norm_num [PatternFacts.size]))
  | ⟨12, _⟩, _ => by
      simpa [entryPC, offsetWidth, tailOffset, PatternFacts.target_size, PatternFacts.size] using tailP376
  | ⟨13, _⟩, _ => by
      simpa [entryPC, offsetWidth, tailOffset, PatternFacts.target_size, PatternFacts.size] using tailP1000
  | ⟨n + 14, h⟩, _ => False.elim (by omega)

theorem partial_outputPC (p : Fin 14) (h : (PatternFacts.target p).size % 32 ≠ 0) :
    entryPC p + 2 + (offsetWidth p).val + 40 =
      TerminalPathsSites.outputPC (PatternFacts.targetIndex p) := by
  fin_cases p
  · rfl
  · rfl
  · exact False.elim (h rfl)
  · rfl
  · rfl
  · rfl
  · exact False.elim (h rfl)
  · rfl
  · rfl
  · rfl
  · exact False.elim (h rfl)
  · exact False.elim (h rfl)
  · rfl
  · rfl

theorem whole_outputPC (p : Fin 14) (h : (PatternFacts.target p).size % 32 = 0) :
    entryPC p + 2 = TerminalPathsSites.outputPC (PatternFacts.targetIndex p) := by
  fin_cases p
  · contradiction
  · contradiction
  · rfl
  · contradiction
  · contradiction
  · contradiction
  · rfl
  · contradiction
  · contradiction
  · contradiction
  · rfl
  · rfl
  · contradiction
  · contradiction

end Challenge.Ripemd160.Submission.H39Memo.PatternTerminalCertificates
