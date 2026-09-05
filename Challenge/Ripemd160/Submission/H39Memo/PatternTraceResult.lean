import Challenge.Ripemd160.Submission.H39Memo.PatternTraceBase
import Challenge.Ripemd160.Submission.H39Memo.PatternFacts
import Challenge.Ripemd160.Submission.H39Memo.TerminalPathsSites

set_option warningAsError true

namespace Challenge.Ripemd160.Submission.H39Memo.PatternTrace
open EvmSemantics EvmSemantics.EVM DispatchState

def Outcome (s : State) (bytes : ByteArray) (start : State) : Prop :=
  Trace start (fallback s) ∨
    ∃ p : Fin 14, bytes = PatternFacts.target p ∧
      Trace start (outputEntry s (TerminalPathsSites.outputPC (PatternFacts.targetIndex p)))

theorem Outcome.prepend {s start mid : State} {bytes : ByteArray}
    (ht : Trace start mid) (hrun : mid.halt = .Running)
    (ho : Outcome s bytes mid) : Outcome s bytes start := by
  rcases ho with hf | ⟨p, heq, hout⟩
  · exact Or.inl (ht.trans hrun hf)
  · exact Or.inr ⟨p, heq, ht.trans hrun hout⟩

def terminalPC (p : Fin 14) : Nat :=
  match p.val with
  | 0 => 3362
  | 1 => 3431
  | 2 => 3500
  | 3 => 3529
  | 4 => 3599
  | 5 => 3669
  | 6 => 3739
  | 7 => 3768
  | 8 => 3838
  | 9 => 3908
  | 10 => 3978
  | 11 => 4007
  | 12 => 4036
  | _ => 4107

def TerminalCorrect (s : State) (bytes : ByteArray) : Prop :=
  ∀ p : Fin 14, bytes.size = PatternFacts.size p →
    Prefix bytes (PatternFacts.size p / 32) →
      Outcome s bytes (stateAt s bytes (terminalPC p))

end Challenge.Ripemd160.Submission.H39Memo.PatternTrace
