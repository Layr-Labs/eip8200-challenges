import Challenge.Ripemd160.Submission.H39Memo.PatternTraceResult
import Challenge.Ripemd160.Submission.H39Memo.PatternTraceBlock3109
import Challenge.Ripemd160.Submission.H39Memo.PatternCorrectDAG2
import Challenge.Ripemd160.Submission.H39Memo.PatternTraceBlock1777
import Challenge.Ripemd160.Submission.H39Memo.PatternTraceBlock1785
import Challenge.Ripemd160.Submission.H39Memo.PatternTraceBlock1826
import Challenge.Ripemd160.Submission.H39Memo.PatternTraceBlock1834
import Challenge.Ripemd160.Submission.H39Memo.PatternTraceBlock1842
import Challenge.Ripemd160.Submission.H39Memo.PatternTraceBlock1883

set_option warningAsError true

namespace Challenge.Ripemd160.Submission.H39Memo.PatternTrace
open EvmSemantics EvmSemantics.EVM

theorem dag1883 (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hfit : bytes.size < 2 ^ 64)
    (hrun : s.halt = .Running) (hcode : s.executionEnv.code = h39Bytecode)
    (ht : TerminalCorrect s bytes) (hp : Prefix bytes 3) :
    Outcome s bytes (stateAt s bytes 1883) := by
  rcases size_cases1883 s bytes hinput hfit hrun hcode with ⟨heq, hjump⟩ | ⟨_, hnext⟩
  · exact Outcome.prepend hjump hrun (ht 8 heq hp)
  · exact Outcome.prepend hnext hrun
      (dag1891 s bytes hinput hfit hrun hcode ht hp)

theorem dag1842 (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hfit : bytes.size < 2 ^ 64)
    (hrun : s.halt = .Running) (hcode : s.executionEnv.code = h39Bytecode)
    (ht : TerminalCorrect s bytes) (hp : Prefix bytes 2) :
    Outcome s bytes (stateAt s bytes 1842) := by
  rcases prefix_cases1842 s bytes hinput hrun hcode with ⟨hw, hnext⟩ | hfail
  · exact Outcome.prepend hnext hrun
      (dag1883 s bytes hinput hfit hrun hcode ht (prefix_next bytes 2 hp hw))
  · exact Or.inl (hfail.trans hrun (cleanup3109 s bytes hrun hcode))

theorem dag1834 (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hfit : bytes.size < 2 ^ 64)
    (hrun : s.halt = .Running) (hcode : s.executionEnv.code = h39Bytecode)
    (ht : TerminalCorrect s bytes) (hp : Prefix bytes 2) :
    Outcome s bytes (stateAt s bytes 1834) := by
  rcases size_cases1834 s bytes hinput hfit hrun hcode with ⟨heq, hjump⟩ | ⟨_, hnext⟩
  · exact Outcome.prepend hjump hrun (ht 7 heq hp)
  · exact Outcome.prepend hnext hrun
      (dag1842 s bytes hinput hfit hrun hcode ht hp)

theorem dag1826 (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hfit : bytes.size < 2 ^ 64)
    (hrun : s.halt = .Running) (hcode : s.executionEnv.code = h39Bytecode)
    (ht : TerminalCorrect s bytes) (hp : Prefix bytes 2) :
    Outcome s bytes (stateAt s bytes 1826) := by
  rcases size_cases1826 s bytes hinput hfit hrun hcode with ⟨heq, hjump⟩ | ⟨_, hnext⟩
  · exact Outcome.prepend hjump hrun (ht 6 heq hp)
  · exact Outcome.prepend hnext hrun
      (dag1834 s bytes hinput hfit hrun hcode ht hp)

theorem dag1785 (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hfit : bytes.size < 2 ^ 64)
    (hrun : s.halt = .Running) (hcode : s.executionEnv.code = h39Bytecode)
    (ht : TerminalCorrect s bytes) (hp : Prefix bytes 1) :
    Outcome s bytes (stateAt s bytes 1785) := by
  rcases prefix_cases1785 s bytes hinput hrun hcode with ⟨hw, hnext⟩ | hfail
  · exact Outcome.prepend hnext hrun
      (dag1826 s bytes hinput hfit hrun hcode ht (prefix_next bytes 1 hp hw))
  · exact Or.inl (hfail.trans hrun (cleanup3109 s bytes hrun hcode))

theorem dag1777 (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hfit : bytes.size < 2 ^ 64)
    (hrun : s.halt = .Running) (hcode : s.executionEnv.code = h39Bytecode)
    (ht : TerminalCorrect s bytes) (hp : Prefix bytes 1) :
    Outcome s bytes (stateAt s bytes 1777) := by
  rcases size_cases1777 s bytes hinput hfit hrun hcode with ⟨heq, hjump⟩ | ⟨_, hnext⟩
  · exact Outcome.prepend hjump hrun (ht 5 heq hp)
  · exact Outcome.prepend hnext hrun
      (dag1785 s bytes hinput hfit hrun hcode ht hp)

end Challenge.Ripemd160.Submission.H39Memo.PatternTrace

