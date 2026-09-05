import Challenge.Ripemd160.Submission.H39Memo.PatternTraceResult
import Challenge.Ripemd160.Submission.H39Memo.PatternTraceBlock3109
import Challenge.Ripemd160.Submission.H39Memo.PatternCorrectDAG3
import Challenge.Ripemd160.Submission.H39Memo.PatternTraceBlock1891
import Challenge.Ripemd160.Submission.H39Memo.PatternTraceBlock1899
import Challenge.Ripemd160.Submission.H39Memo.PatternTraceBlock1940
import Challenge.Ripemd160.Submission.H39Memo.PatternTraceBlock1948
import Challenge.Ripemd160.Submission.H39Memo.PatternTraceBlock1989
import Challenge.Ripemd160.Submission.H39Memo.PatternTraceBlock2030

set_option warningAsError true

namespace Challenge.Ripemd160.Submission.H39Memo.PatternTrace
open EvmSemantics EvmSemantics.EVM

theorem dag2030 (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hfit : bytes.size < 2 ^ 64)
    (hrun : s.halt = .Running) (hcode : s.executionEnv.code = h39Bytecode)
    (ht : TerminalCorrect s bytes) (hp : Prefix bytes 6) :
    Outcome s bytes (stateAt s bytes 2030) := by
  rcases prefix_cases2030 s bytes hinput hrun hcode with ⟨hw, hnext⟩ | hfail
  · exact Outcome.prepend hnext hrun
      (dag2071 s bytes hinput hfit hrun hcode ht (prefix_next bytes 6 hp hw))
  · exact Or.inl (hfail.trans hrun (cleanup3109 s bytes hrun hcode))

theorem dag1989 (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hfit : bytes.size < 2 ^ 64)
    (hrun : s.halt = .Running) (hcode : s.executionEnv.code = h39Bytecode)
    (ht : TerminalCorrect s bytes) (hp : Prefix bytes 5) :
    Outcome s bytes (stateAt s bytes 1989) := by
  rcases prefix_cases1989 s bytes hinput hrun hcode with ⟨hw, hnext⟩ | hfail
  · exact Outcome.prepend hnext hrun
      (dag2030 s bytes hinput hfit hrun hcode ht (prefix_next bytes 5 hp hw))
  · exact Or.inl (hfail.trans hrun (cleanup3109 s bytes hrun hcode))

theorem dag1948 (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hfit : bytes.size < 2 ^ 64)
    (hrun : s.halt = .Running) (hcode : s.executionEnv.code = h39Bytecode)
    (ht : TerminalCorrect s bytes) (hp : Prefix bytes 4) :
    Outcome s bytes (stateAt s bytes 1948) := by
  rcases prefix_cases1948 s bytes hinput hrun hcode with ⟨hw, hnext⟩ | hfail
  · exact Outcome.prepend hnext hrun
      (dag1989 s bytes hinput hfit hrun hcode ht (prefix_next bytes 4 hp hw))
  · exact Or.inl (hfail.trans hrun (cleanup3109 s bytes hrun hcode))

theorem dag1940 (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hfit : bytes.size < 2 ^ 64)
    (hrun : s.halt = .Running) (hcode : s.executionEnv.code = h39Bytecode)
    (ht : TerminalCorrect s bytes) (hp : Prefix bytes 4) :
    Outcome s bytes (stateAt s bytes 1940) := by
  rcases size_cases1940 s bytes hinput hfit hrun hcode with ⟨heq, hjump⟩ | ⟨_, hnext⟩
  · exact Outcome.prepend hjump hrun (ht 10 heq hp)
  · exact Outcome.prepend hnext hrun
      (dag1948 s bytes hinput hfit hrun hcode ht hp)

theorem dag1899 (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hfit : bytes.size < 2 ^ 64)
    (hrun : s.halt = .Running) (hcode : s.executionEnv.code = h39Bytecode)
    (ht : TerminalCorrect s bytes) (hp : Prefix bytes 3) :
    Outcome s bytes (stateAt s bytes 1899) := by
  rcases prefix_cases1899 s bytes hinput hrun hcode with ⟨hw, hnext⟩ | hfail
  · exact Outcome.prepend hnext hrun
      (dag1940 s bytes hinput hfit hrun hcode ht (prefix_next bytes 3 hp hw))
  · exact Or.inl (hfail.trans hrun (cleanup3109 s bytes hrun hcode))

theorem dag1891 (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hfit : bytes.size < 2 ^ 64)
    (hrun : s.halt = .Running) (hcode : s.executionEnv.code = h39Bytecode)
    (ht : TerminalCorrect s bytes) (hp : Prefix bytes 3) :
    Outcome s bytes (stateAt s bytes 1891) := by
  rcases size_cases1891 s bytes hinput hfit hrun hcode with ⟨heq, hjump⟩ | ⟨_, hnext⟩
  · exact Outcome.prepend hjump hrun (ht 9 heq hp)
  · exact Outcome.prepend hnext hrun
      (dag1899 s bytes hinput hfit hrun hcode ht hp)

end Challenge.Ripemd160.Submission.H39Memo.PatternTrace

