import Challenge.Ripemd160.Submission.H39Memo.PatternTraceResult
import Challenge.Ripemd160.Submission.H39Memo.PatternTraceBlock3109
import Challenge.Ripemd160.Submission.H39Memo.PatternCorrectDAG1
import Challenge.Ripemd160.Submission.H39Memo.PatternTraceBlock1696
import Challenge.Ripemd160.Submission.H39Memo.PatternTraceBlock1705
import Challenge.Ripemd160.Submission.H39Memo.PatternTraceBlock1713
import Challenge.Ripemd160.Submission.H39Memo.PatternTraceBlock1753
import Challenge.Ripemd160.Submission.H39Memo.PatternTraceBlock1761
import Challenge.Ripemd160.Submission.H39Memo.PatternTraceBlock1769

set_option warningAsError true

namespace Challenge.Ripemd160.Submission.H39Memo.PatternTrace
open EvmSemantics EvmSemantics.EVM

theorem dag1769 (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hfit : bytes.size < 2 ^ 64)
    (hrun : s.halt = .Running) (hcode : s.executionEnv.code = h39Bytecode)
    (ht : TerminalCorrect s bytes) (hp : Prefix bytes 1) :
    Outcome s bytes (stateAt s bytes 1769) := by
  rcases size_cases1769 s bytes hinput hfit hrun hcode with ⟨heq, hjump⟩ | ⟨_, hnext⟩
  · exact Outcome.prepend hjump hrun (ht 4 heq hp)
  · exact Outcome.prepend hnext hrun
      (dag1777 s bytes hinput hfit hrun hcode ht hp)

theorem dag1761 (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hfit : bytes.size < 2 ^ 64)
    (hrun : s.halt = .Running) (hcode : s.executionEnv.code = h39Bytecode)
    (ht : TerminalCorrect s bytes) (hp : Prefix bytes 1) :
    Outcome s bytes (stateAt s bytes 1761) := by
  rcases size_cases1761 s bytes hinput hfit hrun hcode with ⟨heq, hjump⟩ | ⟨_, hnext⟩
  · exact Outcome.prepend hjump hrun (ht 3 heq hp)
  · exact Outcome.prepend hnext hrun
      (dag1769 s bytes hinput hfit hrun hcode ht hp)

theorem dag1753 (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hfit : bytes.size < 2 ^ 64)
    (hrun : s.halt = .Running) (hcode : s.executionEnv.code = h39Bytecode)
    (ht : TerminalCorrect s bytes) (hp : Prefix bytes 1) :
    Outcome s bytes (stateAt s bytes 1753) := by
  rcases size_cases1753 s bytes hinput hfit hrun hcode with ⟨heq, hjump⟩ | ⟨_, hnext⟩
  · exact Outcome.prepend hjump hrun (ht 2 heq hp)
  · exact Outcome.prepend hnext hrun
      (dag1761 s bytes hinput hfit hrun hcode ht hp)

theorem dag1713 (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hfit : bytes.size < 2 ^ 64)
    (hrun : s.halt = .Running) (hcode : s.executionEnv.code = h39Bytecode)
    (ht : TerminalCorrect s bytes) (hp : Prefix bytes 0) :
    Outcome s bytes (stateAt s bytes 1713) := by
  rcases prefix_cases1713 s bytes hinput hrun hcode with ⟨hw, hnext⟩ | hfail
  · exact Outcome.prepend hnext hrun
      (dag1753 s bytes hinput hfit hrun hcode ht (prefix_next bytes 0 hp hw))
  · exact Or.inl (hfail.trans hrun (cleanup3109 s bytes hrun hcode))

theorem dag1705 (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hfit : bytes.size < 2 ^ 64)
    (hrun : s.halt = .Running) (hcode : s.executionEnv.code = h39Bytecode)
    (ht : TerminalCorrect s bytes) (hp : Prefix bytes 0) :
    Outcome s bytes (stateAt s bytes 1705) := by
  rcases size_cases1705 s bytes hinput hfit hrun hcode with ⟨heq, hjump⟩ | ⟨_, hnext⟩
  · exact Outcome.prepend hjump hrun (ht 1 heq hp)
  · exact Outcome.prepend hnext hrun
      (dag1713 s bytes hinput hfit hrun hcode ht hp)

theorem dag1696 (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hfit : bytes.size < 2 ^ 64)
    (hrun : s.halt = .Running) (hcode : s.executionEnv.code = h39Bytecode)
    (ht : TerminalCorrect s bytes) (hp : Prefix bytes 0) :
    Outcome s bytes (stateAt s bytes 1696) := by
  rcases size_cases1696 s bytes hinput hfit hrun hcode with ⟨heq, hjump⟩ | ⟨_, hnext⟩
  · exact Outcome.prepend hjump hrun (ht 0 heq hp)
  · exact Outcome.prepend hnext hrun
      (dag1705 s bytes hinput hfit hrun hcode ht hp)

end Challenge.Ripemd160.Submission.H39Memo.PatternTrace

