import Challenge.Ripemd160.Submission.H39Memo.PatternTraceResult
import Challenge.Ripemd160.Submission.H39Memo.PatternTraceBlock3109
import Challenge.Ripemd160.Submission.H39Memo.PatternCorrectDAG4
import Challenge.Ripemd160.Submission.H39Memo.PatternTraceBlock2071
import Challenge.Ripemd160.Submission.H39Memo.PatternTraceBlock2112
import Challenge.Ripemd160.Submission.H39Memo.PatternTraceBlock2121
import Challenge.Ripemd160.Submission.H39Memo.PatternTraceBlock2163
import Challenge.Ripemd160.Submission.H39Memo.PatternTraceBlock2205
import Challenge.Ripemd160.Submission.H39Memo.PatternTraceBlock2247

set_option warningAsError true

namespace Challenge.Ripemd160.Submission.H39Memo.PatternTrace
open EvmSemantics EvmSemantics.EVM

theorem dag2247 (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hfit : bytes.size < 2 ^ 64)
    (hrun : s.halt = .Running) (hcode : s.executionEnv.code = h39Bytecode)
    (ht : TerminalCorrect s bytes) (hp : Prefix bytes 11) :
    Outcome s bytes (stateAt s bytes 2247) := by
  rcases size_cases2247 s bytes hinput hfit hrun hcode with ⟨heq, hjump⟩ | ⟨_, hnext⟩
  · exact Outcome.prepend hjump hrun (ht 12 heq hp)
  · exact Outcome.prepend hnext hrun
      (dag2256 s bytes hinput hfit hrun hcode ht hp)

theorem dag2205 (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hfit : bytes.size < 2 ^ 64)
    (hrun : s.halt = .Running) (hcode : s.executionEnv.code = h39Bytecode)
    (ht : TerminalCorrect s bytes) (hp : Prefix bytes 10) :
    Outcome s bytes (stateAt s bytes 2205) := by
  rcases prefix_cases2205 s bytes hinput hrun hcode with ⟨hw, hnext⟩ | hfail
  · exact Outcome.prepend hnext hrun
      (dag2247 s bytes hinput hfit hrun hcode ht (prefix_next bytes 10 hp hw))
  · exact Or.inl (hfail.trans hrun (cleanup3109 s bytes hrun hcode))

theorem dag2163 (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hfit : bytes.size < 2 ^ 64)
    (hrun : s.halt = .Running) (hcode : s.executionEnv.code = h39Bytecode)
    (ht : TerminalCorrect s bytes) (hp : Prefix bytes 9) :
    Outcome s bytes (stateAt s bytes 2163) := by
  rcases prefix_cases2163 s bytes hinput hrun hcode with ⟨hw, hnext⟩ | hfail
  · exact Outcome.prepend hnext hrun
      (dag2205 s bytes hinput hfit hrun hcode ht (prefix_next bytes 9 hp hw))
  · exact Or.inl (hfail.trans hrun (cleanup3109 s bytes hrun hcode))

theorem dag2121 (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hfit : bytes.size < 2 ^ 64)
    (hrun : s.halt = .Running) (hcode : s.executionEnv.code = h39Bytecode)
    (ht : TerminalCorrect s bytes) (hp : Prefix bytes 8) :
    Outcome s bytes (stateAt s bytes 2121) := by
  rcases prefix_cases2121 s bytes hinput hrun hcode with ⟨hw, hnext⟩ | hfail
  · exact Outcome.prepend hnext hrun
      (dag2163 s bytes hinput hfit hrun hcode ht (prefix_next bytes 8 hp hw))
  · exact Or.inl (hfail.trans hrun (cleanup3109 s bytes hrun hcode))

theorem dag2112 (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hfit : bytes.size < 2 ^ 64)
    (hrun : s.halt = .Running) (hcode : s.executionEnv.code = h39Bytecode)
    (ht : TerminalCorrect s bytes) (hp : Prefix bytes 8) :
    Outcome s bytes (stateAt s bytes 2112) := by
  rcases size_cases2112 s bytes hinput hfit hrun hcode with ⟨heq, hjump⟩ | ⟨_, hnext⟩
  · exact Outcome.prepend hjump hrun (ht 11 heq hp)
  · exact Outcome.prepend hnext hrun
      (dag2121 s bytes hinput hfit hrun hcode ht hp)

theorem dag2071 (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hfit : bytes.size < 2 ^ 64)
    (hrun : s.halt = .Running) (hcode : s.executionEnv.code = h39Bytecode)
    (ht : TerminalCorrect s bytes) (hp : Prefix bytes 7) :
    Outcome s bytes (stateAt s bytes 2071) := by
  rcases prefix_cases2071 s bytes hinput hrun hcode with ⟨hw, hnext⟩ | hfail
  · exact Outcome.prepend hnext hrun
      (dag2112 s bytes hinput hfit hrun hcode ht (prefix_next bytes 7 hp hw))
  · exact Or.inl (hfail.trans hrun (cleanup3109 s bytes hrun hcode))

end Challenge.Ripemd160.Submission.H39Memo.PatternTrace

