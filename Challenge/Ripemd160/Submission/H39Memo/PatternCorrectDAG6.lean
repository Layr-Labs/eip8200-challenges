import Challenge.Ripemd160.Submission.H39Memo.PatternTraceResult
import Challenge.Ripemd160.Submission.H39Memo.PatternTraceBlock3109
import Challenge.Ripemd160.Submission.H39Memo.PatternCorrectDAG7
import Challenge.Ripemd160.Submission.H39Memo.PatternTraceBlock2760
import Challenge.Ripemd160.Submission.H39Memo.PatternTraceBlock2802
import Challenge.Ripemd160.Submission.H39Memo.PatternTraceBlock2844
import Challenge.Ripemd160.Submission.H39Memo.PatternTraceBlock2886
import Challenge.Ripemd160.Submission.H39Memo.PatternTraceBlock2928
import Challenge.Ripemd160.Submission.H39Memo.PatternTraceBlock2970

set_option warningAsError true

namespace Challenge.Ripemd160.Submission.H39Memo.PatternTrace
open EvmSemantics EvmSemantics.EVM

theorem dag2970 (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hfit : bytes.size < 2 ^ 64)
    (hrun : s.halt = .Running) (hcode : s.executionEnv.code = h39Bytecode)
    (ht : TerminalCorrect s bytes) (hp : Prefix bytes 28) :
    Outcome s bytes (stateAt s bytes 2970) := by
  rcases prefix_cases2970 s bytes hinput hrun hcode with ⟨hw, hnext⟩ | hfail
  · exact Outcome.prepend hnext hrun
      (dag3012 s bytes hinput hfit hrun hcode ht (prefix_next bytes 28 hp hw))
  · exact Or.inl (hfail.trans hrun (cleanup3109 s bytes hrun hcode))

theorem dag2928 (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hfit : bytes.size < 2 ^ 64)
    (hrun : s.halt = .Running) (hcode : s.executionEnv.code = h39Bytecode)
    (ht : TerminalCorrect s bytes) (hp : Prefix bytes 27) :
    Outcome s bytes (stateAt s bytes 2928) := by
  rcases prefix_cases2928 s bytes hinput hrun hcode with ⟨hw, hnext⟩ | hfail
  · exact Outcome.prepend hnext hrun
      (dag2970 s bytes hinput hfit hrun hcode ht (prefix_next bytes 27 hp hw))
  · exact Or.inl (hfail.trans hrun (cleanup3109 s bytes hrun hcode))

theorem dag2886 (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hfit : bytes.size < 2 ^ 64)
    (hrun : s.halt = .Running) (hcode : s.executionEnv.code = h39Bytecode)
    (ht : TerminalCorrect s bytes) (hp : Prefix bytes 26) :
    Outcome s bytes (stateAt s bytes 2886) := by
  rcases prefix_cases2886 s bytes hinput hrun hcode with ⟨hw, hnext⟩ | hfail
  · exact Outcome.prepend hnext hrun
      (dag2928 s bytes hinput hfit hrun hcode ht (prefix_next bytes 26 hp hw))
  · exact Or.inl (hfail.trans hrun (cleanup3109 s bytes hrun hcode))

theorem dag2844 (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hfit : bytes.size < 2 ^ 64)
    (hrun : s.halt = .Running) (hcode : s.executionEnv.code = h39Bytecode)
    (ht : TerminalCorrect s bytes) (hp : Prefix bytes 25) :
    Outcome s bytes (stateAt s bytes 2844) := by
  rcases prefix_cases2844 s bytes hinput hrun hcode with ⟨hw, hnext⟩ | hfail
  · exact Outcome.prepend hnext hrun
      (dag2886 s bytes hinput hfit hrun hcode ht (prefix_next bytes 25 hp hw))
  · exact Or.inl (hfail.trans hrun (cleanup3109 s bytes hrun hcode))

theorem dag2802 (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hfit : bytes.size < 2 ^ 64)
    (hrun : s.halt = .Running) (hcode : s.executionEnv.code = h39Bytecode)
    (ht : TerminalCorrect s bytes) (hp : Prefix bytes 24) :
    Outcome s bytes (stateAt s bytes 2802) := by
  rcases prefix_cases2802 s bytes hinput hrun hcode with ⟨hw, hnext⟩ | hfail
  · exact Outcome.prepend hnext hrun
      (dag2844 s bytes hinput hfit hrun hcode ht (prefix_next bytes 24 hp hw))
  · exact Or.inl (hfail.trans hrun (cleanup3109 s bytes hrun hcode))

theorem dag2760 (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hfit : bytes.size < 2 ^ 64)
    (hrun : s.halt = .Running) (hcode : s.executionEnv.code = h39Bytecode)
    (ht : TerminalCorrect s bytes) (hp : Prefix bytes 23) :
    Outcome s bytes (stateAt s bytes 2760) := by
  rcases prefix_cases2760 s bytes hinput hrun hcode with ⟨hw, hnext⟩ | hfail
  · exact Outcome.prepend hnext hrun
      (dag2802 s bytes hinput hfit hrun hcode ht (prefix_next bytes 23 hp hw))
  · exact Or.inl (hfail.trans hrun (cleanup3109 s bytes hrun hcode))

end Challenge.Ripemd160.Submission.H39Memo.PatternTrace

