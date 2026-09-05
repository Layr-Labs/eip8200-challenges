import Challenge.Ripemd160.Submission.H39Memo.PatternTraceResult
import Challenge.Ripemd160.Submission.H39Memo.PatternTraceBlock3109
import Challenge.Ripemd160.Submission.H39Memo.PatternTraceBlock3012
import Challenge.Ripemd160.Submission.H39Memo.PatternTraceBlock3054
import Challenge.Ripemd160.Submission.H39Memo.PatternTraceBlock3096
import Challenge.Ripemd160.Submission.H39Memo.PatternTraceBlock3105

set_option warningAsError true

namespace Challenge.Ripemd160.Submission.H39Memo.PatternTrace
open EvmSemantics EvmSemantics.EVM

theorem dag3105 (s : State) (bytes : ByteArray)
    (_hinput : s.executionEnv.calldata = bytes) (_hfit : bytes.size < 2 ^ 64)
    (hrun : s.halt = .Running) (hcode : s.executionEnv.code = h39Bytecode)
    (_ht : TerminalCorrect s bytes) (_hp : Prefix bytes 31) :
    Outcome s bytes (stateAt s bytes 3105) := by
  exact Or.inl ((cleanup3105 s bytes hrun hcode).trans hrun
    (cleanup3109 s bytes hrun hcode))

theorem dag3096 (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hfit : bytes.size < 2 ^ 64)
    (hrun : s.halt = .Running) (hcode : s.executionEnv.code = h39Bytecode)
    (ht : TerminalCorrect s bytes) (hp : Prefix bytes 31) :
    Outcome s bytes (stateAt s bytes 3096) := by
  rcases size_cases3096 s bytes hinput hfit hrun hcode with ⟨heq, hjump⟩ | ⟨_, hnext⟩
  · exact Outcome.prepend hjump hrun (ht 13 heq hp)
  · exact Outcome.prepend hnext hrun
      (dag3105 s bytes hinput hfit hrun hcode ht hp)

theorem dag3054 (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hfit : bytes.size < 2 ^ 64)
    (hrun : s.halt = .Running) (hcode : s.executionEnv.code = h39Bytecode)
    (ht : TerminalCorrect s bytes) (hp : Prefix bytes 30) :
    Outcome s bytes (stateAt s bytes 3054) := by
  rcases prefix_cases3054 s bytes hinput hrun hcode with ⟨hw, hnext⟩ | hfail
  · exact Outcome.prepend hnext hrun
      (dag3096 s bytes hinput hfit hrun hcode ht (prefix_next bytes 30 hp hw))
  · exact Or.inl (hfail.trans hrun (cleanup3109 s bytes hrun hcode))

theorem dag3012 (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hfit : bytes.size < 2 ^ 64)
    (hrun : s.halt = .Running) (hcode : s.executionEnv.code = h39Bytecode)
    (ht : TerminalCorrect s bytes) (hp : Prefix bytes 29) :
    Outcome s bytes (stateAt s bytes 3012) := by
  rcases prefix_cases3012 s bytes hinput hrun hcode with ⟨hw, hnext⟩ | hfail
  · exact Outcome.prepend hnext hrun
      (dag3054 s bytes hinput hfit hrun hcode ht (prefix_next bytes 29 hp hw))
  · exact Or.inl (hfail.trans hrun (cleanup3109 s bytes hrun hcode))

end Challenge.Ripemd160.Submission.H39Memo.PatternTrace

