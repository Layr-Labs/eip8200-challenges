import Challenge.Ripemd160.Submission.H39Memo.PatternTraceResult
import Challenge.Ripemd160.Submission.H39Memo.PatternTraceBlock3109
import Challenge.Ripemd160.Submission.H39Memo.PatternCorrectDAG5
import Challenge.Ripemd160.Submission.H39Memo.PatternTraceBlock2256
import Challenge.Ripemd160.Submission.H39Memo.PatternTraceBlock2298
import Challenge.Ripemd160.Submission.H39Memo.PatternTraceBlock2340
import Challenge.Ripemd160.Submission.H39Memo.PatternTraceBlock2382
import Challenge.Ripemd160.Submission.H39Memo.PatternTraceBlock2424
import Challenge.Ripemd160.Submission.H39Memo.PatternTraceBlock2466

set_option warningAsError true

namespace Challenge.Ripemd160.Submission.H39Memo.PatternTrace
open EvmSemantics EvmSemantics.EVM

theorem dag2466 (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hfit : bytes.size < 2 ^ 64)
    (hrun : s.halt = .Running) (hcode : s.executionEnv.code = h39Bytecode)
    (ht : TerminalCorrect s bytes) (hp : Prefix bytes 16) :
    Outcome s bytes (stateAt s bytes 2466) := by
  rcases prefix_cases2466 s bytes hinput hrun hcode with ⟨hw, hnext⟩ | hfail
  · exact Outcome.prepend hnext hrun
      (dag2508 s bytes hinput hfit hrun hcode ht (prefix_next bytes 16 hp hw))
  · exact Or.inl (hfail.trans hrun (cleanup3109 s bytes hrun hcode))

theorem dag2424 (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hfit : bytes.size < 2 ^ 64)
    (hrun : s.halt = .Running) (hcode : s.executionEnv.code = h39Bytecode)
    (ht : TerminalCorrect s bytes) (hp : Prefix bytes 15) :
    Outcome s bytes (stateAt s bytes 2424) := by
  rcases prefix_cases2424 s bytes hinput hrun hcode with ⟨hw, hnext⟩ | hfail
  · exact Outcome.prepend hnext hrun
      (dag2466 s bytes hinput hfit hrun hcode ht (prefix_next bytes 15 hp hw))
  · exact Or.inl (hfail.trans hrun (cleanup3109 s bytes hrun hcode))

theorem dag2382 (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hfit : bytes.size < 2 ^ 64)
    (hrun : s.halt = .Running) (hcode : s.executionEnv.code = h39Bytecode)
    (ht : TerminalCorrect s bytes) (hp : Prefix bytes 14) :
    Outcome s bytes (stateAt s bytes 2382) := by
  rcases prefix_cases2382 s bytes hinput hrun hcode with ⟨hw, hnext⟩ | hfail
  · exact Outcome.prepend hnext hrun
      (dag2424 s bytes hinput hfit hrun hcode ht (prefix_next bytes 14 hp hw))
  · exact Or.inl (hfail.trans hrun (cleanup3109 s bytes hrun hcode))

theorem dag2340 (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hfit : bytes.size < 2 ^ 64)
    (hrun : s.halt = .Running) (hcode : s.executionEnv.code = h39Bytecode)
    (ht : TerminalCorrect s bytes) (hp : Prefix bytes 13) :
    Outcome s bytes (stateAt s bytes 2340) := by
  rcases prefix_cases2340 s bytes hinput hrun hcode with ⟨hw, hnext⟩ | hfail
  · exact Outcome.prepend hnext hrun
      (dag2382 s bytes hinput hfit hrun hcode ht (prefix_next bytes 13 hp hw))
  · exact Or.inl (hfail.trans hrun (cleanup3109 s bytes hrun hcode))

theorem dag2298 (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hfit : bytes.size < 2 ^ 64)
    (hrun : s.halt = .Running) (hcode : s.executionEnv.code = h39Bytecode)
    (ht : TerminalCorrect s bytes) (hp : Prefix bytes 12) :
    Outcome s bytes (stateAt s bytes 2298) := by
  rcases prefix_cases2298 s bytes hinput hrun hcode with ⟨hw, hnext⟩ | hfail
  · exact Outcome.prepend hnext hrun
      (dag2340 s bytes hinput hfit hrun hcode ht (prefix_next bytes 12 hp hw))
  · exact Or.inl (hfail.trans hrun (cleanup3109 s bytes hrun hcode))

theorem dag2256 (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hfit : bytes.size < 2 ^ 64)
    (hrun : s.halt = .Running) (hcode : s.executionEnv.code = h39Bytecode)
    (ht : TerminalCorrect s bytes) (hp : Prefix bytes 11) :
    Outcome s bytes (stateAt s bytes 2256) := by
  rcases prefix_cases2256 s bytes hinput hrun hcode with ⟨hw, hnext⟩ | hfail
  · exact Outcome.prepend hnext hrun
      (dag2298 s bytes hinput hfit hrun hcode ht (prefix_next bytes 11 hp hw))
  · exact Or.inl (hfail.trans hrun (cleanup3109 s bytes hrun hcode))

end Challenge.Ripemd160.Submission.H39Memo.PatternTrace

