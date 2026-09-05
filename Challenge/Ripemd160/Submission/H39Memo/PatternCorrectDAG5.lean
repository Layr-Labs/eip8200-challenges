import Challenge.Ripemd160.Submission.H39Memo.PatternTraceResult
import Challenge.Ripemd160.Submission.H39Memo.PatternTraceBlock3109
import Challenge.Ripemd160.Submission.H39Memo.PatternCorrectDAG6
import Challenge.Ripemd160.Submission.H39Memo.PatternTraceBlock2508
import Challenge.Ripemd160.Submission.H39Memo.PatternTraceBlock2550
import Challenge.Ripemd160.Submission.H39Memo.PatternTraceBlock2592
import Challenge.Ripemd160.Submission.H39Memo.PatternTraceBlock2634
import Challenge.Ripemd160.Submission.H39Memo.PatternTraceBlock2676
import Challenge.Ripemd160.Submission.H39Memo.PatternTraceBlock2718

set_option warningAsError true

namespace Challenge.Ripemd160.Submission.H39Memo.PatternTrace
open EvmSemantics EvmSemantics.EVM

theorem dag2718 (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hfit : bytes.size < 2 ^ 64)
    (hrun : s.halt = .Running) (hcode : s.executionEnv.code = h39Bytecode)
    (ht : TerminalCorrect s bytes) (hp : Prefix bytes 22) :
    Outcome s bytes (stateAt s bytes 2718) := by
  rcases prefix_cases2718 s bytes hinput hrun hcode with ⟨hw, hnext⟩ | hfail
  · exact Outcome.prepend hnext hrun
      (dag2760 s bytes hinput hfit hrun hcode ht (prefix_next bytes 22 hp hw))
  · exact Or.inl (hfail.trans hrun (cleanup3109 s bytes hrun hcode))

theorem dag2676 (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hfit : bytes.size < 2 ^ 64)
    (hrun : s.halt = .Running) (hcode : s.executionEnv.code = h39Bytecode)
    (ht : TerminalCorrect s bytes) (hp : Prefix bytes 21) :
    Outcome s bytes (stateAt s bytes 2676) := by
  rcases prefix_cases2676 s bytes hinput hrun hcode with ⟨hw, hnext⟩ | hfail
  · exact Outcome.prepend hnext hrun
      (dag2718 s bytes hinput hfit hrun hcode ht (prefix_next bytes 21 hp hw))
  · exact Or.inl (hfail.trans hrun (cleanup3109 s bytes hrun hcode))

theorem dag2634 (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hfit : bytes.size < 2 ^ 64)
    (hrun : s.halt = .Running) (hcode : s.executionEnv.code = h39Bytecode)
    (ht : TerminalCorrect s bytes) (hp : Prefix bytes 20) :
    Outcome s bytes (stateAt s bytes 2634) := by
  rcases prefix_cases2634 s bytes hinput hrun hcode with ⟨hw, hnext⟩ | hfail
  · exact Outcome.prepend hnext hrun
      (dag2676 s bytes hinput hfit hrun hcode ht (prefix_next bytes 20 hp hw))
  · exact Or.inl (hfail.trans hrun (cleanup3109 s bytes hrun hcode))

theorem dag2592 (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hfit : bytes.size < 2 ^ 64)
    (hrun : s.halt = .Running) (hcode : s.executionEnv.code = h39Bytecode)
    (ht : TerminalCorrect s bytes) (hp : Prefix bytes 19) :
    Outcome s bytes (stateAt s bytes 2592) := by
  rcases prefix_cases2592 s bytes hinput hrun hcode with ⟨hw, hnext⟩ | hfail
  · exact Outcome.prepend hnext hrun
      (dag2634 s bytes hinput hfit hrun hcode ht (prefix_next bytes 19 hp hw))
  · exact Or.inl (hfail.trans hrun (cleanup3109 s bytes hrun hcode))

theorem dag2550 (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hfit : bytes.size < 2 ^ 64)
    (hrun : s.halt = .Running) (hcode : s.executionEnv.code = h39Bytecode)
    (ht : TerminalCorrect s bytes) (hp : Prefix bytes 18) :
    Outcome s bytes (stateAt s bytes 2550) := by
  rcases prefix_cases2550 s bytes hinput hrun hcode with ⟨hw, hnext⟩ | hfail
  · exact Outcome.prepend hnext hrun
      (dag2592 s bytes hinput hfit hrun hcode ht (prefix_next bytes 18 hp hw))
  · exact Or.inl (hfail.trans hrun (cleanup3109 s bytes hrun hcode))

theorem dag2508 (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hfit : bytes.size < 2 ^ 64)
    (hrun : s.halt = .Running) (hcode : s.executionEnv.code = h39Bytecode)
    (ht : TerminalCorrect s bytes) (hp : Prefix bytes 17) :
    Outcome s bytes (stateAt s bytes 2508) := by
  rcases prefix_cases2508 s bytes hinput hrun hcode with ⟨hw, hnext⟩ | hfail
  · exact Outcome.prepend hnext hrun
      (dag2550 s bytes hinput hfit hrun hcode ht (prefix_next bytes 17 hp hw))
  · exact Or.inl (hfail.trans hrun (cleanup3109 s bytes hrun hcode))

end Challenge.Ripemd160.Submission.H39Memo.PatternTrace

