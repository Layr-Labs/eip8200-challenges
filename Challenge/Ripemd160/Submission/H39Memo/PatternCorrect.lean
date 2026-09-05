import Challenge.Ripemd160.Submission.H39Memo.PatternCorrectDAG0
import Challenge.Ripemd160.Submission.H39Memo.PatternCorrectTerminals
import Challenge.Ripemd160.Submission.H39Memo.PatternCorrectOutput

set_option warningAsError true

namespace Challenge.Ripemd160.Submission.H39Memo.PatternCorrect
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof DispatchState PatternTrace

theorem trace_cases (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hfit : bytes.size < 2 ^ 64)
    (hrun : s.halt = .Running) (hcode : s.executionEnv.code = h39Bytecode) :
    Outcome s bytes (stateAt s bytes 1696) := by
  apply dag1696 s bytes hinput hfit hrun hcode
    (terminals_correct s bytes hinput hrun hcode)
  intro k hk
  omega

theorem correct (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hfit : bytes.size < 2 ^ 64)
    (hrun : s.halt = .Running) (hcode : s.executionEnv.code = h39Bytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Nonempty (GasSteps (stateAt s bytes 1696) (fallback s)) ∨
      ∃ t : State, Nonempty (GasSteps (stateAt s bytes 1696) t) ∧
        t.halt = .Returned ∧ t.hReturn = spec bytes :=
  finish s bytes 1696 (trace_cases s bytes hinput hfit hrun hcode)
    hrun hcode hfork hnp

theorem correct_at (s : State) (bytes : ByteArray)
    (hpc : s.pc = UInt256.ofNat 1696) (hstack : s.stack = [UInt256.ofNat bytes.size])
    (hinput : s.executionEnv.calldata = bytes) (hfit : bytes.size < 2 ^ 64)
    (hrun : s.halt = .Running) (hcode : s.executionEnv.code = h39Bytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Nonempty (GasSteps s (atPC s 1006 [])) ∨
      ∃ t : State, Nonempty (GasSteps s t) ∧
        t.halt = .Returned ∧ t.hReturn = spec bytes := by
  have he : stateAt s bytes 1696 = s := by
    simp [stateAt, atPC, ← hpc, ← hstack]
  simpa only [he, fallback] using correct s bytes hinput hfit hrun hcode hfork hnp

end Challenge.Ripemd160.Submission.H39Memo.PatternCorrect
