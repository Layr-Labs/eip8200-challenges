import Challenge.Ripemd160.Submission.H39Memo.PatternTraceResult
import Challenge.Ripemd160.Submission.H39Memo.PatternTerminalSites

set_option warningAsError true

namespace Challenge.Ripemd160.Submission.H39Memo.PatternTrace
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof DispatchState

theorem terminals_correct (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = h39Bytecode) : TerminalCorrect s bytes := by
  intro p hsize hp
  by_cases htail : (PatternFacts.target p).size % 32 ≠ 0 →
      MachineState.readWord bytes (PatternTerminalSites.tailOffset p) = PatternFacts.tailWord p
  · have heq : bytes = PatternFacts.target p :=
      PatternFacts.eq_of_prefix_tail bytes p
        (hsize.trans (PatternFacts.target_size p).symm)
        (by simpa only [Prefix, PatternFacts.target_size] using hp) htail
    have hr := PatternTerminalSites.run_match p
      (stateAt s bytes (terminalPC p)) (UInt256.ofNat bytes.size) rfl rfl hrun hcode
      (by simpa only [stateAt, atPC, hinput] using htail)
    refine Or.inr ⟨p, heq, PatternTerminalSites.path p, ?_⟩
    simpa only [stateAt, atPC, outputEntry] using hr
  · rcases _root_.Classical.not_imp.mp htail with ⟨hpartial, hword⟩
    have hr := PatternTerminalSites.run_mismatch p
      (stateAt s bytes (terminalPC p)) (UInt256.ofNat bytes.size) rfl rfl hrun hcode
      hpartial (by simpa only [stateAt, atPC, hinput] using hword)
    refine Or.inl ⟨PatternTerminalSites.path p, ?_⟩
    simpa only [stateAt, atPC, fallback] using hr

end Challenge.Ripemd160.Submission.H39Memo.PatternTrace
