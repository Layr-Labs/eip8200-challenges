import Challenge.Ripemd160.Submission.Proofs.Bytecode.RetainedTerminalMul.CandidateBindings
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RetainedTerminalMul.CandidateInstructions
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RetainedTerminalMul.SemanticBridge

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace RetainedBridge111
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Ripemd160
open Challenge.Ripemd160.Submission.Proofs.Bytecode
open StackRoundTrace RetainedIntegration105

/-- This adapter executes the actual typed candidate slice.  It still requires
    a separate whole-image decode certificate and located-path lift. -/
theorem run_actual_data (s : State) (rho : List UInt256)
    (hs : rho.length ≤ 980) (hrun : s.halt = .Running)
    (ha : s.activeWords = UInt256.ofNat 0) :
    runInstrSeq ((Candidate.instructions.drop 5050).take 161)
      {s with pc := UInt256.ofNat 8157, stack := MachineState.readWord s.executionEnv.calldata 0 :: rho} =
      some {(stored s ExactBindings.digest) with
        pc := pcAfter (UInt256.ofNat 8157) (literalTemplate ExactBindings.digest), stack := retainedResult s.executionEnv.calldata :: rho} := by
  rw [Candidate.actual_data_slice, Candidate.literal_eq_template]
  exact run_literal s ExactBindings.digest rho hs hrun ha

/-- Content equality and the spec value are now available at the exact slice
    exit, not merely an unrelated raw full-word model. -/
theorem run_actual_data_known (s : State) (rho : List UInt256)
    (hs : rho.length ≤ 980) (hrun : s.halt = .Running)
    (ha : s.activeWords = UInt256.ofNat 0)
    (hn : s.executionEnv.calldata.size = 1000)
    (hz : retainedResult s.executionEnv.calldata = 0) :
    runInstrSeq ((Candidate.instructions.drop 5050).take 161)
      {s with pc := UInt256.ofNat 8157, stack := MachineState.readWord s.executionEnv.calldata 0 :: rho} =
      some {(stored s ExactBindings.digest) with
        pc := pcAfter (UInt256.ofNat 8157) (literalTemplate ExactBindings.digest), stack := UInt256.ofNat 0 :: rho} ∧
    spec s.executionEnv.calldata = PatternedDigest.paddedDigest := by
  constructor
  · simpa only [hz, show (0 : UInt256) = UInt256.ofNat 0 by decide] using run_actual_data s rho hs hrun ha
  · exact retained_zero_spec s.executionEnv.calldata hn hz

#print axioms run_actual_data
#print axioms run_actual_data_known
end RetainedBridge111
