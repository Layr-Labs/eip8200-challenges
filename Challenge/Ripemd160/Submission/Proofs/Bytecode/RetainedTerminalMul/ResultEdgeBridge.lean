import Challenge.Ripemd160.Submission.Proofs.Bytecode.RetainedTerminalMul.ExecutionBridge
import Challenge.EvmProof.Memory

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

/-! Focused actual typed-slice result edges, not a whole-image certificate. -/
namespace RetainedResultEdge112
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Challenge.Ripemd160
open Challenge.Ripemd160.Submission.Proofs.Bytecode
open StackRoundTrace RetainedIntegration105
open DenseScheduleTrace (runInstrSeq_append_running)

namespace Candidate
open RetainedBridge111.Candidate

theorem after_data : instructions.drop 5201 = suffixInstructions := by
  have hc : (prefixInstructions ++ literalInstructions).length = 5201 := by
    simp only [List.length_append, prefix_count, literal_count]
  rw [instructions, ← hc, List.drop_left]

theorem actual_result_slice :
    (instructions.drop 5201).take 2 = DirectLiteralRawV4.resultTemplate := by
  rw [after_data]
  rfl

theorem actual_result_bytes :
    assembleBytes ((instructions.drop 5201).take 2) = [0x61, 0x12, 0xb1, 0x57] := by
  rw [actual_result_slice]
  exact ExactBindings.result_binding

end Candidate

theorem data_end_pc :
    pcAfter (UInt256.ofNat 8157) (literalTemplate ExactBindings.digest) =
      UInt256.ofNat 9416 := by decide

theorem result_end_pc :
    pcAfter (UInt256.ofNat 9416) DirectLiteralRawV4.resultTemplate =
      UInt256.ofNat 9420 := by decide

/-- Two adjacent actual vector slices, composed without a whole-image decode claim. -/
def dataAndResult : List Instr :=
  ((RetainedBridge111.Candidate.instructions.drop 5040).take 161) ++
  ((RetainedBridge111.Candidate.instructions.drop 5201).take 2)

def resultState (s : State) (rho : List UInt256) : State :=
  {(stored s ExactBindings.digest) with
    pc := if (retainedResult s.executionEnv.calldata).toNat = 0
          then UInt256.ofNat 9420 else UInt256.ofNat 4785
    stack := rho}

/-- The retained word is consumed on BOTH result edges; memory is the digest store. -/
theorem run_actual_data_and_result (s : State) (rho : List UInt256)
    (hs : rho.length ≤ 980) (hrun : s.halt = .Running)
    (ha : s.activeWords = UInt256.ofNat 0)
    (hv : Decode.isValidJumpDest s.executionEnv.code 4785 = true) :
    runInstrSeq dataAndResult
      {s with pc := UInt256.ofNat 8157, stack := MachineState.readWord s.executionEnv.calldata 0 :: rho} =
      some (resultState s rho) := by
  have hd := RetainedBridge111.run_actual_data s rho hs hrun ha
  rw [data_end_pc] at hd
  apply runInstrSeq_append_running hd
  · exact hrun
  · rw [Candidate.actual_result_slice]
    simpa only [stored, result_end_pc, resultState] using
      DirectLiteralRawV4.run_result (stored s ExactBindings.digest)
        (UInt256.ofNat 9416) (retainedResult s.executionEnv.calldata) rho
        (by omega) hrun hv

theorem run_actual_zero (s : State) (rho : List UInt256)
    (hs : rho.length ≤ 980) (hrun : s.halt = .Running)
    (ha : s.activeWords = UInt256.ofNat 0)
    (hv : Decode.isValidJumpDest s.executionEnv.code 4785 = true)
    (hz : retainedResult s.executionEnv.calldata = 0) :
    runInstrSeq dataAndResult
      {s with pc := UInt256.ofNat 8157, stack := MachineState.readWord s.executionEnv.calldata 0 :: rho} =
      some {(stored s ExactBindings.digest) with pc := UInt256.ofNat 9420, stack := rho} := by
  simpa only [resultState, hz, show (0 : UInt256).toNat = 0 by decide, if_true] using
    run_actual_data_and_result s rho hs hrun ha hv

theorem run_actual_nonzero (s : State) (rho : List UInt256)
    (hs : rho.length ≤ 980) (hrun : s.halt = .Running)
    (ha : s.activeWords = UInt256.ofNat 0)
    (hv : Decode.isValidJumpDest s.executionEnv.code 4785 = true)
    (hz : (retainedResult s.executionEnv.calldata).toNat ≠ 0) :
    runInstrSeq dataAndResult
      {s with pc := UInt256.ofNat 8157, stack := MachineState.readWord s.executionEnv.calldata 0 :: rho} =
      some {(stored s ExactBindings.digest) with pc := UInt256.ofNat 4785, stack := rho} := by
  simpa only [resultState, if_neg hz] using
    run_actual_data_and_result s rho hs hrun ha hv

#print axioms Candidate.actual_result_slice
#print axioms Candidate.actual_result_bytes
#print axioms run_actual_data_and_result
#print axioms run_actual_zero
#print axioms run_actual_nonzero
end RetainedResultEdge112
