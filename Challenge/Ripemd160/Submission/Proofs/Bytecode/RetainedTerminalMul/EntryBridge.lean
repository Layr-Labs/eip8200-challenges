import Challenge.Ripemd160.Submission.Proofs.Bytecode.RetainedTerminalMul.SuccessBridge
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Low64RepeatMath

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace RetainedResultEdge112
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Challenge.Ripemd160
open Challenge.Ripemd160.Submission.Proofs.Bytecode
open StackRoundTrace RetainedIntegration105
open DenseScheduleTrace (runInstrSeq_append_running)

/-- Split a vector slice without reducing the large concrete prefix. -/
private theorem take_plus (xs : List Instr) (m n : Nat) :
    xs.take (m+n) = xs.take m ++ (xs.drop m).take n := by
  induction m generalizing xs with
  | zero => simp
  | succ m ih =>
    cases xs with
    | nil => simp
    | cons x xs => simpa [List.take_succ_cons, List.drop_succ_cons, Nat.succ_add] using congrArg (List.cons x) (ih xs)

/-- The three success chunks are exactly one contiguous candidate-vector slice. -/
theorem actual_data_success_slice :
    (RetainedBridge111.Candidate.instructions.drop 5077).take 166 =
      dataAndResult ++ ((RetainedBridge111.Candidate.instructions.drop 5240).take 3) := by
  rw [show 166 = 163 + 3 by decide, take_plus]
  rw [show 163 = 161 + 2 by decide, take_plus]
  simp only [List.drop_drop, dataAndResult]

/-- Actual entry anchor at PC21, including the retained word DUP. -/
theorem actual_anchor_slice :
    (RetainedBridge111.Candidate.instructions.drop 11).take 9 = anchorTemplate := by rfl

/-- Repeated-word seed reuses the retained word without another load. -/
theorem actual_repeat_seed_slice :
    (RetainedBridge111.Candidate.instructions.drop 20).take 6 = repeatTemplate := by rfl

def entrySuccessPath : List Instr :=
  ((RetainedBridge111.Candidate.instructions.drop 11).take 9) ++
  ((RetainedBridge111.Candidate.instructions.drop 5077).take 166)

/-- Dynamic path from the size1000 anchor all the way through actual RETURN.
    Exact typed-vector slices only: a located-instruction/GasSteps lift is still required. -/
theorem run_entry_success (s : State) (rho : List UInt256)
    (hs : rho.length ≤ 980) (hrun : s.halt = .Running)
    (ha : s.activeWords = UInt256.ofNat 0)
    (hvAnchor : Decode.isValidJumpDest s.executionEnv.code 8157 = true)
    (hvMiss : Decode.isValidJumpDest s.executionEnv.code 4785 = true)
    (hne : Low64RepeatMath.condition s.executionEnv.calldata ≠ 0)
    (hz : retainedResult s.executionEnv.calldata = 0) :
    runInstrSeq entrySuccessPath {s with pc := UInt256.ofNat 21, stack := rho} =
      some (returned (stored s ExactBindings.digest) rho) := by
  unfold entrySuccessPath
  rw [actual_anchor_slice, actual_data_success_slice]
  exact runInstrSeq_append_running (run_anchor_taken s rho hs hrun hne hvAnchor) hrun
    (run_actual_return s rho hs hrun ha hvMiss hz)

/-- On the repeated-word edge the actual seed leaves only its equality flag
    and the original reference word, followed by the untouched frame. -/
theorem run_entry_repeat (s : State) (rho : List UInt256)
    (hs : rho.length ≤ 980) (hrun : s.halt = .Running)
    (hvRepeat : Decode.isValidJumpDest s.executionEnv.code 9429 = true)
    (heq : KnownInputCompactState.referenceWord s.executionEnv.calldata = KnownInputData.fullWord) :
    runInstrSeq (((RetainedBridge111.Candidate.instructions.drop 11).take 9) ++
      ((RetainedBridge111.Candidate.instructions.drop 20).take 6))
      {s with pc := UInt256.ofNat 21, stack := rho} =
      some {s with pc := UInt256.ofNat 9429, stack :=
        [PcSeedRaw.seed s.executionEnv.calldata,
         KnownInputCompactState.referenceWord s.executionEnv.calldata] ++ rho} := by
  rw [actual_anchor_slice, actual_repeat_seed_slice]
  exact runInstrSeq_append_running (run_anchor_fall s rho hs hrun heq) hrun
    (run_repeat s rho hs hrun hvRepeat)

#print axioms actual_data_success_slice
#print axioms actual_anchor_slice
#print axioms actual_repeat_seed_slice
#print axioms run_entry_success
#print axioms run_entry_repeat
end RetainedResultEdge112
