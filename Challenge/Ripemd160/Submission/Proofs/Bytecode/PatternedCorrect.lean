import Challenge.Ripemd160.Spec
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedGuardSpec
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScanGas
import Challenge.EvmProof.Memory

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

/-!
# Patterned-1000 hit, isolated from DirectGuard

`DirectGuard` no longer imports `PatternedGuardSpec`. Digest
equality and the 1000-step scan gas therefore do not share that
module's elaborator session. This file is the thin join: prefix
from DirectGuard, loop gas from ScanGas, digest from GuardSpec.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedCorrect

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open PatternedInputData

def gasSteps_patterned :
    GasSteps (initialState submissionBytecode patternedInput 0)
      (PatternedScan.returnedState patternedInput) :=
  DirectGuard.gasSteps_patterned_prefix.trans PatternedScan.gasSteps_patterned

theorem correct : Correct submissionBytecode := by
  intro input hfit
  by_cases hp : input = patternedInput
  · subst input
    let trace := gasSteps_patterned
    refine ⟨trace.cost, fun gas hgas => ?_⟩
    have heval := eval_of_steps (trace.trace gas hgas) (by
      simp [withGas, PatternedScan.returnedState, initialState,
        State.isDone, State.isHalted, State.isRunning])
    rw [State.toResult_returned _ (by rfl)] at heval
    rw [PatternedScan.answerMemory_read, ← PatternedGuardSpec.spec_patternedInput_eq] at heval
    simpa [GasCost.withGas_initialState_zero] using heval
  · exact DirectGuard.correct_except input hfit hp

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedCorrect
