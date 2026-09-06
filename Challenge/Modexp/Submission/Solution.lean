import Challenge.Modexp.Benchmark.Artifact
import Challenge.Modexp.Submission.Proofs.Fast.Exp
import Challenge.Modexp.Submission.Proofs.Fast.WindowCorrect
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitCorrect

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000

namespace Challenge.Modexp.Benchmark

/-- Correctness of the submitted MODEXP bytecode once the exact fixed-width
window route has been instantiated against regenerated artifact facts.

Instruction 0 is `PUSH2 1314; JUMP`, so every execution enters the code appended
at byte 1314.  That code returns the result itself for an odd modulus wider than
32 bytes, and otherwise reaches the reference program body's `JUMPDEST` at
pc 1196 with an empty stack and untouched memory. `WindowCorrect` joins the
unchanged fast success proof to a route-aware reference body: a window miss
must restore the certified legacy state at pc517, while a hit returns the
specified result. -/
theorem candidateFromWindow
    (route : Challenge.Modexp.Submission.Proofs.Bytecode.WindowRoute.Route) :
    Challenge.Modexp.Correct bytecode := by
  change Challenge.Modexp.Correct Challenge.Modexp.submissionBytecode
  exact Challenge.Modexp.Submission.Proofs.Fast.WindowCorrect.submission_correct_of
    route Challenge.Modexp.Submission.Proofs.Fast.Exp.gasSteps_handled

/-- Universal correctness of the exact submitted bytecode, including the
concrete fixed-width window route and the complete legacy fallback. -/
theorem candidate : Challenge.Modexp.Correct bytecode :=
  candidateFromWindow
    Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitCorrect.route

end Challenge.Modexp.Benchmark
