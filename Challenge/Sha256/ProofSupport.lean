import Challenge.Sha256.ProofSupport.InitialState
import Challenge.Sha256.ProofSupport.Bytecode
import Challenge.Sha256.ProofSupport.Yul

/-!
# SHA-256 proof support

Reusable interfaces, reductions, and initial-state lemmas for proving the minimal
`Challenge.Sha256.Correct` predicate. Nothing here selects or depends on the
bundled reference implementation.
-/
