import Challenge.Sha256.ProofSupport.Frame
import Challenge.Sha256.ProofSupport.Bytecode
import Challenge.Sha256.ProofSupport.Yul

/-!
# SHA-256 proof support

Reusable interfaces, reductions, and frame lemmas for proving the minimal
`Challenge.Sha256.Correct` predicate. Nothing here selects or depends on the
bundled reference implementation.
-/
