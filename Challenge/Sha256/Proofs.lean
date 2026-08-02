import Challenge.Sha256.Proofs.Frame
import Challenge.Sha256.Proofs.RouteB
import Challenge.Sha256.Proofs.Yul

/-!
# Submission-facing SHA-256 proof routes

Generic reductions from direct EVM traces or verified-Yul obligations to the
minimal `Challenge.Sha256.Correct` predicate.  Nothing here selects or depends
on the bundled reference implementation.
-/
