import Challenge.Sha256.Reference.Proofs.Bytecode.ReferenceCorrect
import Challenge.Sha256.Reference.Proofs.Gas

/-!
# Correctness proof for the bundled reference

The complete direct-bytecode proof. It proves the frozen bytes directly in the
EVM semantics and does not require a second correctness proof for the Yul source.
This layer is implementation-specific and is not part of the challenge specification.
-/
