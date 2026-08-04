import Challenge.Modexp.Reference.Proofs.Bytecode.ReferenceCorrect

/-!
# Correctness and gas proof for the bundled MODEXP reference

The complete direct-bytecode proof for the frozen 1,284-byte artifact.  It
proves the emitted EVM instructions against the minimal MODEXP specification
and derives the exact gas used on every valid public branch.
-/
