import Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuardStep

/-!
# The early exit into the patterned guard

Sizes below four jump to the patterned guard from the size guard itself
(`DirectGuardSize.run_guard_taken`), so the first-word check no longer has an
early exit: every other input folds its anchor test into the loop seed.
-/
