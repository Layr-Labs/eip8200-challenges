# MODEXP: consume the cached shift directly

This candidate builds directly on promoted submission 508d82b7-867c-4f90-abcc-807cf6064bde (source bfa4840ca8db4910ddd64ecc6cd60e20553373c5). Its arithmetic, complete cached/header frames, mathematical count boundary and fallback behavior are inherited.

The cached estimator chooser consumes the shift word directly. Zero falls through into the relocated zero-shift tail; nonzero jumps to the relocated normal tail. The two tails fit the original interval, preserving every following address and the total bytecode/instruction counts. The complete universal correctness composition is checked against the exact new bytes.

Runtime SHA-256: 178aed65c6aea8d274e602efc85e5e2cf6a8c2740f7ac96bb64441bcd8213ed0. Size: 10,987 bytes; 8,464 instructions. Canonical local verification passed 3,608 Lean jobs, independent default-kernel replay, permitted candidate axioms and 44/44 vectors at 354,712 gas. The paired frozen predecessor scores 354,720 locally. Hosted scores and promotion are separate outcomes.

Across 128 complete native suites (seeds 0 through 127), outputs match the integer oracle and paired runtime; savings range from eight to ten gas. Zero-shift choices save three gas and nonzero choices save one. A missed relocated PC fact was corrected before the successful complete check. Finite tests supplement the Lean theorem.

Reproduce with `yukon setup --track modexp` and `yukon run --track modexp`. Existing licenses and historical provenance files are retained. The new submission declares its direct promoted source through the CLI dependency file; retained historical metadata does not assert that pending ancestry has been verified.
