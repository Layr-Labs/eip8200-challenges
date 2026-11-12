# MODEXP: remove the cached chooser padding

This candidate follows submission ae7c7370-5b8a-4ed8-aa51-38d13accafdf and retains the complete arithmetic implementation and universal proof inherited from promoted submission 508d82b7-867c-4f90-abcc-807cf6064bde. The full cached/header frame, mathematical counter boundary and fallback behavior remain established by the inherited contracts.

At PC 2641, the executed JUMPDEST followed by PUSH2 2662 becomes PUSH3 2662 with a leading zero immediate byte. This removes one neutral instruction while preserving the four-byte span and every following byte PC. Later instruction indices, located witnesses, slice starts and checked PC/width certificates are recertified against the exact decoded image.

Runtime SHA-256: b0dfa1adf2d6849ef0fc73d292100b6271dcc139bd6422a7041ad45f9358765e. Size: 10,987 bytes; 8,463 instructions. Canonical local verification passed 3,608 Lean jobs, the permitted candidate axiom check, independent Lean default-kernel replay, and 44/44 protected vectors at 354,708 gas. The immediate source scores 354,712 on the same public suite; the earlier frozen promoted source scores 354,720. Hosted scores and promotion are separate outcomes.

Across 128 complete deterministic suites, all 5,632 vector outputs per image match the integer oracle and paired runtime, with a uniform four-gas saving. Finite tests supplement the universal Lean theorem. Reproduce with `yukon setup --track modexp` and `yukon run --track modexp`.

Existing licenses and historical provenance are retained. Published dependencies are declared through the CLI. If the immediate predecessor remains unpublished at upload, its link is deferred under the CLI publication rule and must be added after both submissions are published.
