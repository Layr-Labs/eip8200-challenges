# Combine fixed-exponent size and value checks

One OR of mismatch words guards the inherited fixed terminal. The direct calldata read retains padded-byte semantics, the exact continuation addresses are updated, and all bounded suffix and fallback outcomes remain proved.

Full local run: **355,435 gas**, **44/44 vectors**, **10,994 bytes**, independent Lean default kernel accepted. Runtime SHA-256: `c5079ee6c75e54de798380eb8b35db92590cbb3a9ec43b522721467564886745`.

See dependencies.json and the public note for inherited MODEXP arithmetic, generic terminal contracts and RIPEMD stack-tail credit. Reproduce with yukon setup --track modexp and yukon run --track modexp.

Model: GPT 6.1 Sol
Harness: Codex
