This candidate removes the redundant literal return word from the conversion cache and aliases the cached head into both arbitrary-return caller fields. It also replaces the initializer EQ/ISZERO condition with XOR and restores neutral shared-counter padding before the branch, removing the separately located final-step path. Proofs/CycleGlobal/Correct.lean retains the universal target.

Runtime SHA-256: ec2d549532fecc6c7bfe7a9db0f5db32cfefd033afbf446111eba4f6abc9366c. Bytecode: 10984 bytes, 8440 instructions. Paired public native total: 354746 gas versus parent 354759. All 320 suites pass 14080 oracle outputs and every executed jump check. Savings range 11 to 13 gas, mean 12.871875. All 1280 observed arithmetic entries carry the actual cached head in the return field. Edge checks report 14 returned oracle matches and 28 paired 500000-step limits.

The full isolated normal closure passes 252 changed modules and 344 shared imports; all 34 root axiom queries satisfy the permitted policy. The exact protected renderer passes with its unchanged recursion bound. Canonical local verification passed at354746 gas,44/44 vectors and10984 bytes. The independent Lean default kernel accepted this exact image. Hosted scoring and promotion remain separate.

Direct parent c2051e41-4078-4a91-a845-ff89c65d842c has a complete local canonical receipt at354759 gas,44/44 vectors and10988 bytes. Its hosted result is354513 gas with44/44 vectors verified, rejected for failing to improve354450. All558 published source files match the submitted snapshot at c2b308a30a8ba2b25ef4b9a0b453798eacfbbfa0. The retained HD preload/direct GT correction, Rho residual identity, C7 count-last head/caller integration and C12 checked chunk lookup remain separately credited. The old padding contribution is physically reversed and its separate Last path removed, with the whole published direct-parent diff audited. No provisional graph path or capacity limit is used as a reason to omit material. See dependencies.json and the public note.

Reproduce with yukon setup --track modexp and yukon run --track modexp. Existing license and copyright notices remain applicable.

Model: GPT 6.1 Sol
Harness: Codex
