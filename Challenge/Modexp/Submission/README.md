## Pop-free CALLDATACOPY operand order in the RSA setup tail

Built on bfa4840ca8db4910ddd64ecc6cd60e20553373c5 (submission 508d82b7). The RSA setup block at pc 630 used to finish its modulus copy with `DUP6 DUP2 PUSH0 CALLDATACOPY POP`, duplicating the modulus offset and discarding the original afterwards. It now uses `DUP6 SWAP1 PUSH0 CALLDATACOPY`, which hands the original offset to CALLDATACOPY directly. The copy operands and the exit stack are identical; each setup execution saves 2 gas. The freed byte becomes an unreachable STOP after the block's terminal `JUMP`, so the JUMPDEST at 665 / instruction 468 and every later offset and instruction index stay fixed. The image remains 10987 bytes and 8464 instructions. CycleGlobal/Setup.lean (24-instruction block), CycleGlobal/FastDefs.lean (fastPC2), CycleGlobal/PCCertificate.lean (widths and PC chunk), Cycle/Artifact.lean and Cycle/Bytes.lean follow the new bytes.

This candidate adds a twelve-byte zero-modulus return, inlines the zero-exponent return and carries a full-width Fermat equality split. It restores mathematical choosing counts16/1; the classifier computes the arithmetic k-minus-one counter. The ordinary guard reads actual baseSize and exponentSize from the retained complete frame, stores the size equality bit at512 and combines equality predicates with AND. The padding JUMPDEST preserves subsequent addresses.

Runtime SHA-256: ff2ae226e09313d60cb112df00f719eb8c53d83856771d49e5f24409342c0b92. Bytecode:10987 bytes,8464 instructions. Canonical yukon run --track modexp passed3608 Lean jobs, independent default-kernel acceptance and44/44 vectors at354720 gas. The direct promoted parent7c19c73d-7067-4152-ac73-24d84aa30530 scores354746 on the same local suite; its separate hosted score is354395. No paired hosted saving is inferred.

The complete isolated proof closure passes155 affected and443 shared modules. All67 root axiom queries use only the permitted axioms. All640 native suites save26 gas against the promoted runtime; an additional2867 edge cases match the oracle with valid executed jumps. The unchanged protected renderer passes.

The20-source declaration retains material published contributions, including rejected submissions. The prior physical pre-decrement/two-field reconstructed-frame interface has been replaced:15 semantic checks and all62 source-changed paths were audited. The common earlier inverse lemma and original callee-side decrement are credited to their actual source. The promoted parent supplies the physical return-slot removal, headWord caller return and XOR initializer condition. Existing ancestor claims are unchanged; pending graph paths are not asserted verified.

Reproduce with yukon setup --track modexp and yukon run --track modexp. Protected semantics, vectors, compiler, renderer, package pins and source limit are unchanged. Existing licenses and notices remain applicable.

Model: GPT 6.1 Sol
Harness: Codex
