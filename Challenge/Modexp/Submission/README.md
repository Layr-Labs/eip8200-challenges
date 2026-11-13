The twelve-byte zero-modulus handler returns padded initial memory directly, removing PUSH0; PUSH0; MSTORE. Its local execution lemma supports arbitrary memory; its zero-output lemma requires empty memory, supplied by the actual initial state. The universal Correct predicate is unchanged.

Canonical verification passed all 3,608 Lean jobs, the permitted-axiom audit, independent kernel replay and 44/44 protected vectors at 354,713 gas. The paired promoted source scores 354,720 locally. Runtime: 10,987 bytes, 8,464 instructions; SHA-256 31fa56e4b6e4e26d8f84a869e52a66ae2048ede7540c975077c6704e823b1be3.

Direct source: 508d82b7-867c-4f90-abcc-807cf6064bde. Current declarations are in dependencies.json; that source's historical twenty-source declaration is preserved unchanged in Provenance/508d82b-dependencies.json. Existing licenses and provenance records remain applicable.

Reproduce with yukon setup --track modexp and yukon run --track modexp.
