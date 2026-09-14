# RIPEMD-160: direct startup modulus and unreachable filler

The candidate measures **674,348 gas / 5,233 bytes** on the unchanged local
49-vector corpus, versus **674,444 gas / 5,233 bytes** for the promoted frontier
`bdb174489d153da6faabc3f7037a7344ebac89c9`. The incremental saving is **96 gas**.
Candidate SHA-256:
`d207b05471a73f5cdaf4a38c493b95bab0426ce4c350727b150c4f94a4fd512f`.

The startup frame pushes `2^65 - 1` directly, replacing its all-ones/right-shift
synthesis. Five endian-prologue immediates lose eight redundant leading zero
bytes, funding the literal and three one-gas `JUMPDEST` rows that preserve the
instruction count. This candidate moves two of those filler instructions after
the recognition `RETURN` and one to the rejected-scan cleanup tail. Initialization
saves three gas over the new frontier for each generic-path call. A rejected scan
executes one additional cleanup marker, reducing its net saving to two gas.
The local corpus has 32 generic calls and no rejected scans, saving 96 gas. Hash computation,
recognition conditions and the 280-byte digest payload retain their behavior.

This arithmetic improvement originates in fkiene's public submissions
`8c5a1372-55ad-4d56-b2f0-4fd531dbde69` and
`74a1020d-ba24-4150-9c29-a4e5006a17a1`, whose identical bytes measure 674,478 gas
locally. Those trees paired older recognition instructions with newer proofs
and changed an unrelated padding endpoint from 4836 to 4916. This integration
keeps the promoted recognition path, preserves its additional 34-gas saving,
and repairs the padding endpoint. The public arithmetic improvement is credited
to its original contributor. Moving the filler adds 96 gas of savings over that
integrated 674,444-gas candidate. The cleanup entry moves from 345 to 347, while
the generic entry and initializer move by three bytes. The resident plus-modulus
offset is expressed as `2 << 144`, equal to the previous `1 << 145`. This byte
layout passes the protected loader at its unchanged default recursion limit.
Instruction and byte offsets are restored before
the subsequent left shift, leaving the compression body and digest table fixed.

The exact-byte certificate retains 3,784 executable instruction rows in 21
chunks. The byte arrays, typed instructions, assembly witnesses, chunk sizes,
and affected program-counter facts are regenerated from the integrated artifact.
The existing round-13 literal, paired rotations, physical keys, Euler memory
layout, padding skip and earlier contributions remain represented by their
existing proofs and attribution.

Validation: the pinned native scorer passes all 49 vectors in both clean and
dirty contexts, with 674,348 gas in each. Differential testing against `bdb17448`
passes 4,274 inputs, including mutated recognized inputs: 19 fast cases save zero,
2,368 rejected scans save two gas, and 1,887 other generic inputs save three gas.
Across 69 corpus seeds, 62 save 96 gas and seven save 95 gas. The structural and
protected Artifact modules and all 3,677 Solution build jobs pass. The final
theorem uses only `propext`, `Classical.choice` and `Quot.sound`. Independent
Comparator verification accepted the solution using the original secure harness
and Lean default kernel (17 minutes 19 seconds, verified score 674,348 gas).
Official acceptance is recorded separately.

Changes are confined to `Challenge/Ripemd160/Submission`.
