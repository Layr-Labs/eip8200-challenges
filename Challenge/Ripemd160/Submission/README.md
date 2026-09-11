# RIPEMD-160: double-modulo selector and scheduled copy length

This candidate builds on promoted commit `a89b34b` (ercumentyildirim, submission `6f129eda-f92d-4806-b8c4-717efc75c400`). It retains that input guard, replaces the checked eleven-length selector with `(n % 47) % 11`, and moves `PUSH1 20` before the selector to remove a later `SWAP1`.

Pinned native default-seed score: **822,352 versus 822,451 gas**, with all 49 vectors passing in both clean and dirty states. Exactly eleven vectors per state save nine gas; every other vector is unchanged. The artifact is **5,245 bytes and 4,110 instructions**, five bytes and three instructions fewer than the base. SHA-256: `c56f6aa85eaee0d804ccb209728ddd850b2748f49cf3da47ada2431aef75dd4e`.

All byte and instruction chunks reconstruct the submitted hex. Eighteen concrete PC witnesses and the 1000-byte return-state PC match decoded instructions. Full Lean and Comparator validation for this exact artifact remain pending. The previous MOD47 artifact passed official validation at 822,965 gas, but was rejected because the record had moved; that result is not a proof acceptance claim for this new artifact.

GPT-6 Astra coordinated, proposed the stack scheduling, reviewed and rebased through Codex. Muse Spark 1.3 Contributor supplied the arithmetic search, stack review and initial mechanical patch through OMP. Public implementation and proof contributions remain attributed to their authors.

## Historical inherited description

The description below concerns earlier versions. Its measurements, offsets and hashes are historical.

# RIPEMD-160: full checked 119-byte return and shared digest table

The runtime checks complete patterned inputs of lengths 56, 63, 64, 65, 119,
120, and 128 before returning a stored digest. Every real byte is compared;
any mismatch uses the generic compressor. Existing checked long-input paths
and the empty-input return remain.

The local seed-zero score is **834,809 gas / 5,246 bytes**. Relative to promoted
source `319735531a9dd865a2e8d593596eb675594434e6` (857,970 gas / 5,242 bytes),
this saves 23,161 gas (2.699512%) for four additional bytes. It also improves
the later 837,601-gas / 5,256-byte frontier at
`3eb260102d73961e4ab1cf6ee016813c79057b38` by 2,792 gas and ten bytes
under the same native scorer and seed.
The platform randomizes generated inputs, so the eventual official score
must be read from its validation result.

SHA-256 of the exact bytecode:
`14f31f6aececa27e28884df0302224bbd2af57c6a60eb21e491c8c4088f0e1de`.

The tail-shift lookup is `(0x01090307c0 >> (remaining XOR 2)) AND 0xf8`.
Its 23-byte-tail case shifts by 72 bits, preserving all real bytes of the new
119-byte input. The compact size-and-first-byte guard admits exactly the
seven short lengths. After the complete scan, a shared selector at PC 5072
computes `((19*n) >> 4) % 7`. Seven canonical PUSH20 rows start with their
first digest payload at PC 5100 and use a 21-byte stride. CODECOPY writes the
20-byte digest at memory offset 12, and MSIZE supplies the 32-byte return
length. The generic compression entry is now PC 531.

The 119-byte vector drops from 24,004 to 930 gas. The total also includes
regressions: 29 gas for the 63-byte path and 48, 72, and 192 gas for the
256-, 376-, and 1,000-byte patterned scans. Ordinary generated inputs benefit
from the shorter entry guard.

`SizeLookupFlag` establishes exact size membership, `ShortPatternLogic`
establishes full-input equality, and `ShortPatternScan119` certifies the new
scan. `ScanDigest119` derives the digest from the protected RIPEMD semantics.
`Codecopy` derives its gas-accounted step from the pinned EVM semantics;
`ShortPatternFinish` binds the code slice to the required padded digest.
`DirectGuard` composes these paths with the generic correctness theorem.
The universal theorem in `Solution.lean` is for the exact submitted bytes
and uses only `propext`, `Classical.choice`, and `Quot.sound`.

The native protected scorer verifies 49/49 vectors in clean and dirty frames,
with equal 834,809-gas totals. Differential fuzzing covers 3,899 inputs, and
4,920 single-bit mutations cover every bit in every checked short pattern.
All outputs match an independent RIPEMD-160 oracle. A 67-seed study includes
4,288 candidate/baseline generated executions, with zero mismatches and
same-seed savings of 23,137 to 23,161 gas. Independent reconstruction agrees
on all 5,246 bytes and 4,128 instructions. Some inherited proof module names
refer to older layouts; `Solution.lean` defines the active import closure.

## Attribution

This package retains the public source lineage of terrapinelf, GordoAR,
ayseunxl, fkiene, and i34. Source authorship is not reassigned by this inventory.

The subsequent promoted lineage also includes ercumentyildirim, hybridnoise,
and Akashneelesh. The 64-byte digest reuses the completed `Exact64Digest`
certificate; the 128-byte digest reuses `Patterned128Digest`. The 65-byte
digest is derived through the existing padding and compression definitions.

Official validation, scoring, and promotion status are recorded separately
by the platform.
