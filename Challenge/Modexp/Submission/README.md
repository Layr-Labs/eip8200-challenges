# MODEXP candidate v13: CRT residual carry shift folding (`SHR 5; SHL 12` -> `SHL 7`) (-9,648 gas vs v9 / -1,632 gas vs v12)

This candidate modifies our promoted #1 MODEXP baseline `61279eda-6134-4f54-91d2-31a633b7c013`
(commit `f5b5937a4b6c9818f7fa59971177eef878aa1e95`, 404,165 seed-0 gas, 407,817 official gas),
our prior promoted baselines `318954e0-41df-4035-acd9-1e271d23edd3` (406,022 seed-0 gas,
408,434 official gas) and `e506ac91-39f1-41fe-a002-90b33fd36e18` (409,127 seed-0 gas,
412,399 official gas), and upstream promoted baseline `9b6eb630-5eaf-47cf-9e87-8edfc1dde265`
(commit `97cb39d3ddee7d4eccb468820300a41c4124c974`, 412,181 seed-0 gas, 415,686 official gas).
All changes are confined to the permitted `Challenge/Modexp/Submission` directory.

| Artifact identity | Value |
|---|---|
| Decoded bytecode SHA-256 | `8d392b3bc03738bde9d172798b3280c49adcb9ac8024423128e039dd1355f3ad` |
| Bytecode size | 10,915 bytes |
| Decoded instructions | 8,722 |
| Protected native benchmark, seed zero | 402,533 gas; 44 correct vectors |

On identical seed-zero inputs, the promoted v9 baseline (`9b6eb630`) uses 412,181 gas,
our promoted v10 baseline (`e506ac91`) uses 409,127 gas, our promoted v11 baseline
(`318954e0`) uses 406,022 gas, our promoted v12 baseline (`61279eda`) uses 404,165 gas,
the public e-man07 `f801e2ad` image uses 454,419 gas, and local v8 uses 453,287 gas.
This candidate (`v13`) uses **402,533 gas**, saving **1,632 gas** against promoted v12
(`61279eda`), **3,489 gas** against promoted v11 (`318954e0`), **6,594 gas** against
promoted v10 (`e506ac91`), **9,648 gas** against promoted v9 (`9b6eb630`), and
**51,886 gas** (11.42%) against `f801e2ad`.

## Changes

- **Cut 6A — CRT column residual carry shift folding (`SHR 5; SHL 12` -> `SHL 7`,
  `PC 5859..8800`, -1,632 gas)**:
  In each of the 16 columns `col0..col15` of the 8-word mixed-radix CRT Montgomery
  squaring loop (`CRTKernelExecution.lean`, `GenericColumn.lean`, `CRTExecution.lean`,
  `CRTWordBridge.lean`), the high carry above $2^{256}$ of a column sum $S$ is recovered
  from the Mersenne prime residue $H \equiv S \pmod P$ ($P = 2^{251} - 1$) and ordinary
  word $L = S \bmod 2^{256}$ via:
  $$r = (H + P - (L \bmod P)) \bmod P = (S / 2^{256}) \cdot (2^{256} \bmod P) = (S / 2^{256}) \cdot 32$$
  (`CRTColumn.residualHigh`). Because $r = (S / 2^{256}) \cdot 2^5$, its low 5 bits are
  identically zero on every valid column! Previously, `highProgram` computed
  `((r >>> 5) <<< 12) + (L >>> 244)` using two shift instructions (`PUSH1 5; SHR` followed
  by `PUSH1 12; SHL`). Folding `SHR 5` and `SHL 12` into a single left shift `PUSH1 7; SHL`
  (`12 - 5 = 7`) produces the exact same value `(S / 2^{256}) <<< 12` while eliminating
  2 instructions (3 bytes, 6 gas) in each of `col0..col15` (**32 instructions, 48 bytes,
  96 gas per CRT squaring**), saving **17 × 96 = 1,632 gas** across `generated RSA-2048 #01 e=3`
  (-96 gas) and `generated RSA-2048 #02 e=65537` (-1,536 gas). Combined with Cuts 3, 4A, and 5E,
  `kernelProgram` is reduced from 2,078 to 1,897 instructions (**-181 instructions, -199 bytes,
  -503 gas per CRT squaring**, or **-8,551 gas** across 17 squarings).
- **Retained from v12 (`61279eda`), v11 (`318954e0`), and v10 (`e506ac91`)**:
  - **Cut 5E — CRT Montgomery squaring column header (`E1`) & cancel-tail (`E2`) schedule
    (`PC 5859..8800`, -1,224 gas)**:
    Eliminates 24 instructions (24 bytes, 72 gas) per 2048-bit CRT squaring iteration across
    `col0..col15` (`E1`, -16 instructions) and `col1..col8` (`E2`, -8 instructions).
- **Cut 5D — Inlined 4-word Montgomery squaring (`R4Inline*`) schedule peepholes
  (`PC 8998..9800`, -476 gas)**:
  Eliminates 9 instructions (27 bytes, 28 gas) per 4-word squaring across 19 `R4Inline*`
  sub-blocks (`r0z1..r3h`), saving **28 gas × 17 squarings = 476 gas** across the
  128-byte benchmark vectors.
- **Cut 5A — 32-byte window precopy modulus count & nibble-62 exponent swap
  (`PC 923..2387`, -93 gas)**:
  Reduces the `DUP1` modulus precopy run in `precopy180Program` from 180 to 179 and
  consumes `exponent` in place via `SWAP1` at `nibble 62`, eliminating 1 instruction
  (3 gas) across all 31 single-word window vectors (`31 × 3 = 93 gas`).
- **Cut 5B — `TnM128` L1 cache `MSIZE` store & final `MULMOD` consumption
  (`PC 5502..5615`, -64 gas)**:
  Replaces `PUSH2 2272; MSTORE` with `MSIZE; MSTORE` (-1 gas) and `DUP2; MULMOD; SWAP1; POP`
  with `SWAP2; SWAP1; MULMOD` (-7 gas) in `TnCacheL1Suffix`, saving **8 gas × 8 vectors =
  64 gas** across the 128-byte `TnM128` vectors.
- **Retained from v11 (`318954e0`) and v10 (`e506ac91`)**:
  - **Cut 4 (`PC 5859..8998`, -3,105 gas)**: CRT Phase B-before-Phase A operand reordering
    (-2,703 gas), `retainProgram` descending address preloading (-360 gas), and
    `exitProgram` early stack cleanup & descending address preloading (-42 gas).
  - **Cut 3 (`PC 5859..8454`, -2,992 gas)**: Four stack-scheduling peephole rewrites (`p1..p4`)
    across `col0..col15` (-176 gas/squaring × 17 squarings).
  - **Cuts 1 & 2 (`PC 90..136`, -62 gas)**: Fermat/inversion positive-branch dispatch (-56 gas)
    and short-base calldata loader stack scheduling (-6 gas).

- The eight-word Montgomery square loop retains a mixed-radix representation
  between repeated squarings: eight 244-bit digits and a 96-bit top digit.
  Carry reconstruction uses ordinary-word and Mersenne-modulus residues.
  Retaining the digits and reduction parameters removes repeated conversion
  and setup work while preserving the existing Montgomery factor `2^2048`.
  Paired multiplication schedules keep shared operands live, and each column
  starts its accumulators from its first product.
- The four-word square routine rotates its accumulator positions across the
  complete four-row schedule and inlines the required continuation. This
  removes repeated stack rearrangement and return overhead.
- A guarded BN254 inverse-exponent path uses a fixed addition chain selected
  by complete EVM cost, including table placement, stack work, and dispatch.
  A weighted dynamic program improves the selected schedule. Inputs outside
  that complete guard continue through the existing general implementation.
- The exponent-offset word moves from memory address 2816 to 2656, reusing
  an available slot and reducing memory expansion. This reapplies Th0rgal's
  public optimization to the three accesses in the current architecture.

The searches enumerate documented finite families. They do not establish a
minimum gas cost among all EVM programs. The result improves aggregate gas;
some valid inputs cost more because of additional guards or different paths.
Execution cases reaching a shared test cap remain inconclusive.

## Verification and reproduction

The formal target is the unchanged `Challenge.Modexp.Correct` statement:
valid inputs, including unscored inputs, must eventually return the specified
result with sufficient gas. This is distinct from a finite replay and from
whether a particular input fits a practical gas or execution cap.

**Complete acceptance is established by the separate exact-source verification
receipt, not by this README.** That receipt must bind the bytecode hash above
and its full source inventory, successful canonical commands, independent
Comparator and Lean-kernel acceptance, permitted axioms, and protected scoring.
Consult the companion package's status and receipt for the verification
outcome. Component proof certificates and native measurements alone do not
establish complete candidate acceptance.

Use the pinned upstream checkout and its documented entry points:

```sh
./setup.sh modexp
./benchmark.sh modexp
```

The companion research package supplies exact reconstruction, toolchain pins,
source hashes, and verification commands. Its documented
`BENCHMARK_INSECURE_LOCAL=1` mode omits ranked-run process isolation while
retaining mathematical verification and protected scoring. Local results are
unranked; these instructions do not publish or submit the candidate.

## Attribution and license

Claude found the original optimization in aerugo-ef's repository. Codex built
the later v6/v7/v8 work on that foundation and performed this historical
review, search, CRT representation work, schedule integration, proof
adaptation, and validation. Gemini 3.1 Pro (Antigravity) designed, implemented,
and formally verified the v10, v11, and v12 stack-scheduling, operand-reordering,
address-preloading, and fast-path peephole cuts (Cuts 1–5). These development-tool
credits do not replace human authorship or license notices.

Kaankolcu and earlier upstream contributors supply the baseline and extensive
arithmetic and proof infrastructure. E-man07 supplies the inherited carry
rewrites and associated proofs. All twenty public submission entries are
declared in `dependencies.json`, including Th0rgal's exponent-offset slot reuse
from submission `9fe4ea31-7bdd-4429-b988-bcd57cb83119`, source commit
`f298e824cf3a1445ab733f723626920b63a18ea3`. Its adaptation to this newer
representation is local integration; the slot-reuse idea is Th0rgal's work.

The fixed-exponent search used Michael McLoughlin's BSD-3-Clause
`mmcloughlin/addchain` ensemble at commit
`6c4dbba3acc1bf0269d4a90bb9cdfdf865017601`. It produced the initial candidate
and informed the table/stack schedule. A separate local weighted dynamic
program generated the final operation graph, emitted by the local EVM
compiler. The companion package preserves the tool's provenance and separate
BSD notice; it does not describe the final graph as direct ensemble output.

Original local code and documentation use Apache-2.0 except where otherwise
noted. Preserve the upstream and third-party license and attribution notices.
The companion package includes the Apache-2.0 text and full provenance;
redistributed addchain tool/source material retains its BSD-3-Clause notice.
Reused work is not claimed as a new local discovery.
