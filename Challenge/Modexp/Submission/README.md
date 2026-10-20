# MODEXP candidate v11: CRT Montgomery squaring Phase B/A reordering + retain/exit address preloading (-6,159 gas)

This candidate modifies our promoted MODEXP baseline `e506ac91-39f1-41fe-a002-90b33fd36e18`
(409,127 seed-0 gas, 412,399 official gas) and upstream promoted baseline
`9b6eb630-5eaf-47cf-9e87-8edfc1dde265` (commit `97cb39d3ddee7d4eccb468820300a41c4124c974`,
412,181 seed-0 gas, 415,686 official gas). All changes are confined to the permitted
`Challenge/Modexp/Submission` directory.

| Artifact identity | Value |
|---|---|
| Decoded bytecode SHA-256 | `d48e64f9207a8efe5f33f2d2f67aa18cea44320c11e015208bebcb83fae80974` |
| Bytecode size | 10,915 bytes |
| Decoded instructions | 8,722 |
| Protected native benchmark, seed zero | 406,022 gas; 44 correct vectors |

On identical seed-zero inputs, the promoted v9 baseline (`9b6eb630`) uses 412,181 gas,
our promoted v10 baseline (`e506ac91`) uses 409,127 gas, the public e-man07 `f801e2ad`
image uses 454,419 gas, and local v8 uses 453,287 gas. This candidate (`v11`) uses
**406,022 gas**, saving **3,105 gas** against promoted v10 (`e506ac91`), **6,159 gas**
against promoted v9 (`9b6eb630`), and **48,397 gas** (10.65%) against `f801e2ad`.

## Changes

- **Cut 4A — CRT Montgomery squaring kernel Phase B-before-Phase A operand reordering +
  11-instruction `cancel` tail (`PC 5859..8454`, -2,703 gas)**:
  Eliminates 53 additional instructions (53 bytes, 159 gas) per 2048-bit CRT squaring
  iteration on top of Cut 3 (-72 instructions, -74 bytes, -176 gas/squaring), for a
  combined reduction of **125 instructions (127 bytes, 335 gas) per CRT squaring**
  (`17 × 335 = 5,695 gas` total across `generated RSA-2048 #01 e=3` and
  `generated RSA-2048 #02 e=65537`). Specifically:
  - In `col3..col13`, off-diagonal pair multiplication reorders Phase B (`MUL`, `ADD`, `MUL`)
    before Phase A (`MULMOD`, `ADD`, `MULMOD`), consuming shared operand copies directly
    and saving 2 instructions (6 gas) per column (`-22 instructions, -66 gas/squaring`).
  - In `col1..col15`, omitting the trailing `SWAP1` of `p1` leaves `acc_w` above `acc_m`
    entering the Montgomery phase; reordering Montgomery Phase B before Phase A saves
    2 instructions (6 gas) per column in `col9..col15` (`-14 instructions, -42 gas/squaring`)
    and, combined with an 11-instruction `cancel` tail, saves 2 instructions (6 gas) per
    column in `col1..col8` (`-16 instructions, -48 gas/squaring`).
  - In `col0`, applying the 11-instruction `cancel` tail saves 1 instruction (3 gas)
    (`-1 instruction, -3 gas/squaring`).
- **Cut 4B — `retainProgram` descending address preloading & `mask` reuse (`PC 8479..8648`, -360 gas)**:
  Preloads `1600`, copies `mask` once via `DUP12`, and preloads `1568..1344` in descending
  order at the start of `retainProgram`, replacing all 8 duplicate `PUSH2 addr; MLOAD`
  pairs with `DUP2`/`DUP3` and consuming the copied `mask` directly on the 8th `AND`.
  Shrinks `retainProgram` from 117 instructions (193 bytes) to 109 instructions (169 bytes),
  saving **24 gas per retain × 15 retains = 360 gas** on `generated RSA-2048 #02 e=65537`.
- **Cut 4C — `exitProgram` early stack cleanup & descending address preloading (`PC 8800..8976`, -42 gas)**:
  Moves the 12 `POP` instructions right after `JUMPDEST 8800` and preloads `1568..1344`
  in descending order, replacing 7 duplicate `PUSH2 addr; MLOAD` pairs with `DUP2`.
  Shrinks `exitProgram` from 121 instructions (197 bytes) to 114 instructions (176 bytes),
  saving **21 gas per exit × 2 exits = 42 gas** across `generated RSA-2048 #01 e=3` (-21 gas)
  and `generated RSA-2048 #02 e=65537` (-21 gas).
- **Retained from v10 (`e506ac91`)**:
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
and formally verified the v10 and v11 stack-scheduling, operand-reordering, and
address-preloading cuts (Cuts 1–4). These development-tool credits do not replace
human authorship or license notices.

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
