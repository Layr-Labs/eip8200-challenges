# MODEXP candidate v10: CRT Montgomery squaring peephole schedule + Fermat dispatch optimization (-3,054 gas)

This candidate modifies the promoted MODEXP baseline `9b6eb630-5eaf-47cf-9e87-8edfc1dde265`
(commit `97cb39d3ddee7d4eccb468820300a41c4124c974`) and our earlier verified submission
`f992ebce-abaf-4912-acfe-1b8abc6da1ce`. All changes are confined to the permitted
`Challenge/Modexp/Submission` directory.

| Artifact identity | Value |
|---|---|
| Decoded bytecode SHA-256 | `f7bfe2f8dbd4f810b9f43ec5d91af31d1a714e904cd8770e19167bb4b7e1b8c6` |
| Bytecode size | 10,915 bytes |
| Decoded instructions | 8,722 |
| Protected native benchmark, seed zero | 409,127 gas; 44 correct vectors |

On identical seed-zero inputs, the promoted v9 baseline (`9b6eb630`) uses 412,181 gas,
the public e-man07 `f801e2ad` image uses 454,419 gas, and local v8 uses 453,287 gas.
This candidate (`v10`) uses **409,127 gas**, saving **3,054 gas** against promoted v9
(`9b6eb630`), **2,992 gas** against `f992ebce`, and **45,292 gas** (9.97%) against
`f801e2ad`.

## Changes

- **CRT Montgomery squaring kernel peephole schedule (`PC 5859..8507`, -2,992 gas)**:
  Eliminates 72 instructions (74 bytes) per 2048-bit CRT squaring iteration across four
  definitionally-preserving (`by rfl`) stack-scheduling rewrites in `CRTKernelExecution.lean`
  (`p1` double-accumulator addition in `col1..col15`, `p2` carry shift-add in `col0..col15`,
  `p3` Montgomery `MULMOD` accumulation in `col0..col8`, and `p4` initial `col0` square-and-`MULMOD`
  ordering), saving **176 gas per CRT squaring** (`-176` gas on `generated RSA-2048 #01 e=3` and
  `-2,816` gas on `generated RSA-2048 #02 e=65537`).
- **Fermat/inversion positive-branch dispatch (`PC 90..101`, -56 gas)** and **short-base calldata
  loader stack scheduling (`PC 112..136`, -6 gas)**: Saves 17 gas each on `eipExample1` and
  `eipExample2`, and 14 gas each on `bn254Fermat` and `bn254ModularInversion`.

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
adaptation, and validation. These development-tool credits do not replace
human authorship or license notices.

Kaankolcu and earlier upstream contributors supply the baseline and extensive
arithmetic and proof infrastructure. E-man07 supplies the inherited carry
rewrites and associated proofs. All twenty inherited public submission
entries remain in `dependencies.json`. The added twenty-first entry credits
Th0rgal's exponent-offset slot reuse from submission
`9fe4ea31-7bdd-4429-b988-bcd57cb83119`, source commit
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
