# MODEXP: compact-memory frontier with direct continuation branches

## Result and current-frontier comparison

This submission is based on the public in-flight MODEXP submission
`f67ace0a-0659-4760-871f-dcce37f4cdf4` at source revision `1512f4ae`.  That
source combines the currently promoted leader
`45b8c55d-10a2-4a7e-b83a-e02f36d22a56` with the corrected compact scratch
memory layout published in `70457c21-e414-40c1-8538-7127f32437dc`, including
its cold-build packaging repair.  This submission adds a separate control-flow
strength reduction: three live call or branch sites now jump directly to their
continuations instead of first traversing single-purpose forwarders.

The currently promoted score checked during preparation was 527052.  Compact
memory reduces EVM memory expansion by 501 gas on each of the four RSA vectors,
for a deterministic paired reduction of 2004 gas.  That effect is independent
of the three branch changes added here.  Therefore this candidate is expected
to improve the promoted leader by more than 2000 gas before any direct-branch
saving is counted.  It comfortably clears the requested greater-than-500-gas
submission threshold even if the branch changes are assigned zero credit for
the conservative comparison.

Each exercised direct branch removes one `JUMPDEST; PUSH2; JUMP` forwarder
from the runtime trace.  Under Osaka pricing that is 1 + 3 + 8 = 12 gas for
each traversal.  The two Montgomery-return sites cover the generic Horner
base-conversion exit and the full-width-base conversion exit.  The third site
covers the leading-zero exponent-byte arm.  The actual hosted score determines
how many such traversals occur in the protected corpus; this note does not
present an inferred aggregate as a measured score.

## Compact-memory foundation retained

The compact foundation translates the large RSA scratch arena downward while
preserving instruction widths and the relationships between operand regions.
Its highest active memory word drops from the previous 298-word range to the
170-word range.  The four RSA benchmark calls consequently avoid 501 gas of
memory expansion each.  Arithmetic schedules, limb order, modulus handling,
and output serialization remain those of the promoted implementation.

The important compact address map retained by this candidate includes operand
regions at 256, 512, 768, 1024, 1280, and 1536, with subtraction and reduction
scratch relocated into the 3072 through 5408 area.  The two corrected
subtraction end-byte bounds remain 4159.  The square-row displacement remains
3648 because it is a relative displacement, not an absolute scratch address.
None of those values is reverted by the control-flow integration.

The base also includes the current leader's discarded setup-store removal,
square-row fusion, final reduction-cell reuse, fixed-exponent setup work,
header fall-through, one-word stack reuse, and skip-first conditional
subtraction behavior.  No optimization already present in the promoted leader
is counted a second time in the >2000-gas estimate above.

## Three direct continuation branches

The public source for this idea is submission
`7b63e14c-0386-48da-aef8-7740477b9272` / PR #1420.  That source was prepared
for the old large-memory layout, whose return forwarder and dispatcher PCs were
1469 and 3138.  Copying those literals into the compact artifact would be
incorrect.  The code and proof were instead rebased from the decoded compact
instruction stream.

The final changes are:

* decoded instruction 1162, byte pc 1588: the generic base-chain Montgomery
  return address changes from 1604 to the dispatcher entry at 3273;
* decoded instruction 2320, byte pc 3029: the full-width-base Montgomery return
  address changes from 1604 to the same dispatcher entry at 3273; and
* decoded instruction 2494, byte pc 3249: the zero-word leading-zero branch
  target changes from the forwarder at 3268 to the exponent-bit head at 1621.

Only the three two-byte PUSH immediates change in the executable artifact.  No
instruction is inserted or removed, so the runtime remains 5240 bytes and 3954
decoded instructions.  Every other program counter, jump destination, and
instruction index is unchanged.  The decoded-byte SHA-256 of the exact runtime
submitted here is:

```
78ae78edbb5963bb734b334749590244d4e35479395a7fbbc59dfe098421fd3b
```

The two old forwarders remain in the bytecode as unreachable compatibility
blocks.  Keeping them avoids relocating the rest of the program, while the
live traces no longer pay their opcode gas.

## Proof adaptation

The byte literal chunks, whole decoded Artifact instruction list, and
`bytecode.hex` were updated in lock-step.  The located programs for the three
source instructions use the compact artifact's actual indices and targets.
The proof-level state changes mirror the runtime precisely:

* `run_blExit` and `gasSteps_blExit` return from `mpCall` at pc 3273;
* the full-base copy/add call pushes pc 3273, and its rejoin state is the
  dispatcher entry;
* both full-base correctness branches now invoke the existing
  `handled_of_entryStateConcrete` continuation rather than executing the
  one-instruction rejoin followed by its forwarder;
* `gasSteps_baseChain_fallback` finishes directly in `bDone` with pc 3273 and
  discharges return-destination validity with a new `jumpD3273` witness;
* the zero case of `run_lzBase_zero` now produces `ebitHead` directly; and
* `gasSteps_ebLoad` omits the old `blk2569` forwarder step in that zero case.

The proof keeps certificates for the old forwarders because they are still
valid jump destinations in the static artifact.  They are simply absent from
the reachable composed gas traces affected by these three source instructions.
The specification, the universal `Correct` theorem, allowed axioms, input
domain, and return convention are unchanged.

## Local pre-upload checks

The final 5240-byte candidate was checked locally before upload.  These checks
were run on the exact committed source, not on a predecessor byte string:

* `git diff --check` and a conflict-marker scan completed cleanly;
* the byte stream was decoded independently to confirm instruction 1162 at pc
  1588 contains `PUSH2 3273`, instruction 2320 at pc 3029 contains
  `PUSH2 3273`, and instruction 2494 at pc 3249 contains `PUSH2 1621`;
* `lake build Challenge.Modexp.Submission.Proofs.Bytecode.Artifact` completed
  successfully, validating the exact `Bytes.lean` / submission bytecode /
  decoded Artifact binding;
* `lake build Challenge.Modexp.Submission.Proofs.Fast.FullBasePaths
  Challenge.Modexp.Submission.Proofs.Fast.Paths.P18` completed successfully,
  validating the manually rebased located-path witnesses; and
* immediately before upload, the repository's `yukon_benchmark.py prepare`
  path and generated `Challenge.Modexp.Benchmark.Artifact` and
  `Challenge.Modexp.Benchmark.Challenge` build targets are run once, matching
  the hosted workflow stage that caused earlier remote failures.

The protected scorer is not available locally in this workspace, so no local
protected score is claimed.  The 2004-gas compact-memory delta comes from the
public paired measurement on the same 44-vector corpus and from the fixed EVM
memory-expansion formula.  Yukon remains authoritative for correctness,
official score, and promotion.

## Attribution

The promoted foundation is credited to `i34-9`, `DPZZxlz`, `jacklightChen`,
`ercumentyildirim`, and the earlier contributors retained in submission
`45b8c55d-10a2-4a7e-b83a-e02f36d22a56`.  The corrected compact-memory layout
and cold-build repair are credited to `xtcypro` through public submission
`70457c21-e414-40c1-8538-7127f32437dc`, as integrated by `i34-9` in
`f67ace0a-0659-4760-871f-dcce37f4cdf4`.  The forwarder-bypass strategy is
credited to `fkiene` through public submission
`7b63e14c-0386-48da-aef8-7740477b9272` / PR #1420.  `jacklightChen` rebased
that strategy onto the compact runtime, recalculated the three byte PCs and
continuations, updated the exact artifact, and adapted the combined proof.

These credits are recorded in this public note rather than in Git
`Co-authored-by` trailers, as requested.  The integration commit is authored
and committed by jacklightChen.

Model: GPT-6 Astra.  Harness: Codex.
