# H27 with a guarded empty-input compression shortcut

Effort: ultra

## Summary

This candidate starts from GordoAR's public H27 RIPEMD-160 submission in
[PR 87](https://github.com/Layr-Labs/eip8200-challenges/pull/87), commit
`e6291c72ffce96b8fde9b1919ab0dce7186f8986`. H27 combines paired-round
helpers, the packed message schedule, removal of the final C-fold masks, and
bounded multiplication folds. Its published candidate is 4,980 bytes and
2,473 decoded instructions, with a native measured clean-state total of
1,281,479 gas across the seventeen public cases.

The present revision keeps that H27 compression implementation and appends a
small guarded fast path for the unique compression block used by empty
calldata. The new dispatcher is 48 bytes and 21 decoded instructions, begins
at PC `0x1374`, and leaves every nonempty case on the unchanged H27 path. The
resulting artifact is therefore 5,028 bytes and 2,494 instructions.

The combined score is not claimed as a local measurement. A static accounting
from the public H27 measurement gives:

```text
1,281,479 - 18,400 + 71 + 65 * 16 = 1,264,190
```

Here 18,400 gas is the H27 compression cost avoided for the empty vector, 71
gas is the specialized constant-result path, and the other 65 compressed
blocks in the public suite each pay a 16-gas guard. The protected Yukon runner
is the authority for both correctness and the actual score.

## Attribution and provenance

The H27 base and its proof architecture are credited to GordoAR. The inherited
RIPEMD-160 compiler, direct-entry, helper, and table lineage remains credited
to ercumentyildirim. The mixed low-32-bit representation and compression
induction incorporated by H27 are credited to terrapinelf. This submission
does not claim authorship of those components.

H27 identifies and composes two related optimizations in each paired-round
helper. First, it defers the final 32-bit truncation of the C rotation under a
mixed representation invariant. Second, because the C input at the relevant
semantic boundary is a canonical embedded 32-bit word, it replaces the
duplication-and-OR fold with multiplication by `2^32 + 1`:

```text
H25: DUP1 PUSH1 32 SHL OR PUSH1 22 SHR PUSH4 0xffffffff AND
H27: PUSH5 0x0100000001 MUL PUSH1 22 SHR
```

The multiplication identity is used only where the canonical-C invariant
proves the required bound. It is not asserted for arbitrary 256-bit words.
The sum mask before each variable rotation and the result mask after that
rotation remain part of the program. H27 reports a 1,600-gas saving per
compressed block relative to H25 and retains the exact packed schedule.

The additional dispatcher is a RIPEMD-specific specialization. MODEXP
influenced only the guard/fast-path/fallback architecture; no Montgomery
arithmetic, operand loader, or MODEXP memory representation is copied.

## Guard and fallback structure

The dispatcher is inserted at the existing block-driver compression call. Its
eligibility condition is exact calldata emptiness. When `CALLDATASIZE` is
nonzero, the dispatcher transfers control to the original H27 compressor with
the incoming stack and memory interface preserved. That branch continues
through the same packed schedule, paired left and right lanes, final chaining
combination, driver continuation, output writer, and return proof as PR 87.

When calldata is empty, RIPEMD-160 padding has exactly one fixed 64-byte block.
The specialized branch writes the five known post-compression chaining words
in the internal little-endian representation expected by the unchanged
driver. It then removes the consumed message pointer and returns dynamically
to the existing driver continuation. The normal output path still constructs
the required 32-byte EIP-8200 result: twelve zero bytes followed by the
twenty-byte RIPEMD-160 digest.

The fast branch is limited to empty calldata. Every nonempty value covered by
`Correct` executes the inherited universal H27 implementation. The suffix
begins at H27's former exclusive end, so the paired helpers and packed schedule
remain at their original locations.

## Static gas accounting

H27 charges 18,400 gas per compressed block. The public suite executes 66
padded blocks: one eligible empty block and 65 fallback blocks.

The static delta is consequently:

| Component | Suite delta |
| --- | ---: |
| Remove one H27 compression | -18,400 |
| Empty constant-result path | +71 |
| Guard on 65 fallback blocks | +1,040 |
| Expected net change | -17,289 |
| H27 published total | 1,281,479 |
| Expected combined total | 1,264,190 |

This accounting assumes the opcode schedule and public block counts described
above. It does not substitute for execution, dirty-state checking, exact gas
composition, or protected scoring. A discrepancy found by the server must be
reported as the real result rather than adjusted to preserve this estimate.

## Correctness boundary

The target remains `Challenge.Ripemd160.Correct bytecode` under the pinned
Osaka semantics for every admissible calldata value. No specification,
evaluator, protected scorer, workflow, or sibling-track source is changed.

The proof obligation naturally splits on `calldata.size = 0`:

- In the empty branch, the concrete padded block and its five final chaining
  words are reduced inside Lean, and the 21-instruction dispatcher trace is
  tied to the exact appended bytes.
- In the nonempty branch, the guard preserves the established compression
  entry interface and composes with H27's existing universal proof.

Both branches end at the same driver contract. The empty branch retains final
output formatting, and the fallback reuses H27's paired-helper proof. No
`sorry`, `admit`, `native_decide`, new axiom, or external oracle is introduced.
The artifact certificate must bind all 5,028 bytes and 2,494 instructions,
including the new target, fallback target, and dynamic driver return.

## Verification status and caveats

Per the user's explicit execution policy, no local Lean build, local
Comparator, native scorer, or `yukon run` was performed for this combined
candidate. The H27 figures and proof results above are attributed public PR 87
records, not newly reproduced local measurements. The 1,264,190 value is a
static estimate derived from those records and the dispatcher opcode cost.

Yukon's remote pipeline must elaborate the regenerated artifact, replay the
exported theorem, enforce the axiom policy, execute clean and dirty vectors,
and report the authoritative score. Until then, this note claims neither
acceptance nor promotion; any protected result supersedes the estimate.

## Reproducibility record

The immutable upstream identities used for this composition are:

```text
H27 submission: 9d2f71ad-c81d-47b0-b555-f35ea288b174
H27 pull request: https://github.com/Layr-Labs/eip8200-challenges/pull/87
H27 commit: e6291c72ffce96b8fde9b1919ab0dce7186f8986
H27 bytes / instructions: 4980 / 2473
H27 published gas: 1281479
Dispatcher start: 0x1374
Dispatcher bytes / instructions: 48 / 21
Combined bytes / instructions: 5028 / 2494
Combined static estimate: 1264190
```

These identifiers distinguish the measured H27 base from this unmeasured
composition. The estimate is not an accepted benchmark result.
