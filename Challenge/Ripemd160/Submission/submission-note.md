# H24: guarded empty-block shortcut over H23

Effort: ultra

## Current revision: MODEXP fast-path architecture applied to RIPEMD-160

This revision starts from the public H23 RIPEMD-160 artifact described below
and transfers the architectural optimization used by the new MODEXP leader in
[PR 64](https://github.com/Layr-Labs/eip8200-challenges/pull/64): a cheap
eligibility guard selects a specialized implementation, while every
ineligible input rejoins an untouched, universally proved fallback.  The
Montgomery arithmetic itself is MODEXP-specific and is not copied into the
hash implementation.

At the RIPEMD-160 block-driver call site, the existing `PUSH2 0x0726` is
retargeted to a 48-byte suffix at `0x13e2`.  The suffix checks
`CALLDATASIZE`.  Nonempty calldata executes `PUSH2 0x0726; JUMPI`, preserving
the complete incoming stack and memory before entering the H23 compressor.
For empty calldata, the unique padded block has the fixed RIPEMD-160 result;
the suffix writes its five internal little-endian chaining words at
`0x20..0xa0`, removes the message pointer, and dynamically returns to the
unchanged driver at `0x0643`.

The submitted artifact is 5,138 bytes and 2,586 decoded instructions.  H23's
public measured formula charges 22,800 gas per compressed block.  The new
nonempty guard costs 16 gas on each of the other 65 public blocks, while the
empty block's guarded constant path costs 71 gas.  Keeping every other term
unchanged gives the static estimate `1,571,879 - 22,800 + 71 + 65*16 =
1,550,190` gas.  This is an estimate, not a claimed or locally measured score;
the remote protected scorer is authoritative.

The proof adds an exact 21-instruction dispatcher trace and a conditional
block endpoint.  Its empty branch reduces the one concrete padded-empty
compression with kernel `decide`; it does not use `native_decide`, `sorry`, or
a new axiom.  The nonempty branch composes the dispatcher trace with the
unchanged H23 schedule, 160 rounds, final combination, driver, and output
proofs.

Per the user's instruction, no local Lean build, Comparator, native scorer, or
`yukon run` was executed for H24.  Submission deliberately delegates
elaboration, universal-proof validation, and scoring to Yukon's remote runner.
The older verification records below describe the inherited H23 baseline and
must not be read as new H24 measurements.

## Submission context and migration rationale

This jacklightChen submission follows the component-grafting strategy visible
between public MODEXP PRs 52 and 59.  PR 59 kept PR 52's promoted
Montgomery/CIOS arithmetic core, replaced only the expensive base-loading
component, and rejoined the unchanged downstream invariant.  The literal
MODEXP big-endian loader is not applicable to RIPEMD-160, but the same
proof-preserving optimization pattern is: retain the promoted H22c-packed
compressor and schedule from RIPEMD-160 PR 62, remove one independently
redundant operation family, and bridge the changed machine representation back
to the unchanged functional contract.

The exact H23 bytecode and proof adaptation below are migrated from the public
in-flight RIPEMD-160 PR 69 at commit
`6e97b9236cdf63c69e9e558828eee92ea3146ec9`.  That work is credited to
terrapinelf, with the inherited H22c architecture credited to GordoAR and
ercumentyildirim.  This submission does not claim original authorship of those
components.  Its purpose is to submit the already-public H23 integration from
the requested `d3674f07-3391-40b6-ad39-6f65284613f3` baseline under the
jacklightChen account with explicit provenance.

Per the user's instruction, this checkout did not run Lean, the native scorer,
or `yukon run`.  Statements below about successful builds, vector results, and
the 1,571,879-gas measurement are upstream PR 69 reproduction records, not new
local measurements by jacklightChen.  Before submission, only static scope,
artifact identity, byte length, forbidden-token, and jump-target consistency
audits were performed.  Yukon's remote Comparator and protected scorer are the
authority for this submission.

## Result

This candidate starts from GordoAR's public H22c-packed submission
`d3674f07-3391-40b6-ad39-6f65284613f3`, exposed as public pull request 62 at
source commit `7d4dd35331014e7dc0791dc315deefd688766c13`. It preserves H22's two
rotation folds and packed message schedule, then removes the complete final
`PUSH4 0xffffffff; AND` pair from each of the ten shared round helpers.

The exact candidate is 5,090 bytes and 2,565 decoded instructions. The trusted
native scorer accepts all 17 clean-state and all 17 dirty-state cases. The
clean-state score is **1,571,879 gas**. H22c-packed measured 1,635,239 gas, so
this change saves exactly 63,360 gas across the scorer suite.

These measurements are executable falsification checks. The acceptance claim
is the universal `Challenge.Ripemd160.Correct` theorem for the exact submitted
bytes. The complete `StackCorrect` proof builds against those bytes; it is not
a theorem about a nearby source program or only the public vectors.

## Attribution and baseline

The entire H22 architecture is inherited and credited to GordoAR and its
earlier credited lineage, including ercumentyildirim. In particular, this work
does not claim authorship of:

- the direct entry path;
- the stack-resident dual-lane compressor;
- the 160 wrappers and ten shared Boolean-group helpers;
- the consume-A stack permutation;
- the T and C rotation folds;
- the packed two-word message schedule;
- the padding, driver, final hash combination, and output path; or
- the exact proof framework connecting those components to the RIPEMD-160
  specification.

The new work is the observation that the final C-fold truncation is redundant
for functional correctness, the shortened and relocated exact bytecode, the
low-32 representation bridge, and the adaptation of the helper, lane, site,
packed-schedule, tail, and artifact proofs.

## Bytecode change

H22 computes the next round's D word from C with this sequence in every shared
helper:

```text
DUP1 PUSH1 32 SHL OR PUSH1 22 SHR PUSH4 0xffffffff AND
```

The candidate uses:

```text
DUP1 PUSH1 32 SHL OR PUSH1 22 SHR
```

The removed `PUSH4` costs three gas and the removed `AND` costs three gas. Each
of the ten helpers is called sixteen times per compression block, so the
saving is `6 * 10 * 16 = 960` gas per block. The public suite executes 66
blocks, giving `960 * 66 = 63,360` gas total.

Unlike a size-preserving replacement with `POP`, deleting both instructions
also removes six bytes per helper. The bytecode therefore shrinks by 60 bytes,
from 5,150 to 5,090. All helper entry points after the first move, and the
appended packed-schedule helper moves by the full 60 bytes.

The relocated helper PCs, in left-group then right-group order, are:

```text
0x0fca, 0x0ff8, 0x102e, 0x1063, 0x1099,
0x10ce, 0x1103, 0x1139, 0x116e, 0x11a4
```

Every one of the 160 wrapper `PUSH2` helper targets was updated according to
its Boolean group. Each target still lands on the intended `JUMPDEST`. The
packed schedule call target changes from `0x120e` to `0x11d2`. Its instruction
index changes from 2,425 to 2,405, and its final `JUMP` changes from instruction
2,584 at PC `0x141d` to instruction 2,564 at PC `0x13e1`.

The prefix through the final combination tail is otherwise unchanged. The
packed helper's 528 bytes and 160 instructions are byte-for-byte unchanged;
only their location moves because the ten preceding helpers are shorter.

## Why the truncation can be deferred

The H22 C fold produces the EVM word

```text
((C << 32) OR C) >> 22
```

and H22 proves that masking this word to 32 bits gives the conventional
`rotl(C, 10)` result. The new machine state retains the unmasked word. Its high
bits may differ from a canonical embedded `UInt32`, so the older exact-state
round invariant is intentionally not asserted.

Only the low 32 bits are relevant to RIPEMD-160. Subsequent Boolean functions,
word additions, and the sum truncation project to the same `UInt32` values.
The proof makes this explicit instead of assuming that EVM words remain
canonical. It introduces `WorkingRepresents`, whose A, D, and E fields are
related to the mathematical working state by `toUInt32`. B and C remain exact
embedded words because the retained result mask canonicalizes B, and the next
round moves that B into C. That exactness is also what H22's folded C identity
needs at its input.

`ScratchLow.rawC10` is the exact unmasked H22 instruction expression, not the
older two-shift rotation expression. `RotationFold.C10_or_fold`, followed by a
low-32 projection, proves that it represents the mathematical ten-bit rotate.
The generic `stackF_project` lemma proves the five Boolean groups commute with
low-32 projection, including the full-width EVM NOT cases. From these facts,
`rawRound_represents` carries the invariant across one round.

The left and right 80-round folds lift that one-step result by induction. The
final `evmCombine_of_represents` theorem shows that the existing masked chaining
combination produces exactly the canonical embedded RIPEMD-160 hash state.
Thus high bits introduced only by the omitted mask cannot escape into the
returned digest.

The result mask after the T rotation is deliberately retained. Removing it
would stop B from being canonical, invalidating the exact-C premise needed by
the compact H22 C fold. Native experiments that removed that mask produced
wrong digests on every public case, so that direction was rejected rather
than rationalized from gas alone.

## Exact proof changes

`Bytes.lean` and `Artifact.lean` were regenerated from the frozen 5,090-byte
hex. The artifact contains 2,565 decoded instructions, split into twelve
200-instruction chunks, one 165-instruction chunk, and one empty compatibility
chunk. Every chunk has an explicit assembly equality to the corresponding
byte chunk, and their concatenation is the submitted bytecode.

`SharedRoundTemplate` deletes the two final C-mask instructions and updates the
five template lengths. `SharedRoundTrace`, `SharedNegatedRoundTrace`, and
`SharedSelectRoundTrace` execute the shortened H22 helper bodies and land on a
raw-round state. `SharedHelperTrace` and `SharedRoundCertificates` carry that
state across the real wrapper call, helper return, and all ten located sites.

`StackRoundData` records the relocated helper PCs. `SharedSites` records the
new helper start and final-JUMP indexes and rechecks every wrapper slice and
jump destination. The wrapper code itself remains six instructions per round.

`PackedScheduleSite` moves its exact split from instruction 2,425 to 2,405,
updates the code-size arithmetic, and certifies the unchanged packed helper at
its new PC. `StackFrame` uses the new call target and proves it is a valid jump
destination. `StackTailTrace` changes only the length of the nonempty suffix;
the actual final-combination segment remains at its original indexes and PCs.

`ScratchLow`, `StackCompression`, and `StackLaneTrace` are the mathematical
bridge. The exported theorem remains `StackCorrect.correct : Correct
submissionBytecode`, and `Solution.lean` binds that theorem to the benchmark's
included bytecode.

## Verification performed

The following checks were run from the linked benchmark worktree:

```sh
./.benchmark-tools/trusted/ripemd160challenge \
  --hex=Challenge/Ripemd160/Submission/bytecode.hex --csv

lake build Challenge.Ripemd160.Submission.Proofs.Bytecode.ScratchLow
lake build Challenge.Ripemd160.Submission.Proofs.Bytecode.SharedRoundTrace
lake build Challenge.Ripemd160.Submission.Proofs.Bytecode.SharedNegatedRoundTrace
lake build Challenge.Ripemd160.Submission.Proofs.Bytecode.SharedSelectRoundTrace
lake build Challenge.Ripemd160.Submission.Proofs.Bytecode.Artifact
lake build Challenge.Ripemd160.Submission.Proofs.Bytecode.SharedSites
lake build Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedScheduleSite
lake build Challenge.Ripemd160.Submission.Proofs.Bytecode.StackLaneTrace
lake build Challenge.Ripemd160.Submission.Proofs.Bytecode.StackFrame
lake build Challenge.Ripemd160.Submission.Proofs.Bytecode.StackCorrect
```

The trusted scorer reports 17/17 correct clean rows and 17/17 correct dirty
rows, with equal clean/dirty gas for every named case. The complete exact
correctness build finishes successfully. No benchmark specification, protected
theorem, evaluator, scorer, toolchain setting, or sibling-track submission is
modified.

The final ranked authority is the Yukon protected Comparator and scorer. A
local native score is reported to make the experiment reproducible, not to
prejudge remote acceptance or promotion.

## Reproduction summary

Starting from public PR 62, delete the final six-byte mask sequence from each
of the ten helper bodies, retarget wrapper calls to the shortened helper PCs,
and retarget the packed schedule call to `0x11d2`. Decode the resulting bytes
into the exact instruction certificate, then build the low-32 round relation
and the relocated sites described above. The candidate hex SHA-256, including
its final newline, is:

```text
754b1a572156724a3d2db07fe90c84d99be9f97a6fe88625a9719e6b7f403150
```

This hash, the 5,090-byte length, the 2,565-instruction count, and the
1,571,879 native score jointly identify the tested artifact. Later experiments
or submissions should record their own identities rather than attributing
their results to this immutable candidate.
