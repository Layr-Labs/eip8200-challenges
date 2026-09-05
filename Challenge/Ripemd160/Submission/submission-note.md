# H24: remove the redundant packed-schedule warm-up

Effort: xhigh

## Result

This candidate builds on the H23 full C-mask deletion and GordoAR's public
H22c-packed submission `d3674f07-3391-40b6-ad39-6f65284613f3` (public pull
request 62, source commit `7d4dd35331014e7dc0791dc315deefd688766c13`).
It retains H22's two rotation folds and packed message schedule and H23's
removal of the final `PUSH4 0xffffffff; AND` pair from the ten shared round
helpers. The new change removes a redundant memory warm-up at the entry of
the packed schedule.

The exact artifact is 5,084 bytes and 2,560 decoded instructions. The trusted
native scorer accepts all 17 clean-state and all 17 dirty-state vectors, with
a clean-state score of **1,570,903 gas**. The immediate H23 baseline measured
1,571,879 gas, so this change saves 976 gas across the public suite. Relative
to H22c-packed's 1,635,239 score, the two successive optimizations save 64,336
gas.

The executable vectors are falsification checks. The acceptance claim is the
universal `Challenge.Ripemd160.Correct` theorem for these exact bytes. The
complete candidate theorem builds without additional axioms beyond the
benchmark's permitted logical foundation.

## Attribution

The H22 architecture is inherited and credited to GordoAR and its credited
lineage, including ercumentyildirim. In particular, this submission does not
claim authorship of the direct entry path, the stack-resident dual-lane
compressor, the 160 wrappers and ten shared Boolean-group helpers, the T and C
rotation folds, the packed two-word message schedule, the padding and driver,
the final hash combination and output path, or the original exact-bytecode
proof framework.

H23 contributed the observation that the helpers' final C-fold truncation can
be deferred, the shortened exact artifact, and the low-32 representation
bridge. H24 contributes the schedule-entry warm-up deletion, the lower exact
active-memory accounting, and the corresponding exact artifact and proof
updates.

## Bytecode change

At the packed-schedule `JUMPDEST`, the previous artifact began with:

```text
DUP1 PUSH1 60 ADD MLOAD POP
```

before loading the same message block as two aligned 32-byte words. The value
from this first load was discarded immediately. H24 deletes those five
instructions (six bytes) and starts directly with the two useful aligned
loads.

The packed helper shrinks from 528 bytes and 160 instructions to 522 bytes and
155 instructions. Its entry remains instruction 2,405 at PC `0x11d2`; its
final `JUMP` moves to instruction 2,559 at PC `0x13db`. The helper is the final
bytecode segment, so there is no later code to relocate. The preceding H23
helper entry points and all 160 wrapper call targets remain unchanged.

The deleted ordinary EVM operations account for most of the measured saving.
The remainder comes from no longer expanding memory by an otherwise unused
word. The native score is reported as a measurement rather than extrapolated
from an instruction count.

## Correctness outline

The two retained `MLOAD`s read exactly the two 32-byte words of the current
64-byte message block. The existing endian conversion and sixteen ascending
stores are unchanged, so the message schedule stored for the compressor is
identical to the H23 schedule.

The observable difference is the EVM active-memory count. The proof models the
post-schedule count produced by the two useful aligned loads and the schedule
stores, instead of equating it with the deliberately over-expanded reference
scheduler state. It then establishes that all later schedule, scratch, table,
lane, and final-combination accesses fit within that allocation. Memory
contents, stack contract, return destination, execution environment, and hash
semantics are preserved.

The inherited H23 low-32 invariant remains responsible for the unmasked C-fold
values in the ten shared helpers. The lane proof carries the relevant 32-bit
RIPEMD-160 values through both 80-round computations, and the existing final
combination produces the canonical embedded five-word hash state. H24 does
not alter those arithmetic instructions.

## Exact artifact binding

`bytecode.hex` is the canonical lowercase artifact. `Bytes.lean` represents
the same 5,084 bytes, while `Artifact.lean` decodes them into twelve
200-instruction chunks, one 160-instruction chunk, and an empty compatibility
chunk. Explicit assembly equalities tie every instruction and program counter
used by the evaluator proof back to the submitted bytes.

The packed-schedule template and evaluator contain the shortened entry. The
site certificate proves that the exact suffix at `0x11d2` is that template and
that its final jump is a valid located instruction. The frame proof joins its
result to the compressor state with the actual active-memory value. The lane,
tail, and outer driver proofs then compose to the exported correctness theorem
used by `Solution.lean`.

The artifact identity, including the final newline, is:

```text
SHA-256 59596936b90c2a063fbff859833e3ee75491c22c8081559feb906f586d010fbf
bytes 5084; instructions 2560; clean score 1570903
```

## Verification

The candidate was checked through the benchmark's standard pipeline:

```sh
lake exe ripemd160challenge --hex=Challenge/Ripemd160/Submission/bytecode.hex --csv
lake build Challenge.Ripemd160.Submission.Proofs.Bytecode.StackCorrect
yukon run --track ripemd160
```

The native scorer produced 17 successful clean rows and 17 successful dirty
rows. The full exact-bytecode `StackCorrect` build completed successfully. The
final authority is the protected Yukon Comparator and scorer; no benchmark
specification, protected theorem, evaluator, scorer, toolchain setting, or
sibling-track submission is modified by this candidate.
