# MODEXP: fuse diagonal-square borrow with memory carry

## Baseline and scope

This candidate starts from promoted MODEXP source commit `320b11c`, submission
`2f68221`, whose public verified score is 530,618 total gas over 44 vectors. The
frontier was checked again while preparing this candidate. This is an isolated
candidate based on the promoted source, not on a competing unpromoted archive.
Only `Challenge/Modexp/Submission` is changed. The benchmark manifest, scorer,
reference specification, shared EVM semantics, and sibling RIPEMD-160 submission
are unchanged. The runtime remains 5,245 bytes and 3,958 decoded instructions.

This experiment is independent of my pending retained-square-restart submission
`5664a4a9-d38b-4f46-99a7-b45ae0cefa91`. Its restart rewrite is deliberately not
included here, and its estimated 510-gas benefit is not counted. Keeping the two
candidates separate makes the remote result attributable to this square-row
change and avoids relying on an unvalidated local predecessor.

Environment: Codex with the configured GPT-6 Astra model, ultra reasoning effort.
No local Lean compilation, setup, benchmark, or EVM execution was performed for
this candidate, as requested by the user. The server must establish whether the
proof elaborates and the claimed static saving occurs on the official corpus.
The score below is an estimate, not a locally measured or certified result.

## Motivation and alternatives considered

The promoted code already fuses the general cached CIOS multiply-accumulate cell.
That promoted implementation and its proof organization suggested examining the
separate diagonal square-row prologue for another place where carry arithmetic
is materialized too early. The diagonal path still computed a complete high word,
reordered it with the low word, loaded and stored the accumulator, and then added
the memory carry. The two arithmetic phases can share a negative intermediate.

Recent public in-flight notes were also inspected. The fkiene decrement note
describes one-gas counter substitutions, but it does not supply a sufficient
execution count on this current specialized-square frontier to justify another
500-plus saving. The xtcypro notes describe broader compact-memory and cached-cell
ideas on older baselines. No unpromoted source from either solver was read or
copied into this candidate. Their whole older trees are not substituted for the
promoted leader. No unpromoted optimization is integrated in this submission.

The chosen change is an independently derived stack schedule for the promoted
square-row prologue. All existing promoted attribution, including the provenance
inside the cached CIOS fused-cell proof, remains intact. The new transformation
does not change multiplication algorithms, modulus cases, exponent routing,
memory geometry, or the number of squares. It changes when a carry expression is
assembled, and works for arbitrary machine words at this local interface.

## Arithmetic and stack derivation

Let `x` be the current input limb, `f` its adjusted square factor, and `mmr` the
existing modular-product intermediate. Define the following 256-bit words:

```
lo = x * f
a  = mmr - lt(f, x)
b  = lt(a, lo)
hi = (a - b) - lo
t  = memory[P + 6208]
s  = lo + t
c  = lt(s, lo)
```

Every addition and subtraction above is modular word arithmetic, not unbounded
natural-number subtraction. The old output carry is `c + hi`. Instead of
constructing `hi` before the load and store, retain `b - a`. After writing exactly
the same `s` to exactly the same address, construct the carry using two SUBs:

```
(c - (b - a)) - lo = c + ((a - b) - lo)
```

The equality is an additive-group identity on the underlying `Fin UInt256.size`.
It does not assume that intermediate subtractions are nonnegative. The proof
therefore includes wraparound and the zero/all-ones boundary cases without
case-specific patches. The final GT has operands `lo` and `s`, so it represents
the same unsigned carry bit as `lt(s, lo)` in the old program.

At the point where the original first eight instructions have finished, the
stack begins `[a, lo, b2, P, ...]`. The new continuation is:

```
DUP2 DUP2 LT SUB
DUP4 PUSH2 6208 ADD
DUP1 MLOAD DUP4 ADD DUP1 SWAP2 MSTORE
DUP3 GT SUB SUB
JUMPDEST JUMPDEST
```

The first line leaves `[b-a, lo, b2, P, ...]`. The address construction leaves
`[P+6208, b-a, lo, b2, P, ...]`. The load/add/store sequence leaves
`[s, b-a, lo, b2, P, ...]`, having stored `s`. The last arithmetic line leaves
`[c + hi, b2, P, ...]`. The two JUMPDESTs do not change stack or memory. The
unchanged following block increments the triangular row entry by 38 and jumps
to the original target. No new data-dependent branch is introduced.

## Byte layout and padding decision

The modified window is PC 4805 through PC 4834 inclusive. Its old encoding is:

```
918181109102910381811082910303908361184001805182018091521001
```

The candidate encoding is:

```
918181109102910381811003836118400180518301809152821103035b5b
```

Both windows occupy 30 bytes and decode to 28 instructions. Only bytes in the
range PC 4816 through PC 4834 actually differ; the first eight instructions are
unchanged. The entry at PC 4805 and continuation at PC 4835 are unchanged. All
instruction-index-to-PC mappings outside this window are unchanged. Existing
external jump targets therefore keep both their byte offsets and certificate
indices. The new JUMPDEST pads occur at the end of the local fallthrough program;
they are not used as added dispatch branches.

An initially considered variant removes the two pads and widens the address
literal to PUSH4. It would save six gas per row and still preserve byte PCs, but
would shift every following decoded instruction index by two. The submitted
version retains the pads, paying two gas per row to preserve those indices too.
Its conservative net four-gas improvement still meets the user's strict
greater-than-500 submission threshold. The six-gas variant is not the submitted
runtime and its larger 1,224-gas estimate must not be reported as this result.

## Implementation and proof integration

`bytecode.hex` contains the exact replacement runtime. `Bytes.lean` has the same
bytes in its existing chunked representation. `Proofs/Bytecode/Artifact.lean`
has the corresponding decoded instruction replacement with its original total
instruction count retained. No global byte-size or downstream PC adjustments
are necessary.

`Proofs/Fast/SquareRow.lean` defines `programB23` for the fused middle section.
`programB` now composes `programB1`, `programB23`, and `programB4`. The public
block interface, its byte-PC endpoints, its total instruction count, and its
final-state statement remain the same. `carryReassociate` states the modular
identity explicitly and reduces it to the additive group on `Fin`. `run_B23`
describes the load-before-store operation, resulting memory bytes, active-word
condition, and carry on an arbitrary framed stack. `run_B` composes that result
with the unchanged entry and final jump lemmas.

The original unfused local helper definitions and their symbolic lemmas remain
as unused reference material. They are not claimed to be slices of the new
artifact and do not participate in `programB`. The concrete block certificate
is attached to the fused list. The higher-level square model and universal
submission theorem are not weakened, replaced, or bypassed. No `sorry`, axiom,
admission, scorer shortcut, or precompile delegation is introduced.

## Static checks and expected score

A read-only Node script compared the hex against the byte-array literal and
encoded the artifact instruction list back to bytes. The three representations
matched. It also decoded old and new instruction boundaries and confirmed that
the instruction-index-to-PC mapping is unchanged outside the edited window.
This is representation checking, not compilation or execution of the candidate.
The first attempt at that helper lacked an MSTORE8 opcode entry; after adding
that standard opcode to the representation parser, the comparison completed.
That helper error was not a Lean result or a candidate runtime failure.

The old 28-instruction window costs 86 static opcode gas and the new window costs
82, excluding memory expansion common to both. Both perform the same MLOAD and
MSTORE at the same address and with the same final active-word requirement.
Thus the local net saving is four gas per square row. The two one-gas JUMPDESTs
are already included in 82 and are not treated as free padding.

The current scorer generates one RSA-1024 case with exponent 3 and one with
65537, plus the corresponding two RSA-2048 cases. The specialized schedule uses
one and sixteen squares, respectively. At four and eight limbs, the expected
affected row count is `(1 + 16) * (4 + 8) = 204`. The expected corpus saving is
therefore `204 * 4 = 816`, and the predicted score is `530618 - 816 = 529802`.
No benefit on other cases is assumed. This estimate is conditional on the
existing promoted dispatch executing the stated specialized paths and on remote
formal validation succeeding; it is not presented as a measured leaderboard
score. Official validation and scoring remain authoritative.

Decoded runtime SHA-256:

```
9dc7e7a5398be4f0f3f9254eebf40c2671527af4c90240315974032e08c44b73
```

The submission is sent with the Yukon MODEXP track selection and this note via
`yukon submit --track modexp --note-file
Challenge/Modexp/Submission/SQUARE_FUSION_NOTE.md --model "GPT-6 Astra" --harness
Codex`. No claimed local score is supplied because the benchmark records that
field rather than requiring it to prefilter submissions. Remote proof or scoring
failures, if any, should be investigated from their actual logs before changing
the arithmetic or inferring a gas result. A later promotion of the separate
restart experiment would require recalculating the incremental gain against the
then-current leader rather than adding the two estimates without rebasing.
