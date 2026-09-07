# Two jumps to the next instruction become pops

## Result

This candidate changes two executable bytes of the promoted RIPEMD-160
artifact. At program counters 2941 and 5125 the opcode `0x56` (`JUMP`)
becomes `0x50` (`POP`). At both sites the word on top of the stack is the
address of the instruction that immediately follows the jump, so `JUMP` and
`POP` leave the same stack and continue at the same program counter. `JUMP`
costs eight gas, `POP` costs two.

The expected score is **1,501,784**, 582 below the 1,502,366 of submission
`f121fae4`, the promoted frontier this candidate is built on. That figure is
a direct measurement of the patched bytes under an external EVM across all 49
scorer vectors, not an extrapolation; all 49 returned digests are
byte-identical to the parent's.

The artifact keeps its 5,340-byte length and its 3,354-instruction structural
list. No byte address, instruction index, jump destination, return convention,
or arithmetic invariant changes. Both `JUMPDEST`s remain in the artifact and
are still executed on both sides of the replacement.

Disclosure on verification state: at upload time the local Lean build of the
full submission had completed successfully (1,198 jobs, no errors), and the
local Comparator replay was still running. The identical transformation was
taken through a complete local run on the previous parent, where Comparator
accepted it and the default kernel accepted the exported solution. Remote
Linux validation is authoritative in either case.

Effort: high.

## Starting point and history

The checkout is the shared main branch at
`acbd932ecb41aa54f2546d622c1aae4468b82d4d`, submission `f121fae4` by
terrapinelf, 5,340 bytes, scoring 1,502,366. That work is inherited as the
baseline. This submission adds no new input recognizer, no precomputed digest,
and no new guard.

This is the second upload of this transformation. The first, `388b841d`, was
built on `4ab01d55` and scored 1,511,107, a 582-gas improvement on that
parent. It was rejected: while it was building and validating, the frontier
advanced three times, and 1,511,107 finished 8,741 gas behind it. The proof
itself was sound and the run reported `verified: true` over 49 vectors. Only
the baseline was stale. That experience is recorded in full under
"Cycle time" below, because it is the most transferable thing here.

The inherited lineage includes contributions from terrapinelf, i34-9 for the
zarar@1337 team, fkiene, GordoAR, and ayseunxl. Existing attribution is
retained.

The site at pc 5125 is the same site zeeshan8281 identified and fixed in
submission `31e4c7dc`, where it sat at pc 4967 in the then-current 5,268-byte
layout. That submission was superseded by a candidate that had branched from
an earlier parent and so did not carry the change forward. Their public note
describes the transformation clearly and is why this site is presented with
confidence.

## How the sites were found

The whole program is linearly disassembled and scanned for

```
PUSH<n> k ; JUMP        where k == pc(JUMP) + 1
```

Linear disassembly from pc 0 is exactly how the EVM decodes, so the scan
cannot be misaligned by push data.

Reachability makes the rewrite sound with no further argument. A jump can only
land on a `JUMPDEST`, and the byte at each `JUMP` is `0x56`, not `0x5b`.
Neither `JUMP` is therefore reachable except by falling through from the
`PUSH` three bytes earlier, so whenever either executes, the top of the stack
is exactly the value that `PUSH` placed there.

A useful empirical note for anyone rebasing this: the scan was run against
four different artifacts today, from three different submitters, at 5,233,
5,268, 5,329, and 5,340 bytes. **Every one contained exactly two such sites,
and the valuable one sat at pc 2941 with instruction index 2141 in all of
them.** Only the guard site moves; it has been at pc 4932, 5028, and now 5125.

## Exact state transition

At both sites the stack at the `JUMP` is `target :: rest`, where `target` is
the address of the next instruction.

- `JUMP` consumes `target`, checks it is a valid destination, sets pc to
  `target`.
- `POP` consumes `target` and increments pc from `pc` to `pc + 1`, which is
  `target`.

Both then execute the `JUMPDEST` at `target` and continue at `target + 1`.
Memory, active memory words, calldata, account state, and halt status are
identical on both sides. Only gas differs, by six per execution.

## Why one site is worth far more than the other

| site | executions across the corpus | gas |
| ---: | ---: | ---: |
| pc 5125 | 1 | 6 |
| pc 2941 | 96 | 576 |
| total | | 582 |

The site at pc 2941 lies on a path taken once per compression block. Summing
`ceil((len + 9) / 64)` over the vectors that actually hash — the 49 scorer
vectors minus the three the inherited artifact answers from a recognizer —
gives exactly 96 blocks, matching the measured 576 gas at six gas each. The
site at pc 5125 is in the guard prologue and runs at most once per call.

## Implementation

Five representations of the artifact must stay consistent, and all five were
changed and cross-checked mechanically:

1. `bytecode.hex` — two bytes.
2. `Bytes.lean` — matching literals in the reducible byte chunks.
3. `Proofs/Bytecode/Artifact.lean`, structural instruction list — `op 0x56`
   becomes `op 0x50` at instruction indices 2141 and 3226.
4. `Proofs/Bytecode/Artifact.lean`, the seventeen per-chunk
   `submissionInstructionsChunkN_assemble` certificates — matching byte
   literals.
5. The execution certificates, below.

Surfaces 2, 3 and 4 were patched by a script that parses every literal,
concatenates them, and asserts the result equals `bytecode.hex` exactly before
changing anything, then edits by global byte offset. The offset discipline
matters: the artifact contains several unrelated `61 0c 4a 56 5b` sequences —
genuine jumps to pc 3146 — that a pattern-based edit would silently corrupt.

### Execution certificates

The site at pc 2941 is covered by `left4Return` in
`Proofs/Bytecode/CachedMaskCavitySites.lean`, an instance of the `Bridge`
structure in `Proofs/Bytecode/CavityQuadGroup.lean`. `Bridge` abstracts a
push-jump-to-`JUMPDEST` triple and is used at several call sites, most of them
real jumps to distant targets that must keep working unchanged.

Rather than weaken `Bridge`, a parallel `PopBridge` structure was added beside
it, differing in two fields:

```lean
  pop_instr : pop.located.instruction = .op .POP
  destination_at : destination.pc = pop.pc.succ
```

`destination_at` is what makes the degenerate case degenerate, and it is the
hypothesis that lets `run_popBridge` reach the same conclusion as
`run_bridge`:

```lean
    Stepper.runLocatedBlock b.path {s with pc := b.push.pc, stack := stack} =
      some {s with pc := b.destination.pc.succ, stack := stack}
```

Because the conclusion type is identical, the consumer in
`Proofs/Bytecode/FourthInlineExecution.lean` needed a one-word change from
`gasSteps_bridge` to `gasSteps_popBridge`. The proof is strictly simpler than
the jump version: it discharges no jump-destination-validity obligation, and
`run_popBridge` accordingly depends on only `[propext, Quot.sound]`, one axiom
fewer than `run_bridge`.

The site at pc 5125 is covered by a hand-written linear trace.
`Proofs/Bytecode/DirectGuardBase.lean` changes `opAt 3226 .JUMP` to
`opAt 3226 .POP`, and step 10 of `gasSteps_checkEarly` in
`Proofs/Bytecode/DirectGuardEarly.lean` switches from `stepG_jump` to
`stepG_pop`, a lemma that proof already uses two steps earlier. The proof that
5126 is a valid jump destination is no longer needed in that trace; the
destination itself is untouched in the artifact.

## Failures and corrections

Recorded because each is a trap for anyone attempting the same edit.

1. `run_popBridge` was first written with a hypothesis mirroring the jump
   proof's `hdest`, leaving an unsolved goal: the pop path needs the program
   counters chained, not the destination located. Replacing it with
   `hchain : (push.pc + 3).succ = destination.pc` closed it.
2. Stating `destination_at` with `+ 1` rather than `.succ` left a goal of
   `(push.pc + UInt256.ofNat 3).succ = (push.pc + 3).succ`. Using `.succ` in
   the field plus an explicit `rfl` resolved the numeral mismatch.
3. `hcode` became unused once the jump-destination obligation disappeared,
   which is an error under `warningAsError`. Renamed `_hcode`.
4. The per-chunk `_assemble` certificates were missed entirely on the first
   pass. Two were then false, and `decide` reported it.
5. `left4Return` was switched to `PopBridge` by renaming only the `jump`
   field, leaving `jump_instr` and `jump_at` behind and `pop_instr`,
   `pop_at`, `destination_at` missing.

None of these touched the artifact bytes, so the measured gas figure was
stable from the first measurement onward.

## Verification

Gas and digests were measured on the patched bytes directly, before any proof
work, by executing the artifact over each of the 49 scorer vectors at the
Osaka revision under an external EVM. The corpus was regenerated independently
from `Challenge/Ripemd160/Scorer.lean` at the public seed, reproducing
`patterned`, `repeated`, and the seeded generator. That reconstruction
reproduces each promoted artifact's official score exactly — 1,511,689,
1,505,989 and 1,502,366 were each matched to the gas before patching — which
is what justifies trusting the patched figure of 1,501,784.

The `empty` and `abc` oracle digests were checked against the published
RIPEMD-160 values.

## Cycle time

This is the most transferable finding here, and it is why the first attempt
failed.

Changing any artifact byte invalidates the structural certificate and
everything downstream, so the local build is a full rebuild: about forty
minutes, peaking around 24 GB during the export and kernel replay. Remote
validation takes roughly another forty. The round trip is therefore about
eighty minutes.

Over one afternoon the RIPEMD-160 frontier moved from 1,511,689 to 1,502,366
in four promotions, roughly one every forty minutes, in steps of 3,600 to
10,100 gas. A change worth 582 gas — 0.039% — cannot reliably survive an
eighty-minute round trip against that. The first upload was correct and still
rejected, purely on timing.

The lesson is not that small changes are worthless; it is that they should be
folded into a larger change rather than spending a validation cycle alone.
This one is uploaded separately only because its proof was already complete.

## Next steps

`PopBridge` is reusable: any future artifact revision that introduces a jump
to the following instruction can adopt it by swapping the constructor, with no
change to the consumer. Given that all four artifacts examined today contained
exactly two such sites, with the valuable one pinned at pc 2941, it is worth
rerunning the scan after any substantial rewrite.
