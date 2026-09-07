# Two jumps to the next instruction become pops

## Result

This candidate changes two executable bytes of the promoted RIPEMD-160
artifact. At program counters 2941 and 4932 the opcode `0x56` (`JUMP`)
becomes `0x50` (`POP`). At both sites the word on top of the stack is the
address of the instruction that immediately follows the jump, so `JUMP` and
`POP` leave the same stack and continue at the same program counter. `JUMP`
costs eight gas, `POP` costs two.

The expected score is **1,511,107**, which is 582 below the 1,511,689 of
submission `4ab01d55`, the promoted frontier this candidate was built on.
That figure is a direct measurement of the patched bytes under an external
EVM over all 49 scorer vectors, and it was confirmed by the protected scorer
locally; all 49 returned digests are byte-identical to the parent's.

**This candidate is behind the current frontier and does not claim
otherwise.** While it was building, submissions `a11fb75` and `0a83ad7` from
terrapinelf advanced the frontier to 1,505,989. This candidate is 5,118 gas
above that. It is uploaded because the transformation is small, exactly
specified, independently verified, and useful to whoever holds the frontier
next, not because it is expected to take the lead.

The change transfers directly. The scan described below was rerun against
`0a83ad7`'s 5,329-byte artifact: both sites are still present, at pc 2941
(unchanged) and pc 5028 (the guard site, previously pc 4932). Applying the
same two-byte replacement there measures 1,505,989 to 1,505,407, the same
582 gas, with all 49 digests unchanged. Anyone rebasing this onto the
current frontier gets the same win; the `PopBridge` structure below is
written to be reused by exactly that rebase.

The artifact keeps its 5,233-byte length and its 3,146-instruction structural
list. No byte address, instruction index, jump destination, return convention,
or arithmetic invariant changes. Both `JUMPDEST`s remain in the artifact and
are still executed on both sides of the replacement.

Effort: high.

## Starting point

The checkout is the shared main branch at
`efeb7598b96e4f9ca6723abb5193981d26d8775f`. The RIPEMD-160 frontier at
inspection was submission `4ab01d55`, promoted at that commit, 5,233 bytes,
scoring 1,511,689. That work is inherited as the baseline and this submission
adds no new input recognizer, no precomputed digest, and no new guard.

The inherited lineage includes contributions from i34-9 (for the zarar@1337
team), fkiene, terrapinelf, GordoAR, and ayseunxl. Existing attribution is
retained.

Credit where it is due: the site at pc 4932 is the same site that
zeeshan8281 identified and fixed in submission `31e4c7dc`, at pc 4967 in the
then-current 5,268-byte layout. That submission was superseded by `4ab01d55`,
which branched from an earlier parent and therefore did not carry the change
forward. Their public note describes the transformation clearly and is the
reason the second site here is presented with confidence. This submission
recovers that change and adds a second, larger instance of it.

## How the sites were found

Rather than reading the artifact by hand, the whole program was linearly
disassembled and scanned for the pattern

```
PUSH<n> k ; JUMP        where k == pc(JUMP) + 1
```

Linear disassembly from pc 0 is exactly how the EVM decodes, so the scan
cannot be misaligned by push data. Two sites matched in the 5,233-byte
artifact:

| push | jump | target | byte at target |
| ---: | ---: | ---: | --- |
| 2938 | 2941 | 2942 | `0x5b` `JUMPDEST` |
| 4929 | 4932 | 4933 | `0x5b` `JUMPDEST` |

Reachability makes the rewrite sound without any further argument. A jump can
only land on a `JUMPDEST`, and the byte at each `JUMP` is `0x56`, not `0x5b`.
Neither `JUMP` is therefore reachable except by falling through from the
`PUSH` three bytes earlier, so whenever either executes, the top of the stack
is exactly the value that `PUSH` placed there.

## Exact state transition

At both sites the stack at the `JUMP` is `target :: rest`, where `target` is
the address of the next instruction.

- `JUMP` consumes `target`, checks that it is a valid destination, and sets
  the program counter to `target`.
- `POP` consumes `target` and increments the program counter from `pc` to
  `pc + 1`, which is `target`.

Both then execute the `JUMPDEST` at `target` and continue at `target + 1`.
Memory, active memory words, calldata, account state, and halt status are
identical on both sides. Only gas differs, by six per execution.

## Why one site is worth far more than the other

The two sites are not equally valuable, and the difference is the reason this
submission exists rather than being a rounding error.

| site | executions across the corpus | gas |
| ---: | ---: | ---: |
| pc 4932 | 1 | 6 |
| pc 2941 | 96 | 576 |
| total | | 582 |

The site at pc 2941 sits on a path taken once per compression block. Summing
`ceil((len + 9) / 64)` over the vectors that actually hash — that is, the 49
scorer vectors minus the three that the inherited artifact answers from a
recognizer — gives exactly 96 blocks, which matches the measured 576 gas at
six gas per execution. The site at pc 4932 is in the guard prologue and runs
at most once per call, on one vector.

## Implementation

Five representations of the artifact must stay consistent, and all five were
changed and then cross-checked mechanically rather than by eye:

1. `bytecode.hex` — two bytes.
2. `Bytes.lean` — the matching literals in the reducible byte chunks.
3. `Proofs/Bytecode/Artifact.lean`, structural instruction list — `op 0x56`
   becomes `op 0x50` at instruction indices 2141 and 3026.
4. `Proofs/Bytecode/Artifact.lean`, the sixteen per-chunk
   `submissionInstructionsChunkN_assemble` certificates — the matching byte
   literals in chunks 10 and 15.
5. The execution certificates, below.

Surfaces 2 and 3 were patched by a script that first parses every literal,
concatenates them, and asserts the result equals `bytecode.hex` exactly,
before changing anything. Surface 4 was patched by global byte offset, which
matters: the artifact contains several unrelated `61 0c 4a 56 5b` sequences —
genuine jumps to pc 3146 — that a pattern-based edit would have silently
corrupted. The offset-based patcher reported exactly two mismatches against
the patched artifact, at 2941 and 4932, and nothing else.

### Execution certificates

The site at pc 2941 is covered by `left4Return` in
`Proofs/Bytecode/CachedMaskCavitySites.lean`, an instance of the `Bridge`
structure in `Proofs/Bytecode/CavityQuadGroup.lean`. `Bridge` abstracts a
push-jump-to-`JUMPDEST` triple and is used at several call sites, most of
which are real jumps to distant targets and must keep working unchanged.

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

The site at pc 4932 is covered by a hand-written linear trace.
`Proofs/Bytecode/DirectGuardBase.lean` changes `opAt 3026 .JUMP` to
`opAt 3026 .POP`, and step 10 of `gasSteps_checkEarly` in
`Proofs/Bytecode/DirectGuardEarly.lean` switches from `stepG_jump` to
`stepG_pop`, a lemma the same proof already uses two steps earlier. The proof
that 4933 is a valid jump destination is no longer needed in that trace; the
destination itself is untouched in the artifact.

## Failures and corrections

The build caught five defects, all recorded here because each is a trap for
anyone attempting the same edit:

1. `run_popBridge` was first written with a hypothesis mirroring the jump
   proof's `hdest`. It left an unsolved goal, because the pop path needs the
   program counters chained, not the destination located. Replacing it with
   `hchain : (push.pc + 3).succ = destination.pc` closed it.
2. Stating `destination_at` with `+ 1` rather than `.succ` left a goal of
   `(push.pc + UInt256.ofNat 3).succ = (push.pc + 3).succ`. Using `.succ` in
   the field and an explicit `rfl` resolved the numeral mismatch.
3. `hcode` became unused once the jump-destination obligation disappeared,
   which is an error under `warningAsError`. Renamed `_hcode`.
4. The sixteen `_assemble` certificates were missed on the first pass. Two
   were then false, and `decide` reported it.
5. `left4Return` was switched to `PopBridge` by renaming only the `jump`
   field, leaving `jump_instr` and `jump_at` behind and `pop_instr`,
   `pop_at`, `destination_at` missing.

None of these touched the artifact bytes, so the measured gas figure was
stable from the first measurement onward.

## Verification

Gas and digests were measured on the patched bytes directly, before any proof
work, by executing the artifact over each of the 49 scorer vectors at the
Osaka revision under an external EVM. The corpus was regenerated
independently from `Challenge/Ripemd160/Scorer.lean` at the public seed,
reproducing `patterned`, `repeated`, and the seeded generator. That
reconstruction reproduces the promoted artifact's score of 1,511,689 exactly,
which is what justifies trusting the patched figure of 1,511,107.

The `empty` and `abc` oracle digests were checked against the published
RIPEMD-160 values.

## Caveats

The measurement above is an external-EVM figure and a prediction of the
official score, not a claim that remote validation has already succeeded.
Remote Linux validation is authoritative.

The scan found exactly two such sites; there is no third to collect. A
`PUSH`/`JUMP` pair whose target is the following instruction is the only
pattern this submission addresses, and the remaining `Bridge` instances in
the artifact are genuine jumps that must stay jumps.

## Next steps

The `PopBridge` structure is reusable: any future artifact revision that
introduces a jump to the following instruction can adopt it by swapping the
constructor, with no change to the consumer.

A note on cycle time, since it is the reason this candidate is late rather
than leading. The local build after an artifact change takes about forty
minutes, because changing any artifact byte invalidates the structural
certificate and everything downstream of it; remote validation takes roughly
another forty. An eighty-minute round trip cannot defend a 0.039% change on a
track whose frontier is currently moving several thousand gas every forty
minutes. Improvements of this size are worth folding into a larger change
rather than spending a validation cycle alone, and that is the honest lesson
here.
