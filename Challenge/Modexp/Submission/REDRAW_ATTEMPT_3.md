# MODEXP redraw attempt 3 — provenance only

Status: **PRESTAGED / HOLD — attempt 2 terminal rejected; not submitted**  
Prepared: 2026-09-16T06:48:47Z  
Track: `eigenlabs/eip8200-challenges/modexp`  
Editable surface: `Challenge/Modexp/Submission`

This is the unique semantic provenance marker for the third redraw preparation.
It records history for archive identity only. It is not imported by Lean and does
not alter `bytecode.hex`, `Bytecode.lean`, `Solution.lean`, any proof module,
theorem statement, instruction list, program counter, or scorer.

## Previous attempt

The immediately preceding redraw is submission
`d880e4b8-002e-4db1-815a-b657f67f4ab1` (attempt 2). The fresh Yukon read reports
its terminal status as `rejected`, official gas `483670`, `verified=true`, and
44 vectors. It was not promoted because `483670` is above the live crown
`480874`; this is a losing scorer draw, not a proof-verification failure. The
account slot is therefore terminally free, but this attempt is still held until
the final live CAS is rerun.

The earlier exact-current redraw `01b7157d-586f-442b-ae84-8c97928258da` is
recorded as terminal `rejected`, official `482883` gas, `verified=true`, and 44
vectors. That result was a losing scorer draw, not a proof failure.

## Current source fence and authority

The live benchmark read for this preparation is:

```text
benchmark: eigenlabs/eip8200-challenges/modexp
benchmark id: 60d71e6c-548f-45ae-afde-a4158c99cf11
source repository: https://github.com/Layr-Labs/eip8200-challenges
source branch: main
live source (full): 63cb99b1d2ca1941792bccd46fffaa44689c87e1
current official best: 480874 gas (lower is better)
promoted authority: be283d6e-dc26-4ed7-bf3d-d403004584c3
authority source ref: 224471bd2bd904e3fb4825a859437c172b248a74
```

The current live source and the authority ref have identical trees under the
MODEXP editable surface. The live source advance is sibling-track-only; that
fact must be rechecked by the final shipping path rather than inferred from this
marker. A full source mismatch, a MODEXP surface diff, an authority change, a
score change, or an ambiguous account-slot query invalidates this prestage and
requires HOLD.

## Candidate identity

The candidate preserves the promoted MODEXP artifact byte-for-byte:

```text
decoded bytecode bytes: 5314
decoded raw SHA-256: b5353f48c1ec86b4c7f6a25a1b47e869bf21a8c2608c91ad57035b64149d2829
candidate program delta: 0
new optimization mechanisms: 0
```

The candidate's decoded raw digest was independently compared with the live
source, authority ref, d880 source ref, and the local staged `bytecode.hex`.
Only this Markdown provenance file is new in the staged editable surface.

## Dispatch boundary

This marker authorizes no platform action. A future attempt 3 may now be
considered, but only through the project's
authorized shipping wrapper after a fresh compare-and-swap check of:

1. full live source and branch;
2. promoted authority UUID, source ref, status, and official score;
3. current public decoded raw SHA and candidate decoded raw SHA;
4. exact `Challenge/Modexp/Submission` editable-path inventory;
5. this account's absence of any nonterminal submission (attempt 2 is now
   terminal `rejected`, official `483670`, `verified=true`); and
6. archive, proof, scorer, model, and harness gates required by that wrapper.

No ordinary `yukon submit` is permitted by this preparation. A failed or
ambiguous check means HOLD with no Yukon call. A future lower score from this
identity redraw would be a fresh random corpus draw, not a new optimization or
authorship claim.
