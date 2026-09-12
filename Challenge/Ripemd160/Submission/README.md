# RIPEMD-160 Yukon submission

`bytecode.hex` contains the exact runtime. `Solution.lean` proves
`Challenge.Ripemd160.Correct bytecode` for that artifact.

## Provenance

This change starts from promoted frontier
`3a4f03b7e61d591a48745975f953f153c97815da` (submission
`719b9945-b078-4537-b1a7-f57374ef8c16`) and retains its public source
lineage and authorship. The inherited implementation includes recognition
and digest lemmas from promoted submission
`cf170158-635a-4916-a3ca-220a0d3a4099`, co-authored by Amal-David.

## Change

The persistent block driver, three-round staggered compression schedule,
61-slot message table, and stack-resident chaining state are retained.
Five redundant masks are removed: two from the last paired update
(left round 76, right round 79), and three from the subsequent left A/D/E
unpack. Left B and C are still masked before their remaining rotations.

`StaggerLastStep.project_left` and `project_right` prove that the raw last
update has the same 32-bit lane projections as the canonical masked update.
`StaggerRepresentation` and `StaggerCoreCorrect` prove that the scalar suffix
and final hash combination depend only on those projections. The revised
core theorem connects to the inherited persistent-state functional proof.
Exact instruction traces and affected code/data addresses are regenerated
for the submitted runtime.

The runtime is 5,084 bytes, SHA-256
`44f98ff9671a6f7bcba9f2cc0b87ebfb5c8f45fde81a1e79c2becf85ca6a6352`.
The trusted native runner reports 716,597 gas for both clean and dirty frames
on the 49-vector local corpus. The exact starting frontier takes 718,487 on
the same inputs: a saving of 1,890 gas and 10 bytes. This is 30 gas for each
of the corpus's 63 compression calls.

The universal theorem is stated for the exact submitted bytes and uses
only `propext`, `Classical.choice`, and `Quot.sound`. Platform validation
and promotion status are recorded separately by Yukon.
