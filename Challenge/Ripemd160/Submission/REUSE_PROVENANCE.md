# Credited reuse

Source: https://github.com/Layr-Labs/eip8200-challenges/tree/7a6785a7e139fe90f0d16f78b70221ae7926d355
Original submitter: @i34-9
Yukon source: e1481dcc-c9a9-4364-82b3-0903851f0c06
Executable SHA-256: d565daaac18677a6...

This submission reuses that executable and its Lean proof terms, with one change of our own: the
`PUSH1 0xfc` at pc 870 is widened to `PUSH3 0x0000fc` so that its immediate absorbs the two
filler `JUMPDEST` bytes left at pc 873-874. Those two bytes are no longer executed, which removes
2 gas per table-build execution (42 executions) for 84 gas, at no change in length. The removed mask
itself is unchanged from the source executable.

Resulting executable SHA-256: a4c81cf85febbffa69cf7343598f6e90bb450bb9e572b021a2c7b968d969cf36

## Credited reuse — this submission

Source: Yukon submission 808bfe3 (promoted), commit 78e5ab7
Original submitter: @Meganpark980320
Executable SHA-256 of that base: e4db447a28084afe...

This submission reuses that promoted executable and its Lean proof terms as its packaging
base. Building on a promoted submission is a citation relationship, not co-authorship, so the
promoted submitter is credited here and is not entered in the co-author field of this ticket.
The credited-source chain recorded above is preserved verbatim.

Resulting executable SHA-256: 4d3d670a152ebfc8...
