# Neutral-gas PUSH-width redistribution: literal headroom

Scope: measured research, not the current submitted/Lean-verified artifact.
Base: 651575-gas PC738 candidate, executable SHA-256 b9182bbcc8258af8bc5e754e1c71c7c0fa52275e282da7d02049f55fe926e095.

A search over pairs of PUSH-width changes inside exact raw-template blocks
found four independent one-unit byte-literal savings. The numeric PUSH values
are unchanged; each block loses one payload byte on one PUSH and gains one
on another. Instruction counts and each block's end PC are unchanged. All
selected PUSH widths remain nonzero, so their runtime gas is unchanged.
The local exact-byte certificates and mid-block PCs must be rechecked; this
is not an assertion that the unmodified Lean proof covers these bytes.

Base literal cost: 8194
Best independent gas-neutral pair per uniquely located raw block:
(1, 'StaggerRawPaired41Raw.lean', 2833, 2878, [(2841, 2, 234, 1), (2850, 13, 4912146077028087063374012088321, 14)])
(1, 'StaggerRawPaired33Raw.lean', 2543, 2590, [(2575, 2, 24, 1), (2560, 13, 4912146077028087063507156074528, 14)])
(1, 'StaggerRawPaired23Raw.lean', 2045, 2098, [(2060, 3, 954, 2), (2085, 1, 20, 2)])
(1, 'StaggerRawPaired21Raw.lean', 1950, 2003, [(1965, 3, 684, 2), (1975, 13, 475368975196266490020700880900, 14)])
These reductions are not necessarily additive across shared chunks.

Combined list of edits:
[(2841, 2, 234, 1), (2850, 13, 4912146077028087063374012088321, 14), (2575, 2, 24, 1), (2560, 13, 4912146077028087063507156074528, 14), (2060, 3, 954, 2), (2085, 1, 20, 2), (1965, 3, 684, 2), (1975, 13, 475368975196266490020700880900, 14)]
Combined literal cost: 8190 (base 8194).

Protected direct scorer reproduced 49 vectors in both frames, all correct.
Clean and dirty totals: {'clean': 651575, 'dirty': 651575}.
