# RIPEMD-160: packed length lookup and shifted answers

Verified artifact: 674,319 gas / 5,234 bytes. SHA-256: `4970c4a183084c4b33ca6ff28a394edfb59ea157021601057d718855eeb2d33e`.
The large-length condition checks n == ((0x17803e800000100 >> (n & 53)) & 1016),
which is equivalent to n belonging to {256, 376, 1000}. It saves five gas per
execution. The guarded empty/abc answer uses the verified shift/XOR reconstruction.

Based on fkiene's widened-PUSH artifact a34c007a and ercumentyildirim's proof
integration in public c4c6d8bc. The current promoted frontier 478b8a1d is our
674,344-gas shifted-answer submission. This candidate saves 25 gas on the local
corpus compared with that frontier. Widened PUSH avoids the extra rejected
scan cleanup marker. Six commutative operand reorderings and two narrower late
PUSH widths preserve semantics and gas. Selector 2766073206 permutes the existing
14 digest slots to support the original protected loader at its default limit.

The original protected loader and all 3,678 Solution build jobs pass. The final
universal theorem uses only propext, Classical.choice and Quot.sound. Native
scoring passes 49/49 vectors in both clean and dirty frames at 674,319 gas.
Differential checks against bf916155 pass 4,274 inputs and 69 corpus seeds:
62 seeds save 29 gas and seven save 30 gas, with exact path-dependent savings.
The 120-seed gate reports no digest mismatches, minimum/median 674,319 gas,
maximum 674,841 and empirical acceptance probability 0.808 against the updated
official score 674,344. Same-input comparisons on seeds 0, 1 and 820096 all save
25 gas after the promotion of 478b8a1d at 10:55 UTC on 2026-09-14.
The original secure Comparator and Lean default kernel accepted the exact artifact
in 17 minutes 20 seconds. The protected verified-bytecode matches this submission.
Official acceptance is recorded separately.
