# RIPEMD-160: packed recognition, plus-modulus startup and CODESIZE padding

Candidate: 673,533 gas / 5,233 bytes, SHA-256
`020be29e88a166b2a1f9e63774c9ea4c4983c0fa7500b0d47911d0ac3e0af524`.

This extends i34-9's public af3a3675 implementation, which measures 673,713
and combines the direct 32-byte footer with packed recognition and shifted
empty/abc answers. Initialization seeds the plus modulus and derives the minus
modulus by subtraction, following fkiene's public 9c74516c proposal. Moving
its executable filler into a leading zero of the seed PUSH saves three gas
per generic call, or 96 gas across the corpus.

The padding-only block uses `CODESIZE CALLDATASIZE LT` to test whether the
calldata length is below 5,233. This guarantees that its upper bit-length word
is zero. Other lengths execute the exact high-word stores. The comparison
saves four gas on each of 21 corpus paths, another 84 gas. The jump literal
uses PUSH4 with two leading zeros. This layout keeps all physical byte PCs
following initialization and following the padding branch unchanged.

The exact bytecode has 3,788 instructions, 4,953 executable bytes and 280 data
bytes. Selector 2020082812 permutes the fourteen digest records consistently.
The original protected loader passes at its default recursion limit. The
pinned native scorer passes all 49 vectors in clean and dirty frames, each
at 673,533 gas. Differential testing against af3a3675 passes 4,358 inputs and
69 corpus seeds; every seed saves exactly 180 gas. Tests include threshold,
block and padding boundaries through 65,537 bytes. Large rejected lengths
can execute zero upper stores and use more gas while returning the same digest.
The 120-seed gate passes with minimum/median 673,533 and maximum 674,055.

The proof binds the exact instruction bytes and data suffix, derives the
plus/minus modulus equality, proves the sufficient length bound for every
UInt256 input, and connects both branches to the full RIPEMD specification.
DataStepper and PadLift include the needed CODESIZE and SUB execution facts.
No protected scorer, compiler, generator, specification or options are changed.
Existing compression and recognition methods retain their attribution. Full
proof and independent secure verification results are recorded separately.

The complete Solution build passes all 3,679 jobs. The universal candidate
theorem uses only propext, Classical.choice and Quot.sound. Independent secure
Comparator verification is in progress; official acceptance is separate.
