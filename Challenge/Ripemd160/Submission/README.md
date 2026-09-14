# RIPEMD-160: preserve the already-zero padding prefix

Candidate: 673,491 gas / 5,233 bytes, SHA-256
`47c8de15a97b0797dc1656630da61601d1d46b4a8b56d5abe9008f5b61ab840c`.

The padding-only setup clears bytes [28,1112), using CALLDATACOPY with length
1084 and destination 28. The persistent Context.lowClear invariant already
makes bytes [0,28) zero: MLOAD at zero is below 2^32. PadZeroPrefix proves this
byte property and proves that the shortened copy produces exactly the same
memory as the prior full 1112-byte clear. StaggerPad.run_low takes this invariant
explicitly; the actual block proof supplies it from the existing context.
The complete functional table and compression models stay applicable.

CALLDATACOPY charges for 34 copied words instead of 35. PUSH1 28 costs one
more gas than PUSH0, leaving a two-gas reduction on each padding-only call.
The 21 such calls in the corpus save 42 gas relative to combined parent
8972a5b4 (673,533 gas). The branch literal changes from PUSH4 to PUSH3 to keep
the artifact length fixed. Its PC changes from 4802 to 4803; JUMPI remains at
4807 and the high block at 4808. There are still 3,788 executable instructions,
4,953 executable bytes and 280 data bytes. Assembly and payload binding pass.

The parent combines i34-9's direct 32-byte footer and packed recognition with
fkiene's plus-modulus arithmetic, our removal of its executable filler, and our
CODESIZE padding guard. The earlier shifted empty/abc answers, compression,
endian handling and table layout retain their existing attribution. This
candidate's incremental contribution is the shortened clear and its proof.
It saves 159 gas against promoted 8e0c001e (673,650) on identical corpus seeds.

The original protected loader passes. The pinned native scorer passes all
49 vectors in clean and dirty frames at 673,491 gas. Differential validation
against 8972a5b4 passes 4,358 inputs through 65,537 bytes and 69 corpus seeds;
each seed saves 42 gas. Of those inputs, 528 save two gas and 3,830 are unchanged.
The complete 120-seed gate, 2,500 additional fuzz inputs, reassembly, jumps and
CODECOPY range checks pass. The initial empirical acceptance probability is .808.

The complete Solution build passes all 3,680 jobs. Its universal candidate
theorem depends only on propext, Classical.choice and Quot.sound. No protected
scorer, compiler, generator, specification or options are changed. Independent
secure Comparator verification is in progress; official acceptance is separate.
