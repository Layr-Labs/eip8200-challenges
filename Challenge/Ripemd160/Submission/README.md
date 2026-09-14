# RIPEMD-160: packed classifier and CODESIZE padding cutoff

Candidate: 672,252 gas / 5,218 bytes, SHA-256
`464966b56b1a08ec1c5f7d4f868f0cbec8c1efb1441bd15397a93d38646a2f71`.

This combines the verified packed classifier of 2052d385 (672,336 gas) with
a cheaper cutoff for the padding-only path. The underlying Shared32/J2 parent
is ercumentyildirim's promoted 6d7f412a/fc2c0d19 at 672,499 gas. Our 13a7ebda
adds cheaper modulus initialization and the shortened prefix clear; the packed
classifier contributes a further 25 gas and this cutoff contributes 84.

The old padding guard computes ISZERO(CALLDATASIZE >> 29). The new guard uses
CALLDATASIZE < CODESIZE, with this exact artifact's size of 5218. It costs seven
gas instead of eleven. A length below 5218 also has a zero high length word,
so the fast padding table is valid. Larger aligned inputs use the parent's
existing general padding writer, whose proof is generalized to the new cutoff.
The resulting hash remains correct for every input admitted by CalldataFits.

The literal holding packed 0x80 markers widens from PUSH19 to PUSH21 to absorb
the two bytes freed by the new guard. The branch starts at PC4812 as before;
all subsequent physical instruction positions and the payload base are fixed.
There are 3765 executable instructions, 4938 executable bytes and 280 payload
bytes. The classifier retains the loader-compatible operand order from 2052d385.

StaggerPad.highZero_true_iff characterizes the new comparison as n.toNat < 5218.
Its highZero_true_imp lemma proves that the high length word is zero on that
route. ColdOrdinaryPrepare uses this implication to identify the exact padding
memory. ColdHighModel and the top-level Cold route use the complementary bound.
The existing full general-padding memory and output proofs apply without any
assumption that inputs are small. Submission-local DataStepper and PadLift
include our previously verified CODESIZE soundness extension. Protected EVM
semantics, compiler, generator, scorer, specification and options are unchanged.

The full Solution build passes all 3714 jobs. The candidate theorem depends
only on propext, Classical.choice and Quot.sound. The original protected loader
passes. The original native scorer passes all 49 corpus vectors in clean and
dirty frames at 672,252 gas. The mandatory 120-seed correctness gate, 2500 fuzz
cases, executable reassembly, runtime jumps and CODECOPY bounds pass.

Expanded differential checking against 2052d385 passes 4358 inputs and 69
corpus seeds. All corpus seeds save 84 gas. Of the expanded inputs, 3830 are
unchanged and 508 save four gas. Twenty large aligned inputs use the additional
general padding path and cost 1014 to 1073 gas more, while returning the same
correct digest. This is a corpus gas improvement; it does not reduce gas for
every input. Independent secure Comparator verification is pending.

Attribution: the Shared32/J2/general cold route is ercumentyildirim's work;
the compact five-byte classifier constant is i34-9's refinement of our earlier
lookup. The plus-modulus idea credits fkiene, with our removal of its filler.
The shortened clear, its memory proof, the CODESIZE proof support and this
cutoff integration are our work. Earlier compression, endian and digest payload
contributions retain their provenance. Only Submission files are changed.
