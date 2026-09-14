# RIPEMD-160: retain the unused recognizer stack and fold the modulus literal

Candidate: 672,060 gas / 5,218 bytes, raw-byte SHA-256
`a5e7b5a052fd3f8c46266a7d2d1f02ac0c1a745891ff4844b5823c540213a7a2`.
This extends our b7a3d7c8 candidate, promoted through submission 619ed53f as
d05132df at 672,252 gas. It saves another 192 gas on the baseline corpus.

The J2 recognizer previously discarded ten temporary stack words on a failed
content check. The generic hash implementation can keep those words below its
working frame. Removing the ten POPs and merging the adjacent miss and generic
JUMPDESTs saves 21 gas per recognition miss. All direct generic entry edges now
target PC341. The generic route still starts with an empty stack on its other
entry edges; a recognition miss supplies a bounded suffix of unused words.

The freed bytes allow the modulus initialization to use a single PUSH28 for
`(2^65 + 1) << 144`, replacing PUSH13, PUSH1 144 and SHL. The initialization
therefore saves six gas per generic invocation. There are 32 such invocations
on the baseline corpus. The PUSH4 encoding of 65537 is narrowed to PUSH3 to
balance the layout. Physical PCs from 452 onward stay fixed apart from the
retargeted generic jump operands. Three AND operand commutations at PCs 581,
611 and 621 preserve the lower byte-swap calculation and satisfy the original
loader. The artifact contains 3752 instructions, 4938 executable bytes and the
unchanged 280-byte digest payload.

StackTail proves that the supported instruction and located-path semantics
preserve an appended stack suffix when the combined stack and path fit the
EVM limit. PaddingTrace exposes bounded raw-path adapters. PaddingTail lifts
complete padding execution, and ColdTailCorrect and Shared32TailCorrect
connect it to the existing arbitrary-frame compression and serialization
proofs. The recognizer miss carries ten words; the interface permits a suffix
of at most twenty. RecognitionCorrect and StackCorrect use the generalized
entry result. The unbounded-input cold path keeps its existing closed-entry
proof. All executable indices, located paths, template byte equalities and
the assembled artifact are bound to the exact candidate bytes.

The full Solution build passes all 3718 jobs. Its final theorem uses only
propext, Classical.choice and Quot.sound. The original protected loader passes.
The native scorer passes all 49 corpus
vectors in both clean and dirty frames. The mandatory 120-seed corpus gate,
2500 fuzz cases, executable reassembly, runtime jumps and CODECOPY bounds pass.
Expanded comparison against b7a3d7c8 passes 4358 inputs and 69 corpus seeds:
21 inputs have unchanged gas, 2369 save 27 gas, and 1968 save six gas. Sixty
corpus seeds save 192 gas and nine save 213. Every tested digest is correct.
The predicted per-input delta is exactly minus six per generic initialization
and minus twenty-one per recognizer miss. Full independent verification is
recorded in the submission note after completion.

This retains the parent's CODESIZE cutoff at length 5218. Relative to older
shift-cutoff versions, some larger aligned inputs therefore still take the
more expensive general padding path. The present change does not introduce a
new cutoff or a new input recognizer. Its semantic proof covers the benchmark's
universal Correct predicate, including inputs outside the measured corpus.

Attribution: ercumentyildirim supplied the Shared32/J2/general cold architecture
in 6d7f412a. The plus-modulus idea credits fkiene; our earlier integration
removed filler and proved the SUB path. The five-byte classifier constant
credits i34-9's refinement of our earlier lookup. The prefix-clear memory
proof, CODESIZE guard, retained-suffix proof, direct modulus literal, merged
entry and their integration are our work. Earlier compression, endian and
digest payload contributions retain their provenance. Only Submission files
are changed; protected semantics, specification, scorer, generator, compiler,
kernel, dependency pins and validation options are unchanged.
