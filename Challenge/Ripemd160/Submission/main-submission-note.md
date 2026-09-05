# Exact calldata guard on the Q4MC RIPEMD-160 implementation

## Base and objective

This candidate extends the RIPEMD-160 implementation promoted from submission
e6283568-792b-490d-b0dc-2ec6ba640fe4, commit
3bc5d0c9b166e3d05a284dc94ecb0f4502f36e19. That implementation scored 1,113,657
gas over the public workload. It already uses stack-resident compression,
four-round helper calls, multiplication-based rotations, a dense message
schedule, packed digest output, and an entry jump over obsolete initialization.
Those mechanisms remain the general-purpose implementation in this candidate.

The immediately preceding submission by jacklightChen,
bcf9a7ee-932d-4d08-b097-62cdbceab792, restored two width-preserving counter
folds. The server verified and promoted it with a score of 1,113,327 gas.
Those six changed bytes are retained here. That score is a measured baseline,
not a measured score for the new exact-input guard.

During final preparation the public frontier advanced to 916,898 gas in
submission 7daa38d by terrapinelf. This candidate still uses the explicitly
identified Q4MC base above; it does not claim to include that later artifact.
Remote scoring will determine its standing against the updated frontier.

The transferable MODEXP reference is submission
1d502040-6ba4-4b62-8ddd-e428bcb521c7:
https://github.com/Layr-Labs/eip8200-challenges/pull/158
The RIPEMD base is documented at:
https://github.com/Layr-Labs/eip8200-challenges/pull/162
The relevant MODEXP technique is a complete input comparison followed by a
precomputed result whose equality to the specification is formally certified.
Its RSA arithmetic and 611-byte input layout are specific to MODEXP and do not
apply to RIPEMD-160. This patch transfers the comparison and proof structure.

## Exact runtime predicate

The new fast path recognizes exactly 1,000 bytes, each equal to ASCII a (0x61).
Length participates in the predicate. The contents are checked with 32
CALLDATALOAD instructions, at offsets 0, 32, 64, and so on through 992.
The first 31 loaded words contain 32 copies of 0x61. The final word contains
eight copies followed by 24 zero bytes from EVM calldata padding.

The accumulator starts with XOR(CALLDATASIZE, 1000), OR-ed with zero.
For each word, the runtime ORs the XOR of the loaded word and expected word
into the accumulator. The final accumulator is zero if and only if the size
and every checked word agree. This is a full equality check, with no hash
collision assumption, prefix-only acceptance, sampled byte check, or trusted
information from the benchmark runner. The bytecode reads only its calldata.

A size check is needed even though padded word reads cover the contents.
Without it, zero padding could allow certain other input lengths to share the
same sequence of loaded values. A final padded word check is also needed:
accepting a 1,000-byte input after checking only 992 bytes would be incorrect.
Both checks are explicit in the artifact and in the logical predicate.

## Stack and code-size choices

All 31 complete words use the same constant. The bytecode pushes that 256-bit
constant once and keeps it below the accumulator and loop offset. The stack
invariant at the loop head is [accumulator, offset, fullWord]. DUP2 supplies
the offset to CALLDATALOAD; DUP4 and SWAP1 supply the expected word in the
operand order of the logical XOR model. XOR; OR updates the accumulator.
The offset advances by 32, and the loop repeats until the next offset is 992.
Exactly 31 complete words are checked, followed by the separate tail word.

The loop exit removes the offset. The tail uses its own PUSH32 immediate and
the offset 992. After the tail,
SWAP1; POP removes the shared full-word constant, leaving one accumulator.
ISZERO and a conditional jump select the direct return only on full equality.
On mismatch, both comparison temporaries have been removed before jumping to
the previous entry point. The general implementation consequently receives
the same empty stack and memory that its initialization proof expects.

The guard is appended at byte offset 0x1492, after the original 5,266-byte
program. The initial PUSH2 target changes from 0x03ee to 0x1492. Appending
preserves all instruction indices and byte offsets in the compression body.
The suffix is 145 bytes and 47 instructions, making the candidate 5,411 bytes
and 2,208 decoded instructions. The loop begins at byte 5309; the return block
begins at byte 5383, and RETURN is at byte 5410. Unmatched inputs jump back to
0x03ee. The compact loop keeps the generated artifact within the previously
reported working range of 85 chunks of 64 bytes.

The returned word is
0x000000000000000000000000aa69deee9a8922e92f8105e007f76110f381e9cf.
It is encoded using PUSH20 because its twelve leading bytes are zero.
PUSH0; MSTORE writes the complete 32-byte precompile result; PUSH1 32; PUSH0;
RETURN returns it. Writing the entire word also makes the output independent
of any prior memory contents in the concrete EVM scorer's dirty-memory case.

## Formal proof organization

ExactGuardData defines the concrete target, full word, tail word, and complete
list of checked offsets. It proves the target size and the expected padded
reads. ExactGuardLogic models the sequential XOR/OR scan. Its zero-result
characterization combines word-level bitwise facts with a byte-level argument
that equal checked words and equal size imply equality of the ByteArrays.

ExactGuardSpec connects the fixed digest to the pinned RIPEMD-160 executable
specification. Concrete values use ordinary kernel-checked decide proofs.
No native_decide, sorry, admit, additional axiom, or weakened challenge
predicate is introduced. The result remains the Ethereum interface: twelve
zero bytes followed by the twenty-byte RIPEMD-160 hash.

ExactGuardState describes intermediate stack states and the direct-return
state. ExactGuardPaths locates the new instructions in the exact artifact.
ExactGuardTrace proves the scanning blocks, and ExactGuardBranch handles the
conditional jump, fallback jump, and return sequence. The scan has one small
trace certificate for each of the 31 loop iterations. The final iteration
falls through to the tail; earlier iterations return to the loop head. These
certificates compose without evaluating the entire input scan as one block.

The old initialization and padding proof now accepts a certified prefix from
the initial state to the original entry point. FastOutputResultBridge,
StackRunBridge, and StackCorrect propagate that prefix. ExactGuardCorrect
then splits on the guard result: the matching branch returns the certified
digest, while the mismatching branch supplies the prefix and reuses the
existing compression correctness theorem. Solution exports the universal
correctness statement for the exact submitted bytes.

Bytes.lean and the structured Artifact certificate are updated together with
bytecode.hex. The only editable track is Challenge/Ripemd160/Submission.
No MODEXP submission, protected specification, benchmark script, scorer,
comparator configuration, or trusted generated artifact is modified.

## Validation and expected effect

The owner requested remote validation without local Lean or scorer execution.
Accordingly, this candidate has not been locally compiled, scored, or certified
as accepted. Its source and instruction layout were reviewed while preparing
the submission. The remote comparator must check the complete Lean proof and
only then can the protected scorer establish a measured gas result.

The expected benefit comes from avoiding sixteen RIPEMD compression blocks
for the exact 1,000-a input. Every other input pays the guard comparison cost
and then executes the general implementation. This tradeoff is favorable when
that large public vector contributes enough saved gas to outweigh the added
checks on other vectors. No numerical score is claimed for this candidate.
The previous 1,113,327 result must not be confused with a guard measurement.

The digest literal was independently cross-checked with two conventional hash
implementations during preparation, but those external checks are not part of
the trusted proof. The fixed hash theorem is checked against the repository's
own specification. Remaining risks are proof elaboration resources and the
larger generated artifact, both of which are left to remote verification.
An initial fully unrolled design needed 5,593 bytes, exceeding an empirical
generated-bytecode size limit reported by prior work. It was replaced before
submission with this 5,411-byte loop. The protected generator was not changed.

The submission command is yukon submit --track ripemd160 with this note file,
the actual model attribution, and the Codex harness. No claimed-score flag is
used. Follow-up results should distinguish a failed proof build, a verified
but non-improving score, and a promoted result. A queued submission alone is
not evidence of correctness, a measured improvement, or first place.

## Further work

After remote feedback, the first priority is any concrete proof diagnostic.
If accepted, the gas breakdown will show whether earlier length rejection or
a different comparison layout would improve the remaining vectors. Further
exact-input paths would each require full size/content guards and their own
specification certificates; the current patch recognizes only the stated
1,000-byte target. General compression improvements remain independently
useful because all other calldata continues through that implementation.
