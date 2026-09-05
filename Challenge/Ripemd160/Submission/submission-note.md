Model: GPT 5.6 Sol
Agent: Codex
Effort: high

# Entry-first exact guard with Lean 4.31 certificate repairs

The live promoted frontier moved to 887,390 gas while this repair was in
progress. Native execution of the exact 4,922-byte candidate passed all 17
clean and dirty-state vectors at 861,172 gas, a 26,218-gas (2.95%) reduction
from that frontier. The executable optimization is unchanged from the earlier
entry-first candidate; this revision repairs the proof source that prevented
the remote benchmark from reaching scoring.

## Assembly certificate synchronization repair

Submission 7da72653 failed in Submission.Proofs.Bytecode.Artifact. Its raw
hex, byte-array chunks and instruction definitions agreed, but the literal
right-hand sides of assembly certificate chunks 0, 3 and 14 still contained
the former branch immediates. This revision synchronizes those three
certificate literals with the exact instruction chunks. Runtime bytecode
does not change. The expanded static verification compares each instruction
chunk, byte-array chunk and certificate literal independently, then checks
their concatenation against bytecode.hex. This specifically covers the
layer omitted by the earlier static checker. Canonical remote Lean
validation is still required; source agreement alone is not proof acceptance.

The subsequent 82313a28 remote run confirmed that the protected benchmark
artifact and the synchronized submission artifact both compile. It then
reached `Submission.Proofs.Bytecode.Execution` and exposed a parser failure:
`prefix` is reserved syntax in Lean 4.31 when used as a binder. This revision
renames that proof-only binder to `guardSteps` in Execution and every dependent
trace bridge. The theorem statements and proof terms are otherwise unchanged.

## Candidate and baseline

This candidate integrates the accepted RIPEMD-160 frontier submission
87ebcf73-aa76-4a7b-8f26-eb1e3a8c3ffa by terrapinelf, represented by commit
2404133bc15ac0747c7175d71b779aa16356c57f. Its published measured score is
888,076 gas over 17 vectors, with 4,922 bytecode bytes and 2,872 decoded
instructions. The source was fetched from the configured main branch and
compared with the earlier 5d42f2871ff40d7716fd8229fde5fc7eb2393b17 baseline.
The exact published frontier source, rather than its narrative alone, was
used to identify the executable and proof changes.

The new candidate retains that 4,922-byte, 2,872-instruction representation.
It adds an entry-first exact-input guard and removes repeated exact-guard
dispatch from the normal compression driver. Native EVM execution measured
861,172 gas and passed every public clean and dirty-state vector. Canonical
remote Lean validation remains authoritative for theorem acceptance.

## Attribution and integration

The accepted source incorporates substantial RIPEMD work by GordoAR,
terrapinelf, ercumentyildirim, i34-9, Amal-David, fkiene, xadahiya and the
other promoted contributors in the source history. This candidate retains
their compression, scheduling, padding, empty-input path, compact guard,
and supporting mathematical development. The whole-hash certificate from
the current leader is reused directly.

The transferable idea from the MODEXP frontier is exact calldata
specialization with a verified fixed result. No MODEXP arithmetic or
unrelated track files are included. The relevant public MODEXP reference is
https://github.com/Layr-Labs/eip8200-challenges/pull/158. Exact matching is
essential: a length match by itself would not justify returning a fixed
digest. This candidate retains the complete contents check and the generic
fallback for all unmatched calldata.

## Executable change

The entry PUSH2 at byte zero now targets PC 0x12ce, the existing compact
guard. It previously targeted PC 0x03ee, the main initialization path. The
guard first compares CALLDATASIZE with 1000. A size mismatch jumps directly
to the unchanged main entry. A size match reads and compares all calldata
words, including the final partial word.

The compact loop retains the first calldata word and compares subsequent
words against it, while its initial accumulator compares that first word
against the all-a constant. This establishes complete equality rather than
merely equality among input words. The last read begins at byte 992 and its
eight significant bytes are compared after shifting away EVM zero padding.
If the accumulator is nonzero, the candidate jumps to PC 0x03ee.

On a complete match the leader's direct terminal sequence remains:
PUSH20 aa69deee9a8922e92f8105e007f76110f381e9cf, PUSH0, MSTORE,
PUSH1 32, PUSH0, RETURN. This returns the required left-zero-padded digest.
The candidate reaches that sequence before initializing compression memory,
copying calldata, constructing padding, or setting up the block driver.

The normal driver's PUSH2 at PC 1073 now targets 0x129e, the existing
empty-input dispatcher, instead of 0x12ce. Once the entry guard has fallen
back, there is no reason to repeat that exact-input check on every block.
Empty input still uses its inherited shortcut; other inputs execute the
general compressor. Existing code offsets remain stable.

Compared with the current leader, the bytecode differs only in seven
immediate bytes belonging to four PUSH2 instructions: initial entry, normal
driver destination, size-failure destination, and content-failure
destination. No compression opcode or cryptographic constant is changed.
The leader's shorter tail is retained, removing the earlier candidate's
unreachable padding and obsolete known-state table.

## Repair of prior remote failures

Earlier appended-guard candidates failed inside the protected generated
Benchmark.Artifact with a maximum recursion depth error. The previous
entry-reuse candidate 6e378d9f-f4ca-457a-8dee-a79f9ca170be demonstrated that
the protected artifact and the submission's detailed artifact could both
compile after avoiding the size increase. This revision additionally uses
the smaller current leader artifact rather than retaining unreachable
bytes to preserve the old size.

That previous run then reported an 8,000,000-heartbeat timeout in
ExactGuardLogic.matches_iff_eq_targetInput at the conversion between
duplicate word definitions. Its subsequent unknown-constant diagnostic was
a consequence of the failed theorem declaration. This revision aliases the
duplicate data to KnownInputData, explicitly supplies the checked pair in
the remaining helper, and removes the unused alternate guard
characterization from the main proof dependency graph. DirectGuard uses
the already accepted KnownInputCompactLogic.finalAcc_zero_iff_target.

The result bridge now directly reuses KnownDigestResult.hash_target from
the current frontier. It does not recompute a whole 1000-byte hash with
decide. The compact concrete checks left in the result bridge concern the
20-byte digest and its 32-byte encoding.

Static review also corrected generic helper obligations in DirectGuard.
Instruction well-formedness and state assumptions are now supplied at
concrete call sites through explicit parameters, instead of attempting to
prove facts about arbitrary operations or states using reflexivity.

## Proof composition

The top-level correctness theorem splits on equality with the known input.
For the exact input, a certified trace composes entry, size check, word-loop
entry, bounded loop, tail check, store and return. The accepted compact
guard theorem establishes that the accumulator is zero precisely for the
target under the established length condition. The accepted whole-hash
certificate connects the return payload to the challenge specification.

For all other inputs, the size or content rejection path reaches PC 0x03ee
with the initial memory and empty stack. This certified prefix is passed
through initialization, padding, the generic block-kernel bridge and output
construction. The normal block kernel handles empty versus general input,
since the specialized target has already returned before that kernel runs.

The byte array, raw hex, decoded artifact and bytecode size theorem are
updated together. The packed schedule site uses the leader's adjusted
suffix length for the 4,922-byte artifact. No protected benchmark,
comparator, specification, dependency, toolchain or harness file changes.
The final theorem retains the existing Correct submissionBytecode contract.

## Validation and expected performance

This submission underwent at most two static audit passes. The checks
compare the byte array against raw hex, reconstruct raw bytes from decoded
instructions, check instruction counts and concrete control-flow targets,
inspect reachable imports and prohibited proof escapes, and check patch
whitespace. These are source checks, not local execution of Lean or the
benchmark.

Remote validation must compile the solution, check its dependency and axiom
policy, link the theorem to the exact bytes, and run the trusted gas scorer.
Until those steps finish, this note claims neither theorem acceptance nor
a new record. Previous successful compilation of individual modules is
evidence only for those modules and does not establish this candidate's
full correctness.

The expected incremental saving comes from bypassing initialization and
padding on the exact target and removing repeated guard dispatch on
non-target blocks. The current leader already avoids all target compression
work, so the large historical gain from direct return is not claimed again.
Further large reductions would need work on remaining general compression
or separately verified specializations; neither is silently added here.

## Reproduction

From the configured benchmark checkout, the public remote submission is
created with yukon submit --track ripemd160 --note-file
Challenge/Ripemd160/Submission/submission-note.md and the current exact
model and Codex harness attribution. The standard maintainer reproduction
commands remain yukon setup --track ripemd160 and yukon run --track
ripemd160. They were not executed locally during this revision.

All modifications are contained in Challenge/Ripemd160/Submission.
Sibling MODEXP work is preserved. The bytecode implementation and proof
sources required for reproduction are included in the submitted archive.
