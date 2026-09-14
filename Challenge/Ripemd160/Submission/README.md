# RIPEMD-160: materialize both lane moduli and preserve the original loader

Candidate: 670,855 gas / 5,223 bytes, raw-byte SHA-256
`1a6a07ff41e77ae689867e75f691493f3d1ae5921d0b2870287b8606f3cded7a`.
The frozen parent 4ea9da13 measures 671,047 gas with a complete universal
proof. This candidate saves another 192 gas by storing the minus modulus
as a literal. Against the newly accepted 1e1885f4 frontier at 671,167,
the baseline saving is 312 gas. The executable contains 3,742 instructions
in 4,943 bytes followed by the unchanged 280-byte digest payload.

The initializer previously pushed the shifted lane bit as a PUSH19 literal,
duplicated the plus modulus, and subtracted. The new initializer pushes the
final minus-modulus value directly with PUSH27. Both values are exactly the
original constants, ((2^65 + 1) << 144) and ((2^65 - 1) << 144). The
three-instruction, nine-gas construction becomes one three-gas instruction.
There are 32 generic initializations in the baseline corpus, saving 192 gas.

The larger literal requires a deliberate byte layout. The repeated 20 in
the payload selector is read with DUP1. A resident literal 23 in paired
round 14 is read with DUP2; that raw round's input model already fixes the
resident word to 23. Both replacements preserve their original three-gas
cost while removing one byte. The jump-to-51 literal and shift-eight literal
use their minimum widths. A single leading zero is allocated to the shift-24
literal at parent PC3977. Six expression sections exchange commutative
operands with the necessary DUP-depth adjustments. Four unnecessary
sections from the search result were restored to the parent instruction
order before proof integration. The exact resulting bytes pass the original
read-only loader with its unmodified recursion limit.

The changed expression sections are the initial all-a comparison, the first
right bootstrap round, paired rounds 39 and 40, the first endian stage and
the packed recognized-length equality. They preserve their logical results.
The endian stage pushes its factor earlier and reads the same mask at its
adjusted depth. The packed length equality computes the same lookup before
reading calldata size for the final equality. All raw instruction templates,
located recognizer paths and index windows are bound to this exact order.

Early width changes relocate code throughout the executable. Every actual
site PC, branch literal, round-PC table, cached instruction fact and payload
address is updated together. The payload begins at 4943 and CODECOPY ends
at 5223. The artifact byte count is 5223; its next aligned boundary remains
5248. The protected artifact generator, compiler and options remain original.
Legacy abstract template proofs keep their own internally consistent PCs.

The selected bytes pass 98 native clean and dirty runs, the original
read-only loader, and the full mandatory 120-seed corpus plus 2500-fuzz gate.
Expanded differential validation against 4ea9da13 covers 4358 inputs:
21 recognition-only cases have unchanged gas and the other 4337 save six.
All 69 additional complete corpus seeds save exactly 192 gas. The per-input
prediction is minus six per parent initializer at PC440. Digests match the
independent RIPEMD implementation throughout. The full universal Solution proof passes all 3720 build jobs. Its final
candidate uses only propext, Classical.choice and Quot.sound. Independent
secure Comparator verification is run against this frozen artifact next.

The current frontier is our memory-plus-initializer artifact ffe632fe,
submitted as 978be615 and promoted to 1e1885f4 at 671,167. Its entire
Submission subtree equals the frozen verified source. On identical seeds
0, 1 and 820096, our loop candidate is 671,143, the permuted-hash parent
is 671,047 and this candidate is 670,855. Research and incoming-branch
reviews continue after each submission and promotion.

The inherited physical frame places six round constants above h4, h3, h2,
h1 and h0, followed by the block offset, loop limit and two endian masks.
Initialization and the scalar bootstrap use this order while preserving the
logical hash fields. The joint packing and scheduled compression tail read
and return the same logical values at their adjusted depths. This removes
the output serializer's SWAP2 and saves 96 gas in the baseline corpus.

The serializer writes h4, h3, h2, h1 and h0 at memory offsets 16, 12, 8, 4
and 0, then reads 32 bytes at offset 16. Descending overlapping stores leave
the five four-byte hash words at memory bytes 28 through 47. The read returns
twelve leading zeros followed by those words. Two whole-word endian stages
and the final return produce the required RIPEMD-160 bytes. MemoryPackedOutput
proves this for arbitrary starting memory and UInt32 hash words. The raw
output and serializer proofs track the resulting scratch memory and active
word count. The universal claim is still the benchmark's original theorem.

The five inherited J2 length reads save 66 gas on the baseline corpus.
jacklightChen's eab66c37 submission, public source cdeec6a304f7bad5db7e4e7e497aa838e13c832c,
contributed the three initializer replacements. We adapted their positions
and all exact assembly bindings. Our extension covers the finish and
transition sites. Each raw helper requires Frame.len to equal the actual
calldata length; the loop invariant supplies that equality for every step.
The selector's new DUP1 reuses its existing 20-byte return-length word.
Its raw prefix theorem quantifies over the complete incoming selector frame.

Earlier contributions remain credited: ercumentyildirim supplied the
Shared32/J2/cold architecture in 6d7f412a; fkiene supplied the plus-modulus
idea; i34-9 refined the packed classifier constant. Our earlier work includes
the retained recognizer suffix, prefix-clear memory proof, deferred limit,
guard placement, memory output and physical hash order. The new minus
literal, byte allocation and expression-order search build on that lineage.

Only Challenge/Ripemd160/Submission is changed. The protected scorer,
artifact generator, EVM semantics, RIPEMD specification, compiler, dependency
pins and Lean kernel are unchanged. No verification option is increased and
no axiom, admission or native_decide is added. Actual located sites refer to
the new bytecode addresses; virtual template models retain their independent
consistent addresses. Exact assembly and raw step proofs connect every
runtime instruction to the original universal correctness statement.
