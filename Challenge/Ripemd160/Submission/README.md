# RIPEMD-160: recognize the 32-byte route before rounding

Research candidate: 671,241 gas / 5,220 bytes, raw-byte SHA-256
`5b301f0477890091afba147d04ce17b7b24309336e2809b449dc56afa594a813`.
The exact assembly and full Solution proofs pass all 3719 build jobs. The
final correctness theorem uses only propext, Classical.choice and Quot.sound.
Independent secure verification is required before submission. This extends
our universally proved 19639119 unit-literal artifact at 671,472 gas.

At the common partial-padding entry, the parent first rounded the resident
length with `(length + 72) & ~63`, then checked whether the input had exactly
32 bytes. The new bytecode performs that check first. Non-32 inputs fall
through the same rounder and padding code. The 32-byte route takes its existing
branch immediately and retains its original resident limit of 32.

This limit still gives exactly one block of compression. The shared 32-byte
route supplies its proven one-block schedule and enters the core at offset
zero. After compression, the offset is 64. The continuation test `64 < 32`
is false, and the separate padding-completion test compares offset 64 with
calldata size 32, which is also false. The existing serialization follows.
The retained limit does not affect the compression arithmetic or digest.
The padded-message specification still has length 64; only the runtime loop
limit on this dedicated route changes.

The change swaps two adjacent instruction groups in bytes 4706 through 4722:
the five-instruction 32-byte guard moves ahead of the seven-instruction
rounder. JUMPDEST at 4705 stays in place. All byte positions outside this
17-byte region remain unchanged. The guard starts at 4706 and its non-32
fallthrough reaches the rounder at 4714. Ordinary padding still starts at
4723. There are 3745 executable instructions, 4940 executable bytes, and the
unchanged 280-byte digest payload. CODECOPY still reads [4940,5220).

The 32-byte branch avoids twenty-one gas. Eleven baseline vectors take that
branch, so it saves 231 gas from 19639119. All other measured inputs retain
the parent's cost. Compared with our accepted frontier 3267c1f8 at 672,060,
the cumulative baseline improvement is 819 gas. The parent contributions
are deferred padding-limit calculation and a direct lane-bit literal.

Expanded differential checks cover 4358 inputs: 4321 have unchanged cost and
37 save twenty-one gas relative to 19639119. Every digest agrees with
independent RIPEMD-160. All 69 additional corpus seeds save 231 gas. The
original native scorer passes 49 clean and 49 dirty executions. The mandatory
full gate passes 120 corpus seeds, 2500 fuzz cases, instruction reassembly,
dynamic jumps and CODECOPY bounds. The original read-only loader accepts
these exact bytes. Encoding size and footprint remain 5220 and 2312.

StaggerPersistentStart splits the common entry into its JUMPDEST, 32-byte
guard and raw rounder. Its composed non-32 trace reaches the same rounded
frame as before. PaddingTrace, PaddingTail and ColdHighPaddingTrace use that
composition; PaddingTraceGeneral handles the unchanged body after it.
Shared32Start and Shared32TailCorrect take the early branch without rounding.
Shared32Core uses resident limit 32 while its completed offset remains 64,
reusing the parameterized compression and serialization proofs. The complete
Solution passes; the protected Comparator must also accept the frozen bytes
before upload.

Attribution: ercumentyildirim's 6d7f412a supplies the Shared32/J2/cold
architecture. Our 5cf31e63 retains the unused recognizer suffix and folds the
plus-modulus literal; the plus-modulus idea credits fkiene. Our d6a787fc defers
padding-limit calculation and proves the shared high-input route. Our
19639119 directly supplies the lane bit. The compact classifier constant
credits i34-9's refinement of our earlier lookup. This guard reorder and its
proof integration are our work. Earlier contributors retain their credit.
All changes are within Submission; protected benchmark components are unchanged.
