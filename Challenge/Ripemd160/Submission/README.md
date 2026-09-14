# RIPEMD-160: reuse the invariant input length in recognizer loops

Candidate: 671,143 gas / 5,220 bytes, raw-byte SHA-256
`150240919d5a65f3cbe3e6750fbf3b9d28f3e3e79b35556252532b0815a79ab6`.
The frozen parent ffe632fe measures 671,167 gas with a complete universal
proof; its independent secure verification is running separately. This
candidate saves another 24 gas by extending length reuse to two recognizer
loop sites. Relative to the accepted 730e7dc2 frontier at 671,241 gas, the
baseline saving is 98: our output assembly saves 32, jacklightChen's initializer
change saves 42, and the two loop reads save 24.
The executable has 3,745 instructions and 4,940 bytes, followed by the
unchanged 280-byte digest payload.

The J2 frame stores the original input length in its len field. The finish
comparison at PC234 and the next-segment calculation at PC258 previously
retrieved that field through DUP6 and DUP7. CALLDATASIZE produces the same
word for one less gas at each site. On the baseline corpus, the two sites
execute 24 times in total. Both opcodes remain one byte, so every PC,
instruction index, jump target and payload offset stays fixed.

The raw finish and transition helpers now require the frame length to equal
UInt256.ofNat of the actual calldata size. J2Moves and J2Sites carry this
invariant. The loop induction carries its existing input-size equality through
one-step and multi-step execution, establishing the condition at every tail
and transition. Initialization supplies the original length, and normal,
tail and transition steps preserve it. The public universal correctness
statement has no new assumption.

The old output assembly discarded six round constants, exchanged two hash
words and combined the five 32-bit words through four shifts and ORs. The new
assembly discards the same six constants, writes h4 at memory offset 16,
exchanges the next hash words, then writes h3, h2, h1 and h0 at offsets 12,
8, 4 and 0. The stores proceed toward lower addresses. Each later store
preserves the four-byte word exposed above its end. Reading 32 bytes at offset
16 therefore gives twelve leading zero bytes and the five big-endian hash
words in the original order. The existing byte-swap stages and final return
then produce the same RIPEMD-160 result.

The old packing window costs 39 gas; the new window costs 38. All measured
generic executions already have the required memory active. There are 32
such returns in the baseline corpus, so output assembly saves 32 gas. The
new window is one byte longer. Narrowing the immediately following shift-eight
literal from PUSH2 to PUSH1 balances that byte without changing its gas.
Every physical PC outside 4654 through 4676 remains unchanged, as do all
instruction indices, jump destinations and payload offsets.

The second change comes from jacklightChen's public submission eab66c37,
source cdeec6a304f7bad5db7e4e7e497aa838e13c832c. At three J2 initializer
sites, the resident value duplicated by the old instruction is exactly the
calldata length. CALLDATASIZE produces that value for two gas instead of
three. We adapted the public PCs 133, 134 and 138 to this parent's PCs 131,
132 and 136. Each instruction remains one byte. The whole initializer proof
binds the values to the actual execution environment. All three byte
representations—typed instructions, exact assembly theorem and raw byte
array—were updated together. The baseline initializer runs fourteen times,
giving 42 gas of savings. That independent contribution is credited to its
author rather than included in our 32-gas output contribution.

MemoryPackedOutput proves the overlapping-store read one byte at a time for
arbitrary initial memory and all five UInt32 hash words. Its readWord theorem
connects that memory result to PackedOutputMath.pack5. StaggerPersistentOutput
proves the complete raw instruction sequence and tracks both memory and
active-word changes. StaggerPersistentSerialize composes the existing endian
and return proofs over that resulting state. Its result model preserves the
execution environment and call stack while permitting the changed scratch
memory. The final returned-bytes theorem remains the original RIPEMD
specification. The J2 raw initializer retains its existing result model.

Runtime validation of these exact bytes passes the original read-only loader,
98 native clean and dirty executions, the mandatory 120-seed corpus gate,
2500 fuzz cases, executable reassembly, jump destinations and CODECOPY bounds.
Expanded differential validation against a64a2bde passes 4358 inputs with no
gas regression. All digests match an independent RIPEMD implementation. Sixty
of 69 additional corpus seeds save 98 gas; the other nine save 102 because
their recognizer execution counts differ. The per-input prediction is minus
one per output packing and minus one per each of the five changed J2 sites.
The full Solution build passes all 3,720 jobs. The final candidate depends
only on propext, Classical.choice and Quot.sound. Independent secure
Comparator verification is run against this frozen artifact next.

The parent retains our deferred padding-limit rounding and literal unit
constant; the exact-32 diversion before rounding is retired into a
stack-neutral passthrough, so the generic padding path now serves every
input size. The parent and earlier artifacts have
independent secure verification. The earlier 671,664 candidate was accepted
as 0f4090d0 and promoted to cdbceb0f. That promotion's complete Submission
tree matches the frozen d6a787fc. New public branches are inspected and active
research is compared against each promoted frontier on identical inputs.

Earlier attribution remains: ercumentyildirim supplied the Shared32/J2/cold
architecture in 6d7f412a; fkiene supplied the plus-modulus idea; i34-9 refined
the packed classifier constant. Our retained recognizer suffix, prefix-clear
memory proof, deferred limit and guard integration remain in the parent.
Earlier compression, endian, payload and proof contributions retain their
provenance. Only Challenge/Ripemd160/Submission is changed. The protected
semantics, specification, scorer, artifact generator, compiler, kernel,
dependency pins and benchmark settings remain unchanged. Research and review
continue after submission and promotion.
