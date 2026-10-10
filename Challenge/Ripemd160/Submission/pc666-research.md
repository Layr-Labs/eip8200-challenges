# Second fixed-PC schedule store: measured 651,533 gas

Status: reported research; not yet a Lean-verified or submitted candidate.
The selected 651,575 PC738 candidate remains unchanged.

## Source and exact experiment

Base artifact is the 651,575 candidate in `bytecode.hex`, SHA-256 of decoded
bytes `b9182bbcc8258af8bc5e754e1c71c7c0fa52275e282da7d02049f55fe926e095`.
The independent experimental artifact is `pc666-experiment.hex`.

Offsets below refer to that base, and edits are applied in descending order:

- At 607, widen `PUSH1 126` to `PUSH2 126`.
- At 616, widen `PUSH1 216` to `PUSH2 216`.
- Insert `DUP16; PC; MSTORE` immediately before old offset 663.
- Remove old offsets 688–692: `DUP14; PUSH2 666; MSTORE`.
- At 2060, narrow `PUSH3 954` to `PUSH2 954`.
- At 2085, widen `PUSH1 20` to `PUSH2 20`.

The new `PC` is at absolute offset 666. The unchanged first PC optimization
remains at offset 738. Total size remains 5,248 bytes. Executable instruction
count remains unchanged. The round-23 PUSH redistribution keeps the round's
entry, end, values, instruction count, and gas unchanged, while reducing the
64-byte chunk's distinct-value count by one. Combined literal budget is
8,194, the current default-elaboration ceiling. The generated trusted literal
for this experiment compiles with unchanged default options.

## Measurements

The pre-existing protected direct scorer executed `pc666-experiment.hex`
over 49 vectors in both clean and dirty frames. All 98 statuses are correct.
Both totals are **651,533**, a further reduction of **42** from 651,575 and
**84** from the promoted 651,617. These totals are scorer evidence only;
the full universal proof for these experimental bytes is not yet built.
The full CSV is `pc666-experiment-gas.csv`.

## Memory-order argument to formalize

The store of words14 at address 666 moves immediately after the store to
792 in writer template1. DUP16 at the insertion selects the same word that
DUP14 selects later after two stack values have been consumed. The inserted
triple leaves the stack unchanged, just as the removed triple did.

The moved write crosses stores at 540, 756, 522, 90, 72, and 54. Every one
of their 32-byte intervals is disjoint from [666,698). Thus the existing
`Pair13WriterRaw.writeWord_comm` can discharge each commutation for arbitrary
256-bit words and arbitrary starting memory. Overlapping slots 684 and 648
retain the necessary relative order: 684 before 666 before 648. Do not
assume arbitrary slot stores commute: schedule slots are only 18 bytes apart.

## Proof work still required

Update template0 PUSH widths and template1/template2 store sequence in both
PoolRawWriter and Pair13WriterRaw. Add an explicit fixed entry-PC premise to
template1 execution, with the computed PC equal to 666. Update writes1 and
writes2 certificates without changing their stack outputs. Prove the memory
reorder against the inherited rawWrites order, or use the existing sorted
write-chain certificates. Preserve the public final memory specification;
PoolShape and its literal write list are consumed elsewhere, so simply
changing their order would create broad downstream obligations.

Writer template1 grows by three instructions, template2 loses three. Their
combined count is unchanged. Their intermediate split PCs move, so derive
new chunk1/chunk2 entry PCs rather than carrying the old constants. Chunk3
entry 708 and later sites remain unchanged. In Paired23Raw, update the two
PUSH widths and rebuild its concrete execution and exact-byte certificates.
Regenerate Artifact and Bytes with the inherited top-level partition, then
run the cheap scorer, serial full proof, and canonical Yukon verifier before
submission. The current 651575 verified candidate should be retained as a
separate immutable checkpoint before starting these source changes.

## New kernel-checked evidence

`Proofs/Bytecode/Pc666WriteOrder.lean` now proves `move_666`: the seven-store
sequence with 666 last is equal to the sequence with 666 first, for arbitrary
ByteArray memory and arbitrary Nat-to-UInt256 word assignment. The proof uses
six applications of the existing disjoint `writeWord_comm`. `lake env lean`
compiles it; its axiom footprint is only propext, Classical.choice, Quot.sound.
This certifies the key memory-order subproblem but not full bytecode execution.

`Proofs/Bytecode/Pc666ChunkExperiment.lean` also now compiles a local execution
lemma for the rewritten plain-word writer chunk. For arbitrary memory/words,
stack suffix length at most 900, a Running state, at least 34 active words,
and entry PC646, the template performs the moved PC666 store and the other
writes, preserving the expected output stack/PC/active-word count. Its axiom
footprint is propext and Quot.sound only. This is not yet connected to the
artifact's indexed-site certificate, packed-word writer, or final correctness
endpoint. The current submitted bytecode and universal proof are unchanged.

`Pc666FullOrder.writerMemory_preserved` now compiles and proves the entire
reordered 45-store sequence equals the inherited writer memory specification,
not just the crossed seven stores. It assumes arbitrary initial memory and
arbitrary word assignment. Only standard axioms appear. The statement still
does not bind the experiment to its byte artifact.

## Composed writer execution checked before integration

Both `Pc666PackedExperiment.lean` and `Pc666PlainExperiment.lean` now
compile. Their `run_writer` and `run_writer_grow` endpoints perform the moved
PC666 store and return the original full writer memory specification,
with fixed writer entry PC606 and the correct active-word behavior. The packed
version retains its word-bound assumptions; the plain version works for
arbitrary word assignments. The axiom sets are the three permitted standard
axioms. The templates are still deliberately outside the Solution import
closure. `update_pc666.py` captures the tested transformation but must only
run after the PC738 checkpoint's canonical verification and submission.
