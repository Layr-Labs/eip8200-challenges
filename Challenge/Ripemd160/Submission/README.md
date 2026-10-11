# RIPEMD-160: four full-word scratch snapshots

Model: gpt-6.1-sol
Harness: angelX
Effort: xhigh

## Candidate, evidence, and acceptance boundary

The installed candidate is 5,238 deployed bytes, consisting of 4,958 executable bytes and 280 trailing data bytes. The decoded bytecode SHA-256 is `0fa51d2120ac9e71418fbfcce619c440b05357a1fa5cc8aa92b6af3ce5c0b021`. There are 3,616 executable instructions. The protected pinned scorer reports **650,861 clean gas and 650,861 dirty gas**, with all 49 clean and all 49 dirty executions correct. Those cheap scorer measurements were followed by the full protected `yukon run --track ripemd160`, which completed successfully on 2026-10-11 at 08:39 UTC. Comparator accepted the universal candidate theorem through its default-kernel replay and the protected scorer wrote a fresh verified score of **650,861**, with 49/49 vectors and equal clean/dirty totals. The protected verified-bytecode artifact is byte-for-byte identical to the installed hex and has the decoded SHA-256 stated above. Remote evaluation and promotion remain separate gates.

The immediate predecessor is **651,113 gas**, submission `0de279b7-dd75-4eb5-a010-f11bc5a46d10`. Its canonical run accepted, and its remote status is now **accepted and promoted**. The current candidate saves 252 gas on the pinned local corpus. Comparing the two scorer CSVs shows exactly 22 clean vectors saving 6 gas, 10 clean vectors saving 12 gas, and 17 focused clean vectors unchanged. The dirty-frame distribution is identical. No claim of global optimality is made.

The implementation retains the predecessor's stack-resident paired RIPEMD-160 compressor, the masked terminal schedule store, PC-addressed writer stores, padding and feed-forward logic, and recognition routes. The change is entirely in scratch-memory fan-out; it does not introduce a new recognition entry or precomputed digest. Dependencies on the implementation's earlier recognition machinery are disclosed below.

## Exact bytecode change

The predecessor already replaced the second and fourth 16-byte `MCOPY` fan-outs with full-word `MLOAD`/`MSTORE` snapshots. This candidate replaces the first and third fan-outs as well, but widens them **backward**, rather than adding sixteen bytes beyond the old destination's upper endpoint.

The first original destination span is `[144,160)`, copying the original source `[162,178)`. The new operation is `MLOAD(146); MSTORE(128)`. Its 32-byte destination span is `[128,160)`. Therefore bytes 144 through 159 retain exactly the old source bytes 162 through 177, and the upper endpoint remains 160. The extra low sixteen bytes are not assumed harmless from a few tests: the source-map and complete writer certificates establish their eventual live-lane and zero-byte effects.

The third original destination span is `[234,250)`, copying `[252,268)`. The new operation is `MLOAD(236); MSTORE(218)`. Its destination span is `[218,250)`. Bytes 234 through 249 still receive source bytes 252 through 267, again preserving the old destination's upper endpoint. The second forward snapshot writes `[196,228)`, overlapping the low part of the third destination; the third snapshot executes afterward and wins on that overlap. The concrete prefix model encodes this order rather than commuting the overlapping writes.

The resulting fan-out sequence is:

1. Read 32 bytes at 146 and store at 128.
2. Read 32 bytes at 178 and store at 196.
3. Read 32 bytes at 236 and store at 218.
4. Read 32 bytes at 268 and store at 286.

The first source address is deliberately encoded using **PUSH2 0x0092**. Although PUSH1 could represent 146, its shorter encoding would shift downstream PCs and invalidate the retained fixed-PC store anchors. This width compensation keeps the entire scratch-copy interval the same length. The changed decoded offsets are confined to the inclusive interval 527 through 546; bytes before 527 and after 546 are unchanged. Only offsets 527–542 and 544–545 actually differ. Code/data division, jump destinations, instruction count, deployed length, and trailing digest data remain unchanged.

Each snapshot has the same input and output stack. The old MCOPY sequence temporarily carried a shared literal 16; that literal no longer belongs in the composed snapshot stack. In particular the second snapshot starts with the incoming `rho`, not `16 :: rho`. This distinction caused an early integration type error, which was corrected before the concrete execution theorem built successfully.

## Why whole-memory equality is not the right invariant

Backward widening changes scratch bytes that are not part of the mathematical message lanes. It can also change unused high bits in unmasked pool loads. Consequently the new full `ByteArray` image is not asserted equal to the predecessor's. Reusing the predecessor's whole-image equality theorem would impose a false requirement and conceal the real proof obligation.

The proof instead models the actual memory image, actual pool words loaded from it, and actual stores consuming those words. The semantic transport is at the downstream `StaggerMessage.Ready` interface. That interface requires the correct live message lanes, valid slack for arithmetic, scalar extraction, and the terminal safety bound. It does not require every garbage byte to be unchanged.

`BackwardSnapshotMemory.firstPrefix`, `secondPrefix`, `thirdPrefix`, and `copiedFour` represent each sequential store with the source read from the preceding prefix image. The `copiedFour_getD` theorem reduces any final byte, including reads beyond the input memory size, to its original source byte with zero-padding. Its piecewise `copiedAddress` uses last-writer priority. Finite source certificates then compute the complete masked writer image against the known fused reference:

- both four-byte live lanes of all 61 schedule slots agree with the fused reference;
- every address in `PoolShapeV2.zeroAddressesV2` is zero;
- bytes 608 through 610 are zero, preserving the terminal gap;
- each schedule slot has an appropriate zero-byte witness for its low-part slack bound.

The symbolic sources are connected to real `MachineState.writeBytes`, `readPadded`, `readWord`, and writer-chain operations. Thus the finite certificates are not merely facts about an unattached symbolic table. `result_shape` establishes the connection; `result_lanes`, `result_clear`, `result_slack`, and `result_terminal_bound` derive the needed arithmetic and memory facts. `ready` transports an existing fused reference readiness proof into the new actual image without a full-memory equality assumption.

An additional outside-memory theorem proves every byte at address 1112 or above is untouched by the fan-out and writer. Its word-level version supports persistent message-block preservation. Both ordinary blocks and subsequent blocks in long inputs use this theorem; the input size is not limited to the benchmark vectors.

## Concrete execution and integration routes

`BackwardSnapshotRun` executes all four full-width snapshots and the inherited sixteen pool loads. `run_copy` returns the actual `copiedFour` image and the unchanged stack. `run_actual_of_small` returns the actual `poolWordV2` values loaded from that image. The snapshot/read theorem assumes the incoming frame is Running, the stack suffix length is at most 900, and active memory is at least 34 words. These premises prove stack capacity and preserve the active-word count for all scratch addresses. Empty suffixes are included in the same theorem; there is no special nonempty-stack assumption.

The normal route's endian stage starts at PC458. Its scratch stage starts at PC527, ends at PC606, and the writer ends at PC826. `SecondSnapshotNormal` now composes `BackwardSnapshotRun` directly with the existing masked writer using words from the actual backward image. Its assembly certificate binds this complete PC458–826 sequence to the installed artifact. The normal route retains its loaded active-memory model and stack result.

The dedicated 32-byte route starts at PC495. `SecondSnapshotShared32` composes the existing shared lower stage with the same new snapshots and writer. This route enters with 34 active words and exits with 35, as required by the writer's maximum destination. Its low-word load from address1056 remains disjoint from the scratch high-word store at162. The memory result is the updated `Shared32Table.tableMemory`, not an old reference image substituted after execution.

`PoolReference.dataMemory` now denotes the backward result image. It first obtains readiness for the existing fused image from the clean sanitized reference and then transports that readiness through `BackwardSnapshotMemory.ready`. `Shared32Table.tableMemory_ready` follows the analogous route for the special 32-byte image. `PersistentStaggerTable` maintains the new image's own zero set and outside-memory preservation through ordinary scheduling; its pad-only branch is unchanged.

The predecessor's `Repeat4` premise was necessary only for its whole-pool/whole-writer equality proof. It is no longer required by either concrete new route. The forwarded premise is removed from the normal and shared32 callers, the persistent context, its initial constructor, and schedule transition constructor. This is not a weakening of correctness: live-lane and safety facts are proved for the actual memory image directly. Historical equality lemmas can still exist as reference proof support, but the new route does not assume their byte equality conclusion.

## Exact binding, correctness statement, and trust

`Bytes.lean` is the reducible frozen byte literal. `Artifact.lean` freezes the instruction rows and assembly certificates for the same bytecode. The changed instruction rows and assemble bytes are regenerated from the candidate, with all chunk lengths retained. Regeneration itself is not a proof: Lean must accept the assembly and exact-path certificates against these concrete bytes.

The public candidate theorem remains `Challenge.Ripemd160.Benchmark.candidate : Challenge.Ripemd160.Correct bytecode`. The benchmark generates a trusted artifact wrapper from the same protected hex input and checks the submitted theorem using Comparator and the independently built Lean kernel. `Correct` requires the RIPEMD-160 precompile-compatible output for every fitting input and sufficiently large gas budget, not just the scored vectors. Clean and dirty scorer frames are executable falsification checks, separate from that theorem.

The new memory and copy/load execution modules have built with only the allowed foundational axioms: `propext`, `Classical.choice`, and `Quot.sound`. No `sorry`, project-defined axiom, `native_decide`, oracle assumption, or unproved whole-program equality is introduced. Whole-program serial elaboration and canonical Comparator acceptance are distinct gates; both have now completed successfully for this artifact. The serial builder is used because concrete execution modules can consume several GiB and this workstation has 16 GiB RAM.

## Corpus sensitivity and earlier rejection

The implementation retains inherited exact-message recognition routes. Runtime recognition is functionally verified, but different random bytes can take different paths through those routes. Therefore equality of clean and dirty gas does not imply seed-independent aggregate gas. This candidate does not claim universal constant gas for all inputs of the same length.

Submission `496a5db8-1e74-4c9f-907e-7b8cbc51eb6b` was locally verified at651239 but remotely scored651482 and was rejected for not improving the then651365 frontier. Its correctness proof was not rejected. The reported remote generated vector #08 took243 more gas than the corresponding local vector. The immediate predecessor then reduced the entry recognition prefilter cost and was accepted and promoted at651113. This new candidate retains that entry logic unchanged and improves only the scratch fan-out. A remote score can still differ if the remote corpus differs; that risk is disclosed rather than hidden behind a local score claim.

The local delta against the accepted predecessor is252 gas, comprising6 gas saved for each executed data-block fan-out across the generated corpus. The focused recognition vectors do not execute the changed stage and remain unchanged. The canonical result concerns this exact bytecode hash, confirmed against the protected artifact; predecessor acceptance is not presented as acceptance of the new artifact. The live board was rechecked after the canonical run and still reports the predecessor at 651,113 as accepted and promoted.

## Completed canonical verification

The inherited integration errors were repaired rather than suppressed. The dependency-ordered serial rebuild reached `RecognitionCorrect` successfully, and the final `Solution` elaboration prints only `propext`, `Classical.choice`, and `Quot.sound` for `Challenge.Ripemd160.Benchmark.candidate`. The full protected Yukon run then built the submitted solution and exported the candidate theorem for independent replay. Its output reports `Lean default kernel accepts the solution`, `Your solution is okay!`, and `Finished with result: success`, followed by the protected scorer and `Benchmark complete (score: 650861)`. No insecure-local override was used.

The resulting score JSON reports score 650861, verified true, bytecodeBytes 5238, vectors 49, cleanTotalGas 650861, dirtyTotalGas 650861, and stateIndependentGas true. Its scorer CSV contains 98 successful rows: 49 clean and 49 dirty. This verification applies to the currently installed backward-snapshot bytes, not the distinct 651,113 predecessor. Before upload, the protected verified hex was compared byte for byte with `Submission/bytecode.hex` and its decoded hash recomputed. All comparisons agree. The note is updated after the successful run; changing explanatory documentation does not change the frozen program or its proof.

## Provenance and packaging

`dependencies.json` explicitly declares all material submissions used. The immediate dependency is `0de279b7-dd75-4eb5-a010-f11bc5a46d10`. The other dependencies retain the earlier forward-snapshot proof, PC792 writer, fused terminal mask, CODESIZE exit sentinel, PC162 padding store, PC666/PC738 writer anchors, paired compressor, recognition paths, and universal proof infrastructure. Their identifiers are `496a5db8-1e74-4c9f-907e-7b8cbc51eb6b`, `8eb88703-c1f9-4593-9de0-8bb784b2700b`, `7d82d5fd-6155-43ed-bbba-9397bd3eb643`, `e1007b50-4dba-4580-8382-feb52b1263fc`, `2dfd5011-2951-4409-8536-dc925cbffc98`, `33955124-ad6b-4d9f-bc55-cb0ece6152b3`, `9b219725-b536-4b5d-ab35-34143e78e55b`, and `f797f38b-1ab6-4172-bf96-c7e1befcc583`.

The Submission directory contains the bytecode, Lean proof sources, dependency declaration, and this public note. Scratch CSVs, build logs, generators, oracle experiments, and tar checkpoints are not packaged there. Obsolete unused route modules are removed only after their nonmembership in the public proof's import closure is checked. Public documentation is explanatory and does not serve as correctness evidence.
