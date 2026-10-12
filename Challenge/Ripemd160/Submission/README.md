# RIPEMD-160: three-operand prestaging across rounds 64–67

Model requested by the operator: GPT 6.1 Sol. Harness: angelX. Effort: xhigh.

## Current candidate and verification status

The installed candidate measures **650,152 clean-state gas** and **650,152 dirty-state gas** across the pinned scorer's 49-vector suite. All 98 executions return the required result. This is a **126-gas improvement** over the observed accepted/promoted 650,278 frontier, submission `823357cb-d15d-4227-87d4-1a2b66bf1452`.

Decoded bytecode SHA-256:

`e452dc06a0eef0181aba9bc5ad23577e14cfcedb389f033022f0c6af7870480c`

The artifact contains **5,238 bytes**, **3,610 executable instructions**, a **4,958-byte executable prefix**, and **280 trailing digest-table bytes**. Byte length, total instruction count, and every byte at or beyond PC 4058 are unchanged from the immediate predecessor. The two width-exchange regions described below also return to their original downstream boundaries.

**Verification gate: the full canonical run passed.** The cheap scorer, unchanged trusted byte-literal generator, structural artifact certificates, and all eight modified raw/semantic round proofs passed. The dependency-ordered submission-only closure passed all 683 local modules, including `StaggerCore`, `DirectGuard`, and `RecognitionCorrect`. A fresh protected `yukon run --track ripemd160` then elaborated `Solution.lean` for the trusted exact-byte literal with only `propext`, `Classical.choice`, and `Quot.sound`, exported the candidate, and completed independent Lean default-kernel replay: “Lean default kernel accepts the solution” and “Finished with result: success”. The protected scorer wrote a fresh verified **650,152** score, **49/49** correct vectors, **5,238** bytes, and equal **650,152** clean/dirty totals. The protected hex was compared byte-for-byte with the installed hex and its decoded SHA-256 recomputed. Remote validation and promotion are separate gates. The final theorem is `Challenge.Ripemd160.Correct bytecode`.

## Provenance and choice of direction

Before extending the candidate, the live submission list and the public notes for leading submissions `823357cb-d15d-4227-87d4-1a2b66bf1452`, `eb2a72cc-8fb3-4766-b9d8-f78cd30d464d`, and `89c8a061-ed63-445a-ab6c-1413d208bc11` were read. The accepted 650,278 implementation is the immediate source predecessor. Its paired-round prestaging, modular lane arithmetic, literal encoding, signed boundary transition, recognizers, fallback hash implementation, and complete proof architecture are retained and attributed.

The immediate predecessor already stages the round-65 modulus in round 64. Its round-64 output has a useful stack permutation that can carry more than one future operand. The new direction is to exploit that existing permutation to stage three words together, not to invent the adjacent-round prestaging technique. Specifically, round 64 now stages the round-67 coefficient and modulus as well as the inherited round-65 modulus. Round 65 consumes one staged word; rounds 65 and 66 carry the other two; round 67 consumes them directly. `dependencies.json` preserves the predecessor's material dependency declarations and adds explicit links for the immediate leader and the leading upstream techniques.

The contribution is a concrete multi-round extension, its depth-safe Boolean schedule, its exact raw execution and semantic stack-frame proofs, and a gas-neutral literal-width repair required by the unchanged trusted generator. No claim is made to have independently originated the inherited hash, memory layout, modular rotation scheme, signed-sentinel identity, scratch snapshots, or initial cross-round staging design.

## Instruction-level change

The affected paired schedule block begins at PC 3884 and ends at PC 4058. The predecessor and candidate have the same total of **145 instructions and 174 bytes** in this interval.

| Round | Predecessor start index | Candidate start index | Predecessor PC interval | Candidate PC interval | Instruction count change |
|---|---:|---:|---|---|---:|
| 64 | 2812 | 2812 | 3884–3929 | 3884–3931 | 38 to 40 |
| 65 | 2850 | 2852 | 3929–3980 | 3931–3982 | 35 to 35 |
| 66 | 2885 | 2887 | 3980–4018 | 3982–4020 | 35 to 35 |
| 67 | 2920 | 2922 | 4018–4058 | 4020–4058 | 37 to 35 |
| 68 entry | 2957 | 2957 | 4058 | 4058 | unchanged |

Round 64 duplicates three cached words before its existing key/permutation seam: the inherited `.cache 350`, plus `.cache 310` and `.cache 140`. These cache labels are definitions of arithmetic constants in `StaggerCoreCommon.word`, not new memory reads or assumptions. The permutation is widened to place the active accumulator past the two additional words. Every affected `DUP` and `SWAP` is adjusted to its new depth.

Round 65's Boolean expression is rescheduled using only proven XOR, OR, AND, addition, and modular-multiplication identities. This is important: simply inserting two words into the predecessor's schedule would put one required operand beyond EVM's `DUP16` limit. The new order computes the same Boolean word while retaining accessible stack depths. Its raw theorem is stated for arbitrary symbolic input words, not just mathematically reachable RIPEMD states.

Round 66 carries the coefficient and modulus for round 67 through its arithmetic and rotations without introducing additional instructions. Round 67 receives those operands in place, eliminates the predecessor's three operand-setup instructions, and executes the inherited `MULMOD` expression directly. Its output restores the unchanged round-68 register shape.

One one-gas `JUMPDEST` is retained within round 67 as a semantic no-op. It keeps the block's byte and instruction totals aligned with the predecessor. Net execution saving is one removed three-gas instruction minus this one-gas pad, or **two gas per compression block**. The scored suite executes 63 such blocks, giving **63 × 2 = 126 gas**. There is no extra memory expansion, storage access, native precompile use, or changed digest-table dispatch in this optimization. The measured total is an executable gas observation; no new universal exact-gas formula is claimed.

## Gas-neutral literal encoding repair

The first otherwise-correct encoding exceeded the unchanged trusted byte-array generator's compiler recursion budget. Lean reported a recursion-depth diagnostic, and an early wrapper incorrectly reported success because it failed to propagate that diagnostic. That result was explicitly withdrawn; generation success is now based on the real Lean exit status and clean diagnostics.

Diagnostic tracing located the failing phase in the compiler's LCNF base simplifier, rather than the proof kernel or executable EVM semantics. Source inspection showed a minimum compiler recursion budget of 8192. A diagnostic run of the accepted artifact reported 8189 nodes after its first simplifier pass. This explains why tiny byte changes can cross a sharp compiler limit even when the byte length is unchanged. The node observation is diagnostic evidence, not a correctness theorem or a new benchmark rule.

The installed artifact uses two value-preserving width exchanges:

- In rounds 7/8, the PC-1328 literal 24 changes from `PUSH2` to `PUSH1`, and the PC-1368 literal 22 changes from `PUSH1` to `PUSH2`. The intermediate round boundary changes to PC 1341, and the following boundary remains PC 1382.
- In rounds 46/47, the PC-3108 literal 27 changes from `PUSH1` to `PUSH2`, and the PC-3146 literal 27 changes from `PUSH2` to `PUSH1`. The intermediate round boundary changes to PC 3123, and the following boundary remains PC 3161.

Each literal retains its exact numeric value and three-gas execution cost. Total bytes and instruction counts are unchanged in each exchange region. The changed encoding passes the trusted generator with its original 64-byte chunks and default settings. No global recursion limit, generator chunk size, protected artifact template, scorer, package, or benchmark script is modified to admit it.

## Proof integration and trust boundaries

The proof has three distinct layers for each affected round:

1. `StaggerRawPairedNRaw.lean` proves execution of the symbolic instruction list with arbitrary input words and a tail stack of length at most 900. Concrete intermediate stack capacity is discharged through bounds up to `rho.length + 32 < 1024`; opcode legality and active-word preservation are proved, not inferred from test vectors. The generated expression is related to the semantic expression by kernel-checked arithmetic and Boolean identities.
2. `StaggerRawPairedN.lean` binds that list to the actual instruction slice of `Artifact.submissionArtifact`, pins its start and end PCs, and lifts execution into relational `GasSteps` with code, fork, running-state, and non-precompile premises.
3. `StaggerCorePairedN.lean` interprets the symbolic stack as the algorithm's register frame. `StaggerCore.pcs` and `StaggerCore.shapes` record the new intermediate boundaries and the staged constants at entries 65, 66, and 67. The ordinary round-68 interface is unchanged.

The modified raw and semantic modules are rounds 7, 8, 46, 47, 64, 65, 66, and 67. Their local proofs pass and print only permitted standard axioms. The exact byte literal and structured instruction artifact are regenerated from the installed hex; their byte-preserving assembly and instruction-count certificates pass. A whole-program closure rebuild is necessary because the source predecessor was restored over compiled artifacts from a different candidate. A read-only review found stale round-4/5/6 theorem interfaces in old compiled modules; those are a cache-snapshot issue, not permission to change any trusted semantics or skip compilation.

The final `Solution.lean` composes the full entry guard, recognizer correctness, fallback hashing, padding, schedule, paired compression, and return result. Its universal target covers every calldata satisfying `input.size < 2^64` and all sufficiently large gas budgets. The expected output is exactly twelve zero bytes followed by the 20-byte RIPEMD-160 digest. Known-input dispatch remains justified by full-input recognition, with the general implementation available for all unmatched inputs.

## Validation discipline and packaging

Cheap tests precede the expensive verifier. The installed bytes have 98 successful clean/dirty scorer executions and equal 650,152 totals. The unchanged generator passes; the changed straight-line and semantic seams pass Lean. The complete dependency-ordered closure and fresh protected canonical run have both passed. The exact bytecode and proof are ready for submission. Submission, remote validation, and leaderboard promotion are separate events and will be reported separately.

The editable surface remains exclusively `Challenge/Ripemd160/Submission`. Specifications, relational EVM semantics, `DataStepper`, the benchmark target, Comparator configuration, corpus, trusted generator, scorer, and pinned packages are unchanged. Research logs, experimental bytes, compiler traces, and build outputs are not packaged under Submission. The archive contains the current bytecode, proof sources, this public note, and the explicit dependency declarations. A transitive-import walk removed 106 unused inherited Lean modules and two stale historical documentation files; all 675 submission modules reachable from `Solution.lean` are retained.

An additional experiment measures 650,089 gas by replacing the retained round-67 `PUSH1 21; JUMPDEST` sequence with `PUSH2 21`. It has the same byte length and passes the cheap scorer and unchanged generator, but loses one instruction and therefore requires downstream instruction-index rebinding. It is not the installed artifact, is not covered by the installed proof, and is not part of this candidate's verification claim. That lead should only proceed after this candidate clears the full gate.
