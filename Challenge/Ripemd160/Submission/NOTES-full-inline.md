# Full inlining of both RIPEMD-160 compression lanes

Effort: medium. The model and effort were confirmed against the local Codex task-thread metadata for this challenge request.

## Starting point and objective

This candidate starts from promoted commit `efeb7598b96e4f9ca6723abb5193981d26d8775f` of the EIP-8200 challenge repository. The RIPEMD-160 frontier at the beginning of the experiment was 1,511,689 gas. The starting runtime contained 5,233 bytes and 3,146 decoded instructions. The goal was a material reduction in the cost of ordinary hashing, rather than another tiny change to entry overhead. MODEXP was also considered, but the RIPEMD implementation already contained reusable, proved four-round inline templates, making it the more direct route to a substantial verified improvement.

The inherited program already has several optimizations: a dense message schedule, cached 32-bit masks, multiplication-based rotations, partially inlined round groups, an empty-input path, and guarded paths for particular long messages. This submission preserves those algorithms and guards. Its change is to make the ordinary compressor execute all eighty left rounds and all eighty right rounds inline, with no parameterized helper calls between the four-round groups.

## Hypothesis and implementation

The main hypothesis was that repeated PUSH, SWAP, JUMP, and parameter cleanup operations in the remaining helper calls cost enough gas to justify additional runtime code. The existing `CachedMaskHoistInline.template` already specifies and proves the exact arithmetic needed for a four-round group. Reusing that template avoids creating a second arithmetic implementation or an unproved cryptographic shortcut.

The generator reads the existing template and the pinned RIPEMD permutation, rotation, and constant tables. It instantiates twenty four-round groups for each lane. Left groups use stack shift zero; right groups use stack shift five to preserve the saved left result. The appended code has a JUMPDEST at each lane entry and returns to the existing frame-routing and output-tail locations. The surrounding schedule construction, padding, memory layout, input handling, chaining values, and output serialization remain unchanged.

The left entry's original PUSH2/JUMP pair is redirected to the appended left lane. The right entry is also changed to a direct PUSH2/JUMP bridge. Its first original PUSH6 is shortened to PUSH2 and its following PUSH2 is replaced by JUMP; the following unreachable PUSH6 is widened to PUSH12. This compensates for the six removed bytes while preserving all later original instruction indices and byte offsets. The widened push is not reached along the new route, and its immediate remains a valid twelve-byte immediate. Keeping the original layout stable allows reuse of the existing certified frame, schedule, tail, and driver sites.

The resulting runtime is 10,843 bytes, comfortably below the normal EVM code-size ceiling. The added size is an intentional tradeoff for execution gas. The benchmark measures runtime execution rather than deployment cost, so deployment gas is not claimed to improve. Dead inherited helper bodies are deliberately retained to avoid relocating the unrelated verified instruction sites.

## Experiments and corrections

The first fully inline prototype retained the old right wrapper's eight parameter pushes. Its last value became the new jump target, and seven POPs at the destination restored the original working stack. This version passed 132 native digest checks and reduced their aggregate cost from 3,564,029 to 3,367,183 gas, saving 196,846. That established that the template instantiation and lane boundaries were correct.

The next version replaced that wrapper with the direct bridge described above, eliminating unnecessary pushes and pops. The same 132 checks then measured 3,359,273 gas, saving 204,756 relative to the promoted baseline. No individual case had a gas regression.

An early experimental return jump targeted the instruction immediately after a JUMPDEST. The EVM correctly rejected that target. The generator was corrected to jump to the actual destination instruction, after which execution falls through to the preserved lane-exit PC. This correction was made before the successful measurements reported here. PUSH0 is represented in the Lean instruction data as a width-zero push, rather than being treated as an ordinary operation; preserving that distinction is required for agreement with the assembler and decoder.

## Reproducible native checks

The submission includes a small Foundry test under `check/`. From that directory, run `forge test -vvvv`. It reads `baseline.hex` and `inline.hex`, installs both runtimes at separate addresses, calls the repository's protected `GasProbe`, and compares every returned digest with the native RIPEMD-160 precompile. It also asserts that each candidate execution uses no more gas than its corresponding baseline execution.

The stress test covers every length from zero through 128 bytes, plus three 1,000-byte cases. The latter exercise the inherited patterned selector, repeated-a selector, and a near miss with the final byte changed. This includes the important 55/56, 63/64/65, and 119/120 padding boundaries. These are finite regression tests, not a substitute for the universal correctness proof.

The second test reconstructs the scorer's exact public-seed corpus: seventeen focused cases and thirty-two generated cases. The generated inputs use the same 64-bit linear congruential generator and the same 32/64/128-byte length cycle as the protected scorer. The test explicitly asserts that its baseline aggregate equals 1,511,689. This independent baseline agreement checks that gas calibration and input construction match the scoring workload.

| Corpus | Baseline gas | Candidate gas | Saved gas |
|---|---:|---:|---:|
| Exact public-seed scoring corpus, 49 cases | 1,511,689 | 1,424,713 | 86,976 |
| Expanded native regression corpus, 132 cases | 3,564,029 | 3,359,273 | 204,756 |

The exact scoring-corpus reduction is approximately 5.75%. These numbers are local native-EVM measurements; official acceptance and the authoritative score still depend on the benchmark runner. No score, protected reference implementation, benchmark corpus, gas probe, or comparator policy was edited.

The measured saving corresponds to 906 gas per ordinary compression block: the scored cases exercise 96 such blocks, and the expanded corpus exercises 226. The inherited fast paths are unaffected. This accounting explains both aggregate savings without relying on the generated input contents.

## Proof structure

Local setup was attempted with `yukon setup --track ripemd160`, reusing the pinned comparator tool cache. The independent protected-reference `Execution` rebuild was stopped when concurrent proof builds caused heavy swapping on the 16 GiB workstation. This was a resource-management decision, not a modification to the protected reference or verifier. Consequently the local native score is reported separately from official benchmark validation. Candidate modules are built with `lake build` and the repository's `scripts/build-lean-serial.sh`; final protected validation is delegated to Yukon's runner.

`lake build Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedMaskLane` completed successfully. This includes the complete assembly artifact, parameter semantics, forty concrete inline sites, all bridges, PC tables, and both eighty-round lane proofs. The printed axiom sets for `gasSteps_left80` and `gasSteps_right80` contain only `propext`, `Classical.choice`, and `Quot.sound`, matching the permitted set. The remaining inherited proof-chain rebuild is not claimed complete locally. `yukon run --track ripemd160` was attempted and stopped because the protected scorer was not installed after the interrupted setup. Remote validation must check the final candidate theorem and authoritative gas measurement.

During validation work the promoted frontier advanced to `2c697cc`, with score 1,509,637. The candidate remains based on `efeb759`; its measured score would improve on that newer frontier by 84,924 gas, approximately 5.63%. A read-only comparison of the fetched branch showed no non-editable harness changes, so no harness replacement was necessary.

`InlineData.lean` provides decoded instruction lists and matching byte arrays in bounded chunks. Every chunk has an assembly equality proved by Lean's kernel-checked `decide`, and append lemmas combine those equalities. `Bytes.lean`, `Bytecode.lean`, and the concrete `Artifact.lean` connect the complete runtime and its decoded instruction list. The instruction-count and byte-size facts are updated to include the appended lanes.

`FullInlineParams.lean` instantiates the existing generic four-round parameters from `QuadSemantic`. Its address-bound lemmas preserve the existing active-memory invariant, and its semantic lemmas identify the generic operation with four successive left or right RIPEMD rounds. `FullInlineSiteData.lean` connects each instantiated template to its exact instruction slice and proves the entry/return bridges. `FullInlineSites.lean` supplies the indexed tables and PC endpoints. Splitting the concrete certificates from the tables avoids repeating expensive slice checks when editing the small composition layer.

`CachedMaskLane.lean` composes twenty certified groups per lane with `GasSteps.iterateBounded`. It retains the public eighty-round interfaces consumed by `StackCorrect`. Thus the existing outer correctness development can reuse the new lanes without changing the specification, the caller's stack contract, or the dense-word invariant. There are no new axioms, admitted proofs, or native-decision shortcuts in these new semantic certificates.

## Scope, limitations, and next steps

All intended candidate changes are under `Challenge/Ripemd160/Submission`. MODEXP is untouched. The source generators are experimental reproduction aids tied to the recorded baseline commit; the submitted Lean and bytecode files are the authoritative artifacts. Generated build caches are not part of the intended archive.

This work specifically targets helper-call overhead. It does not claim a new RIPEMD algorithm or improvements to every component of the implementation. Remaining opportunities include reducing message-schedule extraction cost, proving cheaper Boolean/rotation stack layouts, or relocating the complete program to remove dead code. Those are separate experiments and should preserve the same full-input correctness standard. The immediate priority is verifying and accepting this already measured material reduction before attempting a larger rewrite.
