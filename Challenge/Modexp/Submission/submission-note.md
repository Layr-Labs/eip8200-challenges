# MODEXP: skip clearing the overwritten Montgomery carry flag

## Result and scope

This submission is a small, fully checked optimization of the existing MODEXP implementation. The local trusted score decreases from **771,070 to 770,956 EVM gas**, a reduction of **114 gas** across the pinned corpus. The submitted bytecode remains **5,137 bytes**. All **44 local correctness vectors** pass, and the protected Comparator reports that an independently built Lean kernel accepts the exported solution.

The implementation change is commit `ce6753a`, based on the local starting revision `80a9a79`. The clean archive is taken from `50cab12`, which also includes a diagnostic profiler and a wrapper for serializing memory-heavy proof prerequisites. Those helpers do not replace the protected verifier. Only the MODEXP submission directory is uploaded; no scorer, specification, benchmark manifest, protected artifact, or sibling track is changed.

The coding agent used GPT 6 Astra with medium effort in Codex. Model and harness attribution are also supplied through Yukon's dedicated submission options. This note documents the observable implementation and validation work; it does not claim that this small delta beats the current public frontier.

## Starting implementation and measured workload

The starting solution already contains several specialized arithmetic paths and extensive Lean proofs connecting its instruction list to exact assembled bytes and to the modular-exponentiation specification. The work here reuses that implementation rather than replacing its arithmetic architecture.

The local manifest is schema version 2, and the selected track is `modexp`. Its editable surface is `Challenge/Modexp/Submission`. Although the task description mentioned 13 public cases and paired execution worlds, the checked local harness contains 44 vectors. All score totals in this note refer to that local, pinned 44-vector corpus. The independent dirty-state diagnostic is reported separately below; it is not represented as an additional protected scoring suite.

Profiling the pinned EVM implementation identified repeated Montgomery multiplication initialization as a safe place to remove redundant work. The four RSA cases dominate much of the remaining cost. This patch affects 38 Montgomery calls and removes one cleared memory word from each, matching the observed 114-gas total reduction.

## Exact implementation change

The initialization sequence clears a scratch range before executing Montgomery rows. The carry flag at memory offset 8192 is overwritten by the first row before any read needs the old value. Clearing that one word first is therefore redundant.

The patch changes two immediate bytes while preserving every instruction width, downstream program counter, and overall code size:

- At byte offset 1954, the immediate changes from `0x40` to `0x20`.
- At byte offset 1959, the immediate changes from `0x00` to `0x20`.

Together these change the cleared length from `64 + 32*n` to `32 + 32*n`, and move the clearing destination from 8192 to 8224. The end of the cleared range stays unchanged. The new cleared interval is `[8224, 8256 + 32*n)`. The carry flag is no longer part of that interval, but its first write is still performed by the existing row code.

This is not a precomputed answer table, a corpus-specific result substitution, or a use of the native MODEXP precompile. The existing arithmetic algorithm remains responsible for the result. The corresponding proof changes establish the new initialization and preservation conditions under the same specification.

## Byte/proof binding and changed modules

The exact bytes in `bytecode.hex` are reflected in `Bytes.lean` and the concrete instruction list in `Proofs/Bytecode/Artifact.lean`. The submitted `Solution.lean` continues to expose its correctness theorem through the existing route proof, and imports the generated artifact used by the protected challenge.

The proof changes are concentrated in:

- `MonproKNRowPrograms.lean`, for the revised instruction sequence;
- `MonproKNEntryZero.lean`, for the revised entry clearing behavior;
- `Fast/MonproRowModel.lean`, for the row-level memory model;
- `Fast/MonproPreserveModel.lean`, for the preservation condition;
- `Fast/Monpro.lean`, for composition with the existing Montgomery correctness argument.

The proof is not weakened to cover only the scored examples. The public vectors are an execution check; the submitted theorem still proves the challenge's `Correct` predicate for the exact submitted byte array. No new axiom, `sorry`, or native decision shortcut is introduced by the kept change.

## Reproduction and validation

The fast execution diagnostic is:

```bash
.benchmark-tools/trusted/modexpchallenge \
  --hex=Challenge/Modexp/Submission/bytecode.hex --csv
```

The complete local gate was run with:

```bash
bash Challenge/Modexp/Submission/verify.sh
```

That wrapper first builds `MainTrampolinesLow` and `MainTrampolinesHigh` serially, then runs the unchanged `./benchmark.sh modexp`. The two prerequisites are serialized because a prior concurrent build exhausted local memory. The local Lean job setting was reduced to 32 with the user's approval. That build-resource setting is outside the submission archive and is not an arithmetic or scorer change.

The successful full run reported:

| Check | Result |
| --- | --- |
| Independent Lean kernel | Accepted |
| Trusted vectors | 44 of 44 |
| Total gas | 770,956 |
| Bytecode size | 5,137 bytes |
| Full service runtime | Approximately 82 minutes |
| Peak service memory | Approximately 41.8 GB |

The exact success messages included “Lean default kernel accepts the solution” and “Your solution is okay!”. The source files and bytes were kept only after that complete run succeeded.

## Dirty-state diagnostic

The separate `Profile.lean` helper runs the pinned EVM semantics and checks that execution actually returns, as well as checking returned bytes against the modular-exponentiation specification. Its dirty mode uses nonzero storage, transient storage, and call value. It is run with:

```bash
lake env lean --run Challenge/Modexp/Submission/Profile.lean --dirty
```

All 44 vectors passed this diagnostic, with the same 770,956-gas total. This adds useful execution evidence that the removed clear is not relying on those deployment fields being zero. It does not replace the Comparator, and no claim is made that it exhaustively samples all possible machine states.

## Other experiments and exclusions

Seven gas candidates were screened during the bounded research loop. A shift-for-multiplication change on a legacy path did not change the score and was discarded. A first-Newton-step simplification measured an additional 48-gas saving in diagnostics. A short-base load path also passed the scored examples with a smaller total. Neither of those candidates is included in this archive because its complete exact-byte proof gate was not finished.

A larger dual-prime Fermat shortcut, combined with the Newton simplification, measured 760,698 gas in diagnostics. The general arithmetic and execution lemmas compiled separately, but its concrete prime-certificate check reached a 15-minute timeout without a validated result. That candidate is therefore not submitted. Its unfinished certificate, experimental Lean modules, alternate bytecode files, and local research logs are excluded from this clean archive.

This distinction is important: diagnostic success is evidence for a future candidate, not permission to describe that candidate as independently kernel-verified.

## Limitations and useful follow-up

The accepted saving is deliberately modest and preserves the existing proof layout. Public Yukon results have advanced beyond this local starting point; at submission preparation time the displayed frontier was 743,585 gas. Consequently this upload may be valid without being promoted.

Potential follow-up work includes the small Newton simplification, avoiding additional redundant Montgomery memory work, and proving any larger arithmetic shortcut before changing the submitted route. A useful next experiment should compare against the newest frontier and still bind the exact bytes to a replayable theorem. None of those future possibilities is part of the result claimed here.

