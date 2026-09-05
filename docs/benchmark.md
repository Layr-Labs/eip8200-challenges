# Yukon benchmark

This repository is one schema-v2 Yukon challenge with two independently
scored tracks on a shared branch:

| track | editable path | score |
| --- | --- | --- |
| `modexp` | `Challenge/Modexp/Submission` | total gas over the benchmark vectors |
| `ripemd160` | `Challenge/Ripemd160/Submission` | clean-state gas over the benchmark vectors |

Lower is better in every track. The editable paths are deliberately disjoint,
so Yukon can promote one track without replacing a sibling track's solution.

## Public and benchmark vectors

Public vectors live in `test-vectors/modexp.json` and
`test-vectors/ripemd160.json`. Anyone can run them locally:

```sh
lake exe modexpchallenge --vectors=test-vectors/modexp.json
lake exe ripemd160challenge --vectors=test-vectors/ripemd160.json
```

The actual benchmark uses separate JSON stored in two GitHub Actions repository
secrets: `MODEXP_BENCHMARK_VECTORS` and `RIPEMD160_BENCHMARK_VECTORS`.
Each secret contains a complete vector file in the [same format](../test-vectors/README.md).
An administrator can set them from files kept outside the public repository:

```sh
gh secret set MODEXP_BENCHMARK_VECTORS < /path/to/private-modexp.json
gh secret set RIPEMD160_BENCHMARK_VECTORS < /path/to/private-ripemd160.json
```

Keep each JSON secret below GitHub's [48 KB limit](https://docs.github.com/en/actions/reference/security/secrets).
The workflow passes the selected secret to `benchmark.sh`, which writes it to a
temporary file after proof verification and gives that file to the existing
scorer. Missing secrets fail the benchmark. Private vectors and per-case results
are not uploaded; the score includes the vector count and SHA-256 of the suite.
Keep the secrets fixed while comparing scores; changing a suite changes the benchmark.

Non-ranked local `benchmark.sh` runs use the public JSON when no secret is set.
The CLI runners without `--vectors` still use the original built-in gas-report
vectors.

## Selecting a track

`yukon switch <track>` changes only the repository-local Yukon selection. It
does not change the Git branch, `HEAD`, index, or worktree. Run
`yukon tracks` to see the current selection.

Record meaningful progress with `yukon notes add`: baselines, hypotheses,
experiments, failures, design changes, and blockers are useful to later
solvers. Notes are public; remove secrets, private paths, personal data, and
credentials before uploading them.

## Proof and scoring boundary

Each track accepts an editable `bytecode.hex` and Lean `Solution.lean`.
`benchmark.sh` reads the hex once, copies it outside the editable surface, and
generates a trusted `ByteArray` literal. The trusted challenge and submitted
solution state the same `candidate` theorem for that literal.

Comparator checks the theorem type, permits only `propext`, `Quot.sound`, and
`Classical.choice`, and replays the proof with an independently built kernel.
Only after that succeeds does a protected, precompiled scorer execute the same
protected bytes and write the track's score JSON.

Comparator and its `lean4export` are pinned in `setup.sh`. Linux ranked runs
use Landrun plus a `systemd-run` address-family restriction. A functional,
non-security-bearing local run is available on macOS:

```sh
./setup.sh modexp
BENCHMARK_INSECURE_LOCAL=1 ./benchmark.sh modexp
```

Replace `modexp` with `ripemd160` for the other track. The two dispatch-only
workflows run the same shared implementation with a fixed track argument and
upload only that track's declared `scorePath`.

Setup elaborates the selected trusted proof closure in dependency order because
individual concrete-execution modules are memory intensive. Each Lake
invocation sees at most one stale module, and the package fixes Lean's own worker
count at one. The resulting Lake traces are reused by Comparator, so proof
checking is not repeated with a concurrent build later.
