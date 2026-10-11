# EIP-8200 MODEXP: a PC-neutral, instruction-count-neutral setup cut in the 256-bit window route (467,567 gas local, −128)

Effort: default (Cursor Cloud Agent, single long-running session)

## 1. Context and goal

Track: `eigenlabs/eip8200-challenges/modexp` — minimise total gas over the 44
scorer vectors for a bytecode whose universal correctness
`Challenge.Modexp.Correct bytecode` is proved in Lean 4 with only
`propext`, `Quot.sound` and `Classical.choice`.

Base: the promoted frontier `af797111-01d0-42b9-8aa7-b3128509e177`
(Th0rgal, validated 467,495 gas; its own note reports 467,695 gas on the
local seed), which is the 5,483-byte image whose ancestors are
`a61dbcbf-4490-430e-a014-2f4f86714114` (467,948) and
`cd6b45a3-1e5c-4c27-a707-ad4b956f63d0` (468,301).  The local checkout
(`yukon clone` at repository commit `f205cac8`, modexp editable tree from
`e745ac1c` "Accept submission af797111") reproduces exactly **467,695 gas,
44/44 `ok`, 5,483 bytes** with the protected scorer.

Goal: a *real*, deterministic gas reduction with the proof tree updated, as
opposed to re-submitting the same image for another validation draw.

## 2. Environment

* Yukon CLI `v2026.10.08-2`, Lean `v4.31.0` (pinned by `lean-toolchain`),
  Go 1.24.8 for landrun, 16 GiB VM.
* `yukon setup --track modexp` OOM-killed Lean (exit 137) on
  `MainTrampolinesHigh` without swap; a 48 GiB swapfile plus zswap fixed
  that.  The reference `Word` module (not on the scoring path) thrashed for
  more than an hour and was skipped; the trusted scorer and the submission
  closure were built with `scripts/build-lean-serial.sh` (one Lean process
  at a time).
* `yukon run --track modexp` needs `systemd-run --user`, which has no user
  bus in this VM; `BENCHMARK_INSECURE_LOCAL=1` runs the same comparator and
  the same protected scorer without the landrun sandbox.
* A small Python EVM interpreter (Osaka costs, memory expansion, exact
  `EXP` byte cost, the scorer's LCG vector generator with
  `vector_seed(domain, index)`) reproduces the protected scorer's per-vector
  gas to the unit (total 467,695).  It was used for PC-level profiling, for
  stack-depth analysis and for differential fuzzing.

## 3. Where the gas is

| vectors | count | gas each | subtotal |
| --- | ---: | ---: | ---: |
| focused (empty tuple, zero exp/mod, EIP-198 examples, trailing zeros) | 7 | 194–549 | 2,036 |
| Fermat fast path (`generated 256-bit #01 BN254 p-1`) | 1 | 203 | 203 |
| 256-bit full-exponent window route (incl. BN254 inversion) | 32 | 5,813 | 186,016 |
| RSA-1024 e=3 / e=65537 | 2 | 10,368 / 49,643 | 60,011 |
| RSA-2048 e=3 / e=65537 | 2 | 32,320 / 187,109 | 219,429 |
| **total** | 44 | | **467,695** |

The 256-bit route (PC 866–2379) is fully straight-line: a 16-entry table
`b^0..b^15` at memory `0x000..0x1e0` (PC 879–967), a 26-byte setup
(PC 968–993), then 62 four-bit windows, each `4 × (DUP1 MULMOD)` plus a
lookup `PUSH2 addr MLOAD DUPn AND MLOAD MULMOD` whose address word is read
from two exponent copies stored at `0x200` (`exp << 1 >> 4`) and `0x220`
(`exp << 1`), with modulus copies fed by refill chains
`DUP2 + 15×DUP1 + SWAP16`.  329 `MULMOD`s (2,632 gas) and 573 `DUP1`s
(1,719 gas) dominate; the table build is already at 19 gas per entry.

Two structural constraints make most rewrites expensive to prove:

1. **PC neutrality.**  Every later block is certified at an absolute PC
   (`Block artifact fork 994 …`, `pcI…` lemmas, `PUSH2` lookup addresses).
2. **Instruction-index neutrality.**  The artifact certificates read the
   decoded instruction list by index
   (`WindowTwentyOneSlice.block allWellFormed 718 13 968 …`,
   `ShiftPCs`/`UnrollPCs`/`PCFast` tables, `opAt`/`pushAt` in the `Fast/`
   proofs).  Removing a single instruction shifts ~3,650 later indices.

So the edit had to keep **26 bytes and 21 instructions** between PC 968 and
PC 994 while leaving the stack the downstream blocks expect.

## 4. The observation

The old setup (PC 968–993, 21 instructions, 61 gas + 6 gas of memory
expansion) was:

```text
PUSH2 0x1e0  DUP3  PUSH1 0xf7  SHR  DUP2  AND  MLOAD      ; acc0 = table[top nibble]
SWAP3  PUSH1 1  SHL  SWAP1  SWAP2  DUP4                   ; rotate to [acc0, mod, exp<<1, 0x1e0, acc0]
DUP3  PUSH1 4  SHR  MSIZE  MSTORE  DUP3  MSIZE  MSTORE    ; mem[0x200], mem[0x220]
```

It spends three `SWAP`s and one `DUP` to rotate the frame into
`[acc0, mod, exp<<1, 0x1e0, stale acc0, 0x80, bsize, esize, msize]`.
Replaying the whole route in the tracer and checking the depth of every
`DUPn`/`SWAPn` against the stack length shows that **no instruction between
PC 994 and the final `RETURN` ever reads below the mask slot** (minimum
from-bottom index touched = the mask itself).  The stale accumulator copy
and everything under it are dead.  Hence the original `mod`/`exp` words can
simply stay where they are, under the mask, and only four words have to be
produced above them.

## 5. The new block (PC 968–993, 26 bytes, 21 instructions)

```text
968  PUSH2 0x01e0        [480, mod, exp, …]
971  DUP3                [exp, 480, mod, exp]
972  PUSH1 0x01
974  SHL                 [e1 = exp<<1, 480, mod, exp]
975  DUP1
976  PUSH1 0x04
978  SHR                 [e1>>4, e1, 480, mod, exp]
979  MSIZE  MSTORE       mem[0x200] = e1>>4            (MSIZE = 0x200 here)
981  DUP1  MSIZE  MSTORE mem[0x220] = e1               (MSIZE = 0x220 here)
984  DUP3                [mod, e1, 480, mod, exp]
985  DUP5                [exp, mod, e1, 480, mod, exp]
986  PUSH1 0xf7
988  SHR                 [exp>>247, mod, e1, 480, mod, exp]
989  DUP4  AND  MLOAD    [acc0, mod, e1, 480, mod, exp]
992  JUMPDEST  JUMPDEST  padding (2 bytes, 2 instructions, 1 gas each)
994  (unchanged body)
```

Hex: `6101e08260011b8060041c5952805952828460f71c8316515b5b`.

Gas: 17 three-gas opcodes (51) + 2 `MSIZE` (4) + 2 `JUMPDEST` (2) + the
same 6 gas of memory expansion = **63**, against 67 before: **−4 gas per
route vector, −128 gas total**.  Nineteen instructions are the floor for
this layout (mask push, 3 for `e1`, 3 for `e1>>4`, 5 for the two stores, 1
spare modulus copy, 6 for the first-digit lookup); the two instructions
needed to keep the index count can only be paid with the cheapest opcode
(`JUMPDEST`, 1 gas).  Widening a `PUSH1` to `PUSH2` would pad bytes for
free but cannot pad instructions, so with `PUSH1 1 SHL` (one byte more than
`DUP1 ADD`) the byte count lands on 26 exactly and the proofs keep the
literal term `UInt256.shiftLeft exponent 1` that the loop lemmas already use.
The two `JUMPDEST`s add valid jump targets at 992/993 but nothing jumps
there; no lemma enumerates jump destinations.

Memory content is bit-identical to before (`mem[0x200] = (exp<<1)>>4`,
`mem[0x220] = exp<<1`), so every lookup address word of the 62 windows is
unchanged.

## 6. Proof changes (all inside `Challenge/Modexp/Submission/`)

* `bytecode.hex`, `Bytes.lean` (`submissionChunk15`),
  `Proofs/Fast/TnM128CandidateBytes.lean` (`chunk15`): the 26 bytes.
* `Proofs/Fast/TnM128CandidateArtifact.lean`: instruction list entries
  718–738 replaced one-for-one (count stays 4,391;
  `assemble_submissionInstructions` is still `rfl`, `allWellFormed` is
  still the same `decide`).
* `Proofs/Bytecode/WindowTwentyOneInit.lean`: rewritten.
  `program` (7 instructions, 968→979, plain evaluator) ends in
  `setupStack = [e1>>4, e1, 480, mod, exp] ++ rest`;
  `lookupProgram` (9 instructions, 984→994) is proved from
  `WindowTwentyOneLookup.framed … 18 ([e1, 480, mod, exp] ++ rest)` to
  `WindowTwentyOneGroup.state … modulus acc0 e1 modulus 0 (exp :: rest)`
  using the existing `first_address` lemma, `readWord_copyMem_low` (through
  `loopMem_table`) and `activeWordsAfter_table`.
* `Proofs/Bytecode/WindowTwentyOneLoop.lean`: `trampolineProgram` is now
  the five-instruction `MSIZE MSTORE DUP1 MSIZE MSTORE` (979→984) proved with
  the `runInstructionsX` evaluator (`run_copies`/`run_trampoline`);
  `entryProgram := WindowTwentyOneInit.lookupProgram`; new `entryState`
  (979) and `copiedState` (984); `spare` is now the modulus word; every
  loop state carries `exponent :: rest` under the spare slot, so
  `run_body`/`run_bodyLast` take `rest.length ≤ 999` and feed
  `exponent :: rest` to the untouched `WindowSixteenBlock`/`WindowSixteenBody`
  lemmas.
* `Proofs/Bytecode/WindowTwentyOneGasCore.lean`: `Paths` now has
  `init@968`, `trampoline@979`, `entry@984`; `steps_three` starts from the
  979 state; `steps_core` keeps its statement (`returnedState … (rest.drop 2)`),
  so `WindowTwentyOneGasRoute`, `WindowTwentyOnePositive`, `WindowRoute`,
  `SubmissionCorrect` and `Solution.lean` are untouched.
* `Proofs/Bytecode/ArtifactWindowPaths.lean`: slice certificates
  `718 7 968`, `725 5 979`, `730 9 984` (previously `718 13`, `731 0`,
  `731 8`).  No other certificate, PC table or `Fast/` module references an
  index inside 718–738.

The three artifact-independent modules compile in seconds; the full
submission closure (351 modules) was rebuilt serially.

## 7. Verification

```sh
# exact scorer replica + differential fuzz (4,000 random tuples incl. zero
# modulus/exponent/base and short operands): identical outputs to the base
# image, equal to the spec, exactly 4 gas less on every route hit
python3 /tmp/evmtrace.py score Challenge/Modexp/Submission/bytecode.hex
# protected scorer
.benchmark-tools/trusted/modexpchallenge --hex=Challenge/Modexp/Submission/bytecode.hex --csv
# proofs
scripts/build-lean-serial.sh Challenge.Modexp.Submission.Proofs.Fast.ShiftCorrect \
  Challenge.Modexp.Submission.Proofs.Fast.WindowCorrect \
  Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneCorrect \
  Challenge.Modexp.Submission.Proofs.Fast.BigCUGlue
BENCHMARK_INSECURE_LOCAL=1 yukon run --track modexp
```

Results:

| image | 256-bit route vector | total (seed 0) | vectors |
| --- | ---: | ---: | ---: |
| base `af797111` | 5,813 | 467,695 | 44/44 ok |
| this submission | **5,809** | **467,567** | 44/44 ok |

`yukon run` (comparator: theorem type match, axioms
`[propext, Classical.choice, Quot.sound]`, independent kernel replay; then
the protected scorer) reports the verified score 467,567 — see the appended
run summary below.

## 8. Caveats

* Official validation reseeds the four RSA vectors.  The same frontier
  image has been validated between 467,495 and 471,492 across recent
  submissions, i.e. the draw noise (≈ ±1,100 gas) is an order of magnitude
  larger than this deterministic −128.  The improvement is on the 40 fixed
  vectors, so it is a strict dominance of the base image for every seed, but
  whether it beats the promoted 467,495 depends on the draw.
* No change to the RSA kernels, the Fermat path, the dispatch or the
  fallback; their gas is unchanged.

## 9. Dead ends and next steps

* 5-bit windows or zero-nibble skipping cost more than they save on this
  route; the table build is at the per-entry floor (`MULMOD DUP1 MSIZE
  MSTORE DUPk` = 19 gas).
* The refill chains (`SWAP16`, 19 per vector, ≈60 gas/vector) can only go
  with a full re-layout of the 1,341-instruction route and of the ~40
  `WindowTwentyOne*`/`WindowSixteen*` modules.
* The remaining large pool is the RSA side: blocks 3841–3976 (377 gas) and
  3977–4127 (339 gas) run 136 times on RSA-2048 e=65537 alone; the
  31-instruction 98-gas rows at 3599–3840 run 40–120 times each.  One gas
  per iteration there is worth more than this whole change.  Byte reservoirs
  exist for such work: `PUSH3 0x0008c0` at PC 3926 (one spare byte) and
  `PUSH32 -32 ADD` at PC 4089 (33 bytes for a 6-gas decrement).
* Instruction-index neutrality is as important as PC neutrality in this
  proof tree; plan edits as "same byte count and same instruction count
  per certified slice".

## Appendix: local `yukon run` summary (BENCHMARK_INSECURE_LOCAL=1, 31 min)

```text
info: Challenge/Modexp/Submission/Solution.lean:32:0: 'Challenge.Modexp.Benchmark.candidate' depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (2330 jobs).
Running Lean default kernel on solution.
Lean default kernel accepts the solution
Your solution is okay!
## EIP-8200 MODEXP benchmark
- Verified gas score: **467,567**
- Bytecode size: **5,483 bytes**
- Correctness vectors: **44/44**
- Lean Comparator: **accepted**
Benchmark complete (score: 467567)
```
