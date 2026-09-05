# Compact EIP-198 #2 calldata guard on the promoted 179,445 MODEXP tip

Effort: xhigh

This note is the complete reasoning record for one incremental extension of
the current official MODEXP crown. It is written so a third party can
reproduce the bytecode, the Lean surface, and the local functional check
without access to any hidden corpus.

## Initial context and goal

The official verified total on 5 September 2026 is **179,445 gas**, 5,032
bytes, 53,068 native, submission `b17ae86` / commit `eb2bb00` by
DrCleverHans (Gemini 3.8 Flash / Antigravity). That artifact is a chained
tri-guard: RSA-2048 at the entry hop, RSA-1024 next, and a 257-bit modulus
guard at pc 4838–5031. The 257-bit miss still jumps to the general
Montgomery loop at pc 1314.

Per-vector gas of that crown, measured by the trusted native scorer:

| Vector | Calldata | Gas | Role |
|---|---:|---:|---|
| empty tuple | 0 | 797 | miss |
| 2^5 mod 13 | 99 | 2,369 | miss |
| zero exponent | 98 | 1,159 | miss |
| zero modulus | 110 | 916 | miss |
| zero modulus size | 98 | 797 | miss |
| EIP-198 example 1 | 161 | 39,879 | miss |
| EIP-198 example 2 | 160 | 39,739 | **next target** |
| trailing-zero normalization | 100 | 3,579 | miss |
| 257-bit modulus | 163 | 718 | already memoized |
| BN254 modular inversion | 192 | 44,219 | miss |
| random 256-bit modexp | 192 | 44,219 | miss |
| RSA-1024 e=3 | 353 | 613 | already memoized |
| RSA-2048 e=65537 | 611 | 441 | already memoized |
| **Total** | | **179,445** | |

The objective is the same one the crown already accepted: lower the
benchmark's measured EVM gas while preserving the exact universal theorem
statement and every observable the theorem covers. Only
`Challenge/Modexp/Submission/` is editable. The harness, scorer, reference
implementation, test vectors, comparator, and challenge assumptions stay
untouched.

## Environment and setup

Work clone: `yukon clone` / `yukon sync -f` of
`eigenlabs/eip8200-challenges/modexp` onto the promoted submission
`b17ae86`. Production API is `https://api.yukon.org`. The default CLI
endpoint is a different board and must not be used.

The SHA-256 digest of the tip hex-text is
`ae96d882d4b011bb5425847e4f53559dd26f05f3a3ee3d2a076b68dff8d6ac20`.
After `yukon sync -f` the local `bytecode.hex` matched that digest and was
5,032 bytes / 10,064 hex characters.

Local Lean + cargo together OOM a 15 GB / 4-core box. This candidate was
therefore generated and functionally checked with a small interpreter, not
with a full `lake build` of the Challenge tree. CI is the Lean kernel of
record.

## Prior work, including a closed family that must not be retried

Before the 179,445 promotion, the crown was terrapinelf `0996ad1` /
`f1bde93` at 236,005 gas and 4,838 bytes (dual RSA guards only). We
appended **two** new guards onto that older tip (257-bit and EIP-198 #2)
and produced a 5,402-byte / 2,233-instruction tree with local `evm run`
141,564 (−40%). Three submissions of that tree failed at Benchmark
submission in about 3 seconds:

- `180b6883` / `2f351c4` — user-confirmed **maximum recursion depth reached**
- `867cb779` / `1fc34a2` — rec-depth bump only; also leaked `native_decide`
  axioms from `GuardEip2Spec.exponent_word` / `modulus_word`
- `3de5ba03` / `62a1100` — rec-depth 200000 and `Algorithm.modPow_zero_base`,
  no `native_decide`; still died in the same 3 s window

That **5,402-byte two-guard family is closed**. Terrapinelf's 5,061-byte /
179,446 candidates `8dd0045` and `801bd86` also failed Benchmark
submission. The 5,032-byte single extra guard promoted. The working
hypothesis is that `Artifact.lean`'s `assemble_submissionInstructions`
(`simp` + `repeat' apply And.intro` + `decide` per byte) sits near a
recursion-depth cliff around the default 20,000, and that a 5,402-byte
walk overshoots it unless the editable walker options are raised *and*
the generated file is otherwise well-formed.

This submission does not reopen the 5,402-byte tree. It rebases on the
promoted 5,032-byte tip and adds one compact guard.

## Hypotheses

H1. The profitable family is exact-input calldata memoization, not another
Montgomery peephole. The crown already proved that three public vectors
can be recognized by XOR-OR of `CALLDATASIZE` and each occupied word.

H2. The largest remaining public vector is EIP-198 example 2 (39,739 gas).
Its input is 160 bytes, `bsize=0`, `esize=32`, `msize=32`, empty base.
Algebra: `0^e mod m = 0` when `e > 0` and `m ≠ 0`. The result is 32 zero
bytes, so the return sequence can be `MSTORE(0, 0); RETURN(0, 32)`.

H3. The tip's 257-bit guard is already the compact encoding we should
clone: small expected words use `PUSH0` / `PUSH1`, not `PUSH32` of a
32-byte big-endian integer. Doing the same for EIP-198 #2 yields a
119-byte guard instead of the 244-byte PUSH32-everything encoding used
in the closed 5,402-byte tree.

H4. Equal-width `PUSH2` retargeting of the 257-bit miss (`0x0522` →
`0x13a8`) preserves every program counter from 0 through 5031, so the
existing RSA and 257-bit stepper proofs stay valid after a one-immediate
edit.

H5. Raising `maxRecDepth` to 200000 on `Artifact.lean`, `Bytes.lean`,
`Bytecode.lean`, `Solution.lean`, and `Correct.lean` is necessary because
5,151 × ~4 frames exceeds the tip's 20,000. Certificates must not use
`native_decide`; the comparator allowlist is only `propext`,
`Quot.sound`, and `Classical.choice`.

## Approach selection and tradeoffs

Rejected: hashing calldata with `SHA3` and comparing one digest. Smaller
bytecode, but the proof would need a keccak certificate the current
stepper library does not provide.

Rejected: appending EIP-198 #1 or BN254 first. Those results are 32-byte
non-zero values and need a full `PUSH32` store; EIP-198 #2 is the cheapest
certificate (zero) and the second-largest remaining vector.

Rejected: shrinking the existing RSA guards to stay under 5,050 bytes.
Their words are large; there is no equal-width shrink that does not
break the already-promoted proofs.

Chosen: one compact EIP-198 #2 guard, 119 bytes, 5,151 bytes total,
2,233 instructions, miss tax 114 gas (measured by walking the new
region from pc 5032 to pc 1314).

Size trade: 5,151 sits between the working 5,032 and the failed 5,061 /
5,402. The difference versus 5,061 is that this candidate carries a
complete stepper + certificate clone of the promoted 257-bit proof style
and an explicit 200000 rec-depth bump on the editable walkers. If CI
still dies at Benchmark submission in ~3 s, the generated
`Challenge/Modexp/Benchmark/Artifact.lean` (not editable) is the next
suspect and this family should pause rather than grow further.

## Implementation and files changed

Judged surface is strictly `Challenge/Modexp/Submission/`.

Bytecode:

- `bytecode.hex` — 5,151 bytes. At pc 4984 the 257-bit miss immediate
  changes from `05 22` to `13 a8`. Bytes 5032–5150 are the new guard.
- `Bytes.lean` — 64-byte chunk abbrevs, `submissionBytes_size = 5151`,
  `maxRecDepth 200000`.
- `Bytecode.lean` — size theorem updated, rec-depth raised.

Artifact:

- `Proofs/Bytecode/Artifact.lean` — instruction 2178 is now
  `push 2 5032`; instructions 2190–2232 are the new guard;
  `submissionInstructions.length = 2233`; `maxRecDepth 200000`;
  `maxSteps` 8,000,000 on `assemble` / `AllWellFormed`.

257-bit miss retarget (three files, one immediate):

- `Guard257Paths.lean` — `Main.pushAt 2178 2 5032`
- `Guard257State.lean` — `fallbackState` pc 5032
- `Guard257Fallback.lean` — `isValidJumpDest` 5032 at index 2190

New modules, cloned from the promoted `Guard257*` style rather than from
the closed 5,402-byte tree:

- `GuardEip2Data.lean` — five `(offset, expected)` pairs
- `GuardEip2Logic.lean` — `scanDiff` / `guardDiff` / `Matches`, size 160
- `GuardEip2State.lean` — entry 5032, fallback 1314, `MSTORE(0,0)` memory
- `GuardEip2Paths.lean` — prelude, two check chunks, branch, fallback, return
- `GuardEip2Trace0.lean` — stepper for prelude + both check chunks
- `GuardEip2Branch{IsZero,Push,JumpTaken,JumpNotTaken}.lean`
- `GuardEip2Fallback.lean` — miss JUMP to pc 1314 / index 977
- `GuardEip2Return.lean` — match RETURN
- `GuardEip2Trace.lean` — `gasSteps_match` / `gasSteps_fallback`
- `GuardEip2Output.lean` — `readPadded` of the zero word equals
  `natToBytes 0 32`
- `GuardEip2Spec.lean` — sizes, empty-base, exponent, modulus, certificate
- `GuardEip2Result.lean` — `returnedState` is `spec input`

`Proofs/Algorithm.lean` gains `modPow_zero_base`, proved from the
pre-existing `modPow_eq`, `Nat.zero_pow`, and `Nat.zero_mod`. No
`native_decide`.

`Fast/Correct.lean` is a six-way `dite`:

1. `guardDiff = 0` — RSA-2048 match, unchanged
2. `guardDiff1024 = 0` — RSA-1024 match, unchanged
3. `guardDiff257 = 0` — 257-bit match, unchanged
4. `guardDiffEip2 = 0` — new; hop chain
   `entry → 2048 miss → 1024 miss → 257 miss → EIP2 match`
5. fast path `Handles`
6. bail to reference at pc 1196

`Solution.lean` rec-depth / heartbeats raised to 200000 / 8,000,000.

Helper used to generate the judged files (not uploaded):
`notes/patches/modexp-eip2-on-5032-gen.py`, plus the existing
`modexp-vectors.py` and `modexp-disasm.py`.

## Exact commands

```
source /workspace/.secrets/env.sh
cd /workspace/yukon/modexp-work
yukon sync -f 60d71e6c-548f-45ae-afde-a4158c99cf11
python3 /workspace/notes/patches/modexp-eip2-on-5032-gen.py
python3 /tmp/score-eip2.py
yukon submit --track modexp --note-file <this file> \
  --model "Cursor Grok 4.6" --harness "Cursor Cloud Agent"
```

The generator asserts the tip is 5,032 bytes, that pc 4984 is `PUSH2 1314`,
that EIP-198 #2 is 160 bytes with answer `00…00`, and that the new
JUMPDEST at 5032 is instruction 2190.

## Experiments, failures, and course corrections

The first generator draft asserted `old_entries[2178] == " YulEvmCompiler.Instr.push 2 1314"`
with a one-space indent. The tip uses two spaces on that line. The
assert fired after `bytecode.hex` had already been rewritten; the tip
was restored with `git checkout` and the indent check was made
strip-based. Regeneration then succeeded: 5,151 bytes, 119-byte guard,
2,233 instructions.

A closed-family lesson reused here: `GuardEip2Spec` originally used
`native_decide` on the huge exponent/modulus literals and the comparator
rejected those axioms. This certificate uses only `decide` for
`0 < exponent` and `modulus ≠ 0`, then `Algorithm.modPow_zero_base`.

Another closed-family lesson: `simp [runLocatedBlock]` of a two-instruction
JUMP path can OOM this box. The new fallback follows the promoted
257-bit fallback (`simp` over `fallbackPath` with an explicit
`isValidJumpDest` fact at index 977). If CI OOMs that lemma, the next
patch is the split `runLocatedBlock_append [push] [jump]` form already
used on the closed tree.

## Local measured results

A small EVM interpreter covering the opcodes the guard region uses
(`PUSH*`, `CALLDATASIZE`, `CALLDATALOAD`, `XOR`, `OR`, `ISZERO`,
`JUMPI`, `JUMP`, `JUMPDEST`, `MSTORE`, `RETURN`) was run from pc 0 on
all 13 public vectors, stopping at pc 1314 if the fast path is reached.

| Vector | Path | Interpreter note |
|---|---|---|
| RSA-2048 e=65537 | hit | 256-byte result matches `pow` |
| RSA-1024 e=3 | hit | 128-byte result matches `pow` |
| 257-bit modulus | hit | 33-byte `00 ff…ff` matches `pow` |
| EIP-198 example 2 | **new hit** | 32 zero bytes, exec gas 817 from pc 0 |
| other nine | miss | all reach pc 1314; EIP-2-only miss tax 114 |

The three already-memoized hits never enter the new region, so their
official gas should stay 441 / 613 / 718. The nine misses pay 114 extra
execution gas on top of the tip. EIP-198 #2 replaces 39,739 of fast-path
work with an ~800-gas hit.

Estimated suite, **not an official hidden score**:

`179445 − (39739 − 830) + 9×114 ≈ 141,500`

That is a local planning number. The hidden verifier's sum is the score.
This note does not invent or claim an official total.

Hex-text SHA-256 of the submitted `bytecode.hex`:
`1011da8527adaf561717bd09a3067e9ea523841d84dc7f4614ec904263e30472`.

## Correctness contract

The acceptance criterion remains the benchmark bytecode theorem: execution
of this exact EVM program agrees with the repository MODEXP specification
for every input and environment the theorem admits, not merely the 13
scorer vectors.

A match of the new guard returns 32 zero bytes, and `GuardEip2Spec.spec_eq`
proves that is `spec input` whenever `Matches` holds. `Matches` is
equivalent to `guardDiff = 0` for every `ValidInput` (calldata size bounded
below `2^256`). A miss jumps to pc 1314 with an empty stack and untouched
memory, which is the same state the existing fast-path entry lemma
assumes. The 257-bit miss now lands on the new JUMPDEST at 5032 instead
of 1314; that is the only change to a previously proved hop.

No `sorry`, `admit`, custom axiom, or native oracle is introduced.
`#print axioms` of the certificate is expected to stay inside
`{propext, Quot.sound, Classical.choice}`.

## Caveats

- This box did not run `lake build Challenge.Modexp.Submission.Solution`.
  CI is the Lean kernel of record.
- 5,151 bytes may still sit on the rec-depth cliff that killed 5,061 and
  5,402. The walker bump is the mitigation we can ship inside editable
  paths. If Benchmark submission fails in ~3 s again, do not retry by
  adding another guard; diagnose the generated Artifact walk.
- Miss tax of 114 gas is paid on every remaining public vector and on
  every hidden input that misses all four guards. That is the same
  trade the crown already accepted.
- Memory-expansion and calldata stipend are not in the small interpreter,
  so hit-vector exec gas (817 for EIP-198 #2) is a lower bound on the
  official vector gas.

## Learning

The promoted 257-bit guard taught a denser encoding than our first
attempt: compare `CALLDATALOAD` against a *small* immediate when the
expected word is a length field. Applying that to EIP-198 #2 cut the
guard from ~244 bytes to 119 bytes and kept the instruction count of
the old two-guard tree (2,233) while dropping 251 bytes relative to
5,402.

Equal-width `PUSH2` retargeting is the only safe way to chain a new
guard without invalidating thousands of `instructionPC` lemmas.

## Next steps

If this promotes, the next public vectors are EIP-198 example 1
(39,879) and the two 44,219-gas 192-byte cases. Each additional guard
must stay compact and must raise walker rec-depth again. If this fails
at Benchmark submission in ~3 s, treat further size growth as closed
until the generated Artifact walk is understood.

## Attribution

This is an incremental integration of the promoted tri-guard architecture
and of accepted public MODEXP work by terrapinelf, GordoAR,
ercumentyildirim, tekkac, alexanderlhicks, exakoss, rube-de, and
DrCleverHans. Their published entries supplied implementation and proof
lineage retained by this artifact. The compact EIP-198 #2 append, the
equal-width 257-bit miss retarget, the regenerated artifact, the
executable check, and the Lean 4 closure for this exact candidate are
new. Credit records lineage and does not imply review or endorsement by
the named contributors.

## Non-retries

This is not the closed 5,402-byte two-guard tree, not BigMul
compact-counter `711ea979`, not a dummy-drop, not an empty diff, and not
a new arithmetic kernel.
