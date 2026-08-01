# EIP-8200 challenges

**Write EVM bytecode that replaces a precompile, and prove it.**

[EIP-8200](https://eips.ethereum.org/EIPS/eip-8200) ("EVMification") proposes
retiring precompiles by deploying EVM bytecode at their addresses: after
activation a call to the address runs ordinary bytecode at ordinary EVM gas
costs instead of a native implementation. The EIP's security section asks only
that the bytecode "must be thoroughly tested and audited". This repository asks
for the stronger thing — a **machine-checked proof** that a candidate bytecode
computes exactly what the precompile computed — so that "audited" becomes
"verified", and so anyone can compete on gas without anyone having to trust
their code.

**SHA-256 (`0x02`) is the pilot.** It is not in EIP-8200's list (which covers
RIPEMD-160, MODEXP, and BLAKE2f): it is the same problem in its simplest form,
it is where [eth-act/evmification](https://github.com/eth-act/evmification/tree/main/src/sha256)
starts, and — decisively — the EVM semantics this repository is built on
already contains a SHA-256 model that the `0x02` precompile itself executes.
That makes the specification side of the equivalence *not ours to get wrong*.

```sh
lake exe cache get                                # prebuilt Mathlib oleans
lake build                                        # the statement + the reduction
lake exe sha256challenge                          # score the reference
lake exe sha256challenge --hex=my_impl.hex        # score your bytecode
```

## Dependencies, and why they are the trust boundary

| dependency | role |
|---|---|
| [powdr-labs/evm-semantics](https://github.com/powdr-labs/evm-semantics) | the EVM (small-step `Step`, big-step `Eval`, gas, precompiles) **and the specification**: `EvmSemantics.Crypto.Sha256.hash` |
| [powdr-labs/yul-compiler](https://github.com/powdr-labs/yul-compiler) | a verified non-optimizing Yul→EVM compiler; lets a Yul-level proof land on bytecode with no bytecode-level reasoning |

Both are pinned by commit in `lakefile.toml`. Nothing about the EVM or about
SHA-256 is re-encoded here — this repository contributes a *statement*, a
*reference implementation*, and a *reduction*.

---

## 1. What "equivalent" means here

```text
FIPS 180-4                                       published standard
    │  human review + the §B.1–B.3 vectors (evm-semantics tests/Sha256Test.lean)
    ▼
EvmSemantics.Crypto.Sha256.hash : ByteArray → ByteArray      ← the specification
    │  Precompile.runSha256 input _ = .success (Crypto.Sha256.hash input) cost
    ▼
what a call to 0x02 does today, in the pinned semantics
```

`Crypto.Sha256.hash` is *literally* the function the precompile dispatch calls.
So proving that a candidate returns `Crypto.Sha256.hash calldata` proves
equivalence **to the precompile as modeled by the reference semantics** — no
second SHA-256 of our own to reconcile.

The challenge is one `Prop`, in [`Challenge/Sha256/Statement.lean`](Challenge/Sha256/Statement.lean):

```lean
def Correct (code : ByteArray) : Prop :=
  ∀ calldata : ByteArray, calldata.size < 2 ^ 64 →
    ∃ g₀ : Nat, ∀ g : Nat, g₀ ≤ g →
    Eval (frame code calldata g) (.returned (spec calldata))
```

*For any realizable message, given enough gas, a frame running `code` halts by returning
exactly the 32 digest bytes.* Three things to notice:

* **It never mentions any implementation.** Not our Yul, not our bytecode, not
  our memory layout, not our gas. Two submissions that both satisfy `Correct`
  are interchangeable at the interface a caller can observe. That is why the
  specification is a *function* and not the incumbent's code: bytecode-to-bytecode
  equivalence would leak one implementation's accidents into the standard.
* **Gas appears, because it must.** Below some level every implementation runs
  out, and no constant is right for all lengths. `∃ g₀, ∀ g ≥ g₀`
  ("given enough gas") is non-vacuous: the conclusion must hold at *every*
  larger budget, so nobody passes by succeeding at one lucky gas value.
* **`Returned`, not `Success`.** Reverting, throwing, or returning the wrong
  number of bytes all fail.

The efficiency-carrying strengthening:

```lean
def CorrectWithSchedule (code : ByteArray) (schedule : Nat → Nat) : Prop :=
  ∀ (calldata : ByteArray) (g : Nat), schedule calldata.size ≤ g →
    Eval (frame code calldata g) (.returned (spec calldata))
```

a *proven* gas bound as a function of input size — what an EIP needs to publish
a gas schedule. `correct_of_schedule` shows it implies `Correct`.

### Scope, stated up front

* `frame` is the canonical precompile-call frame: fresh memory, empty storage
  and transient storage, zero balance, zero call value, depth 0, Osaka. That is
  what a call into a freshly deployed, storage-free account produces — but a
  candidate reading `SLOAD`/`CALLVALUE`/`CALLER` is only pinned at those
  values. `CorrectInAnyFrame` states the generalization (**obligation W**); the
  Tier-1 scorer meanwhile runs every vector a second time in a *dirty* frame.
* The candidate is deployed at a non-precompile address, not at `0x02`, because
  in the pinned Osaka semantics `0x02` *is* a precompile and a frame there
  never executes bytecode. Flipping exactly that bit is what EIP-8200
  activation does; when the semantics grows a post-8200 fork, `deployAddress`
  becomes `0x02` and nothing else changes.

---

## 2. The reference submission, and why the compiler matters

[`Challenge/Sha256/reference.yul`](Challenge/Sha256/reference.yul) is SHA-256
in the verified Yul fragment: message from calldata, digest in returndata, 1524
bytes compiled. It is written **for provability, not gas** — hash state and
message schedule live in memory, so every loop body is a short memory
transformer with a handful of live variables.

Because the Yul→EVM compiler is verified, the reference's obligation is a
statement about *Yul*:

```text
ComputesDigest referenceBlock            ← obligation Y (the real work)
  ∘ compile_correct_eval                   ✔ proved in yul-compiler
  ∘ optimizer / normalizer soundness        ✔ proved in yul-compiler (needs composing: obligation C)
  ∘ parse_canon_block                       ✔ proved in yul-compiler
  ∘ StateMatch for the canonical frame        obligation A (plumbing)
  ⟹ Correct referenceBytecode
```

[`Challenge/Sha256/Reduction.lean`](Challenge/Sha256/Reduction.lean) proves the
reduction (`correct_of_computesDigest`) today, with no unfinished goals and the
same axiom footprint as its dependencies (`propext`, `Classical.choice`,
`Quot.sound`). Its hypotheses are ordinary `Prop`s — the challenge is to
inhabit them — and no step of the proof mentions an opcode.
[`Challenge/Sha256/Reference.lean`](Challenge/Sha256/Reference.lean)
instantiates it for the shipped artifact.

### Open obligations

| # | Name | What it says | Size |
|---|------|--------------|------|
| **Y** | `ComputesDigest` | The Yul program returns `Crypto.Sha256.hash calldata`. | large; decomposed below |
| **A** | `AbstractsFrame` | Each canonical EVM frame is matched by a yul-semantics state with the same calldata and empty memory. | plumbing, ~a day |
| **C** | `PipelineComposes` | `compileSource` = parse ∘ desugar ∘ normalize ∘ optimize ∘ compile, composed into one theorem. Every piece is already sound. | mechanical; belongs upstream as `compileSource_correct` |
| **S** | *(optional)* | A declarative, list-based SHA-256 in Lean plus `spec_eq_hash`, so proofs need not fight `Id.run do` loops over `ByteArray`. | small, unblocks Y |
| **W** | `CorrectInAnyFrame` | Generalize from the canonical frame to any fresh frame. Noninterference for a program that executes no state-reading op. | medium |
| **G** | `CorrectWithSchedule` | A proven gas schedule (Tier 3). | medium |

**Obligation Y decomposes** along the structure of `reference.yul`; each row is
a self-contained Lean goal:

| | Lemma | Statement |
|---|---|---|
| Y1 | round functions | `rotr`, `ssig0/1`, `bsig0/1`, `ch`, `maj` implement their FIPS 32-bit counterparts. Pure, no memory: start here. |
| Y2 | `initK` | after `initK()`, `kAt j = K[j]` for `j < 64`. |
| Y3 | `pad` | after `pad()`, memory at `0xb20 ..+paddedLen` is the FIPS-padded message and `paddedLen = 64·⌈(n+9)/64⌉`. The boundary case analysis lives here. |
| Y4 | `schedule` | after `schedule(off)`, `W[j]` is the FIPS message schedule of the block at `off`. |
| Y5 | `compress` | one call maps `H` to `compressBlock H block`. |
| Y6 | block loop | the loop folds `compress` over the blocks, giving `H^(N)`. |
| Y7 | output | the final word is the eight state words big-endian, and `return(0, 32)` exposes them. |
| Y8 | framing | the memory regions (`K`, `H`, `H_prev`, `W`, message) are disjoint and each helper touches only its own. Feeds everything above. |

---

## 3. Submitting

### Tier 1 — falsification by execution (required, automatic)

```sh
lake exe sha256challenge --hex=my_impl.hex     # raw bytecode
lake exe sha256challenge --yul=my_impl.yul     # Yul, compiled by the verified compiler
```

19 vectors — FIPS 180-4 §B.1/§B.2, the empty message, and every padding
boundary (55, 56, 63, 64, 65, 119, 120, 127, 128, 256, 1000 bytes) — each run
in the clean frame *and* a dirty one, comparing returndata with the
specification and reporting gas. The scorer runs in
`Challenge.Sha256.frame`, i.e. the very frame `Correct` quantifies over, so a
Tier-1 pass is a finite sample of the Tier-2 statement. Necessary, never
sufficient.

### Tier 2 — proved correct

A Lean proof of `Challenge.Sha256.Correct yourBytecode` on the pinned
toolchain: no `sorry`, no new `axiom`, no `native_decide`. Three routes,
easiest first:

* **Route Y (Yul).** Submit Yul in the verified fragment; the compiler gives
  you bytecode and `correct_of_computesDigest` gives you `Correct` from a
  Yul-level proof. Cheaper still: prove your Yul *equivalent to the reference*
  (`YulSemantics.EquivBlock` is exactly that relation) and inherit the
  reference's obligation instead of redoing it.
* **Route O (a verified optimizer pass).** If your improvement is a general
  transformation rather than a hand-written program, land it upstream as a
  sound Yul→Yul pass (`Optimizer.Sound` in yul-compiler). Then *every* program
  that compiler compiles gets faster — the most valuable kind of submission.
* **Route B (raw bytecode).** Prove directly over `EvmSemantics.EVM.Step`. This
  route starts from the submitted bytes and does not assume compiler
  provenance. [`Challenge/RouteB/Bytecode.lean`](Challenge/RouteB/Bytecode.lean)
  provides a verified byte-preserving disassembler
  (`assemble (disassemble code) = code`), including invalid opcodes and
  truncated immediates, plus reusable jump-destination certificates and
  PUSH-immediate normalization. [`Challenge/RouteB/Execution.lean`](Challenge/RouteB/Execution.lean)
  lifts deterministic `stepF` calculations into relational `Step`/`Eval`
  proofs and supplies compositional reachability and indexed-loop lemmas.
  A submission proves straight-line blocks with `Reaches.of_execN`, composes
  them with `Reaches.trans`, and instantiates `Reaches.iterate` with its loop
  invariants. `Challenge.Sha256.RouteB.DirectProof code` packages those traces,
  and `correct_of_directProof` closes `Correct code`.
  [`Challenge/Sha256/RouteB/Reference.lean`](Challenge/Sha256/RouteB/Reference.lean)
  starts this architecture with reusable entry and decoder certificates.
  [`Challenge/Sha256/RouteB/ReferenceCorrect.lean`](Challenge/Sha256/RouteB/ReferenceCorrect.lean)
  completes it for the frozen reference bytes: exact gas-parametric EVM traces
  cover initialization, padding, all schedule and compression loops, digest
  packing, and `RETURN`; the functional invariant identifies every block with
  `Sha256.compressBlock`, and the final theorem proves both `DirectProof` and
  `Correct referenceBytecode`. SHA is computed by the bytecode itself; no
  precompile call or compiler-correctness theorem is used by this proof.

  Optimized raw-bytecode submissions can reuse the same split. Their execution
  proof may use different basic blocks and loop invariants, while targeting
  the stable functional seams in `ScheduleCorrect`, `CompressionCorrect`, and
  `SpecBridge`. `GasSteps.toEventuallyEvaluates` then turns an exact halted
  endpoint into the common `DirectProof` obligation.

### Tier 3 — proved fast

`CorrectWithSchedule yourBytecode schedule` with a concrete `schedule`: the
tier an EIP could cite, since it yields a formula rather than a measurement.

### Ranking

Rows are `(verified tier, measured gas, bytecode size)`. A Tier-2 submission
always outranks a faster Tier-1 one — the point of the exercise is bytecode you
do not have to trust.

---

## 4. Where the reference stands

`lake exe sha256challenge` (pinned semantics, Osaka):

| input | gas | blocks |
|---|---|---|
| empty | 158,035 | 1 |
| `abc` | 158,038 | 1 |
| 55 bytes | 158,041 | 1 |
| 56 bytes | 314,044 | 2 |
| 64 bytes | 314,044 | 2 |
| 1000 bytes | 2,498,174 | 16 |

≈156,000 gas per 64-byte block, against the precompile's schedule of
`60 + 12·⌈len/32⌉` (84 gas for a 64-byte message). The reference trades three
orders of magnitude of gas for a proof structure a person can finish; a
hand-optimized implementation should take one to two of those orders back.
**That headroom is the challenge.**

---

## 5. Roadmap

* **Stage 0 — done.** Reference Yul compiling through the verified compiler;
  the Tier-1 scorer; the statement; the reduction theorem; the obligations
  named.
* **Stage 1.** Obligations A and C — after which `Correct referenceBytecode`
  rests on the Yul-level obligation alone.
* **Stage 2.** Obligation S, then Y1/Y2/Y8: leaf lemmas and the memory framing
  framework.
* **Stage 3.** Y3–Y7. The reference reaches Tier 2.
* **Stage 4 — Route B reference done.** The frozen raw bytecode has an
  end-to-end direct EVM proof. W (any frame), G (a concrete gas schedule), and
  additional opcode-specific automation remain.
* **Stage 5.** Open the leaderboard. Then the precompiles EIP-8200 actually
  names: RIPEMD-160 is the same shape, MODEXP and BLAKE2f are where it gets
  interesting.

## Layout

| path | what |
|---|---|
| `Challenge/Sha256/reference.yul` | the reference implementation |
| `Challenge/Sha256/reference.hex` | the frozen raw-bytecode artifact generated from the reference |
| `Challenge/Sha256/ReferenceBytes.lean` | reducible literal form of the same frozen bytes, pinned by CI |
| `Challenge/Sha256/Bytecode.lean` | the frozen artifact as a Lean value and its disassembly round trip |
| `Challenge/Sha256/RouteB.lean` | direct raw-bytecode obligation and reduction to `Correct` |
| `Challenge/Sha256/RouteB/Reference.lean` | direct `stepF` certificates and traces for the frozen reference bytecode |
| `Challenge/Sha256/RouteB/CompressionCorrect.lean` | reusable bytecode compression invariant and equivalence to `Sha256.compressBlock` |
| `Challenge/Sha256/RouteB/DriverCorrect.lean` | padded-block outer invariant and canonical digest packing |
| `Challenge/Sha256/RouteB/ReferenceCorrect.lean` | end-to-end `DirectProof` and `Correct referenceBytecode` theorem |
| `Challenge/RouteB/Bytecode.lean` | verified raw disassembler/assembler round trip |
| `Challenge/RouteB/Execution.lean` | direct `Step`/`Eval`, reachability, and loop proof combinators |
| `Challenge/RouteB/Gas.lean` | gas-parametric trace composition and `EventuallyEvaluates` bridge |
| `Challenge/Sha256/Statement.lean` | `Correct`, `CorrectWithSchedule`, the frame, frame facts |
| `Challenge/Sha256/Reduction.lean` | `correct_of_computesDigest`: Yul obligation ⟹ challenge statement |
| `Challenge/Sha256/Reference.lean` | the artifact, its obligations, `reference_correct` |
| `Challenge/Sha256/Scorer.lean` | the Tier-1 vectors, frames, and scoring |
| `Main.lean` | the `sha256challenge` CLI |

Apache-2.0.
