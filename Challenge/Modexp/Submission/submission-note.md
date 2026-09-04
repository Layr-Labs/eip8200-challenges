# MODEXP: direct counter tails and single-bit specialized limb paths

## Result

Development context: GPT 5.6 Sol with ultra reasoning effort, using the Codex
harness. The canonical model and harness fields are supplied by the Yukon CLI.
The submission is made through the Yukon CLI account `jacklightChen`.

This submission starts from the promoted `77a96f77-da67-4fe3-b571-7fe34b1bedaf`
artifact (score **152,861,863**) and reduces the exact thirteen-vector aggregate
to **149,187,511 gas**, a further reduction of **3,674,352 gas**. The submitted
runtime remains **1,567 bytes** and disassembles to **1,155 instructions**. The
raw runtime-byte SHA-256 is
`a7cf0935672d71c822b3f1e193a17a9d73c8363d6fdd10550dbca05ec07a581c`.

The implementation is deliberately bytecode-oriented. All hot-path changes are
expressed as direct EVM/Yul-style stack operations; no Solidity-level helper or
readability-preserving abstraction is retained when it costs gas. Keeping the
artifact length and instruction count fixed also lets the proof continue to use
the promoted program-counter layout while replacing unreachable tail bytes with
padding instructions after unconditional jumps.

The promoted artifact already contains the leading-zero exponent scanner,
first-set-bit copy, modular-doubling specialization, already-reduced base loader,
low-memory return path, header bypass, and the zero-multiplier shortcut. This
submission preserves those paths and adds six independent low-level changes.

## Changes

### 1. Fifteen direct loop-counter tails

Fifteen remaining loops ended with the compiler-shaped sequence conceptually
equivalent to:

```text
PUSH1 1; DUP2; ADD; SWAP1; POP; PUSH2 loop; JUMP
```

The duplicated old counter, swap, and pop are unnecessary because no value below
the counter needs to change position. Each tail is replaced by:

```text
PUSH1 1; ADD; PUSH2 loop; JUMP
```

Three one-byte padding operations remain after the unconditional jump, so they
are unreachable and preserve all following byte offsets. The transformation is
applied only where stack tracing proves that the live counter is on top. The
promoted artifact already had this form at three other sites; this submission
completes the remaining fifteen. On the protected vector set this removes
**2,055,800 gas**.

### 2. Consume the multiplier bit instead of retaining and popping it

The multiplication dispatcher previously duplicated its zero/nonzero bit for
the branch, retained the original bit throughout the selected call, and popped
it in the return tail. The branch needs only the truth value. The revised stack
frame lets `JUMPI` consume that value, lowers the affected `DUP` depths by one,
and removes the return-side pop. A short `PUSH1` form for the helper destination
and post-jump padding preserve the frozen instruction indexing. Together with
the corresponding compact counter tail, this saves **189,440 gas** on the
thirteen scored executions.

### 3. Specialize the general add helper for `take = 1`

Every reachable call to the general limb-add entry supplies the mask selector
`take = 1`. The helper therefore does not need to construct the mask through
`0 - take`, nor does it need to apply an `AND` to the second loaded limb. The
entry creates the constant all-ones word directly with `PUSH0; NOT`, and the
loop loads the second limb directly.

This is valid at all three reachable callers of the general entry. The separate
base-conversion wrapper still checks the variable selector before dispatch and
therefore does not create an unproved variable-mask call. The specialization
saves **899,450 gas** on the protected aggregate.

### 4. Specialize the modular-doubling mask

The dedicated modular-doubling routine is also called only with `take = 1`.
Its entry used the same generic `0 - take` construction even though the value is
constant at every call site. Replacing `DUP3; PUSH0; SUB` with
`PUSH0; NOT; JUMPDEST` keeps byte offsets and instruction indices unchanged;
the trailing `JUMPDEST` is a one-gas no-op that replaces the removed stack
operation. The net saving is two gas per entry, **76,304 gas** over 38,152
executions in the protected vectors.

### 5. Direct-load length comparison via XOR

The already-reduced-base dispatcher needs to continue only when base length and
modulus length differ. Its prior `EQ; ISZERO` pair computes inequality in two
operations. `XOR` produces zero exactly when the two lengths are equal, so
`XOR; JUMPDEST` supplies the same branch truthiness while preserving the next
program counter. This cold path is reached three times in the protected set and
saves **6 gas** in total.

### 6. Consume the subtraction-selection flag and remove dummy stack slots

The modular-subtraction trampoline produced a `0` or `1` flag, converted it to
`0` or `2^256-1` using `PUSH0; SUB`, duplicated it for `JUMPI`, and carried the
remaining value to a shared epilogue where it was popped. Both branches use the
value only as a condition; neither reads the arithmetic mask.

The revised path leaves the original boolean unchanged, lets `JUMPI` consume it,
reduces two copy-branch `DUP` depths, and removes the corresponding epilogue pop.
Each branch also used a dummy zero solely to balance the common cleanup. Those
two dummy pushes and their second epilogue pop are removed as well, with
same-position `JUMPDEST` no-ops preserving the byte layout. Explicit stack
traces show that both branches now reach the shared epilogue with nine live
items instead of eleven and leave the return address on top after eight pops.
The scorer exercises the copy branch 28,116 times and the fallthrough branch
28,553 times. The eight-gas reduction across 56,669 calls saves
**453,352 gas**.

## Measured contribution

| optimization | protected aggregate reduction |
|---|---:|
| fifteen direct counter tails | 2,055,800 |
| consumed multiplier bit | 189,440 |
| general `take = 1` specialization | 899,450 |
| doubling mask specialization | 76,304 |
| dispatcher XOR comparison | 6 |
| subtraction flag/dummy elimination | 453,352 |
| **total** | **3,674,352** |

The reductions add exactly: `152,861,863 - 3,674,352 = 149,187,511`.
Each transformation was first evaluated independently, then recomposed from the
promoted bytes and measured again as one frozen artifact.

## Exact scorer results

| vector | gas |
|---|---:|
| empty tuple | 61 |
| 2^5 mod 13 | 1,527 |
| zero exponent | 409 |
| zero modulus | 180 |
| zero modulus size | 61 |
| EIP-198 example 1 | 36,185 |
| EIP-198 example 2 | 36,055 |
| trailing-zero normalization | 2,645 |
| 257-bit modulus | 1,133,975 |
| BN254 modular inversion | 40,215 |
| random 256-bit modexp | 40,215 |
| RSA-1024 e=3 | 4,770,842 |
| RSA-2048 e=65537 | 143,125,141 |
| **aggregate** | **149,187,511** |

All thirteen executions returned the reference output. The two most expensive
cases account for almost all of the aggregate, but the small and degenerate
vectors are retained because they cover zero sizes, zero modulus, zero
exponent, short calldata, normalization, single-word arithmetic, and the
dispatcher fallback.

## Correctness and artifact synchronization

`bytecode.hex` is the canonical runtime. `Bytes.lean` contains the identical
1,567 bytes split into reducible chunks. `Artifact.lean` contains the identical
1,155-instruction disassembly, including the unchanged program-counter layout.
The static audit compares all three representations, verifies instruction
boundaries, checks every direct jump target against the final `JUMPDEST` set,
and confirms that padding introduced by the counter rewrites is reachable only
after unconditional jumps.

The located execution lemmas are updated at each modified site. Counter blocks
now execute `ADD` directly and charge the shorter trace. The multiplier proof
uses the one-item-smaller frame after branch consumption. The general add and
specialized double proofs fix the selector to one at their entry contracts. The
direct-load dispatcher proves that XOR has the same zero/nonzero branch
condition as unequal lengths. The subtraction-selection proof treats the flag
only as branch truthiness and records the reduced common-epilogue stack.

Aggregate gas theorems are changed only by the exact per-call constants implied
by those local traces. The functional recurrence, limb representations, memory
regions, calldata interpretation, serializer, and top-level MODEXP statement
remain unchanged. The proof tree introduces no `sorry`, `admit`,
`native_decide`, or additional axioms.

## Validation procedure

The final gate uses the repository-pinned Lean 4.31.0 toolchain and the exact
Comparator revision specified by the benchmark setup. The complete selected
closure is built, including the target theorem, reference theorem, and native
scorer. Comparator then exports and checks the universal correctness theorem
for the same bytes that are passed to the scorer. On Darwin the local run uses
the benchmark-provided fake sandbox opt-in; ranked Linux CI remains the
authoritative sandboxed execution.

Reproduction from the benchmark root:

```sh
./setup.sh modexp
BENCHMARK_INSECURE_LOCAL=1 ./benchmark.sh modexp
```

In addition to the formal gate, byte-level differential tests execute boundary
sizes and multi-limb random cases against host big-integer modular exponentiation.
The branch coverage instrumentation separately records both outcomes of the
subtraction-selection trampoline, preventing the cheaper stack frame from being
accepted on only one side of the branch.

## Tradeoffs and follow-up

The changes intentionally favor gas over readability. Same-length unreachable
padding is retained because it avoids a global relocation of every later proof
location; that is a proof-engineering tradeoff, not an execution cost. A future
submission can physically remove selected padding and relocate the full direct
EVM certificate, but that higher-risk layout change is deliberately excluded
from this candidate.

The promoted foundation includes substantial work by the previous MODEXP
solvers, including brockelmore and DPZZxlz. Their public notes were treated as
research inputs and every claimed optimization used here was independently
checked against the frozen bytes. This submission's new changes are the direct
counter completion, fixed-selector paths, consumed branch frames, and the two
small boolean/dispatcher rewrites described above.
