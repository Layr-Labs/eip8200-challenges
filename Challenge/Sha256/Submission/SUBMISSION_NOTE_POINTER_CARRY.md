# SHA-256 pointer-carry paired-round optimization

## Context and objective

This submission continues the proof-producing optimization of the EIP-8200
SHA-256 bytecode. The immediately preceding accepted checkpoint scored
2,954,366 gas over the protected 19-vector suite. It already used a paired-round
compression kernel: one loop iteration executes two SHA-256 rounds, keeps the
first round's virtual midpoint on the EVM stack, and commits the canonical eight
working words only after the second round. The remaining repeated work in that
kernel was address formation. Both rounds reconstructed the message-schedule
address from the logical round number with a shift and base addition, and they
independently reconstructed the K-table address with a multiply-by-four shift
and base addition.

The goal of this pass was deliberately narrow: retain the proved paired-round
mathematics, its two-round commit boundary, the frozen byte length, and the
frozen structural instruction count, while replacing those repeated address
calculations with loop-carried pointers. This avoids reopening the SHA-256
algebra or changing the feed-forward result. The candidate is still required to
prove `Challenge.Sha256.Correct` for arbitrary calldata, not merely pass native
test vectors.

Development context: GPT 5.6 Sol, xhigh effort, Codex agent.

## Environment and setup

The work was performed in the SHA-256 submission directory of the Yukon
EIP-8200 challenge repository. `yukon setup` regenerated the protected benchmark
artifact and installed/build-tested the challenge tooling. The first setup
attempt from the restricted process environment could not resolve the remote
host; rerunning the same setup command with the approved network permission
succeeded. On Darwin, the benchmark harness requires its documented local
fallback, so the final run used `BENCHMARK_INSECURE_LOCAL=1`. That flag selects
the local fake sandbox instead of Linux `landrun`; it does not change the Lean
kernel check, Comparator theorem, frozen candidate bytes, or trusted native gas
vectors.

The exact verification commands were:

```text
yukon setup
lake build Challenge.Sha256.Submission.Proofs.Bytecode.ReferenceCorrect
BENCHMARK_INSECURE_LOCAL=1 yukon run
```

During byte-level prototyping, the trusted scorer was also run directly against
temporary candidate hex files. Every promoted prototype was tested from both
clean and dirty initial machine frames. The clean and dirty results and gas were
identical for all 19 vectors before any proof edits were adopted.

## Hypothesis and selected design

For logical round `j`, the schedule word is stored at byte address
`800 + 32*j`, and the K constant is stored at byte address `4 + 4*j`. These
addresses advance linearly. Recomputing them from `j` is therefore unnecessary
if the paired loop carries both current pointers directly.

The candidate introduces the proof-level definitions:

```text
pairWPtr(j) = UInt256.ofNat (800 + j * 32)
pairKPtr(j) = UInt256.ofNat (4 + j * 4)
```

At the executable loop boundary, the stack is now:

```text
[pairWPtr(j), pairKPtr(j), msgOff, returnDest] ++ rest
```

The logical round number remains a ghost index in the Lean invariant. The first
round reads `M[pairWPtr]` and `M[pairKPtr]`; the second reads
`M[pairWPtr + 32]` and `M[pairKPtr + 4]`. At the paired back edge, the code adds
64 to the schedule pointer and 8 to the K pointer. This is exactly the address
advance for two rounds. The loop condition compares the schedule pointer with
the terminal address 2,848 (`800 + 64*32`, hexadecimal `0x0b20`). The invariant
connects that pointer comparison to the ghost bound `j = 64`.

This design was chosen over a more aggressive rotating-memory or four-round
kernel because it preserves the existing virtual-midpoint proof architecture.
It changes concrete stack plumbing and address lemmas but not the SHA-256 round
function, schedule contents, saved chaining state, or feed-forward semantics.
That made it possible to get a fully kernel-checked improvement submitted
quickly instead of leaving a lower-scoring native-only experiment.

## Bytecode implementation

The final candidate remains exactly 1,524 bytes and decodes to exactly 810
structural instructions. The ASCII hex file hash is
`098b8d6f59a37aa87810faec302dfeefd9cebed5972696ee1ea4bf46227b05f3`;
the SHA-256 of the decoded 1,524 raw bytes is
`10e26de38dd555761932893aa3ea46acf1cceee9a0a3bc1571eb785d4970869d`.

Four byte regions implement the functional change relative to the preceding
2,954,366 checkpoint:

1. The entry at PC `0x264` initializes the schedule and K pointers, enters the
   new paired loop at PC `0x27d`, compares the schedule pointer against
   `0x0b20`, and loads first-round W/K values directly from the carried
   pointers. The logical index-to-address shifts disappear from the hot path.
2. The second-round setup at PC `0x2f5` loads the next W and K values from
   `wptr + 32` and `kptr + 4`. Wide immediate padding absorbs bytes that are no
   longer needed for arithmetic and preserves local layout.
3. The paired commit/backedge at PC `0x381` increments the two pointers by 64
   and 8 before returning to PC `0x27d`. Its unreachable suffix is repacked so
   the global decoded instruction count remains 810.
4. The pair exit/fold transition at PC `0x3a7` pops the two carried pointers and
   starts the feed-forward fold with counter zero. Moving this transition shifts
   the fold loop by one byte internally, from PC 938 to PC 939, while restoring
   all later byte boundaries.

The exact generated instruction paths are recorded in `Artifact.lean`. The
important structural ranges are: copy-and-loop-start 473..479, pair condition
480..485, first setup 486..525, first T2 continuation 526..537, second T1 setup
538..575, second T2 continuation 576..587, pair commit 588..643, unreachable
filler 644, pair exit 645..648, and fold start 649. Downstream output indices
are unchanged.

An early prototype decoded to 809 instructions and scored approximately
2,898,596. It was not eligible because the candidate proof and frozen artifact
expect the 810-instruction shape. One unreachable padding instruction was
restored, yielding the submitted 810-instruction candidate and its still-large
verified improvement. This was a conscious correctness/proof compatibility
tradeoff, not a scorer discrepancy.

## Proof implementation

`Bytes.lean` contains the reducible frozen byte array and `Artifact.lean`
contains the complete located instruction list. The assembly equality proof
was changed from a brittle whole-file `rfl` to an extensional byte-array proof
that simplifies `assemble`, `Instr.bytes`, and big-endian immediate encoding,
then discharges each concrete equality by kernel reduction. This still proves
that the located artifact assembles to exactly the submitted bytes.

`CompressionExec.lean` now defines the executable pair-loop state with the two
carried pointers and updates every located path/PC table. The semantic pair
state remains indexed by ghost round `j`; helper lemmas prove:

```text
pairWPtr(j + 1) = pairWPtr(j) + 32
pairWPtr(j + 2) = pairWPtr(j) + 64
pairKPtr(j + 1) = pairKPtr(j) + 4
pairKPtr(j + 2) = pairKPtr(j) + 8
```

under the bounded pair-loop invariant. Those lemmas connect direct `MLOAD`s to
the existing schedule and K-table correctness predicates. The four helper
continuations still compute the same T1/T2 words, and the final eight stores
still commit exactly two applications of the pure SHA-256 `round` function.

The first Lean attempt exposed two useful errors. Some pointer equalities were
left in different `UInt256.ofNat` normal forms, so simplification could not see
that direct loads addressed the same slots as the abstract schedule. Explicit
bounded arithmetic lemmas fixed that seam. A direct-load trace also needed one
additional stack-capacity inequality because the pair state gained a second
carried word. Adding that exact bound, rather than weakening the executor,
closed the trace. Finally, shifting the fold entry by one byte moved its
synthetic helper return destination from PC 981 to PC 982; the first end-to-end
proof build caught the stale destination, which was corrected in
`DriverCorrect.lean`.

The semantic proof composes 32 paired iterations. Induction establishes that
pair `n` represents the first `2*n` standard SHA-256 rounds, that the carried
pointers equal their formulas for `j = 2*n`, and that all schedule/K reads are
the correct words. At `n = 32`, the terminal schedule pointer implies `j = 64`.
The exit removes the concrete pointers, reconnects to the existing canonical
memory state, and then reuses the feed-forward, outer block loop, and final
digest proofs. Thus no native result or concrete test vector appears as an
assumption in the exported theorem.

`lake build Challenge.Sha256.Submission.Proofs.Bytecode.ReferenceCorrect`
completed successfully from current sources. The Yukon build subsequently
compiled `Solution.lean`, and Comparator checked the exact theorem with Lean's
default kernel. No `native_decide`, candidate-specific trusted axiom, or test
vector assumption was added.

## Gas accounting and measured result

The old paired loop cost 894 gas per two-round iteration. The pointer-carry
candidate costs 868:

| Segment | Old | New |
|---|---:|---:|
| condition | 23 | 23 |
| first W/K and T1 setup | 128 | 111 |
| first T1 helper | 99 | 99 |
| first T2 setup | 37 | 37 |
| first T2 helper | 99 | 99 |
| second W/K and T1 setup | 127 | 106 |
| second T1 helper | 99 | 99 |
| second T2 setup | 37 | 37 |
| second T2 helper | 99 | 99 |
| commit and backedge | 146 | 158 |
| **pair total** | **894** | **868** |

The two direct address paths save 38 gas per pair; pointer maintenance spends
12 of that, leaving 26 gas per pair. Across 32 pairs this is 832 gas saved per
padded block. Initial pointer setup costs four additional gas and the pair exit
costs two additional gas, giving the exact net saving:

```text
832 - 4 - 2 = 826 gas per padded block
826 * 65 public-suite padded blocks = 53,690 gas
2,954,366 - 53,690 = 2,900,676
```

The protected Yukon run reported:

```text
Lean default kernel accepts the solution
Your solution is okay!
Verified gas score: 2,900,676
Bytecode size: 1,524 bytes
Correctness vectors: 19/19
Lean Comparator: accepted
```

Empty-input gas is 45,594. Other representative native totals are 45,597 for
`abc`, 89,819 for a two-block boundary case, 134,044 for a three-block case,
222,493 for 256 bytes, and 708,973 for 1,000 bytes. Every clean/dirty pair
returned the same digest and gas.

## Caveats and next steps

The local Darwin run uses Yukon's explicitly requested insecure-local process
sandbox fallback; remote ranked validation is therefore still the final
environmental check. The actual proof was nevertheless accepted by the default
Lean kernel and the protected Comparator, and the score came from the trusted
scorer over the exact frozen bytes.

Optional standalone gas-accounting modules are being updated to mirror the new
segment decomposition, but they are not an assumption of `Solution.lean` or
Comparator. The authoritative result is the protected scorer and the
candidate-correctness theorem described above.

The next architectural opportunity is to keep more working state resident
across pair boundaries or rotate physical H slots so fewer canonical stores are
needed. That has a larger theoretical gas ceiling but a substantially wider
stack-layout and invariant surface. The safe next experiment will start from
this proof-complete pointer-carry checkpoint, require ordinary DUP/SWAP depth
limits, falsify clean and dirty machine frames, retain exact byte/instruction
shape, and only then be promoted into the kernel proof.
