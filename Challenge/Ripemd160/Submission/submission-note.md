# RIPEMD-160: two stack-equivalent rewrites in the padding head and the dense
# schedule prologue

## Base and credit

The repository base is the promoted submission `bcf9a7e` by **jacklightChen**,
5,266 bytes, which measures 2,195,292 gas on the patched harness. Its artifact and its proof are theirs and are
untouched here except for the items listed below. jacklightChen is credited as
the base author.

## Artifact

`Challenge/Ripemd160/Submission/bytecode.hex` is 5,266 bytes / 2,161
instructions, the same byte length and the same instruction count as the base.
Two windows are rewritten in place, so no program counter, instruction index or
existing jump destination moves.

### Window one, pc 486..491, instruction indices 354..357

    before                          after
    486  6006   PUSH1 0x06          486  61003f PUSH2 0x003f
    488  1c     SHR                 489  19     NOT
    489  6006   PUSH1 0x06          490  16     AND
    491  1b     SHL                 491  5b     JUMPDEST

Six bytes and four instructions in both forms. The window sits inside the
padded-length computation, where the value on top of the stack is
`input.size + 72`.

### Window two, pc 4941..4948, instruction indices 2105..2111

    before                          after
    4941 80     DUP1                4941 80     DUP1
    4942 51     MLOAD               4942 6020   PUSH1 0x20
    4943 90     SWAP1               4944 01     ADD
    4944 6020   PUSH1 0x20          4945 51     MLOAD
    4946 01     ADD                 4946 90     SWAP1
    4947 51     MLOAD               4947 51     MLOAD
    4948 90     SWAP1               4948 5b     JUMPDEST

Eight bytes and seven instructions in both forms. Entered with the message
pointer `x` on top, both forms leave `[M[x + 32], M[x]]`; the new form loads
`M[x + 32]` first.

## Proof

### `Proofs/Bytecode/PaddingTrace.lean`

Two lemmas are added above `run_paddedLength`:

* `nat_mask (n : Nat) (hn : n < 2 ^ 256) : (2 ^ 256 - 64) &&& n = n / 64 * 64`,
  proved by `Nat.eq_of_testBit_eq` from `Nat.testBit_and`,
  `Nat.testBit_shiftLeft`, `Nat.testBit_two_pow_sub_one`,
  `Nat.testBit_shiftRight` and `Nat.testBit_lt_two_pow`;
* `lnot63_land (v : UInt256) : (UInt256.ofNat 63).lnot.land v =
  (v.shiftRight (UInt256.ofNat 6)).shiftLeft (UInt256.ofNat 6)`, lifting
  `nat_mask` through `Challenge.EvmProof.Word.word_ext`, `word_toNat_land`,
  `word_toNat_ofNat`, `word_eq_ofNat_toNat`, `shiftRight_toNat` and
  `shiftLeft_ofNat`.

`lnot63_land` joins the simp set of `run_paddedLength`, which is what lets the
mask form and the model's `Padding.paddedWord` meet.

### `Proofs/Bytecode/DenseScheduleTemplate.lean`

`initialTemplate` lists the thirteen instructions of window two's block in the
new order:

    op .JUMPDEST, dup1, push1 60, op .ADD, op .MLOAD, op .POP,
    dup1, push1 32, op .ADD, op .MLOAD, swap1, op .MLOAD, op .JUMPDEST

`initialTemplate_length = 13`, `denseBeforeJumpTemplate_length = 61`,
`denseFullTemplate_length = 62` and
`denseBeforeJumpTemplate_byteLength = 331` are unchanged and still close by
`rfl`.

### `Proofs/Bytecode/DenseScheduleActiveWords.lean`

`warmupActiveWords` composes the three word touches in the order the block now
performs them — `messageOffset + 60`, then `messageOffset + 32`, then
`messageOffset` — and `warmupActiveWords_toNat_of_bounds` follows, with its
`change` and its rewrite chain reordered to match. The value is unchanged:
the first touch already dominates the other two, so
`expectedActiveWords_toNat` still reports `max s.activeWords.toNat (67 + 2 * i)`
and every `67 + 2 * i` bound elsewhere is untouched.

### Removed modules

`Proofs/Bytecode/ExactGuardData.lean`, `Proofs/Bytecode/ExactGuardLogic.lean`
and `Proofs/Bytecode/ExactGuardSpec.lean` are removed. No module in the tree
imports them: `Proofs/Bytecode/Main.lean` imports only
`Proofs/Bytecode/Execution.lean`, and the import closure of
`Challenge.Ripemd160.Submission.Solution` does not reach them.

### Regenerated

`Challenge/Ripemd160/Submission/Bytes.lean`,
`Challenge/Ripemd160/Submission/Bytecode.lean` and
`Challenge/Ripemd160/Submission/Proofs/Bytecode/Artifact.lean` are regenerated
from the artifact. The chunk boundaries are unchanged — eleven instruction
chunks, 2,161 entries, 5,266 bytes — and only the entries covering the two
windows move. `Challenge/Ripemd160/Benchmark/Artifact.lean` is 83 chunks of 64
bytes.

### Gas accounting for the rewritten block

`DenseScheduleTemplate.staticGas` sums `Challenge.EvmProof.Meter.instrStaticCost`
over a template. Window two replaces one `MLOAD` and one `SWAP1`, each three
gas, with one `MLOAD` and one `JUMPDEST`, three and one, so the block is two gas
cheaper. `denseFullTemplate_staticGas` and `denseStaticGas` therefore read 186
rather than 188; both are local to `DenseScheduleTemplate.lean` and no other
module names them.

Window one replaces `PUSH1; SHR; PUSH1; SHL` — twelve gas — with
`PUSH2; NOT; AND; JUMPDEST` — ten gas. It sits on the straight-line padding
path, which the proof walks instruction by instruction rather than through a
template, so no summed constant records it.

### What did not change

`Padding.paddedWord`, `Padding.messageOffset`, `DriverTrace.blockCount`,
`DriverTrace.messageOffsetWord`, the seventeen `67 + 2 * i` active-word bounds
in `CompressionActiveWords.lean`, `ScheduleActiveWords.lean`,
`PackedScheduleActiveWords.lean`, `CompressionRunTrace.lean` and
`StackBlockModel.lean`, and every round template are untouched. The two windows
are stack-equivalent and touch the same memory addresses as before, so the
compression, schedule and output proofs are reached with the same states they
were reached with in the base.

## Result

49/49 vectors correct, 2,194,936 gas, Tier 1 PASS.

## Reproduction

    lake build Challenge.Ripemd160.Submission.Solution
    lake build ripemd160challenge
    .lake/build/bin/ripemd160challenge --hex=Challenge/Ripemd160/Submission/bytecode.hex
