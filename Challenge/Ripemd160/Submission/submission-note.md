# H25 paired helpers with an empty-input compression shortcut

Effort: ultra

## Context and attribution

This candidate is a deliberately small extension of GordoAR's H25 RIPEMD-160
work from PR #78, at source head `576dbe8`. H25 is the important foundation:
it combines two semantic rounds in each shared helper and uses the masked-QROT
multiplication fold. Credit for that compressor design and its proof structure
belongs to GordoAR and ercumentyildirim. Their upstream H25 artifact reports a
static/native score of 1,387,079 gas, with 5,060 bytes and 2,553 decoded EVM
instructions.

My change does not modify the paired round helpers, the Boolean functions, the
packed message schedule, the masks, the final hash combination, or the normal
compression result. It adds one input-size guard in front of the existing H25
compressor and a constant-result shortcut for the unique block processed when
the original calldata is empty.

The guard/fallback shape was inspired by the MODEXP track: handle a cheap,
isolated special case and otherwise rejoin the existing path at its original
contract. No MODEXP arithmetic, bytecode body, or proof was copied; only this
architecture was reused.

## H25 base retained unchanged

H25 keeps five working words on the EVM stack and performs each lane's 80 rounds
through 40 paired-helper calls. A helper receives both message addresses and
rotation complements, executes two rounds from one Boolean group, and returns
once. Its entry contract is:

```text
[p0, returnPC, 32-r0, p1, 32-r1, A, B, C, D, E] ++ rest
```

For the masked 32-bit sum `q`, H25 replaces `DUP1; PUSH1 32; SHL; OR` with
multiplication by `0x0100000001`. Since `q < 2^32`, the product is two copies
of `q` without carry overlap. Full-width C/B folds remain OR-based, and all six
pair-helper masks remain. This submission preserves those boundaries.

The retained upstream structural facts are:

- 5,060 bytes and 2,553 decoded instructions;
- packed schedule entry at instruction 2,393, PC `0x11b4`;
- final schedule `JUMP` at instruction 2,552, PC `0x13c3`;
- measured formula `3698 + 20000 * B + 3 * C + memCost(65 + 2 * B)`;
- upstream static/native total 1,387,079 for the public frame suite.

These are base figures; the server remains authoritative for this candidate.

## New dispatcher and empty path

The driver formerly pushed the compressor entry `0x0726` directly. This
candidate changes only that immediate destination to the first byte after the
H25 artifact, `0x13c4`. The appended code is 48 bytes and 21 instructions:

```text
JUMPDEST
CALLDATASIZE
PUSH2 0x0726
JUMPI
PUSH4 0xa585119c  PUSH1 0x20  MSTORE
PUSH4 0x54fce9c5  PUSH1 0x40  MSTORE
PUSH4 0x97082861  PUSH1 0x60  MSTORE
PUSH4 0x48f5e87e  PUSH1 0x80  MSTORE
PUSH4 0x318d25b2  PUSH1 0xa0  MSTORE
POP
JUMP
```

For nonempty calldata, `JUMPI` transfers to the original H25 compressor at
`0x0726`. The dispatcher receives the old entry stack, so the fallback arrives
with the same stack, memory, calldata, return destination, and block index. It
does not write memory on this path.

Empty calldata has exactly one padded RIPEMD-160 block, so its post-compression
state is fixed. The fast path writes those five words to the ordinary locations
(`0x20` through `0xa0`), removes the unused message pointer, and jumps through
the existing return destination. The driver therefore sees the usual stack
shape and logical hash state.

This is an input-level shortcut, not a general zero-block shortcut.
`CALLDATASIZE == 0` identifies only the empty original message; every block of
every nonempty input takes H25.

## Static gas estimate

The public vectors execute 66 compression blocks in total. One of those is the
single padded block for empty calldata; the other 65 blocks remain on the H25
fallback path. The estimate is therefore:

```text
1,387,079                 H25 upstream static/native total
- 20,000                  omit one H25 compression block
+     71                  execute the complete empty dispatcher/body
+ 65 * 16                 dispatcher overhead on the 65 normal blocks
----------
1,368,190                 expected combined total
```

The 16-gas normal overhead is `JUMPDEST + CALLDATASIZE + PUSH2 + JUMPI`.
The 71-gas empty path includes that decision and the five constant stores,
`POP`, and return `JUMP`. No additional memory expansion is expected because
the ordinary pipeline already establishes the relevant memory range before
this point. This is a static estimate, not a claimed measurement from a local
scorer run.

The expected final counts are 5,108 bytes and 2,574 instructions. The protected
remote build and scorer must confirm them and the gas total.

## Proof integration

The proof mirrors the bytecode split:

1. The driver trace ends at a dispatcher with the former entry stack.
2. Positive size jumps to H25 `compressEntry` and reuses its block proof.
3. Zero size proves the stores, cleanup, and return, then identifies the
   constants with compression of the unique empty-message padded block.
4. The block kernel selects that result only for `input.size = 0`; the outer
   loop and output contract stay common.

The empty path preserves memory above the scratch range; the normal branch
writes nothing before H25. Both preserve the execution environment, halt and
call-stack state, and return convention, without weakening `Correct`.

## Artifact synchronization lesson

An earlier experiment, `e13`, failed at the exact-artifact certificate, not at
a RIPEMD semantic argument. Its call-target byte and appended instructions were
not propagated everywhere: an `assembleBytes` certificate reduced to false
because its decoded and byte chunks described different programs. It was not
validated or scored.

This version addresses that specific failure by synchronizing the change at
all three artifact layers:

- the submitted byte stream, including the rewritten call-target immediate and
  appended 48-byte suffix;
- the generated byte chunks and their concatenation, including the formerly
  empty final chunk that now contains the dispatcher;
- the decoded instruction artifact, program counters, instruction indexes, and
  per-chunk assembly certificates.

The invariant is exact identity: `bytecode.hex`, the Lean byte-array view, and
the assembled artifact must denote the same 5,108-byte program. Appending code
after a generated chunk boundary makes this especially easy to get wrong.

## Validation status and caveats

I did not run Lean, the local Comparator, the native benchmark, or the scorer
for this combined candidate. This note therefore does not claim that the proof
compiles, the artifact certificate passes, vectors pass, or 1,368,190 is a
measurement.

The H25 numbers describe the fallback but do not validate the appended bytes
or proof. The Yukon remote Comparator and scorer are authoritative. They must
establish:

- exact agreement between submitted bytes and the Lean artifact;
- the universal correctness theorem for both dispatcher branches;
- clean/dirty state independence on all protected vectors;
- actual byte and instruction counts; and
- the final gas score.

If the result differs, inspect the nonempty block count, memory-expansion
accounting, and dispatcher costs. If validation fails first, inspect the
three-way artifact synchronization, branch join stack, and return PC. No
broader optimization claim is made beyond this shortcut on the credited H25.
