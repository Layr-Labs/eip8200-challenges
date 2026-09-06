# MODEXP: skip the exponent bit loop's first iteration by copying `BASE` onto `ACC`

## Artifact

`Challenge/Modexp/Submission/bytecode.hex` is 3,027 bytes / 1,846 instructions.
It is the previous artifact (3,000 bytes / 1,831 instructions) with one in-place
window, one retargeted jump immediate, and one appended block.

### In-place window

Instructions 1623..1624 at pc 2496..2497 are `SWAP1; SWAP1`; they become
`JUMPDEST; JUMPDEST`. Two bytes, two instructions, so neither the byte length
nor the instruction count of the artifact moves, and pc 2496 and pc 2497 become
jump destinations that nothing targets.

### Retargeted immediate

The `LZ` block's byte-zero arm ends with `PUSH2 0x06fd; JUMP` at pc 2968. The
immediate alone is rewritten from `0x06fd` (1789) to `0x0bb8` (3000). The
instruction stays a `PUSH2`, so every program counter, instruction index and
existing jump destination in the artifact is unchanged.

### Appended block, 27 bytes at pc 3000..3026, instruction indices 1831..1845

    3000  5b        JUMPDEST
    3001  81        DUP2
    3002  15        ISZERO
    3003  610bce    PUSH2 0x0bce      ; 3022
    3006  57        JUMPI
    3007  612480    PUSH2 0x2480      ; V_S32
    3010  51        MLOAD
    3011  610800    PUSH2 0x0800      ; BASE
    3014  610400    PUSH2 0x0400      ; ACC
    3017  5e        MCOPY
    3018  610728    PUSH2 0x0728      ; 1832
    3021  56        JUMP
    3022  5b        JUMPDEST
    3023  6106fd    PUSH2 0x06fd      ; 1789
    3026  56        JUMP

The block is entered with `[mask, w, i]` on top of the exponent-loop frame,
where `w` is the leading exponent byte. `DUP2; ISZERO` tests `w`. A zero byte
takes the arm at pc 3022 and jumps to the bit-loop head at pc 1789, so that
path is byte-for-byte the old behaviour. A nonzero byte falls through, reads
`32 * n` from the word at `V_S32 = 0x2480`, copies that many bytes from
`BASE = 0x0800` to `ACC = 0x0400` with `MCOPY`, and resumes the bit loop at its
mask shift, pc 1832.

## Proof

### New module

`Challenge/Modexp/Submission/Proofs/Fast/Paths/P18.lean` holds the three basic
blocks of the appended code as located paths:

* `blk1831` — indices 1831..1835, pc 3000..3006, the zero test;
* `blk1836` — indices 1836..1842, pc 3007..3021, the copy and the resume;
* `blk1843` — indices 1843..1845, pc 3022..3026, the zero-byte arm.

### `Proofs/Fast/Lz.lean`

* `lzBase` — the state at pc 3000;
* `run_lzFirst` — retargeted from `lzJoin` to `lzBase`;
* `topExp_le` — `2 ^ topExp w ≤ w` for a nonzero byte.

### `Proofs/Fast/Defs.lean`

* `jumpDest3000` and `jumpDest3022` — the two new destinations;
* `fastPC24` — the program-counter table entry for the appended indices.

### `Proofs/Fast/Exp.lean`

States: `lzBaseCopy` (pc 3007) and `lzBaseSkip` (pc 3022). The resume point at
pc 1832 is the existing `ebitNext`.

Block traces: `run_lzBase_zero`, `run_lzBase_copy`, `run_lzBaseSkip` and
`run_lzBaseCopy`.

Arithmetic: `bitAt_gt_topExp`, `bitAt_topExp`, `montMul_one_left`,
`expAcc_of_zeros_then_one` and `expAcc_skipOne` give the accumulator the skipped
iteration would have produced; `ebInv_accCopy` carries `EbInv` across the copy
using `fastRepresents_mcopyMem` and `fastRepresents_mcopyMem_disjoint`.

Memory: `byteMemAt` now branches on `i = 0 ∧ expByte input bsize i ≠ 0` and, on
that branch, starts from `mcopyMem mem 1024 2048 (32 * n)` at bit index
`lzSkip input bsize i + 1`. `ebMems`, `readWord_ebMems`, `ebMems_frame` and
`ebMems_inv` are threaded through the same branch; `readWord_mcopyMem_disjoint`,
`frame_mcopyMem`, `fastRepresents_mcopyMem` and
`fastRepresents_mcopyMem_disjoint` move above their first use.

Gas: `gasSteps_ebLoad` takes the hypothesis
`¬(i = 0 ∧ expByte input bsize i ≠ 0)` and reaches `ebitHead` through
`blk1831` and `blk1843`; `gasSteps_ebLoadCopy` is new and reaches `ebitNext`
through `blk1831` and `blk1836`; `gasSteps_byteFrom` factors the bit loop from
an arbitrary starting bit; `gasSteps_byteBody` splits three ways on the branch
condition and, in the copy case, on whether `lzSkip input bsize i = 7`.

### Regenerated

`Challenge/Modexp/Submission/Bytes.lean`,
`Challenge/Modexp/Submission/Bytecode.lean` and
`Challenge/Modexp/Submission/Proofs/Bytecode/Artifact.lean` are regenerated from
the artifact; the byte and instruction chunk boundaries are unchanged and only
the entries covering the edited windows and the appended block move.

## Frame the appended block relies on

The copy is sized from the word at `V_S32 = 0x2480`, which the setup writes
once and which `Frame` carries as its `s32` field alongside `minvW` at `0x24a0`,
`ml` at `0x24c0`, `tl` at `0x24e0` and `eoff` at `0x2500`. `frame_mcopyMem`
shows a copy into `ACC` preserves all five, since `0x0400 + 32 * n` stays below
`0x2480` for every `n` the artifact accepts. The memory the copy touches is
`[0x0400, 0x0400 + 32 * n)` for the destination and
`[0x0800, 0x0800 + 32 * n)` for the source, both inside the region the setup has
already made active, so `activeWords_fix2` shows the copy expands nothing and
the block's gas is the sum of its opcode costs.

## Block boundaries in the regenerated tables

`Proofs/Bytecode/Artifact.lean` keeps its existing chunk boundaries. The
appended instructions extend the final instruction chunk by fifteen entries and
the final byte chunk by twenty-seven bytes; every earlier chunk is byte- and
entry-identical to the previous artifact. `Challenge/Modexp/Benchmark/Artifact.lean`
is 48 chunks of 64 bytes.

## Result

44/44 vectors correct, 3,402,255 gas, Tier 1 PASS.

`Challenge.Modexp.Submission.Solution` builds with
`propext`, `Classical.choice` and `Quot.sound` as its only axioms.

## Reproduction

    lake build Challenge.Modexp.Submission.Solution
    lake build modexpchallenge
    .lake/build/bin/modexpchallenge --hex=Challenge/Modexp/Submission/bytecode.hex
