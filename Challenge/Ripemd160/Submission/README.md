# RIPEMD-160: 256-byte recognizer arm laid out as a fall-through into the eight-word chain (615,288 gas)

Parent: promoted commit `dc46627e` (validated `956f3fe4`, 615,299 gas).

The 256-byte patterned arm stored its digest, pushed an empty accumulator
and ended in `PUSH2 4931; JUMP` to the eight-word chain entry. The block
immediately above that entry is the generic-path output, which ends in
`RETURN`, so the gap is free: the arm (JUMPDEST, digest store, `PUSH0`) now
sits at 4931 and falls into the chain JUMPDEST at 4956. `PUSH2` + `JUMP`
(11 gas) leave the 256-byte path: 615,299 -> **615,288**.

The removed jump's two instructions and four bytes reappear as dead
`STOP; PUSH2 0` directly before the 376-byte arm (5771..5774), so code
length (10,511), instruction count (7,003) and every PC/index outside
4931..5774 are unchanged; arm 376 (5775) and arm 1000 (5838) keep their
offsets and only retarget their chain jump to 4956.

Moved: chain entries 4931/5084/5123/5162/5200 -> 4956/5109/5148/5187/5225
(indices +5), shared success MSIZE 5242 -> 5267, arm 31 5245 -> 5270 (MSIZE
5309 -> 5334), arms 32..128 +25 bytes, arm 256 5746 -> 4931 (index 3634 ->
3482). Retargeted at the same-width size-table trampolines, the 256 equality
dispatch, and the 376/1000 chain jumps. `arm256Template` drops its
`jumpTemplate` and `gasSteps_arm256_entry` ends at the fall-through PC.

---

# RIPEMD-160: Calldata-size shift operand for the 55-byte recognizer literal (615,299 gas)

Parent: promoted commit `bc4f945d` (validated `76c2f807`, 615,300 gas).

The patterned 55-byte arm (instruction 3552) rebuilt its last-word literal
as `PUSH23 X; PUSH1 72; SHL`. The arm is entered only with
`CALLDATASIZE = 55`, so the literal is re-based to
`PUSH26 (X << 17); CALLDATASIZE; SHL`, the same word
`ZeroTailModel.expectedLast 55`; `CALLDATASIZE` (2 gas) replaces `PUSH1 72`
(3 gas). -1 gas on the `55-byte` vector: 615,300 -> **615,299**.

The arm grows by 2 bytes with the same instruction count. The bytes come
from two width-pad pushes in the recognizer: the shared chain result
`PUSH3 4651` (now `PUSH2`, `chainResultTemplate`) and the 65-byte arm's
`PUSH2 0x47` (now `PUSH1`, `byte65Template`). Instruction indices are
unchanged everywhere; arm 119 (5589) and every later PC are fixed.

Moved PCs: chain success MSIZE 5243 -> 5242, arm 31 5246 -> 5245 (its
MSIZE 5310 -> 5309), arm 32 5313 -> 5312, arm 55 5342 -> 5341, arm 56
5400 -> 5401, arm 63 5459 -> 5460, arm 64 5523 -> 5524, arm 65
5552 -> 5553, retargeted at the same-width trampoline pushes.
`RecognizerLiteral.run`'s calldata-size hypothesis widens to
`n = 55 ∨ n = 56 → size = n`.

---

# RIPEMD-160: Memory-size shift operand for the 119-byte recognizer literal (615,300 gas)

Parent: promoted commit `23abf6ae` (validated `83c2b330`, 615,301 gas).

The patterned 119-byte arm (JUMPDEST 5589, instruction 3605) rebuilt its
last-word literal as `PUSH23 X; PUSH1 72; SHL`. After the arm's digest
store at offset 0 the frame has exactly one active memory word, so `MSIZE`
pushes 32. The literal is re-based to `PUSH28 (X << 40); MSIZE; SHL`, which
is the same word `ZeroTailModel.expectedLast 119`; `MSIZE` (2 gas) replaces
`PUSH1 72` (3 gas). -1 gas on the `119-byte` vector: 615,301 -> **615,300**.

The arm grows by 4 bytes with the same instruction count. The bytes come
from two width-pad pushes in the 1000-byte arm (`PUSH2 0x008f`, `PUSH2
0x00af` become `PUSH1`; the corresponding `items1000` entries are plain
`.eq`) and from the unreachable pad before JUMPDEST 6144, which loses its
`PUSH2 4931` and is now 26 `JUMP` bytes. Instruction indices are unchanged
everywhere; JUMPDEST 6144 and all later PCs are fixed.

Moved PCs: arm 120 5648 -> 5652, arm 128 5713 -> 5717, arm 256 5742 -> 5746,
376-byte arm 5771 -> 5775, 1000-byte arm 5834 -> 5838, retargeted at the
same-width pushes of instructions 18, 3362, 3380, 3423, 3428.
`RecognizerLiteral.run` gains the `activeWords = 1` hypothesis already
carried by `RecArmsScan.run_prefix`.

---

# RIPEMD-160: Dead-pad-funded full-word literal for the 120-byte recognizer arm (615,301 gas)

Parent: promoted commit `77232a01` (validated `21326e0a`, 615,307 gas).

The patterned 120-byte arm (JUMPDEST 5648, instruction 3617) rebuilt its
last-word literal as `PUSH24 X; PUSH1 65; SHL` (9 gas) before
`PUSH1 96; CALLDATALOAD; XOR` and the three-word chain at 5123. It now pushes
the shifted word directly, `PUSH32 (X << 65)` (3 gas), which is exactly
`ZeroTailModel.expectedLast 120` — the generic `RecognizerLiteral.template`
case. -6 gas on the `120-byte` vector: 615,307 -> **615,301**.

The window grows by 5 bytes and loses 2 instructions. Both are absorbed by
the unreachable pad that followed the 1000-byte arm's final `JUMP` (old PCs
6111..6143: four `PUSH2 4931; JUMP`, `PUSH1 67; JUMP`, 14 `JUMP`; no
JUMPDEST, nothing jumps into it, CODECOPY reads only 10426..10547). The
pad is now `PUSH2 4931; JUMP` plus 24 `JUMP` (28 bytes, 26 instructions),
so JUMPDEST 6144 / instruction 3848 and everything after are fixed and the
artifact stays 10511 bytes / 7003 instructions.

Moved: arm 128 5708 -> 5713 (instruction 3629 -> 3627), arm 256 5737 -> 5742
(3636 -> 3634), 376-byte arm 5766 -> 5771 (3643 -> 3641), 1000-byte arm
5829 -> 5834 (3672 -> 3670). Retargeted pushes: head `PUSH2 5834` (instruction
18), trampoline `PUSH2 5713` (3380), equality dispatch `PUSH2 5742` / `PUSH2
5771` (3423 / 3428). Proof sites: `PrepRecognizerLiterals` (120 case dropped),
`RecArmsScan` arm tables, `RecArmsEach` arm128/arm256, `RecDispatch128`,
`RecArmsDispatch`, `RecArmsLong`, `RecPatternedSites`, `RecDirectGuardBase`,
`RecOriginalAnchor`, `RecHoistedStoreAnchorRaw`, `RecHoistedStoreAnchor`;
`CandidateArtifact` parts 0, 17, 18, 19, `CandidateBytes` chunks 0, 73, 75,
88..95, `bytecode.hex`.

---

# RIPEMD-160: BYTE-0 last-word check for the 65-byte chained recognizer arm (615,307 gas)

Parent: promoted commit `93106912` (validated `f4bb164c`, 615,308 gas).

The patterned 65-byte arm (JUMPDEST 5552, instruction 3593) built its
last-word difference as `PUSH1 0x47; PUSH1 248; SHL; PUSH1 64;
CALLDATALOAD; XOR` (18 gas) before jumping into the two-word chain at 5162.
The arm is reached only when `CALLDATASIZE = 65`, so the word at offset 64
is `b64 << 248`; the check now reads the byte directly:
`PUSH1 64; CALLDATALOAD; PUSH0; BYTE; PUSH2 0x0047; XOR` (17 gas, bytes
5576..5584). Width (9 bytes) and instruction count (6) are unchanged, so no
PC or instruction index outside the window moves. The chain ORs the start
value with the two full-word differences and branches once on zero; the
byte difference `0x47 XOR b64` is zero exactly when the old 256-bit
difference was. -1 gas on the `65-byte` vector: 615,308 -> **615,307**.

Proof: `RecArmsEach.byte65Template` / `run_byte65` give the new start
value; `readWord_64` (size-65 calldata word at 64 is `b64 * 2^248`, tail by
`tail_past_size`) and the kernel-decided `byte65_key` prove
`byte65_zero_iff`; `byte65_rev_iff` lifts it through
`ZeroTailModel.rev_zero_iff`, so `gasSteps_arm65` (now taking
`input.size = 65`, passed by `RecArmsDispatch`) keeps its conclusion.
`CandidateArtifact` part 18, `CandidateBytes` chunk 87, `bytecode.hex`.

---

# RIPEMD-160: BYTE-0 tail check for the one-byte recognizer arm (615,308 gas)

Parent: promoted commit `90c49473` (validated `37a224de`, 615,309 gas).

The patterned one-byte arm (JUMPDEST 4717, instruction 3391) compared its
single calldata word against `PUSH1 7; PUSH1 248; SHL` and then
`PUSH0; CALLDATALOAD; XOR` (17 gas). The arm is reached only when
`CALLDATASIZE = 1`, so the word is `b0 << 248` and the check now reads the
byte directly: `PUSH0; CALLDATALOAD; PUSH0; BYTE; PUSH2 0x0007; XOR`
(16 gas, bytes 4741..4748). The `PUSH0` byte index replaces the `PUSH1 248`
shift operand; the widened `PUSH2` keeps the 8-byte width and the
instruction count (6), so no PC or instruction index outside the window
moves. The XOR is zero exactly when `b0 = 7`, i.e. exactly when the old
256-bit difference was zero, and it is consumed only by the
`PUSH2 4651; JUMPI` result branch. -1 gas on the `1-byte` vector:
615,309 -> **615,308**.

Proof: `RecArmsEach.byte1Template` / `run_byte1` give the new value;
`readWord_one` (size-1 calldata word is `b0 * 2^248`) and the kernel-decided
`byte1_key` over `b0 < 256` prove `byte1_zero_iff`, which rewrites the arm's
branch condition back to `ZeroTailModel.result input 1`, so `gasSteps_arm1`
(now taking `input.size = 1`, passed by `RecArmsDispatch`) keeps its
statement. `RecognitionLift.Advances`/`advancesCheck` admit `BYTE`.
`CandidateArtifact` part 17, `CandidateBytes` chunk 74, `bytecode.hex`.

---

# RIPEMD-160: ordinary pack-window JUMPDEST pad retired by a widened message-load push (615,309 gas)

Parent: promoted commit `cfd609c6` (validated `ba93b2cc`, 615,340 gas).

The ordinary right-lane pack window (`RawPack`, PC 871..977) ended its
straight-line body with a width-pad `JUMPDEST` at 929 in front of the
first-block join `JUMPDEST` at 930. The ordinary prologue falls through both
(31 executions on the corpus). The round-2 message load `PUSH2 728` at 878 is
now `PUSH3 0x0002d8` (same value, same 3 gas), which absorbs the pad byte: the
window keeps 106 bytes, 930 stays the join and no PC moves. -1 gas per
ordinary prologue: 615,340 -> **615,309**.

Instruction count drops 7004 -> 7003, so every artifact instruction index
from 458 (the 930 join) on moves down by one: slice starts, `instructionPC`
facts, jump-destination indices, located instructions, the recognizer
arm/chain/return index tables and the hoisted-store piece indices. PCs and
stacks are unchanged. `RawPack`, `PrefixBefore` and `FirstPrologue.before`
carry the new tail; `CandidateArtifact` part 2, `CandidateBytes` chunks
13-14 and `bytecode.hex` carry the bytes.

---

# RIPEMD-160: calldata-size shift operand for the 56-byte recognizer literal (615,340 gas)

Parent: promoted commit `2783859a` (validated `e48295cc`, 615,341 gas).

The patterned 56-byte recognizer arm (JUMPDEST 5400) builds its expected
final calldata word as `PUSH24 X; PUSH1 65; SHL`. The arm is reached only
after the length dispatch has fixed `CALLDATASIZE = 56`, so the shift operand
is now `CALLDATASIZE` (2 gas) and the literal carries the remaining 9 bits:
`PUSH25 (X << 9); CALLDATASIZE; SHL` (bytes 5424..5450). Width (27 bytes) and
instruction count (3) are unchanged; no PC or instruction index outside the
window moves. -1 gas on the `56-byte` vector: 615,341 -> **615,340**.

Proof: `RecognizerLiteral.template 56`, `value56` and `run` take
`hsz : n = 56 -> calldata.size = 56`; `RecArmsScan.run_prefix`/`run_start`
thread it; `RecArmsEach` discharges it by `decide` for every other arm and by
the dispatch size fact for arm 56; `RecArmsDispatch` passes `h`.
`CandidateArtifact` part 18, `CandidateBytes` chunks 84-85, `bytecode.hex`.

---

# RIPEMD-160: early right-lane C-rotation on the padding-block prologue, SWAP4 retired (615,341 gas)

Parent: promoted commit `3c52899a` (accepted `92a9a66d`, 615,404 gas).

The padding-only block routine (entry 64) runs its right-lane prologue
across the 89..127 front and the 6504..6641 middle (`PadRawRight0`,
`PadRawRight1`, `PadRawPack`); it executes once for each of the 21 corpus
inputs whose length is a multiple of 64. Round 0 now computes the rotated
`C` for round 2 (`DUP2 DUP12 MUL PUSH1 23 SHR`) where it used to copy `e`
(`DUP9`); round 1 reads `e` from the suffix head (`DUP13`, alias `rho[0]`)
and ends `PUSH5 K DUP13`; the pack window loses its leading `SWAP4`.
+14 -14 -3 = -3 gas per padding block, 615,404 -> **615,341**.

Layout: the front keeps 64 bytes by moving its last five one-byte
instructions (`DUP5 AND DUP5 DUP5 DUP7`) behind the 6504 `JUMPDEST`; the
128 stub's continuation push narrows to `PUSH1 0x40` and a dead `STOP`
after its `JUMP` keeps 143 / instruction 81 fixed (stub sites move one
instruction / one byte down: 70, 71, 73, 74, 77, 78 at 128, 129, 132, 133,
137, 138). The middle keeps its byte and instruction count with the
round-1 key widened to `PUSH5`; 6542 and every later PC is unchanged.
The 556..759 ordinary-prologue window of `92a9a66d` is disjoint and kept.

Proof: `PadRawRight0` now carries the 6504 jump (ends at 6507),
`PadRawRight1` runs 6507..6542 with the new `rho[0]` alias, `PadRawPack`
input order `a,k,b,c,d,e`; `PadCore*`, `PadPrologue`, `PadSites`,
`LoopRaw.setContTemplate`, the stub-128 loop/entry sites, `CandidateArtifact`
parts 0/21, `CandidateBytes` chunks 1, 2, 101, 102 and `bytecode.hex`.

---

# RIPEMD-160: PC-sourced 594 store via a hoisted message-word load in the ordinary prologue (615,404 gas)

Parent: promoted commit `0c4cd6f4` (accepted `6928cadd`, 615,435 gas).

The ordinary message prologue (`PrepOrdinary0..7`, PC 530..793, 31 runs on
the corpus) loaded eleven fan-memory words in `Ordinary1`, computing the
biased word `K + m134` eighth and the word at 146 last, then stored the 146
word at 594 with `DUP1 PUSH2 594 MSTORE`. Its `PC` already lands three other
store offsets (666, 720, 792).

`Ordinary1` now loads the 146 word tenth, stores it with `DUP1 PC MSTORE`
whose `PC` byte sits exactly at 594, and computes `K + m134` last, so the
biased word is the top of the loaded group instead of the fourth slot. The
`PUSH1 138` and `PUSH1 168` loads are widened to `PUSH3` so the `PC` lands on 594; the window
grows by two bytes (556..622), which the `Ordinary3` pad `PUSH12 18` returns
as `PUSH10 18`, so the 666, 720 and 792 `PC` sites and every byte from 680
on keep their positions.

With the biased word on top after the `Ordinary2` loads are consumed,
`Ordinary5` writes 558 with `DUP1` and retires the word with `PUSH2 936
MSTORE` before the 846 store; the `DUP PUSH1 72 MSTORE` moves to the head of
`Ordinary6`, which no longer stores 936. Window byte ranges: `Ordinary1`
556..622, `Ordinary2` 623..647, `Ordinary3` 648..679; `Ordinary4..7`
unchanged. Instruction count unchanged.

The store order changes only for 558 and 936 (now steps 20 and 21, before
846). Neither overlaps any store between its old and new step, so
`OrdinaryCertificate.plan` folds to the same byte layout and
`unchanged_sources` / `biased_sources` are unchanged statements.

Gas: `PC` (2) replaces `PUSH2 594` (3); every other instruction is the same
opcode at the same cost: -1 per ordinary prologue, 31 executions:
615,435 -> **615,404**.

---

# RIPEMD-160: early right-lane C-rotation, SWAP4 retired from the ordinary prologue (614,967 gas)

Parent: promoted commit `bb6842e9` (accepted `343b16c8`, 615,497 gas).

The right-lane prologue window (PC 794..977: `RawRight0`, `RawRight1`,
`RawPack`) runs once per compressed block (265 times on the corpus). Round 1
used to end with `DUP15 DUP7 MUL PUSH1 23 SHR` (rotated `C` for round 2) and
the pack window opened with `SWAP4` to exchange it with the round-0 `e` copy
left by a `DUP9`. Now round 0 computes the rotation directly in that slot
(`DUP11 DUP3 MUL PUSH1 23 SHR`, input `b` via the `rho[2]` alias), round 1
reads `e` from the suffix head (`DUP13`, alias `rho[0]`), the round-1 tail is
`PUSH4 K DUP13`, and the `SWAP4` disappears. +14 -14 -3 +1 (width pad) = -2
gas per block, 615,497 -> **614,967**.

Width: one `JUMPDEST` pad at PC 929 (before the 930 loop entry) keeps the
window at 183 bytes / 111 instructions; boundaries 794, 871, 930, 977 and all
later PCs and instruction indices are unchanged (round 0/1 split moves
830 -> 835).

Proof: stack at 977 (and `PrefixBefore.outputs` at 930) unchanged.
`RawRight0` slot 1, `RawRight1` input slot 1 / output slots 0 and 4 and a
new `rho[0]` alias, `RawPack.inputStack` order `a,k,b,c,d,e`; `CoreRight0`,
`CoreRight1`, `CorePack`, `CorePrologue` restated accordingly;
`PrefixBefore.template` = `FirstPrologue.before`; `CandidateArtifact`
parts 1/2, `CandidateBytes` chunks 12..14 and `bytecode.hex` carry the bytes.

---

# RIPEMD-160: PC-sourced 0x80 padding byte relocated beside a shifted 482 store in the first-block prologue (615,497 gas)

Parent: promoted commit `62e72056` (accepted `784a8fe6`, 615,508 gas).

The first-block table prologue (`PrepFirst0..5`, PC 9944..10184, 11 runs on
the corpus) wrote the 0x80 padding marker at 787 with
`PUSH1 128 PUSH2 787 MSTORE8` in `First1`, and in `First3` stored the word
read from 262 at 468 with its high 14 bytes cleared by
`DUP3 PUSH18 (2^144-1) AND PUSH2 468 MSTORE`.

`First3` now stores `x << 112` at 482 (`DUP3 PUSH1 112 SHL PUSH12 482 MSTORE`):
the same 18 low bytes land at 482..499; 468..481 keep their entry zeros and
the 14 zero bytes go to 500..513, which are zero at that point in the
first-block layout. That shortens the window by 17 bytes, which hosts the
padding byte as `PC PUSH4 787 MSTORE8` with the `PC` byte at exactly 10112
(10112 mod 256 = 0x80). `First1` drops its `MSTORE8` and widens the 216
literal from `PUSH16` to `PUSH22`, so every window keeps its byte range and
no PC moves. 787 is touched by no other first-path store or load, so moving
the byte write from step 6 to step 17 leaves `symbols27` unchanged
(`FirstMemory.memory6` is now the identity step; `memory17` writes both
stores; `FirstLayout.shl112_byte` gives the byte view of the shift).

Instruction count unchanged (-3 in `First1`, +3 in `First3`); byte-diversity
budget 15,063 -> 15,062 (limit 15,066).

Gas: `PC` (2) replaces `PUSH1 128` (3), `SHL` replaces `AND`: -1 per
first-block prologue, 11 executions: 615,508 -> **615,497**.

---
