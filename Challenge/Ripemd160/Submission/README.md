# RIPEMD-160: generic block-loop stay falls through into the advance join, stacked on the direct empty-input digest arm (612,296 gas)

Parent: promoted commit `da752dc9` (validated `24701213`, 614,871 gas).

Two disjoint byte windows over the parent:

1. Short-size dispatch table re-laid so the empty input lands on the
   empty-digest arm directly (from fkiene's submission `b315daf6`, whose
   Lean CI passed): region 4616..4755 re-laid with 64 instructions kept, and
   same-width retargets at 4749, 4852, 5266, 5333, 6378. Only the `empty`
   vector changes: -12.
2. Generic block-loop stay fall-through (PC 192..244, below): -2,563.

614,871 - 12 - 2,563 = **612,296**.

Every block of a non-aligned input runs the generic loop: the core leaves
through `SWAP13 JUMP` at 4622 into the last-block test, which either exits to
the output at 4882 or re-enters the schedule writer at 461 through the shared
join (`JUMPDEST SWAP13 POP SWAP11 PUSH1 64 ADD SWAP11 PUSH2 461 JUMP`). The test
used to sit at 222 and reach the join at 210 with `PUSH1 222 PUSH1 210 JUMP`.

The test now starts at 210 (`JUMPDEST PUSH1 128 DUP13 ADD MSIZE LT PUSH2 4882
JUMPI`), its stay branch pushes the continuation `PUSH1 210` and falls straight
into the join `JUMPDEST` at 223. The 192 stub hops to 223 (`PUSH1 223 JUMP`),
the first-block continuation at 199 pushes 210, and the frame continuation in
`ColdLoop`, `ColdPaddingCore2.glFrame` and `ColdArtifact.padExitPath` is 210.
The 192..244 window keeps 53 bytes and 40 instructions; the dead tail after the
join's `JUMP` (235..244) keeps its old bytes, so no instruction index moves and
no PC outside 196, 200 and 210..234 changes.

Gas: the stay branch loses `PUSH1 210` (3) and `JUMP` (8); every other path
executes the same opcodes. The corpus runs 265 blocks through the generic
loop, 233 of them stay (32 inputs exit once): -11 x 233 = -2,563,
614,871 -> **612,308**.

Proof: `glHead`/`glTest`/`glMsize` sites move to instructions 107/112/111
(PC 210/216/215), `glPush` to 115 (PC 221, value 210), `splitJoin` and
`joinSwap` to 116 (PC 223); the `glHopJump` hop is gone; `valid_gl` (210) and
`valid_adv` (223) retarget; `CandidateArtifact` part 0, `CandidateBytes`
chunk 3 and `bytecode.hex` carry the bytes.

---

# RIPEMD-160: fall-through JUMPDEST retired from the 1000-byte recognizer arm, byte returned to the dead JUMP run (614,902 gas)

Parent: promoted commit `83fdda0f` (validated `c46d9598`, 614,903 gas).

The patterned 1000-byte recognizer arm (`RecArmsLong.a1000Template`, entry
PC 5838, instruction 3670) opened its scan head (`head1000`) with a
`JUMPDEST` at PC 5862 directly after the digest store. Nothing jumps to 5862
(no push of that value exists; the arm is entered only at 5838), so the
opcode was a 1-gas fall-through pad. It is removed; the arm body 5863..6134
moves down one byte, and the freed byte is appended to the unreachable
`0x56` run that follows the arm's `PUSH2 4959; JUMP`, so `part19` keeps 192
instructions and 332 bytes and every PC from 6135 on is unchanged. Only the
`Vectors.patterned(1000)` case enters the arm; no generated corpus input has
length 1000. 614,903 - 1 = **614,902**.

Changed: `RecArmsLong.head1000` (now identical in shape to `head376`),
`CandidateArtifact.part19` / `bytes19`, `CandidateBytes.chunk91..chunk95`,
`bytecode.hex`. No instruction index or site witness moves.

---

# RIPEMD-160: ordinary-writer JUMPDEST pad at PC 582 retired, instruction count restored in the dead head pad (614,903 gas)

Parent: promoted commit `0c57f37a` (validated `55693485`, 614,934 gas).

The ordinary table prologue (`Ordinary0..7`, PC 530..793, 31 runs on the
corpus) still carried the `JUMPDEST` at PC 582 that the 615,011 step left
behind when `PUSH1 228; MLOAD` became `DUP2` (`DUP2; PUSH2 224; MLOAD;
JUMPDEST`). It is gone; `PUSH1 180` widens to `PUSH2 180`, so `Ordinary1`
keeps 67 bytes (556..622) and no PC outside 582..588 moves. Stack, memory
writes and the `OrdinaryCertificate` plan are the parent's.

The instruction total is kept at 7000 by decoding the dead pad 56..63
(after the `JUMP` at 55, before `JUMPDEST` 64) as eight `STOP`s instead of
`PUSH1 0` plus six `STOP`s. Artifact instruction indices 28..237 move up by
one; indices 0..26 and 239 on are unchanged. Every index-valued witness in
that range moves, including the hoisted-store piece table
(`RecHoistedStoreSites.index .copy`, 133 -> 134).

Gas: one `JUMPDEST` per ordinary prologue, 31 runs:
614,934 -> **614,903**.

---

# RIPEMD-160: JUMPDEST pad retired from the 32-byte first-block writer head, window kept by a widened 232 push (614,934 gas)

Parent: promoted commit `6d2369d9` (validated `83e98140`, 614,945 gas).

The 32-byte path's first-block writer head (`First0.templateA`, PC 6442..6481,
11 runs on the corpus) carried a `JUMPDEST` after `DUP1` at PC 6472, left by
`79130afb` to keep the instruction total. No jump targets 6472; the head
leaves through `PUSH2 9983; JUMP` at 6482. The pad is removed and
`PUSH1 232` becomes `PUSH2 232`, so the head stays 40 bytes and every PC is
unchanged. `PUSH1` and `PUSH2` both cost 3, so each run saves the 1-gas
`JUMPDEST`: 614,945 - 11 = **614,934**.

The instruction total drops from 7001 to 7000 (part 21 now 180
instructions). Every index witness from 4072 on moves down by one:
`ColdPaddingCore0` (4078..4085), `ColdPaddingCore1` (4086..4092),
`ColdPaddingCore3` `lengthIterationPath` / `validLengthLoopHead`,
`ColdArtifact.padExitPath` (4091, 4092), `PadSites` (4093), `FirstCore`
`tableSite` (6859), `prefixSite` (6930) and `jumpSite` (6998), and the three
count theorems. Bytes: `CandidateArtifact.bytes21`, `CandidateBytes.chunk101`,
`bytecode.hex`. `First0.midStack` / `midMemory` are unchanged.

---

# RIPEMD-160: first-block writer pad pair retired, the 720 store widened in place (614,945 gas)

Parent: promoted commit `57041db9` (validated `d18dbe78`, 614,967 gas).

`First4` (PC 10136..10180, 11 runs on the corpus) carried two `JUMPDEST`
pads after the consuming 720 store. They were inserted when the shifted 814
store left the window, to keep the instruction total at 7003. They are now
gone: `PUSH22 720` widens to `PUSH24 720`, so the window keeps 45 bytes and
every PC from 10176 on is unchanged. Memory writes, stack shape and the
symbolic first-block layout are identical to the parent's.

The instruction total drops from 7003 to 7001. The only instruction-index
witnesses after the window are the `PrefixAfter` site (6933 -> 6931, PC
10185) and the closing `PUSH2 930; JUMP` site (7001 -> 6999, PC 10422) in
`FirstCore`. Every other site sits before index 6926.

Gas: two `JUMPDEST`s (1 each) per first-block run, 11 runs:
614,967 -> **614,945**.

Proof: `First4.template`; `FirstCore.prefixSite` / `prefixSite_pc` /
`jumpSite` / `jumpSite_pc`; `CandidateArtifact` part 36 (87 instructions,
same 295 bytes) and `instruction_count`; `ColdArtifact` /
`RecArtifact` counts; `CandidateBytes` chunk 158; `bytecode.hex`.

---

# RIPEMD-160: first-block 814 shifted store replaced by a plain 224-word store at 816 (614,967 gas)

Parent: promoted commit `a008d942` (validated `4bef73b4`, 615,011 gas).

The first-block writer (`First1..5` at 9983..10184, 11 runs on the corpus)
stored the 236 word at 814 after shifting it right 14 bytes
(`DUP1 PUSH15 112 SHR PUSH2 814 MSTORE`). After the writer finishes, the only
bytes of 814..847 that any round reads (`FirstLayout.low_sources`,
`high_sources`, `barrier_sources`) also match an unshifted copy of the 224
word stored two bytes higher, at 816. The 224 word is still on the stack in
`First3`, so the new store goes there: `DUP1 PUSH2 816 MSTORE` directly after
the 482 store. To pay for those bytes, `PUSH12 482` narrows to `PUSH7 482`,
which keeps the self-referential `PC` (value 10112, whose low byte 0x80 is
stored at 787) at 10112. `First4` drops the shifted store, gets two `JUMPDEST`
pads, and `PUSH2 720` widens to `PUSH22 720`. Both windows keep their byte
lengths (47 and 45), so no PC moves. The instruction total stays at 7003:
part 35 has 206 instructions and part 36 has 89.

After the writer, the symbolic layout differs from the parent only at bytes
826, 827, 846 and 847. The 816 write overlaps no other write in the writer,
so it can sit anywhere in the write order.

Gas per first-block run: the new store costs +9 (`DUP1`, `PUSH2`, `MSTORE`).
Removing the shifted store saves 15 and the two `JUMPDEST`s cost 2. Net -4,
times 11 executions: 615,011 -> **614,967**.

Proofs changed: `FirstLayout.symbols17` (three nested writes) and
`symbols25 := symbols24`; `FirstMemory.memory17` and `memory25 := memory24`;
`First3.template` / `memory`; `First4.template` / `memory`; `First608.read`
(the 814 case is dropped). Artifact files changed: `CandidateArtifact`
parts 35 and 36, `CandidateBytes` chunks 157 and 158, and `bytecode.hex`.

---

# RIPEMD-160: ordinary-writer 228 load replaced by a DUP of the resident 236 word, both 228 stores re-sourced eight bytes up (615,011 gas)

Parent: promoted commit `3988226b` (validated `79130afb`, 615,073 gas).

The ordinary table prologue (`Ordinary0..7`, PC 556..793, 31 runs on the
corpus) loaded the word at 228 (`PUSH1 228; MLOAD` at PC 577) for two stores,
`DUP2 PUSH2 540 MSTORE` and the consuming `PUSH2 504 MSTORE`. Both are now
painted from the word at 236, already on the stack two slots down, at the
same source-minus-destination offsets: `(548, 236)` and `(512, 236)`. The
slot that held the 228 word now holds a `DUP2` of the 236 word, so every
later stack index is unchanged.

`PUSH1 228; MLOAD; PUSH1 224; MLOAD` (12 gas) becomes
`DUP2; PUSH2 224; MLOAD; JUMPDEST` (10 gas): same 6 bytes, same four
instructions, no PC or instruction index moves. -2 gas x 31 executions:
615,073 -> **615,011**.

The new plan paints every lane, barrier, clear and biased byte the rounds
read exactly as before (`low_sources`, `high_sources`, `barrier_sources`,
`clear_sources`, `biased_sources` re-decided). Around the moved stores it is no
longer byte-equal to `result selected` below 662, so `unchanged_sources`
is narrowed to the window 666..944, which is the only range its one consumer
(`Ordinary75.read_add`, bytes 918..944) asks for.

Proof: `OrdinaryCertificate.plan` entries 27 and 29, `unchanged_sources`;
`Ordinary75` call site; `OrdinaryMemory.memory28`, `memory30`, `state1..6`;
`Ordinary1.template` / `outputs`; `Ordinary6.template` / `memory`;
`Ordinary7.template` / `memory`; `CandidateArtifact` part 1,
`CandidateBytes` chunks 9 and 11, `bytecode.hex`.

---

# RIPEMD-160: 228-word load retired from the first-block schedule writer, both of its stores re-sourced from a duplicated 224 word (615,073 gas)

Parent: promoted commit `f049c250` (validated `d91466eb`, 615,095 gas).

The 32-byte path builds its single message table in the first-block writer
(`First0` head at 6442..6481, `First1..5` at 9983..10184; 11 runs on the
corpus). It loaded seven source words (236, 262, 266, 228, 224, 258, 232).
The 228 word fed two stores, `DUP2 PUSH2 522 MSTORE` and the consuming
`PUSH2 558 MSTORE`, and nothing else. Both are moved four bytes down and
re-sourced from the 224 word at the same source-minus-destination offsets
(-294 and -330): `(518, 224)` and `(554, 224)`. After the whole writer the
symbolic layout differs from the parent's only at bytes 554..557, which no
round reads (`FirstLayout.low_sources`, `high_sources`, `barrier_sources`
re-decided).

In the head, `PUSH1 228; MLOAD; PUSH1 224; MLOAD` becomes
`PUSH2 224; MLOAD; DUP1; JUMPDEST`: the old 228 slot now holds the 224 word
and the old 224 slot holds its copy, so the stack depth and every later DUP
index are unchanged, and the window keeps 40 bytes / its instruction count.
No PC or instruction index moves.

Gas: 12 -> 10 per first-block prologue, 11 executions: 615,095 -> **615,073**.

Proof: `FirstLayout.symbols18` / `symbols20`; `FirstMemory.memory18`,
`memory20`, `state0..2`; `First0.template` / `templateA` / `outputs`;
`First3.template` / `memory`; `CandidateArtifact` parts 21 and 35,
`CandidateBytes` chunks 101 and 158, `bytecode.hex`.

---

# RIPEMD-160: 176-word load retired from the ordinary schedule writer, its store re-sourced from the resident 180 word (615,095 gas)

Parent: promoted commit `dbd767d0` (validated `fab6424c`, 615,157 gas).

The ordinary table prologue (`Ordinary0..7`, PC 556..793) loads fifteen
source words and paints 36 stores (`OrdinaryCertificate.plan`). The word at
176 was loaded once (`PUSH1 176; MLOAD` at PC 632) and consumed by a single
store at 630. That store now writes the already-resident 180 word at 634:
the 32-byte window keeps the same source-minus-destination offset (-454), so
bytes 634..661 are painted from the same fan bytes as before; 630..633 are no
longer painted by this store and 662..665 now receive fan bytes 208..211, and
the certificate shows neither range carries a byte the rounds read.
`low_sources`, `high_sources`, `barrier_sources`, `clear_sources` and
`biased_sources` decide unchanged against the new plan.

In `Ordinary2` the load becomes `DUP3; JUMPDEST` (the stack slot keeps its
position, now holding the 180 word), and `PUSH1 142` widens to `PUSH2 142`,
so the window stays 25 bytes / 17 instructions and no PC or instruction
index moves anywhere in the program; the PC-sourced stores at 666, 720 and
792 are unaffected. `Ordinary4` stores at 634 instead of 630.

Gas: `DUP3` (3) + `JUMPDEST` (1) replace `PUSH1` (3) + `MLOAD` (3): -2 per
ordinary prologue, 31 executions: 615,157 -> **615,095**.

Proof: `OrdinaryCertificate.plan` entry 15 is `(634, 180)`;
`unchanged_sources` excludes 662..665 (its only consumer, `Ordinary75`,
reads 918..944); `OrdinaryMemory.memory16`, `state2`, `state3`;
`Ordinary2.template` / `outputs`, `Ordinary4.template` / `memory`;
`CandidateArtifact` part 1, `CandidateBytes` chunks 9 and 11,
`bytecode.hex`.

---

# RIPEMD-160: Fall-through padded-block output tail, 32-byte read hoisted into the vacated slot (615,157 gas)

Parent: promoted commit `66eec9be` (validated `340e677c`, 615,277 gas).

The padded-block compressor (6504..9906) ended with `PUSH1 144; PUSH2 6409;
JUMP` and the output tail lived at JUMPDEST 6409. Every generated 64- and
128-byte vector (21 of the 49) runs that jump once. The tail body (76 bytes,
60 instructions) now sits at 9907, directly after the compressor, so the
`PUSH1 144` falls into its `SHR` (-12 gas per run: PUSH2, JUMP, JUMPDEST).

The 77 bytes vacated at 6409..6485 take the first 72 bytes of the 32-byte
special path (JUMPDEST, calldata read, endian stages, low store at 252, the
218/286 copies and seven table loads, `PUSH1 128`), then `PUSH2 9983; JUMP`.
JUMPDEST 9983 precedes the `PUSH1 147; MSTORE8` that resumes the path, so
every PC from 9984 on (the PC-sourced 0x80 at 10112, the CODECOPY source at
10426) is unchanged. The 143 guard now jumps to 6409. The 11 generated
32-byte vectors pay +12 each. Net: 21 x -12 + 11 x 12 = -120,
615,277 -> **615,157**.

Instruction indices 4079..6799 shift by -11; indices from 6861 on are unchanged.

Proof: `PadSites.middle` absorbs the tail body (site index 4094, output site
retired), `PadTailRaw` / `PadOutput` run without the jump (end PCs
9924/9955/9958/9976/9982), `PadBody` / `PadGas` drop the 6409 validity;
`First0` splits into `templateA` (run at 6442) and `entryTemplate` (run at
9983) with `midStack` / `midMemory`; `FirstTable` starts at 9983 (index 6860);
`FirstCore.midState` / `valid9983`; `FirstReadGas` site at index 4029 covers
the read, the loads and the jump; `FirstRead` at 6409; `ControlSites` /
`FirstEntry` / `FirstCopy` retarget 9911 -> 6409; `ColdArtifact` /
`ColdPaddingCore0/1/3` shift the generic padding-loop indices by -11;
`CandidateArtifact` parts 0/20/21/35, `CandidateBytes` chunks 2/100/101/154/155,
`bytecode.hex`.

---

# RIPEMD-160: Consuming low-64 screen for the two 1000-byte entries (615,277 gas)

Parent: promoted commit `edf8f2d8` (validated `27d78a01`, 615,279 gas).

Both 1000-byte vectors pass the low-64 screen at PC 21. It used to keep
the loaded `W 0` under the screen (`PUSH0; CALLDATALOAD; PUSH15 c; DUP2;
XOR; PUSH1 192; SHL; PUSH2 5838; JUMPI`), so the patterned arm received
`W 0` and popped it, and only the `a` seed at PC 48 used it. The screen now
consumes the word (`PUSH0; CALLDATALOAD; PUSH14 c; XOR; PUSH1 192; SHL;
PUSH2 5838; JUMPI`, -3 on both vectors). The `a` path reloads it with
`PUSH0; CALLDATALOAD` at PC 46..47 (+5), so its `PC` still sits at 48. The
patterned arm enters with an empty frame and its `POP` becomes a `JUMPDEST`
(-1). Net: `1000-byte` -4, `1000 a's` +2, 615,279 -> **615,277**.

The head is one instruction longer up to the `JUMP` at 55. The dead pad
56..63 becomes `PUSH1 0` plus six `STOP` (7 instructions), so JUMPDEST 64
is still instruction 34. No PC or instruction index outside 21..63 /
11..33 moves. The arm byte at 5862 changes in place.

Proof: `HoistedStoreAnchorRaw` (consuming `anchorPrefix`, `run_anchor_taken`
to an empty frame, `run_anchor_low_fall` to PC 46, new `reloadTemplate` /
`run_reload`), `HoistedStoreEntry` reload piece (index 19, PC 46),
`HoistedStoreSites` seed index 21, `HoistedStoreAnchor.taken`,
`Long.head1000` / `run_head1000` / `gasSteps_a1000_entry` / `correct1000`,
`DirectGuard` located anchor and seed indices and PC witnesses 14..25;
`CandidateArtifact` parts 0 and 19, `CandidateBytes` chunks 0 and 91,
`bytecode.hex`.

---

# RIPEMD-160: Re-anchored window cover for the 1000-byte recognizer arm (615,279 gas)

Parent: promoted commit `f3649929` (validated `e9be2c95`, 615,288 gas).

The patterned 1000-byte arm (JUMPDEST 5838, instruction 3670) proves the
input equal to `patterned 1000` from the eight chain words (bytes 0..255),
one literal window and 24 calldata window equalities. In the 251..501
pattern segment a window at `o` repeats an earlier window only at
`o - 145` (needs `o <= 364`) or `o - 401` (needs `o >= 401`), so bytes
396..400 need the literal. With the literal at 369 the segment used
nine windows (four, literal, `(401,0)`, `(433,32)`, `(465,64)`, `(470,69)`).
The literal now sits at 384 (bytes 384..415), and `(416,15)`, `(448,47)`,
`(470,69)` cover 416..501: eight windows.

`(401,0)` was the arm's free head (it XORed the `W 0` left by the entry
guard). The arm now pops that word and starts the accumulator with the
`(256,111)` difference, without an `OR`. Gas on the `1000-byte` vector:
`POP` (2) + first difference (15) + two windows (36) replaces head (9) +
`(256,111)` (18) + `(433, MSIZE)` (17) + `(465,64)` (18): -9,
615,288 -> **615,279**.

The arm is 4 bytes and 3 instructions shorter. The unreachable `JUMP` pad
after its final `JUMP` becomes `PUSH1 0x56` plus 28 `JUMP` (30 bytes,
29 instructions), so JUMPDEST 6144 / instruction 3848 and every later PC and
index are fixed. Part 20 (instructions 3839..) is unchanged.

Proof: `WindowCover.plan1000` / `anchors1000 = [384]` (`cover1000` by
`decide`), `Long.items1000`, `head1000` (now `POP` + the `(256,111)`
difference), `run_head1000`, `val1000`, `plan1000_mem` and the `result1000`
anchor case; `CandidateArtifact` part 19, `CandidateBytes` chunks 91..95,
`bytecode.hex`.

---

# RIPEMD-160: Fall-through 256-byte arm into the eight-word chain entry (615,288 gas)

Parent: promoted commit `dc46627e` (validated `956f3fe4`, 615,299 gas).

The patterned 256-byte arm (formerly JUMPDEST 5746, instruction 3634) ran
`JUMPDEST; PUSH20 d; PUSH0; MSTORE; PUSH0; PUSH2 4931; JUMP` into the
eight-word chain entry. Its five-instruction store/start prefix now sits
directly before that chain entry (arm JUMPDEST 4934, chain 4959), after the
output block's `RETURN` and a dead `PUSH2`, and falls through. The
`PUSH2; JUMP` pair (11 gas) is gone from the `256-byte` vector:
615,299 -> **615,288**.

The old arm slot is reused: two of its instructions become the dead
`PUSH2` before the arm and a dead `STOP` before the 64-byte arm, so the
instruction count is unchanged and every PC from 5775 on is fixed.
Indices 3482..3585 move by +6 and 3586..3633 by +7; PCs 4931..5523 move by
+28 and 5524..5745 by +29.

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
