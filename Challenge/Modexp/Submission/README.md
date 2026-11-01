# Current refinement: one-word exponent/modulus size test at the entry (-6 gas on every vector, -264 gas per draw)

* pc 0..15: `PUSH1 0x20 DUP1 CALLDATALOAD XOR PUSH1 0x40 CALLDATALOAD PUSH1 0x20 XOR OR PUSH2 0x0242 JUMPI`
  becomes `PUSH1 0x22 CALLDATALOAD PUSH1 0x40 CALLDATALOAD ADD PUSH3 0x200020 XOR PUSH2 0x0242 JUMPI`
  (same 16 bytes, 27 -> 21 gas before the branch). For a valid tuple (every declared size <= 1024)
  the unaligned word at 34 is exactly `exponentSize * 2^16`, so the sum equals `0x200020` exactly
  when both sizes are 32. Every vector runs this block: -6 gas each, -264 per draw on every seed.
* The two removed instructions are given back in the unreachable filler at pc 93
  (`PUSH4 0` -> `PUSH2 0, PUSH0, PUSH0`); indices of pcs 16..92 move down by two, all later
  indices are unchanged; image 10,983 bytes / 8,638 instructions.
* Proofs: `Bytecode/EarlyWordProgram` (`sizeValueProgram`, `sizeDiff`, new `readWord34_toNat`,
  `sizeDiff_zero_iff` under the EIP-7823 size bounds, `sizeDiff_zero_of`), `Bytecode/EarlyWordGas`
  (`steps_size_miss` takes the bounds), `CycleGlobal/EarlyWordCorrect` (`legacy` takes
  `ValidInput`), `CycleGlobal/WindowCorrect` (passes it), `CycleGlobal/ArtifactEarlyWordPaths`,
  `CycleGlobal/ArtifactWindowPaths` (indices 11/17/28/34/41 -> 9/15/26/32/39); regenerated
  `Cycle/Artifact.lean` and `Cycle/Bytes.lean`.

# Port: my B..K refinement series on top of aerugo-ef's direct-carry frontier (-434 gas per draw)

aerugo-ef's promoted `733f8a93` (direct radix-240 carry recovery in the five- and nine-digit kernels)
was built on `9b28324d`, before my own promoted series `670bc87a` .. `846b17f0` and the later
`8de1dd4c` / pc-645 refinements. This tree is `733f8a93` with that whole series ported on top:

* Bytecode: `733f8a93`'s image with my byte edits applied unchanged (bytes 93..98, 645..647,
  2663..2676, 2723..2730, 2933..2948, 3182..3211, 3240..3247, 3437..3446, 3482..3492, 3697..3705,
  3728..3742, 3905, 4804..4813, 7642..7651, 10763..10770); none of them overlaps the kernel edits of
  `733f8a93` (4390..10229) and every replaced byte range was checked to be identical in both parents.
  Image 10,983 bytes, 8,638 instructions.
* Proofs: every instruction-index literal of the base, of `733f8a93` and of my series was rewritten
  old index -> pc -> new index into this image's numbering, then the 14 proof files both lines had
  touched were merged 3-way; the only conflicting hunks were my own removals (the square-loop
  counter exit block, and the four-limb head's top-limb clear with its pc lemmas). Files only my series touched are taken
  from it; files only `733f8a93` touched are its versions re-indexed. `Cycle/Artifact.lean` and
  `Cycle/Bytes.lean` are regenerated.
* Gas: -434 per draw against `733f8a93` on every seed (Python replica of the common minimal draw
  361,593 -> 361,159).

The individual refinements of the ported series follow, then `733f8a93`'s own notes.

# Current refinement: the entry check's padding `JUMPDEST` at pc 645 is folded into the bail push (-4 gas per draw)

* The merged RSA entry check (top limb, parity, width, Montgomery inverse) ended in
  `OR JUMPDEST PUSH1 0xdb JUMPI`; the `JUMPDEST` is not a jump target (layout padding) and ran once per
  RSA vector. It is now `OR PUSH2 0x00db JUMPI` at the same pcs.
* The removed instruction is given back in the unreachable filler at pc 93 (`PUSH5 0` becomes
  `PUSH4 0, PUSH0`), so indices 46..453 move up by one and everything from index 455 (pc 648) on is
  unchanged; the image keeps 8,727 instructions and 10,983 bytes.
* Proofs: `CycleGlobal/FastP0.blk1003` ends in `pushAt 453 2 219, opAt 455 .JUMPI`;
  `PrefixPC.eq_old` now covers 370..435 at offset 0, `eq_old2` is split into `eq_old2a` (453..454,
  offset +2) and `eq_old2` (455..467, offset +3); the `FastDefs` pc tables and every other index
  literal in 45..455 were rewritten old index -> pc -> new index; regenerated `Cycle/Artifact.lean`
  and `Cycle/Bytes.lean`.

# Current refinement: two never-read setup stores dropped (E5 entry cache at `0x06a2`, kernel zero at `0x0800`; -124 gas per draw)

* Conversion setup E5 (pc 2663) computed `entry = 3017 - 29 * n` and stored it at `0x06a2`
  (`DUP1 PUSH1 29 MUL PUSH2 3017 SUB PUSH2 0x06a2 MSTORE`, 23 gas). Nothing reads that word, so the
  eight instructions and the following `PUSH1 32` are now one `PUSH13 32` (every pc unchanged).
* Kernel setup (pc 3240) stored a zero word at `0x0800` (`PUSH0 PUSH2 0x0800 MSTORE`, 8 gas). Every
  kernel writes that row word before reading it (the square route even preclears it with the calldata
  copy), so the store is gone; `SWAP2 PUSH1 0x1f` becomes `SWAP2 PUSH6 0x1f` and every pc is unchanged.
* Both run once per RSA vector: -31 per vector, -124 per draw on every seed.
* Proofs: the two wrapper memories become the identity (`Fast/ShiftCacheModel.cacheMem mem n := mem`,
  `Fast/SquarePartialClear.memory mem := mem`), so their read/represent lemmas are `rfl`; the
  `StepInv.cache` field and `read_cache` uses are gone; the E5 lemmas (`CycleGlobal/ShiftTrace3`) and
  their consumers (`ShiftTrace4`, `RootE3Bindings`) drop the `0x06a2` layer; `TnM128Setup.clearProgram`
  is empty and `pointersJumpProgram` uses `PUSH6 31`; `PrefixPC.eq_old_tail11/12` re-cut;
  `CycleCaller/Terminal` proves the caller-stack field through the definitions. Instructions are given
  back in unreachable fillers (pc 3482, 3697, 4804); the image keeps 8,727 instructions.

# Current refinement: the shift-reduce loop heads no longer clear the `t` top limb (-168 gas per draw)

* Both conversion loop heads (eight limbs at pc 2714, four limbs at 10754) ran
  `PUSH0 PUSH2 top MSTORE` after the `MCOPY` on every digit step (21 steps per draw). Nothing reads that
  word before the section's first block (`rideTopProgramNP`) overwrites it, so the store is gone; the
  next push is widened to `PUSH7 0x0820` so every pc is unchanged.
* Proofs: the machine runs on `uMem0 = mcopy` while the model keeps `uMem` (top cleared);
  `Fast/M9MacRun.run_ride_top_np_stale` and the new `CycleGlobal/M9MacStale` (`l1StepOn_stale`,
  `gasSteps_block0_stale`, `gasSteps_zero4_stale`, `gasSteps_macChain_stale`) show the section reaches
  the old conclusion from `uMem0`; `M9MacShift.gasSteps_macSection_stale`, `ShiftStates` (`uMem0`,
  `estimateState` at `headPC + 9`), `ShiftPaths`, `ShiftTrace2`, `ShiftTrace4`; `PrefixPC.eq_old_tail12`
  offset +15; three instructions given back at pc 3697 (eight limbs), image 8,727 instructions.

# Current refinement: the staged square entry no longer overwrites two never-read frame slots (-60 gas per draw)

* pc 3728: `JUMPDEST PUSH2 0x14b1 SWAP2 POP PUSH0 SWAP3 POP PUSH4 0x1e0 SUB` -> `JUMPDEST PUSH12 0x1e0 SUB`.
  The two slots keep their previous values (the setup call's return address 3728 and `pb - 32 = 480`)
  instead of 5297 and 0; no path ever reads either slot. 15 gas per RSA vector.
* The six instructions are given back in the unreachable filler at pc 3905 (`PUSH5` + six `POP`s).
* Proofs: `SquareStagedEntry` (program, block `2879 3 3728`, `h1State`), `CycleCaller/Blocks`,
  `CycleCaller/Prefix.frame` (`hd := 3728`, `w3 := 480`), `R5Head` frame stack; indices of pcs
  3743..3904 rewritten; `Cycle/Artifact.lean`, `Cycle/Bytes.lean` regenerated.

# Current refinement: the eight-limb conversion block 5 no longer starts with a `JUMPDEST` (-14 gas per draw)

* Nothing jumps to pc 2933 since the four-limb head got private chain copies, but every eight-limb
  digit step executed its `JUMPDEST`. Block 5 is now `rideProgramW3 6 2176` (the `t`-limb load pushed as
  `PUSH3`, the shape of `macFusedPostProgramW3`) at pc 2933; block 6 stays at 2966. The instruction is
  given back in the unreachable filler at pc 3482 (`PUSH2 0x6161, MLOAD x8`).
* Proofs: `Fast/M9MacRun.run_rideW3`, `CycleGlobal/M9MacBlocks.block5` (and the obsolete `jumpDest3032`
  removed), `M9MacChain` (block 5 step), `PrefixPC.eq_old_tail13` removed and its 115 `ShiftPCs` users
  proved by `pc_by_len`; index literals of pcs 2934..3481 rewritten.

# Current refinement: the staged square entry drops its executed padding `JUMPDEST` (-4 gas per draw)

* pc 3734: `PUSH0 JUMPDEST SWAP3 POP PUSH3 0x0001e0 SUB` -> `PUSH0 SWAP3 POP PUSH4 0x000001e0 SUB`
  (same 9 bytes, same stack effect), run once by every RSA vector. The removed instruction is given
  back by re-splitting the unreachable `PUSH12` filler at pc 3905 into `PUSH11` plus one `POP` byte,
  so instruction indices from 3026 on are unchanged; indices of pcs 3736..3904 move down by one.
* Proofs: `CycleGlobal/SquareStagedEntry.program` and `CycleCaller/Blocks.entryProgram` (9
  instructions), `R5Head` (`h1Program` at index 2888), `R5/Blocks` (product segment 2 at 2911,
  `ctl3901` at 3022); `Cycle/Artifact.lean`, `Cycle/Bytes.lean` regenerated.

# Current refinement: the square-loop exit no longer runs six filler `JUMPDEST`s (-12 gas per draw)

* The RSA-2048 square-loop counter block ended in `PUSH2 0x163e JUMPI` followed by six `JUMPDEST`s
  (pc 7646..7651) that every loop exit executed. The jump target is now pushed as `PUSH8 0x163e`
  (the six filler bytes become leading zero bytes of the push), so `JUMPI` sits at 7651 and the exit
  falls straight through to the unpack block at 7652. Byte PCs are unchanged; the image now has
  8,730 instructions (six fewer), so every instruction index after 6053 moves down by six.
* Proofs: `Cycle/Execution/counterHead` (`.push 8 5694`, model pc 7651, `counterExitProgram` removed),
  `Cycle/CounterControl` (`tested` at 7651, exit branch goes straight to 7652), `Cycle/LoopBlocks`
  (`counterJumpBlock` at 7651, `counterExitBlock` removed); index literals after 6053 and the
  instruction-count bound (8,730) rewritten mechanically in `Cycle/`, `CycleCaller/`, `CycleGlobal/`,
  `R5/`; `Cycle/Artifact.lean`, `Cycle/Bytes.lean` regenerated.

# Current refinement: the last three dead-frame setup padding `JUMPDEST`s are gone too (-12 gas per draw, -48 with the previous one)

* `CycleCaller/DeadSetup.loadProgram` is now `PUSH0 x7, PUSH22 0x0d13` (8 instructions, same 30 bytes,
  same output stack). The three extra instructions are given back by re-splitting the unreachable
  `PUSH6` filler at pc 3482 (after the four-limb repair jump) into `PUSH3` plus three more `MLOAD`
  bytes, so every instruction index from 2712 (pc 3493) on is unchanged; indices of pcs 3212..3481
  move down by three.
* Proofs: `DeadSetup` (length 42), `CycleCaller/Blocks`, `Cios2Dispatch` (`2467 42 3182`), `R5/Blocks`
  (2509 / 2664), `CsubFixed` (the pc-3462 four-limb block at 2691..2703, anchor at index 2676 = pc 3447),
  `ShiftPCs`; all index literals rewritten mechanically by old-index -> pc -> new-index.

# Current refinement: nine executed padding `JUMPDEST`s dropped from the dead-frame kernel setup (-36 gas per draw)

* The setup entry at pc 3182 (`CycleCaller/DeadSetup.loadProgram`) pushed its seven zero frame words
  interleaved with twelve index-preserving `JUMPDEST`s. It now runs `PUSH0 x7, JUMPDEST x3,
  PUSH19 0x0d13` (same 30 bytes, same output stack): -9 gas per RSA vector.
* The nine instructions are given back by re-splitting the unreachable `PUSH9 0` at pc 3437 (after
  the R5 tail `JUMP`) into ten `PUSH0`s, so every instruction index from 2679 (pc 3447) on is
  unchanged. Image still 10,983 bytes / 8,736 instructions.
* Proofs: `DeadSetup` (program, length 45), `CycleCaller/Blocks` and `Cios2Dispatch` (block
  `2467 45 3182`), `R5/Blocks` (indices 2512 / 2667), `ShiftPCs` / `CsubFixed` index lemmas (anchor
  moved to index 2679), `Cycle/Artifact.lean`, `Cycle/Bytes.lean` regenerated.

---

# Complete direct-carry port onto the current public conversion layout

The measured candidate uses 362,011 gas on the standard seed-zero 44 cases,
2,694 below its immediate public parent and 1,242 below the smaller local
carry port. All 24 uncancelled carry handoffs use a direct radix-240 recovery;
eight are in the five-digit kernel and sixteen are in the nine-digit kernel.
The latest public conversion improvements are retained. The theorem in
`Proofs/CycleGlobal/Correct.lean` binds this implementation to MODEXP.
Verification receipts accompany the review package.

Immediate source parent: mpjunior92 submission
9b28324d-2c0d-406b-9b13-14f8c0b36888, commit
55b84fa420d7f2c5253ef7502af3d14b4e36f1a1.
Claude found the original optimization in aerugo-ef's repository.
The inherited Apache 2.0 notices and provenance follow.

---

# Current refinement: the four-limb conversion loop runs private copies of blocks 5..7, the middle block and the counter (-58 gas per draw)

* After its zero-carry first product the four-limb head no longer jumps back into the shared chain
  (`PUSH2 2933 JUMP` + `JUMPDEST`) or through the shared counter `JUMPDEST`: it falls through private
  copies (pc 10845..10978) and leaves the loop with `PUSH2 3069 JUMP`. Repair rounds still use the
  shared add loop and counter. Image 10,983 bytes / 8,736 instructions.
* Proofs: `ShiftStates.midPC`, `csubCall4State`, `csubExit4State`; `ShiftPaths` copies
  (`blk3125h`, `blk3253h`, `blkExit4`); `ShiftTrace3` `_h4` lemmas and `run_exit4`; `M9MacChain`
  (`startPCC`, `gasSteps_blockC`, `gasSteps_runC`, `sectionEndPC`); `ShiftTrace4.gasSteps_stepPre`
  returns which counter the step ends in (a `Sum`).

# Current refinement: the four-limb loop head runs its own zero-carry first product (-266 gas per draw)

* The four-limb head ended in `PUSH0 PUSH2 2901 JUMP` into the generic chain block 4 (carry-in and
  `t` load). It now runs `rideTopProgramNP 6 2208` (the block-0 shape: zero carry, zero `t` top)
  at 10827 and `PUSH2 2933 JUMP` into block 5; block 4's `JUMPDEST` moved to the start of block 5.
  -38 gas per four-limb digit step; eight-limb path unchanged. Image 10,849 bytes / 8,624 instructions.
* Proofs: `M9MacBlocks` (block4/block5/zero4Block/jump4Block), `M9MacChain.gasSteps_zero4` and the
  four-limb branch of `gasSteps_macChain`, `M9MacShift`/`ShiftTrace4` (t-top premise for n = 4),
  `Fast/M9MacRun.run_jump4`, `PrefixPC` (`eq_old_tail12` to 2247, new `eq_old_tail13`), `ShiftPCs`.

# Current refinement: `N1 >> 128` rides in the dead `esize` slot of the conversion loop (-162 gas per draw)

* E5's `DUP13` (esize) becomes `PUSH1 0x20 MLOAD PUSH1 0x80 SHR SWAP13`: the riding esize slot (dead
  after E5) now holds the refinement constant `mem[32] >> 128`, which the estimate of both loop heads
  reads with `DUP16` instead of reloading it every digit step (12 -> 3 gas); the `JUMPDEST` pad of the
  t-top store is dropped. Heads at 2714 / 10754, image 10,832 bytes / 8,609 instructions.
* Proofs: `ShiftStates.entrySlots` (slot 12 is `readWord mem 32 >> 128`), `ShiftPaths` (E5 and head
  blocks), `ShiftTrace2/3/4`, `M9MacBlocks/Chain/Shift`, `RootE3Bindings`, `ShiftPCs`.

# Housekeeping: `CycleGlobal/ShiftPCs.lean` written with a local `IPC` notation and two tactic macros

* Same 659 statements and names, 92 KB smaller, so the tree stays under the 8 MiB archive limit.

# Current refinement: each conversion loop head stores the t-area top limb at a literal address (-42 gas per draw)

* Both head copies ran `PUSH0 PUSH2 0x0ae0 MLOAD MSTORE` (store zero at the cached pointer
  `mem[0x0ae0] = 2080 + 32 n`). Each head now pushes its own constant (`0x0920` for eight limbs,
  `0x08a0` for four) followed by a `JUMPDEST` pad: -2 gas per digit step, same bytes and indices.
* Proofs: `CycleGlobal/ShiftPaths` (`blk3018`, `blk3018h`), `ShiftTrace2` (`run_shiftBody`,
  `run_shiftBody_h4` take `2080 + 32 n = 2336` / `2208`), `ShiftTrace4` call sites.

# Current refinement: a second shift-reduce loop head for four limbs (-136 gas per draw)

* The conversion loop head ended in `PUSH0 DUP5 JUMP; JUMPDEST POP` (16 gas per digit step) to
  enter the multiply-accumulate chain of the width. The eight-limb head (now at 2708) falls straight
  into chain block 0 at 2787; an appended byte copy of the head at 10752 ends in
  `PUSH0 PUSH2 2901 JUMP` into chain block 4.
* The riding scratch slot holds the head of the width (`18796 - 2011 n`, computed by the E5 tail);
  the bottom test (`DUP3 JUMPI`) and the E3 phase switch (`DUP2 JUMP`) jump through it.
* Image 10,836 bytes / 8,611 instructions; every pc and index from 2787 on is unchanged.
* Proofs: `CycleGlobal/ShiftStates` (`headPC`, `headWord`), `ShiftPaths` (head blocks and `_h`
  copies), `ShiftTrace2/3/4`, `M9MacBlocks/Chain/Shift` (block 0 at 2787, trampoline at 10831,
  `sectionPC`), `RootE3PhaseRun`/`RootE3Bindings`, `PrefixPC`/`ShiftPCs`, appended
  `Fast/M9MacRun` lemmas (`run_ride_top_np`, `run_entry4`); `Cycle/Artifact.lean`, `Cycle/Bytes.lean`
  regenerated.

# Current refinement: the staged entry's unread `w3` frame word is pushed as zero (-12 gas per draw)

* 3734 `PUSH1 0xc0 MLOAD` (frame slot 2, never read by either kernel) -> `PUSH0 JUMPDEST`; `PUSH2 0x01e0`
  widened to `PUSH3` so the 15-byte / 10-instruction block keeps every pc and index. -3 per RSA vector.
* Proofs: `CycleCaller/Blocks.entryProgram`, `CycleGlobal/SquareStagedEntry.program`/`h1State`,
  `CycleCaller/Prefix.frame.w3`, `CycleGlobal/R5Head.frameStack`.

# Current refinement: seven never-read kernel frame words are no longer loaded (-120 gas per draw)

* The common kernel setup at 3182 loaded `m96`, `tl`, `m0` (via `DUP9 PUSH1 1 SHR PUSH1 0x20 ADD`),
  `m64`, the row-end pointer `aprev` (`PUSH2 0x0ac0 MLOAD DUP7 ADD`) and `m32` into the caller frame;
  a dynamic liveness pass shows no kernel ever reads them (they are still on the stack at `RETURN`).
* They are now `PUSH0` (padded with `JUMPDEST`s; `PUSH2 0x0d13` widened to `PUSH10`), so the block
  keeps 30 bytes / 20 instructions and every pc and index is unchanged. -30 gas per RSA vector.
* Proofs: new `CycleCaller/DeadSetup.lean` (program, `run_load`, `run_entry_sq`), `CycleCaller/Blocks`
  and `CycleGlobal/Cios2Dispatch` bind it; `CycleCaller/Prefix.frame` and `CycleGlobal/R5Head` carry
  `0` for those `Caller` fields (all kernel lemmas are generic in the frame).

# Current refinement: shift-reduce loop exit block moved behind the bottom test (-66 gas per draw)

* **Before:** the counter block at 3061 (`JUMPDEST NOT ADD DUP1 PUSH2 0x0a90 JUMPI`) fell through on
  loop exit into `PUSH2 0x0c4a JUMP` (3069), which jumped over the repair add loop (3073..3145) to
  the exit / E3 phase block at 3146.
* **After:** the exit block (35 bytes) sits at 3069 directly behind the bottom test, the repair add
  loop follows at 3104..3176, and the old fall-through of `SUB_CHECK` (unreachable, `TN = 0` always)
  becomes `PUSH2 0x0bfd JUMP` at 3177. 3069..3180 keeps 112 bytes / 77 instructions.
* -11 gas per loop exit, 6 exits per draw: -66 per draw on every seed.
* Proofs: `CycleGlobal/ShiftStates` (repair and exit pcs), `ShiftPaths`/`ShiftBlocks` (located blocks
  re-indexed, new push immediates, `blk3253x` empty), `PrefixPC` (`eq_old_tail12` ends at 2388),
  `ShiftPCs` (`pcSwap2389..2465`), `ShiftTrace3`, `RootE3Bindings`/`RootE3PhaseRun` (E3 phase blocks
  at 3069/3071/3080); `Cycle/Artifact.lean`, `Cycle/Bytes.lean` regenerated.

# Current refinement: square-loop exit filler moved into the counter push (-6 gas per draw)

* **Before:** the RSA-2048 square-loop counter block at 7619 was `PUSH1 0x01 DUP16 SUB SWAP15
  PUSH2 0x163e JUMPI`, followed by the byte filler `PUSH18 0; POP; JUMPDEST x4` (7628..7651),
  executed once on loop exit (9 gas).
* **After:** `PUSH19 0x00..01 DUP16 SUB SWAP15 PUSH2 0x163e JUMPI` (the push carries the 18 filler
  bytes at the same 3 gas) and six `JUMPDEST`s at 7646..7651 (6 gas). The span keeps 33 bytes and
  12 instructions; every pc and instruction index outside it is unchanged.
* -3 gas per RSA-2048 vector, -6 per corpus draw on every seed.
* Proofs: `Cycle/Execution/counterHead` (`counterHeadProgram` with `.push 19 1`, model pc 7645;
  `counterExitProgram` = six `JUMPDEST`s from 7646 to 7652), `Cycle/CounterControl` (pcs 7645/7646),
  `Cycle/LoopBlocks` (`counterJumpBlock` at 7645, `counterExitBlock` at 7646); `Cycle/Artifact.lean`
  and `Cycle/Bytes.lean` regenerated from `bytecode.hex`.

# Current refinement: one JUMPI for the four RSA fast-path entry checks (-36 gas per draw)

* **Before:** `... PUSH1 0xff SHR ISZERO PUSH1 0xdb JUMPI` (zero top bit → 219) at 615..623, then
  the parity / width / all-ones test ORed into `PUSH1 0xdb JUMPI` at 646..648.
* **After:** the top-bit `ISZERO` stays on the stack and is ORed into the second condition
  (`PUSH2 0x0020 DUP8 DUP4 ...`, operands one deeper, an extra `OR`, a padding `JUMPDEST`), so a
  single `JUMPI` at 648 decides all four. Same target and same stack on every edge.
* -9 gas per RSA vector (4 per draw). Bytes 615..648 keep 34 bytes / 26 instructions; nothing else
  moves.
* Proofs: `CycleGlobal/FastP0.blk1003` covers 417..455 (old `blk1028` deleted),
  `CycleGlobal/FastDefs.fastPC1` updated, `CycleGlobal/Setup.run_check_pass/run_check_bail`
  (four-way disjunction for the bail) and `gasSteps_check_pass/bail` replace the separate top-limb
  and odd-check lemmas.

# Current refinement: one merged test for the 256-bit route (base size and Fermat guard, -93 gas per draw)

* **Before:** exponent/modulus size test (0..15), base size test `PUSH0 CALLDATALOAD PUSH1 0x20
  XOR PUSH1 0x65 JUMPI` (16..23), loads (24..32), join `JUMPDEST DUP2 NOT DUP2 ADD PUSH3 0x2e9
  JUMPI` (33..42), special-prime test (43..95).
* **Now:** after the unchanged size test, the three operand words are loaded at 16 and a single
  test at 25 computes `(baseSize = 32) * (modulus + ~exponent)` (`DUP2 NOT DUP2 ADD PUSH0
  CALLDATALOAD PUSH1 0x20 EQ MUL PUSH2 0x02e9 JUMPI`): a 32-byte base with
  `exponent != modulus - 1` (every generic 256-bit vector and the BN254 inversion) enters the
  window core at 745 after one conditional jump instead of two. 9 gas per such vector.
* The rare cases fall through: 39 re-tests the base size and goes to the general-width entry at
  101 (whose loads now rejoin at 47 instead of 33); 47 is the old join (`JUMPDEST DUP2 NOT DUP2
  ADD PUSH2 0x02e9 JUMPI`); a Fermat input (`exponent = modulus - 1`) then jumps from 56 to the
  special-prime test, which moved unchanged to the end of the image (10698..10751) and still
  ends in the Fermat result at 4847 or the window core. The words loaded at 16 for a base size
  other than 32 are garbage the merged test never trusts (the base-size factor is zero); they
  stay below the general-width frame.
* Bytes 0..100 keep their 47 instructions (the tail 60..100 is a dead filler); every PC from
  101 on is unchanged. The image grows by the 54-byte prime test to 10,752 bytes (168 chunks,
  renderer metric 16,021) and 8,548 instructions.
* Proofs: `CycleGlobal/FermatNext` (`mergeProgram`, `recheckProgram`, `joinProgram` at 47,
  `toPrimeProgram`, `primeProgram` at 10698 with its `JUMPDEST`, `mergeWord`), `FermatGas`
  (`fastSteps` to 25, `wideHandled`, `missSteps`, `handled` from the join at 47 through the
  relocated prime test), `EarlyWordCorrect` (both base-size branches and `genBig`),
  `ArtifactWindowPaths`, `ArtifactEarlyWordPaths`, `EarlyWordProgram`/`EarlyWordGas` (the old
  width block is gone); `Cycle/Artifact.lean` / `Cycle/Bytes.lean` regenerated and the
  instruction count bound `8535` → `8548` in the binding files.

---


# Current refinement: no overflow test in the radix-240 square loop (operand guard at the width test, -327 gas per draw)

* **Square loop tail (pc 7619).** The per-square test `DUP14 PUSH1 0xf0 SHR PUSH2 0x2936 JUMPI`
  (top digit of the raw Montgomery square at or above `2^240` → normalization at 10550) and the
  `JUMPDEST` it returned to are gone. The loop control is `PUSH1 1 DUP16 SUB SWAP15 PUSH2 0x163e
  JUMPI` (the `PUSH17` padding is no longer needed); the bytes up to 7651 are a filler
  (`PUSH18 0; POP; JUMPDEST x4`) executed once, on loop exit. 23 gas per square.
* **Why it is safe.** `KernelContract.exact_product` gives `T·R = A·A + Q·N` with `Q < R`,
  `R = 2^2160`. With `4N ≤ R` and `A + 2N ≤ R`, `T + 2N ≤ R` (`SquareStep.bound_step`), so
  `T < R`, the top digit stays below `2^240` (`overflow_zero`), `normalized T = T`, and the
  invariant `value a + 2N ≤ R` is carried through `SquareLoop` (`Outcome.small`). The entry
  value is `A·2^112`; `A < 2^2048 - 2^1938` gives `A·2^112 + 2N ≤ R` (`Core.run`).
* **Operand guard (pc 3739..3774).** The width test is now `... ADD ISZERO PUSH2 0x14d6 JUMPI`:
  width 4 jumps straight to the r5 prologue at 5334 (the 3751 `PUSH2 0x14d6 JUMP` patch is
  gone, 8 gas less per RSA-1024 call); width 8 falls through to
  `PUSH2 0x0940 MLOAD NOT PUSH1 0x92 SHR PUSH2 0x1582 JUMPI`, which enters the cycle at 5506
  unless the top 110 bits of the staged operand's leading word are all ones; in that case
  `PUSH1 0xdb JUMP` hands the call to the general route at 219, as the r5 prologue already does
  for its own guard. The remaining dead bytes are eight `JUMPDEST`s, so the span keeps its
  length and 25 instructions.
* Every byte PC and every instruction index outside 3739..3774 and 7619..7651 is unchanged.
* Proofs: `CycleCaller/Blocks` (test, branch, guard, guard jump and bail jump blocks),
  `CycleCaller/Prefix` (`guardWord`, `suffixTrace` for the passing guard, `bailTrace`/`bail` to
  219, `guard_bound : A < 2^2048 - 2^1938`), `CycleCaller/Terminal`, `OpaqueCore`, `Fixed`
  (`bail`), `CycleGlobal/Terminal`, `CycleGlobal/FixedRoute` (the width-8 branch either runs the
  cycle route or hands the call to `Fallback.correct`), `CycleGlobal/R5Head` (the test jumps to
  5334) and `R5Route` (entry at 5334), `R5/Blocks` (patch block removed),
  `Cycle/Execution/counterHead` (new counter and exit programs), `Cycle/LoopBlocks`,
  `Cycle/CounterControl`, `Cycle/SquareNormalize` (no branch: `gasSteps` needs the zero flag),
  `Cycle/SquareStep` (`bound_step`, `no_overflow`), `Cycle/Round`, `Cycle/SquareLoop`,
  `Cycle/EntryContract`, `Cycle/Core`; `Cycle/Artifact.lean` and `Cycle/Bytes.lean` regenerated.

---

# Current refinement: direct conditional return from the retained-accumulator compare

* The retained-accumulator entry of `CSUB` (pc 3493, called once per RSA route from `blk2874`
  with return address 2412) used to leave through `PUSH2 0x0ebd; JUMPI` into a two-byte
  trampoline `JUMPDEST; JUMP` at pc 3773. Its last two instructions are now `SWAP1; JUMPI`:
  the comparison flag and the return address already on the stack are swapped and the
  conditional jump returns to the caller directly. 9 gas per RSA vector (4 per corpus draw,
  -36 per draw), on every seed.
* Fall-through (accumulator not smaller than the modulus, never taken by the public corpus):
  the return address is no longer on the stack, so the following block pushes the constant
  `2412` before the retained destination `2112` (`PUSH2 0x096c; PUSH2 0x0840`). The two freed
  bytes of the old `PUSH2 0x0ebd` and the former `JUMPDEST` at pc 3508 absorb that push, so the
  span 3501..3508 keeps its length and its four instructions; every other byte PC and every
  instruction index of the image is unchanged.
* The `CSUB` subtraction entry therefore starts at pc 3509 (instruction 2722) instead of the
  removed `JUMPDEST` at 3508. Nothing jumps to 3508: its only entry was the fall-through.
* Proofs: `CycleGlobal/RetainedTEntry.lean` (new entry/push programs; the skip branch now ends
  in `returnedState` directly; `gasSteps_retained` takes `ret = 2412`, supplied by
  `ShiftTrace4` with `rfl`), `CycleGlobal/CsubFixed.lean` / `CsubCore.lean` (entry blocks without
  the `JUMPDEST`, entry pc 3509, PC literals of instructions 2719..2721), and the unused
  `jumpDestSub` / stale `run_jump` lemmas about pc 3508 are removed. `Proofs/Cycle/Artifact.lean`
  and `Proofs/Cycle/Bytes.lean` are regenerated from `bytecode.hex`.

---

# Current refinement: final dead store, remaining executed pads and PUSH0 limb loads in R5 product column 1

* Final packing block: the store of the top limb half below the result buffer is removed; the preceding push of the last result word is widened (`PUSHn` → `PUSH(n+k)` with the same value), so the block keeps its byte length and the `RETURN` block keeps its PC. `packFinalProgram`, its model and `PackExecution.cells` no longer write that cell; the returned bytes are unchanged.
* Executed padding `JUMPDEST`s are removed from the one-word base guard, the final unpack block, the first canonical compare block and the `RETURN` block. In each block one push is widened, so every block-start PC is unchanged.
* The unreachable bytes after the RSA setup block are re-split into one more instruction, so every instruction index from the following block up to the final unpack block is unchanged; the indices between the base guard and those bytes decrease by one, and the indices from the final unpack block on follow the removed instructions.
* R5 product column 1 (`prCol1`): both limb loads from offset zero use `PUSH0`, and a later push of the column is widened, so the column keeps its byte length and its start and end PCs; its internal part-boundary PCs follow.
* `PrefixPC` is re-split by index offset. The per-index PC lemmas, range PC tables, located instruction lists and block bindings follow the new indices; the located entry of the removed base-guard pad and the jump-destination lemma of the removed unpack pad are dropped. Every other theorem statement is unchanged except index, PC and instruction-count literals.
* `Proofs/Cycle/Artifact.lean` and `Proofs/Cycle/Bytes.lean` are regenerated from `bytecode.hex`.

Filing: third evaluation of this tree; bytes and proofs are identical to the earlier filings (`66b33fa2`, `7c46640e`, `4a5a811b`).

---

# Current refinement: direct square-loop entry

* Square-loop caller: the conditional jump of the width test targets the square-loop entry directly instead of the trampoline in front of it. Only the two immediate bytes of that push change; every byte PC and every instruction index is unchanged.
* `CycleCaller/Blocks.testProgram` and `R5Head.h1Program` carry the new jump target, and `CycleCaller/Prefix` takes the jump straight to the entry; the trampoline bytes and block stay in place, unused. Every other theorem statement is unchanged.
* `Proofs/Cycle/Artifact.lean` and `Proofs/Cycle/Bytes.lean` are regenerated from `bytecode.hex`.

---

# Current refinement: executed padding removal in the shift-reduce conversion and the RSA setup

* Shift-reduce base conversion: the padding `JUMPDEST`s in the dispatcher guard, the estimator precomputation, the end of the inline Newton chain, the Newton-batch tail and the shift-loop body are removed. In each block one push is widened (`PUSHn` → `PUSH(n+k)` with the same value), so every block keeps its byte length and every block-start PC is unchanged.
* RSA fast-path setup block: its padding `JUMPDEST`s are removed the same way.
* The unreachable bytes after the first R5 product segment are re-split into more instructions, so the total instruction count and every instruction index after them are unchanged; the indices in between decrease.
* `PrefixPC` relates program counters to the accepted proof base on one width segment per index offset. The per-index PC lemmas, the range PC tables, the located instruction lists and the block bindings of the shifted span follow the new indices; the located entries and per-index PC lemmas of the removed pads are dropped. Every other theorem statement is unchanged except index and PC literals.
* `Proofs/Cycle/Artifact.lean` and `Proofs/Cycle/Bytes.lean` are regenerated from `bytecode.hex`.

---

# Current refinement: PUSH0 limb loads in R5 product columns 2-4

* R5 product columns 2, 3 and 4 (`prCol2`, `prCol3`, `prCol4`): every limb load from offset zero uses `PUSH0`. Each freed byte widens a later push of the same column (`PUSHn` → `PUSH(n+1)` with the same value), so every column keeps its byte length, its start and end PCs and its instruction count.
* `Proofs/R5/ExecProduct.lean` updates the three columns' part programs, column programs and the internal part-boundary PCs; every model value, column statement and binding is unchanged.

---

# Current refinement: direct Fermat join guard

* Join point at 33: the guard is computed as `modulus + ~exponent` (`DUP2 NOT DUP2 ADD`), which is exactly `FermatNext.fermatDiff`, and the jump to the window core uses a widened push. The former padding `JUMPDEST` inside the guard is removed.
* The special-prime test and its jump tail follow two bytes earlier; the unreachable bytes before the general-width entry absorb the two bytes and the two instruction slots, so every byte PC and every instruction index from the general-width entry on is unchanged.
* `FermatNext.run_join` now reads the guard directly as `fermatDiff`; `run_prime`, `run_jumpTail`, `FermatGas` and the three bindings in `ArtifactWindowPaths` follow the new positions. Every other theorem statement is unchanged.

---

# Current refinement: R5 padding removal and a direct Fermat landing

* R5 square columns 0, 4 and 5 and R5 product column 0: every executed `JUMPDEST` pad inside the columns is removed. The freed bytes are absorbed by widening one push per column (`PUSHn` → `PUSH(n+k)` with the same value), so every column keeps its byte length and every byte PC outside the columns is unchanged.
* The unreachable bytes after the R5 product's first segment are re-split so that the total instruction count, and every instruction index after them, is unchanged. Only the R5 square block length and the indices of the loop-control and first product segment blocks are rebound in `Proofs/R5/Blocks.lean`.
* The special-prime branch of the Fermat dispatcher jumps directly to the `JUMPDEST` immediately before the result block, instead of entering the former no-op recheck. `FermatNext.tailProgram` is now that single `JUMPDEST`; `FermatNext`, `FermatGas` and `ArtifactWindowPaths` follow the new landing.

Every theorem statement outside those bindings is unchanged. `Proofs/Cycle/Artifact.lean` and `Proofs/Cycle/Bytes.lean` are regenerated from `bytecode.hex`.

---

# Current refinement: column-0 operand order in the R5 kernels

* R5 square column 0 (`sqCol0`): the modulus copy for the closing `MULMOD` is placed on the stack before the column's mod-`P` products, so the trailing `SWAP1` is dropped. The freed byte is `JUMPDEST` padding at the end of the column.
* R5 product column 0 (`prCol0`): same operand order, and both limb loads from offset zero use `PUSH0`. Two neighbouring pushes are widened to keep the column's byte length, with one `JUMPDEST` pad at the end of the column.

Byte length, instruction count, every byte PC outside the two columns, every `JUMPDEST` that is a jump target and every theorem statement are unchanged. `Proofs/R5/ExecSquare.lean` and `Proofs/R5/ExecProduct.lean` regenerate the column-0 part programs, part models and run lemmas. `Proofs/Cycle/Artifact.lean` and `Proofs/Cycle/Bytes.lean` are regenerated from `bytecode.hex`.

---

# Current refinement: setup-path stack cleanups (-24 gas per draw, on top of R5 fusion)

* `setupPathA` (PCs 649..689): drop a `DUP1` copy that was only popped at the end;
  re-index the following `DUP`s and replace one final `POP` by `JUMPDEST`.
* Newton chain `blkNbSub` (PCs 2543..2593): the last step consumes `p` with `SWAP2`
  instead of `DUP3`, so the trailing `SWAP1 POP` becomes two `JUMPDEST`s.
Both keep byte PCs and instruction indices; the run lemmas keep their statements.
Seed-zero pinned total with the R5 fusion below: 366,542 (44/44).

---

# Current refinement: fused doubled cross products in the R5 square (-204 gas per draw)

Parent: own submission `d052f5da-65fe-4de8-8cf9-6fecac1693a6` (Fermat join).
In R5 square columns 4 and 5, two cross products per column were each doubled
separately (`MUL DUP1 ADD ADD` twice). They are now summed first and doubled once,
on the low (`MUL`) side and the mod-P (`MULMOD`) side; on the mod-P side `P` is
duplicated once (`DUP16 DUP1`) and kept under the operands with `SWAP1`. Freed
bytes are `JUMPDEST` padding, so every byte PC and instruction index is unchanged.
12 gas per R5 square, 17 R5 squares per corpus draw.

`Proofs/R5/ExecSquare.lean` regenerates columns 4 and 5 (part programs, models,
run lemmas, column program/model/run); the column outputs `sqCol4_o*`/`sqCol5_o*`
are unchanged and `sqCol4_eq`/`sqCol5_eq` close with the premise-free lemma
`fusePair : ((b + a) + (b + a)) + c = (b + b) + ((a + a) + c)`.
Seed-zero pinned total: 366,566 (44/44) versus 366,770 for the parent.

---

# Current refinement: single-test Fermat join (-181 gas per draw)

Base: promoted `be76a99a-6bdc-433f-9c2e-cc34523f4381` (juanbono, R5 1024-bit kernel).
Two dispatch blocks change; byte length (10,698), instruction count (8,543), every
byte PC and every pre-existing `JUMPDEST` are unchanged.

* Join guard at PC 33 (bytes 34..40): `DUP2 NOT DUP2 ADD PUSH1 1 LT` becomes
  `PUSH1 1 DUP3 ADD DUP2 XOR JUMPDEST`, i.e. `modulus XOR (exponent + 1)`. It is
  zero exactly when `exponent = modulus - 1`; the old `1 < modulus + ~exponent`
  also let `exponent = modulus - 2` (the BN254 inversion vector) detour through
  the special-prime test and a recheck at 4839 before the window route.
  `FermatNext.joinGuard_zero_iff` proves the guard equivalence without premises.
* PC 4839 (bytes 4840..4847): the recheck `DUP2 NOT DUP2 ADD PUSH2 0x02e9 JUMPI`
  is now `PUSH2 0x0000 POP JUMPDEST JUMPDEST JUMPDEST JUMPDEST`, an exact no-op;
  `FermatGas.handled` passes the join hypothesis to the unchanged Fermat result.

Seed-zero pinned-EVM total: 366,770 gas (44/44) versus 366,951 for the base;
the saving is the same 181 gas on every corpus seed (the changed bytes are not on
any RSA path). Local measurements are not an official score.

---

# Current refinement #115: estimator increment

This version replaces byte PCs2504..2506 `NOT; PUSH0; SUB` with
`PUSH1 1; ADD`. The modular UInt256 identity is universal, including wraparound:
`1 + x = 0 - NOT(x)`. Both byte strings are three bytes; the new image has
11,156 bytes and 9,187 decoded instructions. Existing JUMPDEST PCs and all
following instruction byte PCs are unchanged. Instruction indices starting at
old index1955 move down one and their artifact proof bindings are updated.

Matched seed-zero executable measurements: 374,391 gas, 44/44 correct, versus
374,399 for local #114 (now submitted as
`8209e460-f3f8-4abb-baba-5e14f082044b`) and 374,457 for accepted #105 on that same
corpus. This is not a direct comparison to hosted official scores. The current
hosted frontier remains 373,913 until a new official result is returned.

`Proofs/CycleGlobal/ShiftTrace1.lean` proves the word identity and the exact
`run_negDoneB` state transition with the inherited theorem contract. The focused
artifact-bound build passed; the full protected local gate and hosted status
are documented separately in the submission note and receipt. No proof trust
exception, runtime special case, scorer change, or vector-specific route is used.

Decoded byte SHA-256:
`bea8ea1aa6ea98eb602d509b1097075d3212fb89503699c4012f61b123f87573`.

Run the repository's documented local gate with:
`BENCHMARK_INSECURE_LOCAL=1 ./benchmark.sh modexp`.
It explicitly uses Comparator's insecure local sandbox here, so only an actual
Yukon evaluation can establish an official result. Prior documentation follows
as historical provenance and does not describe the current byte count/hash.

---

# MODEXP: cycle normalizer dead-code elimination

Development base: accepted aerugo-ef v15, commit
`bb2353349ec3854333007e928ef0e4be8843c243`.

The exact executable is 11,156 bytes (8 bytes smaller). In the radix-240
normalizer, eliminate the initial addition of zero and the final borrow
comparison, whose bit is discarded after the top-digit subtraction. Adjust
the terminal stack exchange to skip the removed dead slot. No carry or borrow
assumption is introduced: the modified execution theorem accepts the same
arbitrary word arguments as the original.

The 44 public seed-zero vectors all return the correct result at **374,465
gas**, versus **374,487** for the direct parent (22 gas saved). These are local
pinned-EVM measurements, not an official score. The RSA-2048 e=3 vector improves
from 22,657 to 22,635 gas; the other 43 are unchanged. The optimization saves 22
gas per normalizer invocation, not per MODEXP call. A separate full-program
near-maximum-modulus witness with N=2^2048-3, base=N-1 and exponent=3 returns the
correct value for both images, at 23,489 versus 23,467 gas.

## Proof binding

`Proofs/Cycle/NormalizeExecution.lean` proves the modified exact instruction
sequence with no additional hypotheses. `NormalizeMeaning.lean` and
`NormalizeBinding.lean` connect it to the unchanged word-subtraction meaning.
`Proofs/Cycle/Artifact.lean` assembles the 9,189 instructions to the exact
literal in `Proofs/Cycle/Bytes.lean`. Existing cycle/caller/global correctness
then feeds `Solution.lean` and the protected benchmark artifact. The allowed
axiom set remains `propext`, `Classical.choice`, `Quot.sound`.

Run `BENCHMARK_INSECURE_LOCAL=1 ./benchmark.sh modexp` for the documented local
Comparator and gas gate. Local execution uses the documented fake sandbox and
is not a ranked verification. The full gate result is recorded in the attached
research report; this README is not itself an acceptance receipt.

Decoded byte SHA-256:
`4a43d5e6471264bf96ca8df6229ba175c9539ef16920697b32171bd63a789d5e`.

## Attribution

This refinement builds directly on aerugo-ef v15 (GPT-6 Astra / Codex), the
retained v14 lineage, fkiene's compatible public refinements, and Th0rgal's
Gemini 3.1 Pro / Antigravity schedules. Claude's original contribution and all
inherited provenance and Apache 2.0 notices are preserved below and in the
provenance files. This iteration adds only the normalizer dead-code elimination
and exact proof/artifact integration. See `dependencies.json`.

---

## Inherited v15 documentation

# MODEXP: retain radix-240 values across repeated operations

This v15 candidate uses 374,487 gas on the 44 public seed-zero vectors,
versus 392,554 for fkiene's `de134b66-a42c-4b03-a575-3f9318a88ad8` on the same
inputs: 18,067 gas saved (4.60%). The executable is 11,164 bytes.

The eight-word route retains nine radix-240 digits across repeated Montgomery
squares and the terminal product. Joint operand lifetimes, instruction
scheduling, memory reuse and finalization reduce repeated conversion and
storage work. The four-word setup also specializes its known buffer pointer.

## Verification

`Solution.lean` connects the exact protected literal rendered from
`bytecode.hex` to `CycleSubmission.Global.correct`. The theorem covers every
valid padded MODEXP input, including the general fallback, given sufficient
gas. The proof uses only `propext`, `Classical.choice` and `Quot.sound`.

The main proof layers are:

- `Proofs/Cycle/Core.lean`: repeated arithmetic, normalization and output.
- `Proofs/CycleCaller/Spec.lean`: eight-word caller and operand encodings.
- `Proofs/CycleGlobal/Correct.lean`: dispatch, conversion, both widths and fallback.

From the challenge root, run `./setup.sh modexp`, then `./benchmark.sh modexp`.
The documented local mode is `BENCHMARK_INSECURE_LOCAL=1 ./benchmark.sh modexp`.

Decoded executable SHA-256:
`b158452c8397c428e5a13c0757c453b0462345ce11005604d9e3dee899f7b4e8`.

## Attribution and license

Claude found the original optimization in aerugo-ef's repository. This work
builds on aerugo-ef v14 and fkiene's compatible public refinements. Th0rgal's
Gemini 3.1 Pro / Antigravity schedules and other inherited implementations are
credited in the retained provenance. The new cycle, scheduling and proof
integration were developed with GPT-6 Astra / Codex.

`dependencies.json` declares direct dependencies. `INHERITED_PROVENANCE.json`
and `Provenance/` preserve the v14 declarations, attribution and historical
documents; their measurements and implementation descriptions refer to those
earlier versions. Original local work uses Apache 2.0; see `LICENSE` and the
upstream notices retained in the source.

## Fixed-caller decrement scheduling (iteration 105)

The cycle fixed caller at PC 2369 previously computed `k-1` by
`PUSH0; NOT; DUP3; ADD`. It now uses `PUSH1 1; DUP3; SUB`.
Both sequences are four bytes; the new one saves 2 gas and one instruction.
The existing `1 <= k <= 16` caller conditions are unchanged. Both four-word
and eight-word caller lemmas use the same subtraction fact, with no new
arithmetic premise. No byte address or jump literal moves.

The full artifact remains 11,156 bytes and has 9,188 instructions.
Instruction indexes after the caller decrease by one. The concrete block
slices, located-instruction records, CLZ decoder, suffix base, and prefix-width
bridge are rebound to the exact new artifact; retained legacy bytecode modules
remain unchanged.

Matched local seed-zero EVM runs (44/44 correct in each batch): promoted v15
bytes 374,487 gas; normalizer-only parent 374,465; this revision 374,457.
Each of the four RSA-1024/2048 e=3/65537 vectors saves 2 gas versus the parent;
40 other vectors are unchanged. The promoted official score is 374,737 on a
different evaluation configuration; 280 is not a matched measured saving.
Local gas and local fake-sandbox Comparator acceptance are not official
leaderboard promotion.


### Current frontier checkpoint during iteration 105

The normalizer-only parent `84b3089d-b76a-43ea-907e-0d4357e4f387` was accepted
and promoted at official score **374,193**, source
`8f8a0b2c59e8f761088c97b21a6f4099a67305e1`. Its complete editable Submission
tree is identical to local `429f6dae`. Against that exact current frontier,
the caller revision saves **8 gas** on the matched public seed-zero corpus
(374,465 → 374,457); 30 gas is the combined local saving versus preceding v15.
Do not subtract the local 374,457 from official 374,193: these are different
corpus configurations. The new caller revision still needs its own official
validation. This checkpoint changes only documentation/attribution metadata;
all Lean sources and executable bytes remain frozen for the running gate.


## Shared-complement dispatch predicate (iteration 109)

The modulus-tail dispatch at byte PCs 631..640 now uses
`NOT; DUP1; ISZERO; SWAP1; JUMPDEST; PUSH1 1; AND; OR; JUMPDEST`.
The old sequence was
`DUP1; PUSH0; NOT; EQ; SWAP1; PUSH1 1; AND; ISZERO; OR`.
The new sequence shares the complemented input word between the all-ones
and low-parity tests. For every UInt256 input x, `~x == 0` iff x is the
all-ones word and `(~x & 1)` equals `ISZERO(x & 1)`.
The two sequential JUMPDEST instructions keep all 9,188 instruction indexes,
widths and byte PCs identical to the caller-decrement parent. The PUSH1 at
instruction 449 remains at byte PC 636. No existing destination literal moves.
`PredicateIdentity.lean` proves these scalar identities without premises;
`FastP1.lean` and `Setup.lean` bind the exact dispatcher and preserve all
existing pass and bailout hypotheses, including the inverse precondition.

On the pinned public seed-zero corpus, all 44 vectors are correct at
**374,445 gas**, versus 374,457 for the caller-decrement parent and 374,465
for the promoted normalizer image. Four generated RSA vectors each save
three gas; the other 40 are unchanged. These are matched local totals, not
an official hosted score. The normalizer's official 374,193 is from a
different corpus configuration and must not be mixed with local figures.

Decoded bytecode SHA-256:
`2cbd6189e98e0064602f00dcfe6db4544aa00282a0fbcf67a3bc2683c743d2f5`.
The isolated small gate built dispatcher Setup successfully (1,361 jobs).
Whole-program Comparator and scoring must independently accept this image;
this README alone is not an acceptance receipt. No carry shortcut, test-only
restriction, new axiom, or weakened premise is part of this change.
The caller-decrement parent was submitted separately as
`d1c8717a-46f1-468d-bd74-0eca2543d705`; its hosted validation was still pending
when this proof gate began. All earlier provenance and license notices remain.


## Sentinel-backed quotient-estimate mask (#112)

This revision additionally replaces bytes 2778..2781, `155f0317` with
`8201175b`: `ISZERO; PUSH0; SUB; OR` becomes
`DUP3; ADD; OR; JUMPDEST`. The all-ones sentinel was already on the entry
stack and is preserved. For a comparison bit b, `maxWord + b = 0 - isZero b`
in UInt256 arithmetic. The quotient word ORed with this mask is unrestricted.
The four one-byte instructions preserve every instruction index, width and
byte PC. The final JUMPDEST is padding (1 gas); the old window costs 11 gas
and the new window 10, saving one gas per estimate.

The parent is #109 (shared-complement dispatch predicate), commit
`b6484e8db9af2040ca06d991ac590ba7e6f0f6bd`, which includes caller-decrement #105.
The pinned public seed-zero batch measures **374,424 gas** for #112 versus
**374,445** for #109: 21 gas saved, 44/44 correct. These are local measurements,
not a hosted official score. Versus #105's 374,457, the cumulative saving is 33.

`CycleGlobal/ShiftPaths.lean` binds the changed instructions to the artifact;
`ShiftTrace2.run_estimate` proves the same result with the same premises.
No arithmetic or input restriction is added. The separate report theorem
`SentinelMask112.same_state` proves equality of the gas-erased instruction
runner's full Option State result with the explicit sentinel entry frame;
it does not assert equal remaining runtime gas. Exact decoded artifact:
11,156 bytes, 9,188 instructions, SHA-256
`3c753cd7874508334df1ebe2b555deea4ad0eb5e9359e42abf3c206f2a36d655`.
At this checkpoint the artifact-bound ShiftTrace2 proof passes; submission-level
Comparator and scoring remain mandatory and are recorded separately.


## Consumed dispatcher inequality condition (#113)

Replace PCs 2393..2394, `EQ; ISZERO` with `XOR; JUMPDEST`, retaining the
following `PUSH1 219; JUMPI`. XOR is zero iff its operands are equal. Since
the branch consumes the entire condition, preserving zero/nonzero truth is
sufficient; numeric equality of intermediate conditions is neither claimed
nor needed. `ShiftTrace1.dispatch_xor_isTrue` proves this for arbitrary words
and `run_dispatch` keeps the inherited premises. Artifact-bound ShiftTrace1
build: 1,385 jobs clean. Pinned combined public result: 374,416 gas, 44/44,
8 gas lower than #112 and 41 lower than #105 on the same seed-zero batch.
The artifact is 11,156 bytes / 9,188 instructions, decoded SHA-256
`103eb09ad3db35e38ab34bd7c95621e35a5ed4127b25868031a459e133104d30`.
A separate protected submission-level gate is required for this exact image.


## First-row carried-zero elimination (#114)

At PCs 4221..4226 replace `958510019450` with `505093831093`, i.e.
`SWAP6; DUP6; LT; ADD; SWAP5; POP` with
`POP; POP; SWAP4; DUP4; LT; SWAP4`. This removes addition of the carried
zero produced by the actual `PUSH0` at PC4131. The unsigned overflow
comparison `LT (p4+c) p4` remains intact for arbitrary wrapped sums.
`R4InlineRedt0.run_redt_0Zero114` proves the new schedule, and
`R4InlineBlocks.block_redt_0Zero114` binds it to the changed artifact.
`R4InlineTrace.gasSteps_red0Zero114` composes the entire zero-preserving
reduction, leaving the outer `gasSteps_core` statement unchanged.
Artifact-bound trace build: 1,470 jobs completed. Pinned EVM result:
374,399 gas / 44 correct, versus #113 374,416 on the same public batch.
There is no arbitrary-carried-word equivalence claim. All PCs and widths
are preserved; artifact remains 11,156 bytes / 9,188 instructions,
decoded SHA-256 `9edcd83a2c11e5969ac326c1d37338ca830481b0be998c65bea8bb0cec4ff5f4`.
