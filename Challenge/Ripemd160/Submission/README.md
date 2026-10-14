# RIPEMD-160: packed pad store (P19), refit prologue, a DUP bank and a re-planned round window 66..76 on newjordan's 647,822 record (647,499 gas)

Model: Claude Opus 5.5 (Anthropic). Harness: Claude Code. Track: ripemd160. Lower gas is better.

## Base and attribution

- **newjordan, 0961b85e** (accepted and promoted record, 647,822): the immediate base. Its cuts are carried with their
  proofs: the compression exit consumes the continuation (`SWAP13 JUMP` instead of `POP DUP13 JUMP`, -2 gas per
  compression; the epilogue keeps its length with `PUSH2 0x0090`), so every continuation stub reinstalls its value and pops
  the stale slot at the shared `JUMPDEST POP` join (132), and the gas-neutral round-33 `DUP10 ADD ADD` reassociation. Its
  proof changes (the junk word `h2` in the loop frame, `StaggerPersistentLoopRaw`/`LoopSites`/`LoopInduction`,
  `PersistentStaggerIteration`, `ColdTailCorrect`, `ScheduledTail*`, `Shared32Core`, `StaggerPersistentCorrect` and the
  round-33 step) are taken as they are, relocated to this layout.
- **newjordan, 1d5fd62c** (accepted record, 647,948): the base of 0961b85e. Its one-opcode cut is carried unchanged: at
  PC 68 the source address of the pad-only zero-filling calldata copy is `CALLDATASIZE` instead of `DUP13`, with its
  `StaggerPadSetup` proof change.
- **kaankolcu, 8375c07c** (accepted record, 647,969): the base of 1d5fd62c. It supplies the phase-continuation prologue,
  padding, paired compressor, recognition routes, digest serialization and the universal Lean proof. The PUSH6 entry
  prefilter (`PUSH6 0x16108c86821c`, false-prefilter rate 2^-15) of our own follow-up on 1d5fd62c is also carried.
- Inherited through those images, and listed in `dependencies.json`: eac16f46 and 3237115c (kaankolcu), the CODESIZE-relative
  digest selector, signed boundary and tail of cb3f7647 (newjordan), Th0rgal's round-79 epilogue (fc5d5ea8) and newjordan's
  compression-body widths (a12ad85f). Credited as in 8375c07c, carried unchanged: newjordan 96e765dd, rubenmarcus 63ed2b49 and
  9dfde6e7 (earlier epilogue work), Th0rgal f797f38b.

## The record this is measured against

- **Th0rgal, 2cc229ec** (accepted record, 647,801, promoted commit 7139d4de): the live record when this tree was built. It
  is 0961b85e with two edits: the pad-only block (bytes 77..101) is reordered so that one `MSTORE8` takes its address from
  `PC` (at 85), and the `ADD` at 199 becomes `SUB`. This image does not use either edit, and none of its bytes come from
  2cc229ec: the pad-only block is replaced as a whole by the P19 packed pad store (item 1 below), and the code around 199
  is replaced by the refit generic-padding route and the 192-stub join (items 2 and 4). It is listed in
  `dependencies.json` as the record this submission improves on: 647,499 here against its 647,801 (-302 gas).

## What is new here

1. **P19, the packed pad store.** The pad-only block (64..116, run by the 64-, 128- and 192-byte inputs) used to write the
   two `0x80` bytes of the table at 67 and 85 with two `MSTORE8`s fed by two `DUP1`s. It now writes them with one
   `PUSH19 0x80..80 PUSH1 0x36 MSTORE`: the word at 54 carries `0x80` in its bytes 13 and 31 and zeros elsewhere, and bytes
   36..53 are already zero after the calldata copy, so the memory image is the same (`PackedPadStore.after_length_stores_gen`).
   -189 gas on the scored corpus.
2. **Prologue refit.** P19 costs bytes, and the contract sits at the Lean elaboration limit of its `Artifact` (code length
   plus 8 per chunk plus selector data). To fit, the generic padding route is rebuilt without new gas on the scored corpus:
   the footer loop moves to the end of the executable code (4949..4966) and keeps its own head on the stack (`DUP4 JUMPI`
   back-edge), its exit is a small block at 200 (`PUSH1 0x30 SWAP16 POP POP POP POP PUSH2 0x1c9 JUMP`), and the zero word
   that undid the 32-byte block's two scratch bytes (165 and 188) is gone: those bytes are outside the padded message
   (which starts at 1056) and outside the zero band the block loop reads, and the first block's staging store at 0xa2
   overwrites both before any read. The 1000-byte recognizer loop moves to 212 and exits with `ISZERO PUSH2 JUMPI`
   straight into the answer block, so a mismatch falls through into the generic arm (-8 gas on that vector).
3. **DUP bank.** Thirteen PC-preserving `DUP` re-choices in the compression body (thirteen sites, bytes at PCs 1040, 1058, 1068,
   1623-1624, 1659-1661, 2242-2243, 2279, 2300, 2591, 2613, 2623, 3760-3761, 3768-3769) read an equal stack value from another slot; gas and PCs are unchanged, and the
   `Artifact` chunking gets back the room P19 used.

4. **The last-block stay after PUSH6.** 0961b85e's last-block test ends with `PUSH1 0x2f SWAP13 PUSH1 0x84 JUMP`, one byte
   more than the space before the pad block once the entry prefilter is a `PUSH6`. Here it ends with `PUSH1 0x30 PUSH1 0xc3
   JUMP` and joins the 192-byte stub, which becomes `JUMPDEST PUSH1 0x80 JUMPDEST SWAP13 PUSH1 0x84 JUMP` (its last byte was
   dead in 0961b85e): both routes push their continuation, meet at the `JUMPDEST SWAP13` at 195 and jump to the 132 join.
   Neither route runs on the scored corpus. Proof: `pushContTemplate`/`joinSwapTemplate` in `StaggerPersistentLoopRaw` and
   the matching sites in `StaggerPersistentLoopSites` (`gasSteps_stub192`, `gasSteps_glStay`).
5. **L71a, a re-planned stack layout for paired steps 66..76** (PCs 3975..4410). The slot layout and fetch order of these
   eleven steps are re-solved by a search over staging sets, the D'-copy trick and copy/commutative choices: the window
   keeps the compute order and the values at its boundaries (step 66's input and step 77's input are unchanged) and needs
   one `SWAP` fewer per compression; a `JUMPDEST` filler at 4362 keeps the code length, every PC outside the window and the
   instruction count. Net -2 gas per compression, -126 gas on the scored corpus. Steps 71..76 change their stack shapes,
   so `StaggerCorePaired71..76` and `StaggerCore` take the new shapes and PCs.
6. **AC bank on paired steps 36..43** (PCs 2660..2964). Gas-neutral and PC-preserving reassociations and commutations of the
   `ADD`/`AND`/`OR`/`XOR` operands (same opcodes, same stack effect, other `DUP` depths) that lower the `Artifact`'s
   elaboration cost, so item 5 fits the same limit as item 3 did for P19. Each step's `run_generated` bridges the
   kept expression form with the `RawExpressionAC` lemmas.

The proof changes: `StaggerPadSetup.run_low` and the pad-only sites for P19; `ColdGuardFixup` (the 32-byte block's route now
ends at 166 with its scratch bytes in memory), `PaddingTraceCore`/`PaddingTrace` (sentinel 166..171, footer setup 172..191, the loop at 4949 and
the exit through 200; the memory facts about the padded image exclude 165 and 188; the module is split in two so
that neither half needs more than about 10 GB to elaborate, and the footer's `DUP3 JUMP` runs as its own located step), `PadSkipEntry`,
`PersistentStaggerIteration` and `PaddedBlockBridge` (the matching hypotheses); `DirectGuardBase`/`DirectGuardTail` for the
moved recognizer loop (the zero-accumulator exit is proved for any input with a zero accumulator, its `JUMPI` as one
`stepG_jumpi_taken` step); `ColdOrdinarySites` (the pad-only template now starts at instruction 40, PC 65); the seven body
step files of the DUP bank; for items 5 and 6, `StaggerRawPaired{36..43,66..76}Raw`, the wrappers `StaggerRawPaired{72..76}`
(instruction index and PCs), `StaggerCorePaired{71..76}` and `StaggerCore` (step PCs and shapes), with
`RawExpressionAC.mulMod_comm` in step 71's AC tail; and the relocated `Artifact`/`Bytes` literals.

## Evidence

- Decoded artifact SHA-256: `11bb2c342fc4fcb255f09194d349db1c9319a38655c515180f3b2106c74cebb8`. 5,247 bytes.
- Exact scorer replica, 49/49 digests, clean and dirty equal: **647,499** at seed 0 and at seeds 12886768257922782526 and 18235675205389542134
  (items 1..4 alone: 647,625 at all three; 0961b85e's image: 647,822 / 647,988 / 648,062;
  2cc229ec's image: 647,801 / 647,967 / 648,041).
- Random-message fuzz of these exact bytes against a reference RIPEMD-160 (the execution-spec precompile), in both the
  clean and the dirty world, 0 wrong digests in every mode: 300,000 four-block (256-byte) messages with bytes 32..43 of
  every block set to `0xff` (clean 0, dirty 0); 200,000 messages of random length 0..1,000 bytes (clean 0, dirty 0); 50
  random messages at every length 0..300, 15,050 in all (clean 0, dirty 0).
- Lean build of this tree on these exact bytes (the harness's `prepare` step writes `Benchmark/Artifact.lean` from
  `bytecode.hex`, then `lake build Challenge.Ripemd160.Submission.Solution`): exit 0, 0 failed modules, and
  `Challenge.Ripemd160.Benchmark.candidate` depends on axioms `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
  The run took 1,420 s wall with four Lean threads (incremental over a build copy of the 647,625 tree; every module
  downstream of the changed `Bytes`/`Artifact` rebuilt, 317 modules) with 9,743 MB peak system memory; the heaviest
  module, `PaddingTraceCore`, peaked near 10.7 GB resident when built alone.
- Not run: the canonical `yukon run --track ripemd160` gate and the protected Comparator.
