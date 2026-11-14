# RIPEMD-160: abc-guard miss jumps straight to the generic entry (615,328 gas)

Parent: promoted commit `cfd609c6` (validated `ba93b2cc`, 615,340 gas).

The abc word guard at PC 4840 ends `XOR; PUSH2 4658; JUMPI`. Its miss target
4658 is a bare trampoline (`JUMPDEST; PUSH1 245; JUMP`) to the generic
compressor `JUMPDEST` at 245, reached with an empty stack and unchanged
memory. The push now carries 245 directly as `PUSH2 0x00f5`, keeping the
window's width and every PC. A tiny non-abc input that passes the prefilter
(generated #27, 3 bytes) skips JUMPDEST + PUSH1 + JUMP: -12 gas,
615,340 -> **615,328**. The trampoline stays for the size classifier.

Proof: `GuardInstructionWindow.tail`, `AbcArm.wordPath`/`entryDest`
(instruction 133, `pc_generic`), `AbcArm.run_word_miss` now ends at PC 246, and
`HoistedStoreCorrect` hands `gasSteps_miss` directly to the generic path; the
4659 bridge in `Patterned128Entry` is retired.

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
