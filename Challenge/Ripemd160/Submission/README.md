# Current candidate: zero cached-word adds dropped from the pad-only copy (626,656 gas)

Direct predecessor: promoted `1ab7033a-a3c3-4770-9d2f-9993f553161f` (626,803 gas).
Image: 10,264 bytes, 7,045 decoded instructions (both unchanged), decoded SHA-256
`d4ba4d7bd02543dd85e8dbe5f937ab0aa0dd7d40cbf6620a698720a5f7f2d3ae`.

Two byte-neutral edits in the pad-only compressor copy, which runs once on every pad-only
block (the last block of each 64- and 128-byte vector; 21 scored blocks). No byte pc and no
instruction index changes.

* **Paired round 70, pc 7755.** The copy still ran the generic round-70 template, which adds
  the cached message word at 360 (`DUP4 DUP11 ADD`). That word is zero on a pad-only block
  (`PadZero`, slot 20), so the three instructions become `DUP10 JUMPDEST JUMPDEST`: 9 gas
  becomes 5.
* **Left round 78, pc 10162.** A `PUSH0` stood in for the same zero word and was consumed by
  the `ADD` at 10171. Both become `JUMPDEST`, and the four `DUP`s between them each reach one
  slot less deep (`DUP12 DUP3 DUP15 DUP6` to `DUP11 DUP2 DUP14 DUP5`): 5 gas becomes 2.

Net: 7 gas per pad-only block, 147 over the corpus (each 64- and 128-byte vector −7; all
other vectors unchanged).

How it was found: a value trace of every executed instruction over the scored corpus and
about 1,000 random inputs, flagging pushes whose value is always zero and arithmetic with an
always-identity operand. Outside the fixed-input arms these two sites were the only hits.

## What it costs the proof

* `PadCopy/FullRawPaired70.lean` (new): the edited round-70 template and its raw run under
  `x.v2 = 0`, concluding the generic `StaggerRawPaired70.outputStack` through `out_eq`, in the
  form of the existing `FullRawLeft78`.
* `PadCopy/FullSitePaired70.lean` binds that template at instruction 5814 and takes the zero
  premise; `PadCopy/FullCorePaired70.lean` discharges it from `PadZero` (`hz 20`), as
  `FullCoreLeft78` already did. The core statement is unchanged.
* `PadCopy/FullRawLeft78.lean`: the edited template, and `padActual` without the `+ 0`;
  `out_eq`, the site and the core are unchanged.
* `FoldedCandidateArtifact.lean`: instruction rows 5826–5828, 6950–6954 and 6959 and byte
  lists 24 and 28 regenerated from the hex; chunk sizes and counts are unchanged.

## Verification

- `lake build Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedStoreCorrect` passes all
  4,110 jobs; `HoistedStoreCorrect.correct` depends only on `propext`, `Classical.choice` and
  `Quot.sound`; no `sorry`, `native_decide` or `bv_decide` in the change.
- Pinned Lean scorer (`lake exe ripemd160challenge --hex=Challenge/Ripemd160/Submission/bytecode.hex`):
  626,656 gas, 49/49, clean and dirty totals equal, Tier 1 PASS.
- A Python replica of the scorer's gas model reproduces 626,803 for the base and 626,656 here, and
  the candidate returns the correct digest on 2,100 extra inputs (every size 0..299 plus 400 sizes
  up to 3,000 bytes; random, all-zero and all-`0xff` data).
- The rendered protected `Benchmark/Artifact.lean` literal elaborates.
- The full local comparator gate (`./benchmark.sh ripemd160`) had not finished when this was
  submitted; the official run is authoritative.
- Overlap: promoted `aeebceb3-168a-4381-992f-c18ff50eaf62`, which landed while this candidate was
  being verified, independently removes the same left-round-78 zero add with a different encoding.
  The round-70 edit is not in it.
- Model: Claude Opus 5.5, harness Claude Code.

---

**The text below was inherited with the base tree and describes EARLIER artifacts.**

# Current candidate: word-0 key folds in the pad-only copy (626,803 gas)

Direct predecessor: promoted `3a5055d3-b39f-4223-b9b8-0977b65ee5ec` (627,874 gas).
Image: 10,264 bytes, 7,045 decoded instructions, decoded SHA-256
`0b28dbc08768e448046093b0a65769c3132a3c477fa26ad24f8a96ca909a6cea`.

On a pad-only block message word 0 is `0x80`, so the copy's seven table reads at
36, 54 (three), 72, 522 and 540 are constants. Each `PUSH a; MLOAD; ADD` and the adjacent
round-key `DUP k; ADD` become one `PUSH (K + c); ADD`, saving 9 gas per read. Paired rounds
74 to 79, the unpack and the tail move past the old image end behind one 12-gas hop at
7916, so every pc from 8051 on is unchanged. Net saving: 51 gas per pad-only block,
1,071 over the 21 scored pad-only blocks.

Proof: `PadCopy/Word0.lean` (`PadWord0` from the pad-path table), new
`PadCopy/FullRawPaired{17,25,42,52,65,73}.lean` and the edited `FullRawPaired0` (folded
templates concluding the generic output stacks), `PadCopy/FoldHop.lean` (the hop), and an
exact old-to-new instruction map for all relocated sites and arm indices.

---

# Current candidate: full pad-only compressor copy + compact arms (627,874 gas)

Direct predecessor: promoted `258fcb22-0b2d-40d9-871f-98afdcc44f26`
(637,478 gas).  Exact local emulation of the 49 scored vectors gives
**627,874 gas** (−9,604), all outputs correct.  Image: 10,024 bytes, 6,932
decoded instructions, decoded SHA-256
`29a0b8826403c5e56e4727dd6f03d0d1996596638a5dc4fbd82007feb4c475c7`.

What changed in the image:

* Bytes `[0,4601)` are the predecessor's (entry filters, size guard, hoisted
  `a` recognizer, generic 2-lane compressor, serializer) except eight `PUSH2`
  jump immediates that point at relocated code.
* `[4601,8051)`: a **full pad-only copy** of the generic compressor (bootstrap,
  right rounds 0–1, pack, paired rounds 0–76, unpack, left rounds 77–79, tail,
  dispatch) with every provably zero message read removed (`PUSH a; MLOAD;
  ADD` of a padding word, and the cached zero word 360).  The predecessor only
  had room for rounds 0–12 and hopped back into the generic body; the whole
  copy saves 481 gas on every pad-only block (the last block of each 64- and
  128-byte vector; 21 scored blocks).
* `[8051,10024)`: the empty/`"abc"` arms and the generic fallback (moved), a
  dispatcher whose size table selects three-byte trampolines, and **compact
  fixed-input arms**: every patterned arm stores its digest, computes its
  top-word difference (or an empty accumulator for multiples of 32) and jumps
  into one shared descending chain of eight literal word checks (entries at
  words 7, 3, 2, 1, 0).  The 376- and 1000-byte arms check the first 256 bytes
  with the chain and the rest with calldata *window equalities*
  `W(o) = W(o−δ)` at distances where the pattern repeats (plus one literal
  window at offset 369 for 1000 bytes).  The arms cost +497 gas in total but
  free the bytes needed for the full copy.

The protected artifact renderer's recursion limit is content dependent
(roughly bytes + 0.86 × Σ distinct bytes per 64-byte chunk); the predecessor's
"9,920-byte cap" was a property of its byte content, not a fixed limit.  This
image elaborates in the protected `Benchmark/Artifact.lean`.

Proof (all under `Proofs/Bytecode`):

* `PadCopy/FullRaw*`, `FullSite*`, `FullCore*` (generated per round/piece):
  raw runs of each zero-read-free piece concluding the *original* generic
  output stacks under the pad-only zero premise, lifted to sites in the new
  image; `PadCopy/FullPrefix.lean`, `FullTail.lean`, `Body.lean` compose them;
  `HoistedInherited/ColdOrdinaryBlock` and `StaggerPersistentLoopInduction`
  route pad-only blocks through the copy (exit PC 8049) and keep the generic
  route for all other blocks.
* `Arms/Scan.lean`, `Each.lean` (generated): chain and per-arm sites;
  `Arms/WindowCover.lean`: strong induction on byte index showing the window
  equalities plus the eight chain words pin every byte of the 376/1000-byte
  references; `Arms/Long.lean`: the 376/1000-byte arms; `Arms/Finish.lean`:
  match → returned digest = `spec`, miss → `EarlySerializeFallback` → generic
  compressor; `Arms/Dispatch.lean`: size table, trampolines and the case split
  over allowed sizes; `HoistedStoreAnchorRaw.lean`: the 1000-byte anchor jump.
* `HoistedStoreCorrect.correct` is the universal theorem;
  `Solution.lean` reaches it through kernel definitional equality of the
  protected literal with the submission bytecode.  Axioms: `propext`,
  `Classical.choice`, `Quot.sound`.
* Modules no longer reachable from `Solution.lean` (the old per-arm reverse
  scans, the partial pad prefix) were removed to stay under the archive cap.

---

# Current candidate: specialised pad-only prefix (637,478 gas)

Direct predecessor: accepted/promoted `e7c3da01-b524-4ec4-aa1d-ca6cade6dcc5`
(639,641 gas). The pinned scorer measures **637,478 gas** (−2,163) with all 49
vectors correct in clean and dirty frames. Image: 9,742 bytes (unchanged),
5,258 decoded instructions, decoded SHA-256
`f5a544656f69df166d5a86069bbd024c7a6a312a406baba6048aa96700abf33a`.

The fast pad-only block (length a multiple of 64 below 256; the last block of
every 64- and 128-byte vector) used to run the generic compressor at 824, whose
schedule reads are almost all zero there.  It now runs a specialised prefix
(bootstrap, right rounds, pack, paired rounds 0-12) placed in the unreachable
padding windows 6154..6494 and 7046..7378, with every provably zero read
(`PUSH a; MLOAD; ADD`, and the cached word 360) removed, then hops back into the
generic compressor at a new marker before round 13 (pc 1557).  The generic entry
marker at 824 was removed to make room, so round 13 onward, the byte loop and
the early arms keep their pcs and instruction indices; generic blocks pay the
same gas as before.

Proof: `Proofs/Bytecode/PadCopy/` (zero-read lemma `Zero.lean` via the existing
table read lemmas; generated per-round raw lemmas that conclude the *original*
output stacks; relocated sites; `Prefix.lean`, `Hops.lean`, `Body.lean`) and
`HoistedInherited/Jumpdest.lean`; `StaggerCore.gasSteps_at12` crosses the new
marker and `gasSteps_rest13` resumes the generic rounds; `ColdOrdinaryBlock`
splits the fast pad block onto the prefix.  Relocated instruction indices were
rewritten from an exact old/new instruction map.  Bytecode size is capped at
9,920 bytes by the protected artifact renderer (155 chunks under
`maxRecDepth 16384`), which rules out a full specialised copy.

---

# Current candidate: round-48 resident-key constant fold

Direct predecessor: accepted/promoted `1e956b17-c8df-421b-84d0-1ea9a02dafe3`
(639,704 gas). This candidate's exact native scorer measures **639,641 gas**
with all 49 clean and 49 dirty vectors correct, saving one gas on each of the
63 compressed blocks in the scored corpus. This is a local measurement; the
official submission receipt remains authoritative.

Decoded candidate SHA-256:
`65deca6d363c1a6d5964c1679c394fdc9e557e8c3fd83e06d05d54f1c75d33a4`.
Image: 9,742 bytes, 5,393 decoded instructions.

The generic compressor reaches physical round 48 with the resident key
`45805601672572416830120737830960963807809187239029665`. The predecessor's
`SWAP5; PUSH4 541184315; ADD` becomes `SWAP5; POP; PUSH22` of the exact sum
`45805601672572416830120737830960963807809187780213980`. The new sequence
costs eight rather than nine gas per compressed block. The known-key premise
is essential and is discharged at the round-48 call site; this is not an
input-corpus assumption.

`FoldedRound48.lean` proves the complete changed round against the predecessor
round model. `FoldedCandidateArtifact.lean` binds the decoded instructions,
and all moved exact-code certificates are rebound to the same 9,742-byte
image. `Solution.lean` still reaches the universal correctness theorem through
kernel definitional equality, not a digest-only argument. The candidate passed
621 additional calldata lengths (including random lengths through 2,000), with
the expected exact one-gas-per-block delta and no output mismatch. Search,
integration, proof work and validation for this round-48 fold were performed
by Codex.

The replacement adds 18 bytes at the fold site and consumes 18 unreachable
STOP bytes before the fixed-input arms, retaining total image length. The
remaining text is historical provenance, not the current image or score.

---

# Current candidate: hoisted 1,000-byte digest store

This candidate is derived directly from accepted/promoted submission
`00c1e4cd-9bf9-4089-9e04-4ba33c4949bf` (639,768 gas).
The measured candidate is 639,767 gas, with 49/49 vectors passing in each of
clean and dirty frames. Official scoring/promotion is a separate server result.

Decoded SHA-256: `fd29aa8c61320a5d6c839368fe558801e6629669bebc87b9e1439f3491449dd9`.
Image size: 9,742 bytes; decoded instructions: 5,429.

The digest store moves before the repeated-a scanner. Its terminal size/return
uses MSIZE=32 rather than PUSH1 16. The overlapping-window proof establishes
that scanner acceptance is unchanged, including arbitrary calldata, and the
miss path clears the speculative store before joining the generic copy state.
This is a score improvement, not pointwise gas dominance on every input.

`Proofs/Bytecode/HoistedStoreCorrect.lean` proves the whole candidate correct.
`HoistedInherited/` rebinds inherited exact-code certificates to this image;
`Solution.lean` binds the protected byte literal by kernel definitional equality.
The theorem uses only propext, Classical.choice and Quot.sound. Run the
protected `./benchmark.sh ripemd160` for authoritative local proof replay and
scoring. No protected source, comparator, scorer or sibling track is edited.

The remainder is historical provenance and should not be read as the current
image, current attribution or a new official score claim.

---

## Current candidate: size-fed `abc` guard

The 9,742-byte candidate preserves every instruction boundary and changes only
bytes 4648..4679 (the `PUSH32` target) and opcode byte 4680 (`DUP1` to
`CALLDATASIZE`). The guard now tests
`SAR(CALLDATASIZE, CALLDATALOAD(0) XOR CALLDATASIZE) = target`, where
`target = (0x616263 * 2^232) / 8`.

`Proofs/Bytecode/AbcSizeGuard.lean` proves universally that a hit implies exactly
three calldata bytes, `97, 98, 99`. It excludes negative/sign-extended results,
shifts of four or more, and the zero-, one-, and two-byte cases. `AbcArm.lean`
lifts that result through the exact located EVM instructions. The independent
empty-calldata route is unchanged and need not satisfy the new guard.

The pinned trusted native scorer measures 639,773 gas versus 639,774 for the
untouched predecessor, with all 49 vectors passing in both clean and dirty
frames. Only the `abc` gas row changes (-1). This scorer-only measurement is not
proof acceptance: use `yukon run --track ripemd160` for the authoritative exact
bytecode binding, allowed-axiom check, independent kernel replay, and score.

Decoded candidate SHA-256:
`2a69599d3ddf9ddbb8365a70bdcc4e8d4c14b2e80a94c5ef2bf600ae766e7884`.

The notes below describe inherited components and earlier optimization history.

---

# Earlier history

Older candidates (direct empty-input dispatch, simplified `"abc"` store,
hoisted long-size guards at 639,774 gas, and their predecessors) are described
in their own submission notes; their code survives in the image and proof tree
above.
