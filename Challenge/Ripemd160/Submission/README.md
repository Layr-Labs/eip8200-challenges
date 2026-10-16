# Pruned reverse shared joins — local641029

Effort:xhigh. RawSHA256`3a480d2cb9479f2b2c7d6e3428d5b185594af7cf334b6a5a07d3576df5d8b667`.
98/98runtimeexecutions,641029clean/dirty,9208bytes.Focusedintegrationpasses.
RemovesthreenolongerusedjoinJUMPDESTs;allcomparisonsandfallbackretained.
Historicalpredecessordetailsbelow.

---

# Reverse literal scanner — local 641,038

Effort: xhigh. Raw SHA256: `5532e5cf9ffd530dbf34fb93c42e7973472b5df123cf35ed3af13b4b9f95b039`.
9208 bytes; 98/98 protected runtime executions; 641038 clean/dirty.
One length dispatch, fixed tail shifts, descending full-word checks; no check or fallback removed.
Direct base accepted cf9bba2d at 641679. Full certificate delegated to Yukon.
See reports/ripemd160-iter55-integration/submission-note.md for integration rationale.
Historical metadata below belongs to predecessors.

---

# Self-sized selector and scanner — local641679

Effort:xhigh. SHA256`5cd65f3bb30e90a50c65b758fd14aa035531f13bcdcc8a1d2fb898357ca8bfef`.
9208bytes,3744instructions,98/98protected executions,641679clean/dirty.
CODESIZEis both quotient-selector mask and low-byte scanner multiplier.
Full Lean delegated to Yukon; pending is not accepted. Historical metadata below.

---

# Absolute quotient-mask serializer — local 641707

Effort: xhigh. Runtime SHA256
`054fca0eef7cc7b9fa286be8e51f53b753136a64e1249b45a5b26e546cdfc089`.
9216 bytes; 3744 executable instructions; 98/98 protected local executions;
641707 gas in each clean/dirty frame aggregate. Pending full Yukon validation.
Selector source is `(910065310 / input.size) & 9184`; CODECOPY copies a complete
canonical padded32-byte ABI word to memory0. The17-byte selector interval,
scanner boundaries and return PCs are unchanged. J2Payload uses segmented
literal windows to avoid reducing a multi-kilobyte flat list for each read.
Universal selector, padded-copy memory and payload-window proofs pass locally;
exact artifact and semantic integration checks are in progress. Full certificate
is delegated to Yukon as requested. Historical metadata below is not current.

---

# Four-word scanner — local644636

SHA256a2b01a200655fbdda80b340a96339cce33e6239f12f52191812165968c2f2581.
5862bytes3744instructions,98/98protectedexecutions,644636clean/dirty.
Frame[acc,off,word,stop], perwordliteralconstants. Firstdispatchstride82.
Universalrawproofs,abstractcontrolproofs,exactartifactandsitebindingspass;
fullcertificate delegatedtoYukon. Effort:xhigh.

Historicalmetadata follows,not current.

---

# Literal scanner constants — local644720

Decoded SHA256a6f10586b77a2dac35411e9be8874dc5033bd16446a5ace25522d348b8b58612.
5480bytes3746instructions,98/98protected executions,644720clean/dirty.
Six-wordframe; directliteral m9f initialization and literal sentinel/c14
transitionprefix. Universal raw proofs and exactimage/site checks pass;
fullcertificate delegatedtoYukon. Effort:xhigh.

Historical metadata below is not current.

---

# Six-word scanner — local644830

Decoded SHA2563e8bdee71603c96793baddaecde68033c887b3abf19590677d6dd8a2165955e6.
5392bytes3752instructions,98/98protected executions,644830clean/dirty.
Concrete full slot erased; finalshift=((off−len)+32)<<3, MSIZE=32. Six-word
frame and five-word miss residual. Effort:xhigh. Raw/abstract checks pass;
exact artifact adapters checked, full certificate delegated to Yukon.
Accepted parent1991c997 at04e2ad5a is644876, preserved separately.

Historical metadata below is not current.

---

# Global full, stop-based initial dispatch — local644876

Current5393bytes,3753instructions; decoded SHA-256
`134dc02323d9370095ff62938be3fde90281d99e86200ed3cfcaff37c85c7d73`.
Runtime98/98OK,644876clean/dirty. Effort:xhigh.

Full=length−32 is initialized once, never rewritten by transitions. First
computed dispatch uses32−clampedStop independently of full. Generic/special
cleanup SWAP7 SWAP2 POP preserves the frame. New tail5077, chain4951+18*j,
result5097, return5101, specialized376arm5104. Raw/abstract and exact-site
checks pass; full certificate and official acceptance remain pending Yukon.

Historical notes below have obsolete PCs/sizes.

---

# Unclamped generic stop — local644939

Current image5403bytes,3763 executable instructions, decoded SHA-256
`8c88bf3de84bf824fd4e5fc7be2b23f38eaed7c99f004699efa3742404075186`.
Trusted runtime98/98OK, clean/dirty644939/644939. Effort:xhigh.

Generic stop advances251 without a minimum; finish tests stop<len. Full is
len−32 after the first transition. Nonfinal projection remains literal40;
final1000 shift remains72. New tail5082, chain4956+18*j, result5102,
return5106, specialized376 arm5109. Raw/abstract/concrete changed-region
proofs pass; complete certificate and official acceptance remain pending.

Historical descriptions below have obsolete sizes/PCs.

---

# Hoisted transition classifier — local645008

Current candidate: **5411 bytes**, **3771 instructions**, decoded SHA-256
`71b16440dc9e626373e538a6b2043445da188b7e1b91209175426d73f18bd831`.
Protected runtime **98/98 OK**, clean/dirty **645008/645008**. Effort: xhigh.

Size-bit branch moved to4936. The1000-byte arm runs generic stop/cleanup at4944
and falls through to4964. The376-byte arm at5117 sets stop=CALLDATASIZE,
cleans the frame, and jumps to5036. This saves17 gas versus645025. Universal
raw semantics are in J2HoistRaw; exact sites/composition in J2HoistSites;
reachable specialized minimum is proved by J2Frame.transition_min.

Full certificate validation and promotion remain pending Yukon, not inferred
from runtime samples. Historical descriptions below have different lengths
and PCs. No full local certificate build is required before submission.

---

# Transition branch/fallthrough — local 645,025 gas

Current image: **5,397 bytes**, **3,759 instructions**, SHA-256
`9710fffe8552dbf653d164c76e7c966b1ce9b1c6fadb20f8903da6391bc1d0d4`.
**98/98** protected executions OK; clean and dirty gas **645,025**.
Effort: xhigh; GPT 6.1 Sol through angelX.

Only lengths376/1000 take the remaining nonfinal transitions. The branch at4955
selects block4 (5036) for376, and falls through to block0 (4964) for1000.
This saves16 gas at each of four measured transitions, on top of the carried
whole-word256 fusion. The initial arithmetic dispatch remains, with its base
literal relocated to5090. See J2RawControl.run_dispatch1 and
J2Frame.transition_chain for raw and control-state semantics.

Full validation is delegated to Yukon; local gas evidence is not acceptance.
Historical image descriptions follow below and have different PCs/lengths.

---

# Whole-word 256-byte tail fusion on the computed-jump chain — local 645,089 gas

Current candidate: **5,403 bytes**, 3,764 executable instructions, decoded SHA-256
`9a5704097bbedb8a69f3663b9b0fef7d1c5c07cd165e6d6e6f546d9a31b2e310`.
Protected runner: **98/98 OK**, clean **645,089**, dirty **645,089**.
Effort: xhigh; current submission uses GPT 6.1 Sol via angelX.

Direct base: promoted `1063a889-af49-4f2e-91ce-04ac27b50511`, source
`77c722f497d7e762d81bcc426a625fa8aa418def`, 645,176 gas.
Bytes before PC5044 are unchanged. The five-byte nonfinal boundary projection
expands to28 bytes. Length256 now corrects the whole live tail XOR by
`0x170d3b750f` and combines it with the prior accumulator; a zero result directly
returns the already prepared digest. A mismatch enters unchanged generic fallback
at4565. Longer nonfinal boundaries select the original fixed40 projection.
Only the late fallthrough suffix is relocated by23 bytes; the digest table stays
last and CODESIZE-relative.

The universal correction/equivalence proof is in `J2FusedAccumulator`. Raw
semantics, computed-chain integration, and exact concrete site certificates are
in `J2FusedRaw`, `J2FusedLoop`, `J2FusedCorrect`, and `J2FusedSites`.
Focused semantic and artifact checks are local; the full certificate and final
acceptance are delegated to Yukon. Historical sections below describe earlier
images and their authors, not the current image or its verification status.

---

# Patterned scanner as a computed-jump word chain — local 645,176 gas

Model: Claude Opus 5.5 (Anthropic). Harness: Claude Code. Track: ripemd160.
Base: frontier 24e0bd4d6 (646,197). Exact image: **5,380 bytes**, 3,750 executable instructions,
SHA-256 `72aec7764aec68267480122b0e99d88b5ae550e5946d6a3cbd3fef8c9011cc3b`.
`seedscore`: **645,176** on all 31 corpus seeds (sd 0), **-1,021**.

## The change

The patterned scanner loop (`JUMPDEST; word body; DUP4 DUP3 LT PUSH2 JUMPI`, 73 gas per word, 34 of it loop
control) ran 60 times per corpus frame. A segment has at most seven full words before its tail word (251-byte
segments), so the loop is replaced by a straight chain of seven copies of the unchanged word body
(`normalTemplate`, 18 bytes each, at `4891 + 18 j`) that falls into the unchanged tail at `5017`. A segment with
`m` full words is entered at block `7 - m` by a computed jump

    DUP4 (PUSH0 | DUP3) SUB PUSH1 5 SAR PUSH1 18 MUL PUSH2 5017 ADD JUMP

i.e. `5017 + 18 * ((off - full) sar 5) = 5017 - 18 * ceil((len - 32) / 32)` (37/36 gas per segment entry,
replacing the `size < 33` test of the first entry and the `off < full` guard of a transition). Per word: 51 gas
instead of 73. The first entry uses `PUSH0` for the zero offset.

Layout: PCs 0..4546 and 4598..4876 are unchanged byte for byte (same instruction indices). The transition block
(old 4547..4597) moves behind the tail (boundary projection 5044, transition 5049, `POP` + dispatch 5085); its old
51 bytes now hold the padding footer loop (4547, was 4937; the `PUSH2` at 172 is relocated), the miss handler
(4565, was 4955) and 26 unreachable filler bytes (21 `STOP` + one `PUSH4 0`), chosen so that the instruction count
of 4547..4597 stays 43 and every later index up to 4876 is unchanged. The 280 digest bytes stay last (they are
read relative to `CODESIZE`).

## Proof changes

* `J2RawBase`: `dispatchTarget`, `blockPC`, `dispatch0Template`/`dispatch1Template`; the guard and to-tail
  templates are gone; finish/result jump literals relocated. `J2RawControl`: `run_dispatch0`/`run_dispatch1`.
* `J2Frame`: `segTail`, `blk n k = 7 - (segTail n k - k)` and `ChainFacts` (block bounds, the block step, and
  the two dispatch identities at segment starts), closed by `decide` over the 14 allowed lengths.
* `J2Moves`/`J2Loop`: the loop state of word `k` is at `blockPC (blk n k)`; a normal word moves one block, a
  nonfinal tail runs tail -> boundary -> transition -> dispatch. `J2Sites`: the seven block sites and the new
  dispatch/tail/transition sites and jump-destination facts.
* Relocated indices/PCs: `EarlySerializeReturn` (return at 5041), `EarlySerializeFallback` (miss handler 4565),
  `PaddingTrace`/`PaddingTraceCore`/`DirectGuardBase` (footer loop 4547..4564), `J2Payload` (code size 5380),
  `J2Correct`; `Bytes`, `Bytecode`, `Artifact` (chunks 17..19, counts and the legacy index lemmas).

---

# Nonfinal segment-tail projection — local 646,197 gas

Current exact runtime: **5,242 bytes**, decoded SHA-256
`3bc4db8b7197dd2540a6a0ed58ed22354f38b4997a3bb3b4517673588c2e3162`.
The protected gas runner returns **98/98 executions OK**, clean **646,197**,
dirty **646,197**. Universal certificate acceptance is pending Yukon validation.

This extends the warm-empty MLOAD/MSIZE guard below. At every nonfinal
251-byte patterned-scanner segment, `off = segmentStart + 224` and
`full = segmentStart + 219`; hence the projection shift is exactly 40 bits.
The existing end-of-input branch now runs while the tail XOR is still live.
Its nonfinal arm uses `PUSH1 40; SHR; OR`, instead of dynamically forming the
shift. The final arm retains the original general projection. This saves
12 gas per nonfinal segment boundary, 60 gas per benchmark frame in aggregate.
Eight unreachable serializer filler bytes were removed; a four-byte boundary
projection was inserted, and subsequent positions and pointer immediates were
relocated. Compressor and shared writer schedules are unchanged.

The raw tail/control/transition proofs, finite control-state invariant,
J2 loop induction, exact artifact binding, new site windows, relocated
entry guards and endian output adapter have focused local checks with no
`sorryAx`. Full universal verification is deliberately left to Yukon, not
inferred from local runtime samples. The generic fallback keeps both length32
and ordinary non-32 cases. The source sections below are historical predecessors,
not descriptions of the current hash or size.

---

# Guard MLOAD/MSIZE candidate — local 646,257 gas

This working candidate builds on accepted 646,264 submission `ee41c2be-f76e-4b2f-a6a4-27f9c5f6c6a6`.
The repeated-word guard activates exactly one memory word with `PUSH0; MLOAD`,
reuses the zero as its reference-word calldata offset, and replaces ten `PUSH1 32`
instructions with `MSIZE`. A shorter safe prefilter and a swallowed inert filler
keep length 5,246 bytes and renderer cost 8,194 unchanged. SHA-256:
`425d4cb74c18156807059705bd4b52935a482a8d882de770e69ddd8f0c7ce2bc`.

Trusted runtime: **98/98 ok, clean 646,257 / dirty 646,257**. The seven-gas
reduction is on `1000 a's`. Universal remote validation of this source is pending.
The fallback proof distinguishes empty physical memory from active memory size:
`MLOAD` does not write a zero word. Focused seed/loop/tail, exact artifact,
warm-empty copy and ordinary fallback adapters have been checked locally.

---

# RIPEMD-160: epilogue byte swap without shifts on the 647,047 frontier (646,311 gas)

Model: Claude Opus 5.5 (Anthropic). Harness: Claude Code. Track: ripemd160.

Base: the accepted 647,047 image of submission 10bd246d (frontier 99c19938e), byte for byte except the 33 bytes at
PC 4753..4785 (instructions 3500..3524): the byte swap of the packed 160-bit digest word, its store and the return.
The sections below this one describe the base and are unchanged.

## The change

The five chaining words are stored descending at offsets 16, 12, 8, 4, 0 and read back as one word `V < 2^160`
(unchanged). Each 32-bit lane of `V` must be byte-reversed. The base ran two XOR/shift/multiply stages (64 gas) and a
store at 0. The new code uses, for the half-swap mask `m` of width `k`,

    v + (v & m) * (2^k - 1) = swap_k(v) * 2^k        (exact in 256 bits)

so no right shift runs and the result stays scaled. The stages run 16 then 8 (the byte mask `0x00ff00ff..` is
periodic under a 16-bit lane shift, so it is reused). After both, the word is `bswap(V) * 2^24` (no wraparound since
`V < 2^160`); the scale is absorbed by storing at byte offset 3 and returning `memory[0..32)` (bytes 0..2 are zero:
the last descending store wrote a 32-bit word at offset 0).

    DUP1 DUP6 AND PUSH4 0xffffffff MUL ADD     ; stage 16, mask16 at depth 5
    DUP1 DUP5 AND PUSH2 0xffff MUL ADD         ; stage 8, mask8 at depth 4
    PUSH1 3 MSTORE PUSH1 0x20 PUSH0 RETURN

17 instructions instead of 25, 23 gas fewer per digest written by this epilogue. Eight unreachable `DUP1` fillers
after `RETURN` keep the byte length and instruction count, so every later PC, jump target and instruction index is
unchanged. The epilogue runs once on 32 of the 49 scored vectors: **647,047 -> 646,311 (-736)**, identical on all 31
local corpus seeds (sd 0).

## Proof changes

* `FinishMath.lean` (new): exact `BitVec 256` identities `v + (v&M16)*0xffffffff = P16 v <<< 16`,
  `v + (v&M8)*0xffff = P8 v <<< 8`, and the combined `= P16 (P8 v) <<< 24`.
* `StaggerPersistentFinish.lean` (new): the two executed slices (instruction indices 3500 and 3512, PCs 4753 and
  4771), their raw-run and gas lemmas, the bounds that make the `2^24` scaling exact, and `hReturn_eq` (the returned
  bytes equal `natToBytesPadded (packedWord (packedHash h)) 32`).
* `StaggerPersistentSerialize.lean` composes `StaggerPersistentOutput` with the two new sites; `result`, `value` and
  `gasSteps` keep their interface, plus `result_hReturn`, which `StaggerPersistentSerializeMath.lean` now uses. The
  old endian stage modules are no longer imported by this path.
* `Artifact.lean`, `Bytes.lean`, `bytecode.hex`: instructions 3500..3524 and the chunk-18 byte certificate; counts,
  PCs and all other chunks unchanged.

This is the 647,065 candidate of an earlier run (same rewrite on the 647,801 base, PC 4772) rebased onto this frontier.

# RIPEMD-160: a re-planned stack window over paired steps 62..71 on newjordan's 647,411 record (647,222 gas)

Model: Claude Opus 5.5 (Anthropic). Harness: Claude Code. Track: ripemd160. Lower gas is better.

## Base, record and attribution

- **newjordan, d62f7e87** (accepted and promoted record, 647,411, promoted commit dae6b078): the live record this
  submission is measured against, and a base of this tree. d62f7e87 is 52f50e76 with one change in the recognition
  routes: the empty/`abc` arm used to end with `PUSH2 0x127a JUMP` to the shared return at 4730 (`JUMPDEST PUSH0 MSTORE
  MSIZE PUSH0 RETURN`); it now returns in place (`PUSH0 MSTORE MSIZE PUSH0 RETURN` at 4704..4708, the five bytes of the
  old jump and of the 1000-byte answer block's `JUMPDEST`), that `JUMPDEST` moves one byte to 4709 (the
  `PUSH2` at 243 now targets 4709), that block falls straight into the return tail, and the shared-return `JUMPDEST` at
  4730 is gone. Same code length, PCs from 4731 on unchanged, two instructions more (-25 gas on the scored corpus against
  52f50e76). This tree takes those 28 bytes (PCs 243..4730) and d62f7e87's proof changes (`AbcArm`, `DirectGuardBase`,
  `DirectGuardSize`, `DirectGuardTail`, `GuardInstructionWindow`, `J2*`, `PaddingTraceCore`, `Patterned128Entry`,
  `StaggerPersistent*`, `Bytes`/`Artifact`), relocated to this layout. The two edits are disjoint: d62f7e87 changes
  PCs 243..4730 outside our window, and this tree's own changes sit in PCs 1388..4182. 647,222 here against its
  647,411 (-189 gas).
- **newjordan, 52f50e76** (accepted and promoted record, 647,436, promoted commit cba00f5c): the base of d62f7e87 and the
  tree this one starts from byte for byte. 52f50e76 is our 00b4dbb3 with one
  change: the `JUMPDEST` filler at 4362 is removed and the `PUSH13` at 4348 is widened to `PUSH14` with a leading zero byte,
  which keeps the code length and every later PC with one instruction fewer (-1 gas per compression, -63 on the scored
  corpus). Its proofs, re-indexed for the removed instruction (every instruction index after it moves by one), are carried.
  This tree uses the same widening technique for its own filler (item 4 below).
- **kaankolcu, 00b4dbb3** (accepted and promoted record, 647,499): the base of 52f50e76. Its content is
  listed below under "Carried from 00b4dbb3".
- **newjordan, 0961b85e** (accepted record, 647,822): the base of 00b4dbb3. Its cuts are carried with their proofs: the
  compression exit consumes the continuation (`SWAP13 JUMP` instead of `POP DUP13 JUMP`; the epilogue keeps its length with
  `PUSH2 0x0090`), every continuation stub reinstalls its value and pops the stale slot at the shared `JUMPDEST POP` join
  (132), and the gas-neutral round-33 `DUP10 ADD ADD` reassociation, with their proof changes.
- **newjordan, 1d5fd62c** (accepted record, 647,948): `CALLDATASIZE` instead of `DUP13` at PC 68, with its
  `StaggerPadSetup` proof change, carried unchanged.
- **Th0rgal, 2cc229ec** (accepted record, 647,801): none of its bytes are used (its pad-block and 199 edits sit in code that
  00b4dbb3 replaced); listed because 00b4dbb3 was measured against it.
- **kaankolcu, 8375c07c** (accepted record, 647,969): the phase-continuation prologue, padding, paired compressor,
  recognition routes, digest serialization and the universal Lean proof.
- Inherited through those images, and listed in `dependencies.json`: eac16f46 and 3237115c (kaankolcu), the CODESIZE-relative
  digest selector, signed boundary and tail of cb3f7647 (newjordan), Th0rgal's round-79 epilogue (fc5d5ea8) and newjordan's
  compression-body widths (a12ad85f). Credited as in 8375c07c, carried unchanged: newjordan 96e765dd, rubenmarcus 63ed2b49 and
  9dfde6e7 (earlier epilogue work), Th0rgal f797f38b.

## What is new here

Items 1..4 are this tree's own work on top of d62f7e87; each one is independent of d62f7e87's answer-path change.

1. **L62, a re-planned stack window over paired steps 62..71** (PCs 3796..4210). A search over staging sets, the D'-copy
   trick and copy/commutative choices re-solves the slot layout and fetch order of these ten steps with the compute order
   and the boundary values unchanged (step 62's input and step 72's input are the same as before). The plan stages cached
   words earlier in steps 64 and 66 (with the D'-copy), defers one operand in steps 65 and 67, and drops the copy of the
   cached message word at 360 that 00b4dbb3 carried from step 64 to step 70 (step 70 now fetches it just in time with a
   `DUP`). Net, the window runs one stack operation fewer per compression: -3 gas per compression, -189 on the scored
   corpus. Steps 62..71 change their stack shapes.
2. **A floating `Bytes` chunk cut.** The window makes steps 64..68 two bytes and two instructions shorter before the chunk
   cut at byte 4111 (inside step 69) and step 70 one byte and one instruction longer after it. The chunk cut is no longer
   tied to equal per-chunk instruction counts: it stays at byte 4111 and chunks 15 and 16 go from 224/219 to 223/220
   instructions. Only `Bytes` and `Artifact` know chunk sizes (their size, length and byteLength lemmas); every
   `instructionPC` fact goes through the byte length of the whole list, and the window's byte length and the instruction
   total outside it are unchanged, so every later cut, PC and index outside the window holds.
3. **Wall banks on paired steps 9..17 and 44..51** (PCs 1379..1827 and 2965..3337). Gas-neutral and PC-preserving
   reassociations and commutations of `ADD`/`AND`/`OR`/`XOR` operands (same opcodes, same stack effect, other `DUP` depths)
   in steps 9..11, 13..17 and 44..51 that lower the `Artifact`'s elaboration cost, so items 1 and 2 fit the same Lean
   elaboration limit as 00b4dbb3. No gas change.
4. **The window's filler as a `PUSH` widening** (52f50e76's technique). The window is one byte shorter than the code it
   replaces; instead of a `JUMPDEST` filler at the end of step 71 (4210), which costs 1 gas per compression, the round-71
   `PUSH13 0x7e0000007e0000004000000040` at 4181 is written as `PUSH14 0x007e0000007e0000004000000040`. Same value, same gas,
   same code length, every PC from 4211 on unchanged, and one instruction fewer, so every instruction index after the
   window moves down by one more (two against 00b4dbb3 after 4348, counting 52f50e76's own widening; d62f7e87's answer
   path then adds two after 4704).

The proof changes: `StaggerRawPaired{9..11,13..17,44..51,62..71}Raw` (templates and the generic AC proofs for the new
expression forms), the wrappers `StaggerRawPaired{64..76}` and `StaggerRawLeft77..79`/`StaggerRawUnpack` (instruction index
and PCs), `StaggerCorePaired{64..71}` and `StaggerCore` (step PCs and shapes), the relocated `Bytes`/`Artifact` literals
with the floating cut, and the instruction-index references of the modules after the window (`AbcArm`, `DirectGuard*`,
`GuardInstructionWindow`, `J2*`, `PaddingTraceCore`, `Patterned128Entry`, `ShortSizePrefix`, `StaggerPersistent*`).
d62f7e87's proof changes to those modules are merged in with every instruction index after the window moved down by one
(its new answer-path rows included); the `Artifact` is d62f7e87's with this tree's chunks rewritten.

## Carried from 00b4dbb3 (kaankolcu, 647,499) unchanged

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

Their proof changes, carried: `StaggerPadSetup.run_low` and the pad-only sites for P19; `ColdGuardFixup` (the 32-byte block's route now
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

- Decoded artifact SHA-256: `34b57b79b00486b64a85666336c9e0e48c9822c2fc925bda08ccb3222c17c9c5`. 5,247 bytes, 3,617
  executable instructions (d62f7e87: 3,618).
- Exact scorer replica, 49/49 digests, clean and dirty equal: **647,222** at seed 0 and at seeds 12886768257922782526,
  18235675205389542134 and 777 (d62f7e87's image: 647,411; items 1..4 on 52f50e76 without d62f7e87's answer path:
  647,247; items 1..3 with a `JUMPDEST` filler instead of item 4: 647,310). Tier 1 PASS.
- Random-message fuzz of these exact bytes against a reference RIPEMD-160 (the execution-spec precompile), in both the
  clean and the dirty world: 300,000 four-block messages with bytes 32..43 of every block set to 0xff, 200,000 messages
  of random length 0..1,000 bytes, and 50 random messages at every length 0..300 (15,050): 0 wrong in every mode and
  world. The same fuzz on items 1..4 without d62f7e87's answer path: 0 wrong in every mode and world.
- Lean build of this tree on these exact bytes (the harness's `prepare` step writes `Benchmark/Artifact.lean` from
  `bytecode.hex`, then `lake build Challenge.Ripemd160.Submission.Solution`): exit 0, 0 failed modules; the candidate
  theorem depends only on `propext`, `Classical.choice` and `Quot.sound`. Largest module about 9.9 GB of resident memory
  (`PaddingTraceCore`).
- Not run: the canonical `yukon run --track ripemd160` gate and the protected Comparator.

## Equality-accumulator guard successor (646308 local runtime gas)

Effort: xhigh; GPT 6.1 Sol via angelX. Direct base is accepted submission
`1ae4a5dd-d516-47eb-ae50-f13bd95b36ae` (646311, source185510a4).
The repeated-word guard now uses EQ/AND rather than XOR/OR; its final
ISZERO is removed. A fallthrough JUMPDEST at244 retains byte length and
all downstream instruction indices. `EqualityAccumulator.lean` proves
`equalityAcc input n = UInt256.isZero (reverseAcc input n)` for arbitrary
input. The loop and fallback certificates use this invariant.

Exact runtime SHA-256:
`31325345d4f3eb7089fe05d87ca83e80c73d2a5fbd08db436c5c28d832148a06`.
5246 bytes; local protected scorer98/98 OK,646308 clean/dirty.
The 1000-a row is967 instead of970; all other rows are unchanged.
Remote universal validation is required; local runtime checks alone do not
establish acceptance.

## Live-length short-entry successor (646264 local runtime gas)

Effort: xhigh; GPT 6.1 Sol via angelX. The direct predecessor646308,
submission `fe67a6d0-68a5-4dad-90d5-8bab814e133f`, is officially accepted and
promoted at `1000e41ce5714760920f371b6742366c3aa94a5c`.

Only PC144..165 changes: consume the live length displaced by SWAP13 with
PUSH1 32/EQ rather than POP, retain the predicate across identical padding
stores (DUP5 becomes DUP6), then branch to the same497 or166 join. Two
fallthrough JUMPDESTs retain width and downstream instruction count. New local
head invariant: `F(lim) -> EQ(32,lim) :: F(4729)`. Both padding callers supply
`lim = copiedLimit input = UInt256.ofNat input.size`;32-byte callers supply32.

5246 bytes; SHA256
`bd82d8e3715567bef877c0aaa9d5c9cbc68e41531aafa61216ace10825cf8b82`.
Protected runtime scorer98/98 OK,646264 clean/dirty,44 below predecessor.
The11 generated32-byte executions save4 each. Universal validation remains
required for this successor; runtime and fragment tests are not a proof.


## Nonfinal segment tail specialization

Current measured image: **646,197 clean / dirty gas**, **5,242 bytes**,
SHA-256 `3bc4db8b7197dd2540a6a0ed58ed22354f38b4997a3bb3b4517673588c2e3162`.
98/98 trusted runtime executions pass. Universal certification remains pending.

The patterned scanner now tests the segment endpoint before projecting the
last loaded word. Final segments retain the general shift. Nonfinal 251-byte
segment boundaries always satisfy `off - full = 5`, hence use a fixed 40-bit
shift. No branch was added: the existing endpoint branch was moved while the
XOR stays live. The nonfinal projection saves 12 gas at each boundary, totaling
60 over the measured corpus. Eight unreachable DUP1 bytes are removed to keep
the image smaller; all affected continuation and jump literals are relocated.
The compressor and PC-derived writer sites remain at their original PCs.

The Lean trace splits tail-XOR, endpoint branch, final projection and nonfinal
projection; `J2Frame.boundary_shift` proves the fixed shift from the scanner's
closed allowed-length control-state invariant. It is independent of message
bytes and the loaded tail value. `J2Moves` exposes the two tail cases to the
loop induction. The generic fallback retains the length-32 sparse branch.
