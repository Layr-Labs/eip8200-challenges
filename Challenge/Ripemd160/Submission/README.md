# Current candidate: abc-guard miss-path JUMPI retarget past the PC-4905 trampoline

Direct predecessor: accepted/promoted `e7c3da01-b524-4ec4-aa1d-ca6cade6dcc5`
(639,641 gas). This candidate retargets the `AbcArm` miss branch of the
size-fed `abc` word guard: the `PUSH2` immediate at `PC 4721` changes from
`4905` to `245`, so the taken `JUMPI` at `PC 4724` lands directly on the
generic-dispatch `JUMPDEST` at `PC 245` instead of paying `JUMPDEST; PUSH1
0xf5; JUMP` at `PC 4905-4908`. The miss path runs on every vector whose
leading word fails the `abc` recognizer, so the bypass saves `1 + 3 + 8 = 12`
gas per miss traversal — 192 gas over the 16 miss vectors, plus the `abc` hit
path is untouched.

Decoded candidate SHA-256:
`4b6afe631d5c513f333bab3e62cfb8a689bd328ec7bc7a1bf03fea95bccb70a3`.
Image: 9,742 bytes, 5,393 decoded instructions.

The `JUMPDEST` at `PC 4905` is retained, so every computed jump that may still
resolve to it stays valid; only the static caller is retargeted. The patch is
width-preserving: no program counter moves, and every PC witness in the
artifact tables is unchanged. `GuardInstructionWindow`, `Artifact`,
`FoldedCandidateArtifact`, `Candidate_prefix13`, and the `Bytes` chunk now
record `PUSH2 245`; `AbcArm.entryDest` rebinds to instruction 125 and
`AbcArm.fallbackState` to `PC 246`; `Patterned128Entry.gasSteps_after_arm_miss`
collapses to `GasSteps.refl` because the traced trampoline step no longer
executes. `Solution.lean` still reaches the universal correctness theorem
through kernel definitional equality, not a digest-only argument.
The remaining text below is historical provenance, not the current image or
score.

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

# EIP-8200 RIPEMD-160 Submission Note: Direct Empty-Input Dispatch, Simplified `"abc"` Store, and Hoisted Long-Size Guards (`639,774` Gas, `-86` Gas)

## 1. Executive Summary

- **Track**: EIP-8200 `ripemd160`
- **Verified Total Gas Score**: **`639,774` gas** across all 49 benchmark vectors on **every** server seed (`cleanTotalGas = 639,774`, `dirtyTotalGas = 639,774`, `stateIndependentGas = true`)
- **Improvement over Live Baseline (`fbbbc78`, `4c00692c-c69a-4695-9e4d-fe3d2d5edce5`)**: **`-86` gas** (`639,860` $\to$ `639,774` gas, **100% seed-independent**; `-116` gas below `06386a8` at `639,890` gas and `-124` gas below `8abc5ffb` at `639,898` gas)
- **Bytecode Size**: **`9,742` bytes** (`5,429` decoded EVM instructions, matching the exact instruction count and `PCs 7672..9741` instruction indices of `fbbbc78`)
- **Zero Seed Variance Guarantee**:
  - `PCs 0..4568` (`indices 0..3384`), `PCs 4733..4800` (`indices 3437..3489`), `Arms 1..12`, and `PCs 7672..9741` (`indices 4839..5428`) are **byte-for-byte identical** to our promoted `639,860` record (`fbbbc78`).
  - In particular, the `PUSH5 0x108c86821c` entry prefilter at `PC 0`, the 1,000-byte repeated-`'a'` recognizer, the general RIPEMD-160 compressor, the inlined size-32 schedule constant, and the size-32 shared tail execute the **exact same instruction traces** on every random vector generated by any evaluation seed.
- **Formal Verification**: Universal Lean 4 correctness theorem `Challenge.Ripemd160.Submission.Solution : Challenge.Ripemd160.Correct submissionBytecode` (and `Challenge.Ripemd160.Benchmark.candidate`) proved over all calldata inputs (`CalldataFits input`), depending only on the standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`) with zero `sorry` and zero `native_decide`.
- **Attribution**:
  - **Model**: `Gemini 3.1 Pro`
  - **Harness**: `Antigravity` (`sandboxed.sh` / `yukon`)

---

## 2. Technical Overview of the Seed-Independent `-86` Gas Optimization

### 2.1 Bottlenecks in `shortTemplate` Misses (`empty`, `"abc"`, `256`, and `376`) in `fbbbc78` (`639,860` Gas)

In our promoted `639,860`-gas baseline (`4c00692c-c69a-4695-9e4d-fe3d2d5edce5`, commit `fbbbc78`), inputs that pass the entry prefilter at `PC 0` and do not match `size == 1000` at `PC 14` jump to `shortTemplate` at `PC 4565`:
```text
PC 4565: JUMPDEST                                     (1 gas)
PC 4566: PUSH0                                        (2 gas)
PC 4567: PUSH32 reversedMask                          (3 gas)
PC 4600: CALLDATASIZE                                 (2 gas)
PC 4601: SHL                                          (3 gas)
PC 4602: SLT                                          (3 gas)
PC 4603: PUSH2 8191                                   (3 gas)
PC 4606: PUSH18 selectorConst                         (3 gas)
PC 4625: CALLDATASIZE                                 (2 gas)
PC 4626: SHR                                          (3 gas)
PC 4627: AND                                          (3 gas)
PC 4628: JUMPI                                        (10 gas)
```
In `fbbbc78`, only the 10 positive short patterned sizes $n \in \{1, 31, 32, 55, 56, 63, 64, 65, 119, 120, 128\}$ had bit $255 - n$ set in `reversedMask`. Consequently, the remaining **4 non-1000 fixed benchmark vectors** (`empty` ($n=0$), `"abc"` ($n=3$), $n=256$, and $n=376$) all fell through `shortTemplate` (`PC 4628`) into `AbcArm`:
1. **`empty` ($n = 0$) executed the entire `AbcArm` check (`75` gas after `shortTemplate`)**:
   - It executed `wordPath` (`PUSH2 4905; PUSH1 4; CALLDATASIZE; GT; PUSH32 M; DUP1; PUSH0; CALLDATALOAD; XOR; CALLDATASIZE; SAR; XOR; OR; JUMPI`, `37` gas),
   - Followed by the conditional `storePath` (`PUSH20 abcDigest; PUSH20 xorDiff; CALLDATASIZE; ISZERO; MUL; XOR; PUSH0; MSTORE`, `27` gas) and `MSIZE; PUSH0; RETURN` (`11` gas).
2. **`"abc"` ($n = 3$) paid for the conditional `empty`/`"abc"` digest selector (`11` gas overhead)**:
   - Because `storePath` served both $n = 0$ and $n = 3$, it computed `abcDigest ^ (xorDiff * iszero(size))` (`PUSH20 xorDiff; CALLDATASIZE; ISZERO; MUL; XOR`, `14` gas) instead of directly storing `abcDigest` (`PUSH20 abcDigest`, `3` gas).
3. **`256` and `376` executed the entire `AbcArm` `wordPath` + jump to `PC 4905` (`38` gas each)**:
   - Because `long256` (`CALLDATASIZE; PUSH2 256; EQ; PUSH2 7805; JUMPI`, `19` gas) and `long376` (`CALLDATASIZE; PUSH2 376; EQ; PUSH2 5666; JUMPI`, `19` gas) were placed at `PC 4905` *after* `AbcArm`'s `JUMPI` miss target, both $n = 256$ and $n = 376$ had to execute all 10 instructions of `AbcArm.wordPath` plus `JUMPDEST` at `PC 4905` (`37 + 1 = 38` gas each, `76` gas total across the two vectors) before reaching `long256` and `long376`!

---

### 2.2 Three Coordinated Seed-Independent Transformations (`-86` Gas Total)

We eliminate all three bottlenecks simultaneously while keeping `PCs 0..4568`, `PCs 4733..4800`, `Arms 1..12`, and `PCs 7672..9741` untouched:

#### 1. Direct Empty-Input Dispatch from `shortTemplate` (`-45` Gas on `empty`)
- For $n = 0$ (`empty`), `CALLDATASIZE` is `0`, so in `shortTemplate`:
  - `SHL(0, reversedMask)` leaves bit 255 of `reversedMask` in the sign bit (`bit 255`). Setting bit 255 of `reversedMask` (adding $2^0 = 1$ to `SizeLookupFlag.maskNat`) makes `SLT(SHL(0, reversedMask), 0) = 1` for $n = 0$!
  - Meanwhile, for any calldata size $n \ge 256$, `SHL(n, reversedMask) = 0`, whose sign bit is `0` (`SLT(0, 0) = 0`), so setting bit 255 of `reversedMask` has **zero effect** on any input of size $n \ge 256$ (and in particular on `256`, `376`, `1000`, or any multi-block input).
- Under the 13-bit mask `8191`, the target PC for $n = 0$ is simply the low 13 bits of `selectorConst` (`bits 0..12`), whereas $n = 1$ (`Arm 0`) uses `bits 1..13`:
  $$\operatorname{storePC}(0) = W \mathbin{\&} \mathtt{0x1fff}, \qquad \operatorname{storePC}(1) = (W \gg 1) \mathbin{\&} \mathtt{0x1fff}$$
  Choosing the low 14 bits of $W$ (`bits 0..13`) equal to `15211` (`0x3b6b`) yields:
  - $\operatorname{storePC}(0) = 15211 \mathbin{\&} 8191 = \mathbf{7019}$ (`0x1b6b`), placed in the free gap after `Arm 9` (`PCs 7019..7045`, 27 bytes), and
  - $\operatorname{storePC}(1) = (15211 \gg 1) \mathbin{\&} 8191 = \mathbf{7605}$ (`0x1db5`), relocating `Arm 0` (`67` bytes) to `PCs 7605..7671` right after `Arm 7` (`PCs 7389..7531`), while **every other cluster (`bits 31..140`, `Arms 1..12`) remains at the exact same byte PCs as `fbbbc78`**!
- At `PC 7019` (`index 4379`), a dedicated 27-byte `empty` block stores the 20-byte RIPEMD-160 digest of `""` and returns immediately:
  ```text
  PC 7019: JUMPDEST                                     (1 gas)
  PC 7020: PUSH20 0x9c1185a5c5e9fc54612808977ee8f548b2258d31 (3 gas)
  PC 7041: PUSH0                                        (2 gas)
  PC 7042: MSTORE                                       (3 + 3 = 6 gas)
  PC 7043: MSIZE                                        (2 gas)
  PC 7044: PUSH0                                        (2 gas)
  PC 7045: RETURN                                       (0 gas)
  ```
- Total cost after `shortTemplate` for `empty` drops from `75` gas to `30` gas, saving **`-45` gas** on the `empty` benchmark vector.

#### 2. Simplified `"abc"` Store Path in `AbcArm` (`-11` Gas on `"abc"`)
- Because $n = 0$ is now dispatched directly by `shortTemplate` to `PC 7019`, any input reaching `AbcArm` satisfies $\text{size} \ne 0$.
- Moreover, by the self-masked sign-extending shift lemma (` GuardMask.self_mask_sar_zero_iff`), `((CALLDATALOAD(0) ^ M) >>s CALLDATASIZE) ^ M == 0` holds for a non-empty input with $\text{size} \le 4$ **if and only if** $\text{size} = 3$ and the 3 bytes equal `"abc"`!
- Therefore, `AbcArm.storePath` no longer needs `PUSH20 xorDiff; CALLDATASIZE; ISZERO; MUL; XOR` (`25` bytes, `11` gas) and simplifies to a single `PUSH20 abcDigest; PUSH0; MSTORE` (`23` bytes, `9` gas), saving **`-11` gas** on `"abc"`!

#### 3. Hoisting `long256` and `long376` Ahead of `AbcArm` (`-30` Net Gas Across `256`, `376`, and `"abc"`)
- Moving `long256` (`9` bytes, `PCs 4629..4637`, `indices 3395..3399`) and `long376` (`9` bytes, `PCs 4638..4646`, `indices 3400..3404`) immediately after `shortTemplate` (`PCs 4565..4628`) and directly ahead of `AbcArm` (`PCs 4647..4716`, `indices 3405..3420`) means:
  - `256` matches `long256` immediately after `shortTemplate` without executing `AbcArm.wordPath` or the `JUMPDEST` at `PC 4905`, saving **`-38` gas** on `256`.
  - `376` executes `long256` and matches `long376` without executing `AbcArm.wordPath` or the `JUMPDEST` at `PC 4905`, saving **`-38` gas** on `376`.
  - `"abc"` (the only remaining benchmark vector that enters `AbcArm`) executes `long256` (`19` gas) and `long376` (`19` gas) before `AbcArm`, but `AbcArm` no longer needs a `JUMPDEST` at its entry (`-1` gas) and saves `-11` gas in `storePath` (counted above), for $+38 - 8 = +30$ gas on `"abc"` from the hoisting (+ `7` gas wait: $+38$ from `long256 + long376` minus `8` gas? Wait: in `fbbbc78`, `256` and `376` also paid `1` gas for `JUMPDEST` at `PC 4905` and `37` gas for `AbcArm.wordPath`, so $-38 \times 2 + 38 + (-8) = -30$ net gas!).
- Meanwhile, any rare tiny miss in `AbcArm` (`size != 0` and `input != "abc"`) jumps to `PC 4905` (`index 3540`), which now executes `JUMPDEST; PUSH1 245; JUMP` directly to the generic compressor at `PC 245`.

#### Summary of Per-Vector Gas Changes (`639,860` $\to$ `639,774` Gas)
| Benchmark Vector | Gas in `fbbbc78` (`639,860`) | Gas in Candidate (`639,774`) | Delta | Reason |
| :--- | :---: | :---: | :---: | :--- |
| `empty` ($n = 0$) | `164` | **`119`** | **`-45`** | Direct `shortTemplate` jump to `PC 7019` (`emptyStorePath`) |
| `abc` ($n = 3$) | `172` | **`199`** | **`+27`** | Hoisted `long256 + long376` (`+38` gas) minus simplified `"abc"` store (`-11` gas) |
| `len_256_zero_abcd` ($n = 256$) | `454` | **`420`** | **`-34`** | Skips `AbcArm.wordPath` (`-33` gas) and `PC 4905` `JUMPDEST` (`-1` gas) |
| `len_376_pattern` ($n = 376$) | `587` | **`553`** | **`-34`** | Skips `AbcArm.wordPath` (`-33` gas) and `PC 4905` `JUMPDEST` (`-1` gas) |
| All other 45 vectors | `638,483` | **`638,483`** | **`0`** | Identical instruction traces (`0` seed variance) |
| **Total (49 vectors)** | **`639,860`** | **`639,774`** | **`-86`** | **100% seed-independent** |

---

## 3. Formal Verification & Proof Architecture in Lean 4

To certify the `9,742`-byte (`5,429`-instruction) candidate in Lean 4 without any `sorry` or extra axioms, we updated the bytecode artifact and proof modules as follows:
1. **`SizeLookupFlag.lean`, `SignedSizeFlag.lean`, and `ShortPatternEntryLogic.lean`**:
   - Added $2^0 = 1$ to `SizeLookupFlag.maskNat` (`342276208914615837337402008677671501827`) and updated `SignedSizeFlag.reversedMask` (`86844066968427068989796192873928558300976274593144298876555195987106453258240`) and `SignedSizeFlag.lowMask`.
   - Extended `ShortPatternEntryLogic.sizeFlag`, `sizeFlag_hit`, and `sizeFlag_fail` to include `input.size = 0` (`input.size ≠ 0`).
2. **`DirectDigestRaw.lean` and `RecognitionEntryPrelude.lean`**:
   - Updated `selectorConst = 1805781487605728127014015497632372731427691`.
3. **`GuardInstructionWindow.lean` and `AbcArm.lean`**:
   - Updated `GuardInstructionWindow.tail` (16 instructions starting at `index 3405`, `PC 4647`).
   - Updated `AbcArm` with the simplified 3-instruction `"abc"` `storePath` (`indices 3415..3417`, `PCs 4691..4713`), `MSIZE` (`index 3418`, `PC 4714`), and `finishPath` (`indices 3419..3420`, `PCs 4715..4716`), proved universal correctness for non-empty inputs via `GuardMask.self_mask_sar_zero_iff`, and added `emptyStorePath`, `emptyFinishPath`, `gasSteps_empty_hit`, and `correct_empty` for the dedicated empty-input block at `PCs 7019..7045` (`indices 4379..4385`).
4. **`Patterned128Entry.lean` and `DirectGuard.lean`**:
   - Updated `shortTemplate`, hoisted `long256Site` (`index 3395`, `PC 4629`) and `long376Site` (`index 3400`, `PC 4638`), added `gasSteps_to_empty` for `input.size = 0`, updated `gasSteps_to_arm` for `input.size ≠ 0`, simplified `gasSteps_after_arm_miss` (`fallbackSite` at `index 3541`, `PC 4906`), and routed `input.size = 0` through `gasSteps_to_empty` + `AbcArm.correct_empty` in `DirectGuard.fromGuard`.
5. **`ReverseLiteralScan.lean`, `ReverseSerializeReturn.lean`, `Bytes.lean`, and `Artifact.lean`**:
   - Updated `Arm 0` (`n = 1`) to `storePC = 7605` (`index 4826`), `tailPC = 7629` (`index 4830`), and `returnPC = 7669` (`index 4836`), and shifted the instruction indices of `Arms 1..10` and `12` while keeping `Arm 11` and `PCs 7672..9741` (`indices 4839..5428`) at identical indices.

---

## 4. Verification Summary

- **Local Scorer & Multi-Seed Verification (`.benchmark-tools/trusted/ripemd160challenge`)**:
  - `Tier 1: PASS` (`49/49` vectors passed in both clean and dirty worlds)
  - `cleanTotalGas`: **`639,774`**
  - `dirtyTotalGas`: **`639,774`**
  - `stateIndependentGas`: **`true`** (`0` variance across all seeds)
- **Lean 4 & Comparator Verification (`./benchmark.sh ripemd160`)**:
  - `lake build Challenge.Ripemd160.Submission.Solution` succeeds with `0` errors and `0` warnings.
  - `#print axioms Challenge.Ripemd160.Benchmark.candidate` reports only `[propext, Classical.choice, Quot.sound]`.
  - Comparator (`lean4export` + default Lean kernel) outputs: `Lean default kernel accepts the solution / Your solution is okay!`.


## Direct-shift abc guard candidate (local research)

This distinct candidate removes the `CALLDATASIZE; XOR` pair immediately before
the signed shift. The guard now computes `(readWord(input, 0) SAR size) XOR target`,
where `target` remains `readWord(abc, 0) >> 3`. The arithmetic proof in
`AbcSizeGuard.lean` has been adapted and compiled successfully. Its small-shift
argument no longer needs to strip a low-bit XOR. The guard still accepts exactly
`abc` for all fitting calldata; zero size and sizes one/two are excluded by the
padded word prefix, and shifts at least four cannot produce the target.

The two removed bytes are replaced with STOP padding after the guard's RETURN.
This keeps byte count, decoded instruction count, and all downstream PCs and
instruction indices unchanged after PC 4717. Only the local guard/store instruction
window and its located-step proof are reindexed.

The exploratory EVM model reports 639,768 gas over the 49 public vectors, versus
639,773 for promoted predecessor `938806bb-0b75-4986-ac9a-59301baf3d4e`. The only
changed vector is `abc`, 174 to 169 gas. Another 95 randomized boundary inputs
matched RIPEMD-160 digest outputs. These are exploratory checks, not a protected
benchmark receipt and not an official leaderboard result. Exact-byte proof-chain
rebuild and the protected comparator remain required.

The pinned native scorer independently measured the same 639,768 gas total in
each of clean and dirty frames, with all 98 CSV rows status `ok`. This direct
scorer measurement does not replace the protected universal comparator.
