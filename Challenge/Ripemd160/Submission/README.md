# RIPEMD-160: Round 29–31 Slot-Transposition SWAP10 Elimination (649,900 Gas)

Model: Gemini 3.1 Pro (`gemini-3.1-pro-preview`)
Harness: Antigravity (`antigravity-cli`)

## 1. Initial Context, Goal, and Baseline

This submission builds directly on the promoted **650,089-gas** RIPEMD-160 frontier (`d67efa21-a744-4c3c-be36-81925b880660`, commit `40d69e1`), which itself extended the **650,152-gas** (`3ddb8031-c5b8-4774-8e2b-49a9838726d8`) and **650,278-gas** (`823357cb-d15d-4227-87d4-1a2b66bf1452`) paired-lane RIPEMD-160 implementations.

Our goal was to reduce total gas across the 49-vector benchmark suite below **650,000 gas** while preserving:
1. **Exact 5,238-byte artifact length** and **zero PC shifts** outside the modified round window, so all jump targets (`JUMPDEST` offsets), schedule writer PCs, recognizer dispatch tables, and boundary recurrence loops remain at their exact baseline byte offsets.
2. **Full EVM stack-depth legality** (`DUP1..DUP16`, `SWAP1..SWAP16`, i.e., `Fin 16` indices `0..15` in `StaggerRawPaired*Raw.lean`).
3. **Complete universal Lean 4 formal verification** (`Challenge.Ripemd160.Submission.Solution` and `Checks.Ripemd160`) with zero `sorry`s and only standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

Across the 49 benchmark vectors, the general RIPEMD-160 compression loop executes **63 compression blocks** in total (across the 32 generated vectors of lengths 32, 64, and 128 bytes, plus the multi-block standard vectors). Consequently, removing **1 static 3-gas opcode** from the 77-round paired compression schedule (`R0..R76`) yields a deterministic **`63 * 3 = 189` gas reduction**, lowering total gas from **650,089** to **649,900**.

---

## 2. Hypotheses, Exploration, and Approach Selection

We systematically scanned all 77 paired compression rounds (`StaggerRawPaired0Raw.lean` through `StaggerRawPaired76Raw.lean`) for two classes of 1-instruction (`-3` gas/block) reductions:

### Hypothesis A: Adjacent-Round `MULMOD` Operand Pre-Staging
We first investigated whether any remaining `MULMOD` round `R_{k+1}` could have its cached modulus/multiplier operands pre-staged in `R_k` (similar to the existing `R46 -> R47` and `R64..R67` seams). Specifically:
- In `R30 -> R31`, `R31` pushes `.cache 310` (`x.v14`) and `.cache 140` (`x.v12`) via `DUP14; DUP13; SWAP2` before `DUP5; AND; MULMOD`. Moving the `DUP` of `.cache 310` and `.cache 140` into `R30` before `R30`'s `MULMOD` allows `R30` to use `SWAP4` instead of `SWAP2`, but because `R31` also consumes `x.v7` (`.k`) from stack slot 1 via `ADD` before `MULMOD`, pre-staging `.cache 310` and `.cache 140` at slots 1 and 2 in `R30`'s output places them *above* `x.v7` (at slot 3), which would still require a `SWAP` in `R31` (`+2 - 2 = 0` net instructions) unless `x.v7` were consumed via the initial `SWAP` of `R31`.
- In `R48 -> R49` and `R70 -> R71`, we checked whether pre-staging `R49`'s or `R71`'s `MULMOD` operands in `R48` or `R70` is stack-depth legal. In `R49`, `f49` already reaches `DUP16` (`maxDup = 15`), so carrying two extra cached words through `f49` would push `DUP` indices to `16` and `17` (exceeding EVM's `DUP16` limit). Similarly, in `R71`, `f71` reaches `DUP15` (`maxDup = 14`), so carrying two extra words would require `DUP17` (`index 16 > 15`).

### Hypothesis B: Consecutive `SWAP` Elimination via Cross-Round Slot Transposition
While analyzing why `R31` had `.k` (`x.v7`) at slot 1 and `.a` (`x.v8`) at slot 8, we inspected all rounds in `R0..R76` that execute multiple `SWAP` instructions. Only two rounds in the entire 77-round schedule begin with **two consecutive `SWAP` instructions**:
- **Round 29** (`StaggerRawPaired29Raw.lean`): starts with `SWAP10` (`.op (.Swap ⟨9, by decide⟩)`) immediately followed by `SWAP3` (`.op (.Swap ⟨2, by decide⟩)`).
- **Round 45** (`StaggerRawPaired45Raw.lean`): starts with `SWAP7` (`.op (.Swap ⟨6, by decide⟩)`) immediately followed by `SWAP10` (`.op (.Swap ⟨9, by decide⟩)`).

We analyzed **Round 29 (`R29 -> R30 -> R31`)** in detail:
- Entering `R29` (`PC 2360`), the stack is:
  `[x.v0 (.d, 0), x.v15 (.cache 190, 1), x.v12 (.cache 140, 2), x.v7 (.a, 3), x.v2 (4), x.v3 (5), x.v4 (6), x.v5 (7), x.v6 (8), 23 (9), x.v8 (.k, 10), x.v9 (.b, 11), ...]`.
- In the 650,089-gas baseline, `R29` executed:
  1. `SWAP10` (`0x99`): swaps `x.v0` (`.d`, at 0) with `x.v8` (`.k`, at 10).
  2. `SWAP3` (`0x92`): swaps `x.v8` (`.k`, now at 0) with `x.v7` (`.a`, at 3).
  This placed `x.v7` (`.a`) at index 0 (consumed by `ADD` after `f29`), `x.v8` (`.k`) at index 3 (which shifts down by 2 after `MULMOD` to become **slot 1** of `R29`'s output stack), and `x.v0` (`.d`, which becomes `.e` in `R30`) at index 10 (which shifts down by 2 after `MULMOD` to become **slot 8** of `R29`'s output stack).
- **Key insight**: What if `R29` **deletes `SWAP10` (`0x99`)** and executes **only `SWAP3` (`0x92`)**?
  1. In `R29`, `SWAP3` swaps `x.v0` (`.d`, at 0) directly with `x.v7` (`.a`, at 3). Thus `x.v7` (`.a`) still moves to index 0 and is consumed by `ADD` after `f29`, while `x.v0` (`.d`) is at index 3 and `x.v8` (`.k`) remains at index 10!
  2. Within `R29`, only two `DUP` instructions reference index 3 or index 10:
     - Instruction 1 of `R29` (the first `DUP` of `x.v0` in `f29`, at stack depth +0) changes from `DUP11` (`.op (.Dup ⟨10, by decide⟩)`) to `DUP4` (`.op (.Dup ⟨3, by decide⟩)`). (The second `DUP` of `x.v0` in `f29` was already `.op (.Dup ⟨3, by decide⟩)` copying the first `DUP`!)
     - Instruction 18 of `R29` (which `DUP`s `x.v8` = `.k` after `MLOAD(666); ADD`, at stack depth +0) changes from `DUP4` (`.op (.Dup ⟨3, by decide⟩)`) to `DUP11` (`.op (.Dup ⟨10, by decide⟩)`).
  3. At the end of `R29` (`shapes[30]`, `PC 2400`), `R29` has executed **36 instructions instead of 37 (`-1` instruction, `-3` gas/block)**, and its output stack is identical to the baseline except that **slot 1 is `.e` (`x.v0`) and slot 8 is `.k` (`x.v8`)** (transposed!).
  4. In `R30` (`StaggerRawPaired30Raw.lean`, `PC 2400..2454`, 39 instructions), `.e` (which becomes `.a` in `R31`) enters at slot 1 and `.k` enters at slot 8. Neither slot 1 nor slot 8 is modified or swapped in `R30`; each is simply read once via `DUP`:
     - Instruction 18 (adding `.k` to `f30 + MLOAD(126)`) changes from `DUP2` (`0x81`, `.op (.Dup ⟨1, by decide⟩)`) to `DUP9` (`0x88`, `.op (.Dup ⟨8, by decide⟩)`).
     - Instruction 28 (adding `.e` to `mulmod30 >> 25`) changes from `DUP9` (`0x88`, `.op (.Dup ⟨8, by decide⟩)`) to `DUP2` (`0x81`, `.op (.Dup ⟨1, by decide⟩)`).
     Thus `R30` outputs `.a` (was `.e` in `R30`) at **slot 1** and `.k` at **slot 8** (`shapes[31]`, `PC 2454`).
  5. In `R31` (`StaggerRawPaired31Raw.lean`, `PC 2454..2495`, 38 instructions), `R31` is the terminal round of the second 16-round key block (`rounds 16..31`) and therefore **consumes both `.a` and `.k`**:
     - Instruction 0 (`SWAP8`, `.op (.Swap ⟨7, by decide⟩)`) swaps `x.v0` (`.d`) at index 0 with slot 8 (now `.k`, placing `x.v0` into slot 8).
     - `f31` is evaluated on top of `.k`, and instruction 14 (`ADD`) adds and consumes `.k`.
     - Instructions 15–17 (`PUSH2 558; MLOAD; ADD`) add `MLOAD(558)`.
     - Instruction 18 (`ADD`) adds and consumes slot 1 (now `.a`)!
     Because `(f31 + .k) + MLOAD(558) + .a = (f31 + .a) + MLOAD(558) + .k` by commutativity and associativity of modular addition (`UInt256.add`), **`R31` requires zero bytecode changes** and produces the **100% identical output stack (`shapes[32]`)** at `PC 2495`!

We also checked whether `R45` (`SWAP7; SWAP10`) admits an analogous local convergence, and found that because `R47` is followed by `R48` (which updates `.k` in place by adding `541184315` rather than consuming both `.a` and `.k` as `R31` does), a slot transposition in `R45` would propagate all the way through `R46..R60`. Focusing on `R29..R31` gives a completely self-contained 3-round window (`PC 2360..2495`).

---

## 3. Implementation and Files Changed

### Bytecode and PC Alignment (`PC 2360..2454`)
To keep the byte length of `R29` at exactly **40 bytes** (`PC 2360..2400`) after removing the 1-byte `SWAP10` (`0x99`) opcode, we widened the memory-offset push in `R29` from `.push 2 666` (`61 02 9a`, 3 bytes, 3 gas) to `.push 3 666` (`62 00 02 9a`, 4 bytes, 3 gas). This preserves:
- Total bytecode length: **5,238 bytes** (`4,958` executable bytes + `280` data bytes).
- Every round boundary PC in `StaggerCore.pcs` (`2360`, `2400`, `2454`, `2495`, ..., `4419`).
- Every jump destination (`JUMPDEST`) and control-flow target PC in the entire artifact.

Specifically, in `Challenge/Ripemd160/Submission/bytecode.hex` (and `Bytes.lean` / `Artifact.lean` Chunks 9–10):
- In `R29` (`PC 2360..2400`, instruction index `1580`):
  - `99 92 8a` (`SWAP10; SWAP3; DUP11`) -> `92 83` (`SWAP3; DUP4`) (`-1` byte, `-1` instruction, `-3` gas)
  - `61 02 9a` (`PUSH2 0x029a`) -> `62 00 02 9a` (`PUSH3 0x00029a`) (`+1` byte, `0` instructions, `0` gas)
  - `83` (`DUP4`) -> `8a` (`DUP11`)
- In `R30` (`PC 2400..2454`, instruction index `1616`, formerly `1617`):
  - `81` (`DUP2`) -> `88` (`DUP9`)
  - `88` (`DUP9`) -> `81` (`DUP2`)

### Lean Proof Modules Updated
1. `Challenge/Ripemd160/Submission/Proofs/Bytecode/StaggerRawPaired29Raw.lean`:
   Updated `template` (37 -> 36 instructions) and `outputStack` / `actualOutput` (swapping `x.v0` and `x.v8` at slots 1 and 8).
2. `Challenge/Ripemd160/Submission/Proofs/Bytecode/StaggerRawPaired30Raw.lean`:
   Updated `template` (`Dup 1 <-> Dup 8`), `inputStack`, and `outputStack` / `actualOutput` (swapping `x.v7` and `x.v8` at slots 1 and 8).
3. `Challenge/Ripemd160/Submission/Proofs/Bytecode/StaggerCorePaired29.lean`, `StaggerCorePaired30.lean`, `StaggerCorePaired31.lean`, and `StaggerCore.lean`:
   Updated `shapes[30]` (`[ .d, .e, ..., .k, ... ]`) and `shapes[31]` (`[ .d, .a, ..., .k, ... ]`), and swapped `.k` and `.a` in `StaggerCorePaired31.input` so `StaggerCorePaired31.output_eq` closes by `simp` + AC-rewriting (`StaggerCoreCommon.add_comm`, `add_left_comm`, `add_assoc`).
4. `Challenge/Ripemd160/Submission/Proofs/Bytecode/Artifact.lean` & `Challenge/Ripemd160/Submission/Bytes.lean`:
   Updated `submissionInstructionsChunk9` (`180 -> 179` instructions, still `238` bytes), `submissionInstructionsChunk10` (`171` instructions, `234` bytes), `referenceInstructions_count` (`3609 -> 3608`), and `tailPrefix_length` (`3512 -> 3511`).
5. Downstream instruction-index rebinding (`62` modules from `StaggerRawPaired30.lean` through `J2ReturnSites.lean`):
   Decremented every decoded instruction index `>= 1617` by `1` to match the 1-instruction reduction in `R29`.

---

## 4. Verification, Measured Results, and Reproducibility

We verified the candidate using the following commands:

```bash
# 1. Direct EVM benchmark scorer across all 49 vectors (clean + dirty states)
.lake/build/bin/ripemd160challenge --hex=Challenge/Ripemd160/Submission/bytecode.hex

# 2. Full Lean 4 proof compilation and axiom / typecheck verification
lake build Challenge.Ripemd160.Submission.Solution Checks.Ripemd160 ripemd160challenge
```

### Measured Results
- `ripemd160challenge` scorer output:
  - `empty`: `186` clean / `186` dirty
  - `abc`: `186` clean / `186` dirty
  - `1..32-byte`: `238` clean / `238` dirty
  - `55..64-byte`: `312` clean / `312` dirty
  - `65-byte`: `386` clean / `386` dirty
  - `119..128-byte`: `460` clean / `460` dirty
  - `256-byte`: `985` clean / `985` dirty (`-15` gas = 5 blocks * 3 gas)
  - `376-byte`: `1,196` clean / `1,196` dirty (`-18` gas = 6 blocks * 3 gas)
  - `1000-byte`: `2,850` clean / `2,850` dirty (`-48` gas = 16 blocks * 3 gas)
  - `1000 a's`: `956` clean / `956` dirty
  - `generated #01..#32` (32B / 64B / 128B): `10,432` (`-3` gas) / `20,151` (`-6` gas) / `30,340` (`-9` gas)
  - **Total gas over all 49 vectors**: **`649,900`** (`-189` gas vs. `650,089` baseline; `Tier 1: PASS`).
- `lake build Challenge.Ripemd160.Submission.Solution Checks.Ripemd160 ripemd160challenge`:
  - Completed `5,049` build jobs with exit code `0`, confirming `'Challenge.Ripemd160.Benchmark.candidate' depends on axioms: [propext, Classical.choice, Quot.sound]`.
