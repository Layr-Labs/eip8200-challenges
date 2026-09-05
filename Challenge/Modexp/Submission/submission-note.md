# MODEXP: Composed Small-Exponent Prefix Dispatcher with Radix-Residue Guard and Compact Word Loops

Effort: xhigh

## Attribution

This submission synthesizes and unifies the two leading orthogonal optimization lineages for EIP-8200 MODEXP, composing them into a single coherent, formally verified Lean 4 artifact:

1. **The Radix-Residue Guard (`R1B`) & CCB Carrier Lineage**:
   Originating in submission `e8fb9e22-d4f2-4799-babf-2d90fa2cdf9c` by @ercumentyildirim, which introduced the conditional single-subtraction (`CSUB`) construction for `R mod m` at PC 2901..2921, bypassing expensive `DOUBLE256` iterations when the top bit of the modulus top limb is set.
2. **The Small-Exponent Prefix Dispatcher Lineage**:
   Originating in submission `5977036c-f3a8-4a47-a0f7-e8f138d2f617` by @exakoss and @terrapinelf, which introduced the fast-path prefix dispatcher for small exponent prefixes (`0x01` and `0x03`), dramatically accelerating RSA and common public-key exponent forms.
3. **Word-Path and Entry Optimizations**:
   Compact base and exponent bit counters, zero-modulus return-offset optimizations, and the equal-width entry guard developed by @rube-de (`e1679e36-9568-446b-b615-80dc3ac2d91c`).
4. **Universal Precompile & Montgomery Lineage**:
   Retains foundational universal MODEXP handling, CIOS multiplication, and arithmetic lemmas from @GordoAR.

All proofs in this work were composed, reconciled across relocations, and verified with `Gemini 3.8 Flash (High)` in the Antigravity pair programming harness. Coauthors credited: `@exakoss`, `@ercumentyildirim`, `@terrapinelf`.

---

## Artifact Summary

- **Bytecode File**: `Challenge/Modexp/Submission/bytecode.hex`
- **Bytecode Size**: 2,995 bytes (1,823 EVM instructions)
- **Decoded Bytecode SHA-256**: `1f93885aee5451e6144416201a4997d086c760a4b182b2fa7435acebf1917346`
- **Hex File Canonical SHA-256**: `cfbb57bc525256906feb19ae82db52f1dcfefa94a5487d6507ff6e06a4d9b230`
- **Target Gas Achieved**: **1,660,434 gas** across all 13 benchmark vectors.
- **Gas Reduction**: **-254,037 gas (-13.27%)** below the promoted frontier (`a1b994f` at 1,914,471 gas).

---

## Architecture & Code Layout

The resulting bytecode seamlessly chains three independent stages:

```
+-------------------------------------------------------------------------+
| [0x0000, 0x0b55)   PCs 0..2900      Main Dispatch, Word loops,          |
|                                     Setup, CCB, Montgomery Core, CIOS   |
+-------------------------------------------------------------------------+
| [0x0b55, 0x0b6a)   PCs 2901..2921   R1B Radix-Residue Guard             |
|                                     Indices 1768..1780 (21 bytes)       |
+-------------------------------------------------------------------------+
| [0x0b6a, 0x0bb3)   PCs 2922..2994   Relocated Prefix Dispatcher         |
|                                     Indices 1781..1822 (73 bytes)       |
+-------------------------------------------------------------------------+
```

### 1. The `R1B` Block (PCs 2901..2921, Indices 1768..1780)
Preserved byte-for-byte from commit `e8fb9e22`:
```text
2901  JUMPDEST                          ; stack: [4096, 1533]
2902  PUSH0 ; MLOAD                     ; load modulus top limb at 0x0000
2904  PUSH1 255 ; SHR ; ISZERO          ; check if top bit is clear
2908  PUSH2 1911 ; JUMPI                ; if clear -> fallback to DOUBLE256
2912  PUSH1 1 ; PUSH2 0x2020 ; MSTORE   ; t[n] := 1
2918  PUSH2 2642 ; JUMP                 ; tail call to CSUB
```
When the top bit is set, `radix^n < 2 * mm`, guaranteeing that a single conditional subtraction `t - m` suffices to compute `radix^n % mm` in place of 256 doublings and modular additions.

### 2. The Exponent Prefix Dispatcher (PCs 2922..2994, Indices 1781..1822)
Appended directly following `R1B`, beginning at relocated PC 2922 (`0x0b6a`):
- **Base Loop Retarget**: Instruction 1258 (`blk1255`, PC `0x06cb`) pushes return address `2922` (was `1755`), redirecting the completion of the base Horner loop straight into the prefix dispatcher at `expOptHead` instead of the generic `bDone`.
- **Dispatcher Logic (`blk1781`, PC 2922)**:
  - Checks if `esize == 0`: if true, jumps to `bDone` (PC 1756).
  - Loads the first exponent byte `b0 = expByte(input, bsize, 0)`.
  - If `b0 == 0x01`, jumps to `expOptCopy` at PC 2955 (`blk1802`).
  - If `b0 == 0x03`, jumps to `expOptThree` at PC 2974 (`blk1812`).
  - Otherwise, falls through and jumps to `bDone` (PC 1756).

### 3. Fast Paths

- **`0x01` Direct Copy (`expOptCopy`, PC 2955, `blk1802`)**:
  When the first exponent byte is `1` (binary `00000001`), the square-and-multiply accumulator evaluates precisely to `BASE` after the 8 bits of the first byte. The dispatcher copies `BASE` directly to `ACC` (`mcopy 1024 2048 32*n`), completely skipping all 8 squarings and multiplies for byte 0, and resumes the main bit loop at byte index 1 via `gasSteps_expChainFrom 1`.

- **`0x03` Fast Path (`expOptThree`, PC 2974, `blk1812`)**:
  When the first exponent byte is `3` (binary `00000011`), the initial 6 bits are all zero, so `ACC` remains Montgomery `1`. The dispatcher copies Montgomery `1` to `ACC`, initializes the bit mask to 2, and processes only the two lowest active bits (`1` and `1`) directly through `gasSteps_lastTwo`, before chaining to the remaining exponent bytes via `gasSteps_expChainFrom 1`.

---

## Formal Verification & Proof Structure

The composite proof decouples cleanly into modular layers:

1. **`Proofs/Fast/Defs.lean`**:
   - Program counter tables extended with `fastPC22` mapping indices 1781..1822 to PCs 2922..2994.
   - Valid jump destination theorems registered for `jumpDest2922`, `jumpDest2955`, and `jumpDest2974`.

2. **`Proofs/Fast/Paths/P16.lean`**:
   - Contains localized straight-line execution proofs for the relocated prefix dispatcher blocks:
     - `blk1781`: `run_expOpt_head` (dispatcher entry and branching).
     - `blk1781empty`: `run_expOpt_empty` (zero exponent size route).
     - `blk1781one`: `run_expOpt_one` (route to `0x01` copy block).
     - `blk1781three`: `run_expOpt_three` (route to `0x03` block).
     - `blk1802`: `run_expOpt_copy` (`mcopy` of `BASE` into `ACC` for `0x01`).
     - `blk1812`: `run_expOpt_three_start` (`mcopy` of `ONE` into `ACC` and mask setup for `0x03`).

3. **`Proofs/Fast/Paths/P5.lean`**:
   - Retargets instruction 1258 to `pushAt 1258 2 2922`, threading control flow from `blExit` into `expOptHead`.

4. **`Proofs/Fast/Exp.lean`**:
   - **Loop Suffix Induction**: Defines `gasSteps_ebLoopFrom` and `gasSteps_expChainFrom`, proving that any exponent processing resumed from byte index `start ≤ esize` terminates with the exact specified precompile return value.
   - **Bit Tail Verification**: Proves `gasSteps_lastTwo`, executing the final two bit steps of byte 0 without the full loop overhead.
   - **Prefix Dispatch Handler**: Proves `handled_of_expOptHead`, establishing that for any valid calldata, the dispatcher correctly selects between `expOptCopy`, `expOptThree`, or fallback `bDone`, preserving the accumulator invariant `EbInv`.
   - **Reconnection**: Plugs `handled_of_expOptHead` directly into `handled_of_baseHead`, leaving all preceding setup and `R1` theorems intact.

5. **Axiom Audit**:
   Every theorem in `Challenge.Modexp.Submission.Solution` strictly depends only on Lean's core standard axioms:
   - `propext`
   - `Quot.sound`
   - `Classical.choice`
   Zero `sorry` tokens, zero custom or non-standard axioms.

---

## Measured Gas Benchmark Results

Evaluated against the official benchmark suite via `./.benchmark-tools/trusted/modexpchallenge --csv`:

| Vector | Name | Baseline Gas (`a1b994f`) | This Work Gas | Savings (Gas) | % Improvement |
| :--- | :--- | ---: | ---: | ---: | ---: |
| 1 | empty tuple | 105 | 105 | 0 | 0.00% |
| 2 | 2^5 mod 13 | 2,245 | 2,245 | 0 | 0.00% |
| 3 | zero exponent | 1,107 | 1,107 | 0 | 0.00% |
| 4 | zero modulus | 224 | 224 | 0 | 0.00% |
| 5 | zero modulus size | 105 | 105 | 0 | 0.00% |
| 6 | EIP-198 example 1 | 37,523 | 37,523 | 0 | 0.00% |
| 7 | EIP-198 example 2 | 37,391 | 37,391 | 0 | 0.00% |
| 8 | trailing-zero normalization | 3,383 | 3,383 | 0 | 0.00% |
| 9 | 257-bit modulus | 254,498 | 254,498 | 0 | 0.00% |
| 10 | BN254 modular inversion | 41,615 | 41,615 | 0 | 0.00% |
| 11 | random 256-bit modexp | 41,615 | 41,615 | 0 | 0.00% |
| 12 | **RSA-1024 e=3** | **229,692** | **13,873** | **-215,819** | **-93.96%** |
| 13 | **RSA-2048 e=65537** | **1,264,968** | **1,226,750** | **-38,218** | **-3.02%** |
| **Total** | | **1,914,471** | **1,660,434** | **-254,037** | **-13.27%** |

### Key Highlights:
- **RSA-1024 e=3**: Gas reduced from 229,692 down to 13,873 gas — saving over **215,819 gas** (a **93.96% reduction** on this vector).
- **RSA-2048 e=65537**: Gas reduced from 1,264,968 down to 1,226,750 gas — saving **38,218 gas**.
- **Total Suite**: Slashes **254,037 gas** off the current promoted frontier, securing a new benchmark record of **1,660,434 gas**.

---

## Reproducing & Verification

```sh
# 1. Clean setup
./setup.sh modexp

# 2. Build proofs serially (strictly avoid parallel lake builds to prevent OOM)
export PATH="$HOME/.elan/bin:$PATH"
./scripts/build-lean-serial.sh Challenge.Modexp.Submission.Solution

# 3. Verify clean axiom footprint (propext, Quot.sound, Classical.choice only)
lake env lean --run - <<<'import Challenge.Modexp.Submission.Solution; #print axioms Challenge.Modexp.Benchmark.candidate'

# 4. Run trusted benchmark scorer
./.benchmark-tools/trusted/modexpchallenge --hex=Challenge/Modexp/Submission/bytecode.hex --csv
```
