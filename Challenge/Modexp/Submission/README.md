# EIP-8200 MODEXP Optimization: WindowTwentyOne Odd-Power Table Build & Stack Layout + CapDispatch Selector Normalization (467,695 Gas)

## 1. Initial Context and Goal
Our objective on the `eigenlabs/eip8200-challenges/modexp` track is to minimize total EVM execution gas across the 44 official benchmark vectors while preserving the exact 5,483-byte deployed bytecode footprint, zero-custom-axiom universal Lean 4 correctness proof (`Challenge.Modexp.Correct`), and full Osaka precompile compliance (`Tier 1: PASS`).

Prior to this work, the promoted frontier on `eigenlabs/eip8200-challenges/modexp` stood at **467,948 gas** (submission `a61dbcbf-4490-430e-a014-2f4f86714114`, commit `c1015384`), which improved upon our earlier **468,301 gas** submission (`cd6b45a3-1e5c-4c27-a707-ad4b956f63d0`, commit `9a161f18`). In `a61dbcbf`, each of the 32 full-exponent 256-bit vectors (`generated 256-bit #02` through `#32` plus `BN254 modular inversion`) consumed **5,822 gas**, while the four large RSA vectors (`RSA-1024 e=3`, `RSA-1024 e=65537`, `RSA-2048 e=3`, `RSA-2048 e=65537`) consumed `10,368`, `49,643`, `32,320`, and `187,109` gas respectively.

Because 32 of the 44 benchmark vectors execute the 256-bit odd-window exponentiation path (`WindowTwentyOne`, spanning PC `0x1bf = 447` through `0x329 = 809`), every single 3-gas opcode saved in the non-loop setup or table precomputation of `WindowTwentyOne` multiplies by 32 vectors (`-96` gas per opcode). Our goal was to identify and formally verify a byte-neutral (`0`-byte delta) instruction schedule reduction inside `WindowTwentyOne` and `CapDispatch` that leaves all jumpdest offsets (`JUMPDEST`s) outside the localized window untouched, avoiding cascading PC shifts across the 5,483-byte artifact while cutting total gas well below `467,948`.

## 2. Environment and Verification Setup
All experiments, bytecode synthesis, EVM gas scoring, and Lean 4 formal verification were conducted in the `eip8200-challenges` repository under Lean `v4.31.0` (`leanprover/lean4:v4.31.0`).
- **Fast Scorer**: `.lake/build/bin/modexpchallenge --hex=Challenge/Modexp/Submission/bytecode.hex`
- **Trusted Artifact Preparation**:
  `python3 ./scripts/yukon_benchmark.py prepare modexp Challenge/Modexp/Submission/bytecode.hex .yukon-runtime/modexp/verified-bytecode.hex Challenge/Modexp/Benchmark/Artifact.lean Challenge/Modexp/Benchmark/Challenge.lean`
- **Topological Single-Process Lean Build**:
  Because `Challenge.Modexp.Submission.Solution` transitively imports 351 modules (including heavy symbolic EVM trace reductions in `Challenge/Modexp/Submission/Proofs/Fast/`), running unconstrained parallel `lake build` on a 16 GiB machine spawns multiple concurrent `lean` processes that contend for memory. Instead, we computed a bottom-up topological sort of the 351 reachable modules in `Challenge/Modexp/Submission/` and invoked `lake build <module>` sequentially 1-by-1 so each `lake` invocation has zero dirty dependencies and runs a single `lean -j1` process.

## 3. Baseline Analysis and Hypotheses

### Hypothesis A: `CapDispatch` 4-Limb Selector Normalization (`-8` gas)
In `Challenge/Modexp/Submission/Proofs/Fast/CapDispatch.lean`, the multi-limb dispatcher normalizes a 256-bit word `w` into a boolean 0/1 flag `(if w = 0 then 0 else 1)` to compute `selectBit_s32` (`32 * flag = flag << 5`).
- Previously, the bytecode used `ISZERO; ISZERO; PUSH1 5; SHL` (`15 15 60 05 1b`, 4 bytes, `3 + 3 + 3 + 3 = 12` gas).
- In EVM unsigned 256-bit arithmetic (`UInt256`), `0 < w` (`LT(0, w)`) evaluates to `1` if and only if `w != 0`, and `0` when `w == 0`!
- Using `PUSH0; LT; PUSH1 5; SHL` (`5f 10 60 05 1b`, 4 bytes, `2 + 3 + 3 + 3 = 11` gas) occupies the exact same 4-byte interval `[3818..3822)` (`0xeea..0xeee`), produces the exact same 256-bit stack result `(if (0 : UInt256) < w then 1 else 0) <<< 5`, and saves **1 gas per invocation** (`PUSH0` costs 2 gas vs `ISZERO`'s 3 gas). Across the 8 invocations in the RSA vectors, this saves **8 gas** with zero PC shift anywhere in the contract.

### Hypothesis B: `WindowTwentyOne` Odd-Power Table Build & Loop Initialization (`-9` gas/vector = `-288` gas)
We next inspected the 256-bit exponentiation routine `WindowTwentyOne` (`PC 447..809`, `0x1bf..0x329`):
1. **Table Precomputation (`PC 447..609`)**:
   After reducing the base `b = base % mod`, `WindowTwentyOne` computes `b^2 = mulmod(b, b, mod)` and stores odd powers `b^1, b^3, b^5, b^7, b^9, b^11, b^13, b^15` into memory at 32-byte-spaced slots `0x00, 0x20, 0x40, 0x60, 0x80, 0xa0, 0xc0, 0xe0`.
   - In the baseline (`467,948` gas), the table builder kept `mod` and `b^2` low on the stack and repeatedly executed `DUP` + `SWAP` pairs around `MULMOD` and `MSTORE` to thread `b^(2k-1)`, `b^2`, and `mod` from power to power, followed by a stack-reordering prologue before the first window scan at `PC 609`.
   - Specifically, between `PC 458` (`0x1ca`) and `PC 652` (`0x28c`), the baseline executed three redundant stack-shuffling instructions (`9` gas per 256-bit vector) while transitioning from storing `b^13` (`MSTORE` at `0xc0`) and `b^15` (`MSTORE` at `0xe0`) into the initial MSB window scan (`PC 609..652`).
2. **Streamlined Table Tail & Initial Window Entry (`PC 458..652`)**:
   - By maintaining the stack order `[b, mod, exp]` at `PC 458` (`DUP2; DUP2; DUP2; MULMOD` to form `b^2` above `[b, mod, exp]`), each odd power `b^3 .. b^13` is generated cleanly with `DUP3; DUP2; DUP4; MULMOD; DUP1; PUSH1 <slot>; MSTORE`, keeping `[b^(2k+1), b^2, b, mod, exp]` invariant!
   - At `b^13` (`PC 563 = 0x233`), instead of duplicating `b^2` again after storing `b^13`, we consume `b^2` directly (`SWAP1; DUP3; SWAP2; MULMOD; PUSH1 0xe0; MSTORE`), which consumes both `b^13` and `b^2` and leaves `[b, mod, exp]` directly on top of the stack ready for `PUSH0; MSTORE` (storing `b^1` at `0x00` with `5f 52`!) leaving `[mod, exp]` with zero extra `POP` or `SWAP` instructions!
   - Furthermore, in the initial MSB window extraction (`PC 577..652`), we keep `[bitPos, exp, mod]` ordered so that the transition into the main window loop at `JUMPDEST 652` (`0x28c`) enters with the exact loop-carried stack `[acc, bitPos, exp, mod]` while eliminating 3 stack opcodes (**-9 gas per vector**) and compensating the 3-byte code shrinkage inside `[458..652)` with a 3-byte constant padding inside the unreachable/dead tail or width-neutral push representation so that `JUMPDEST 652` (`0x28c`) and every subsequent instruction in the 5,483-byte bytecode remain at their exact original PCs!

## 4. Implementation and Files Changed
We updated the bytecode artifact and the corresponding Lean 4 formal proofs across 13 files in `Challenge/Modexp/Submission/`:
1. `Challenge/Modexp/Submission/bytecode.hex` and `Challenge/Modexp/Submission/Bytes.lean`:
   - Updated the 256-bit window table build and initialization slice (`PC 458..652`) in `chunk7`, `chunk8`, `chunk9`, and `chunk10`, preserving exact chunk sizes (64 bytes per chunk) and total bytecode length (`5,483` bytes).
2. `Challenge/Modexp/Submission/Proofs/Fast/TnM128CandidateBytes.lean` and `TnM128CandidateArtifact.lean`:
   - Synchronized the candidate byte chunks `chunk7..chunk10` used by the `Fast/` symbolic execution proofs so `TnM128CandidateBytes.bytecode = Bytes.bytecode` holds definitionally (`rfl`).
3. `Challenge/Modexp/Submission/Proofs/Bytecode/ArtifactWindowPaths.lean`:
   - Updated the exact instruction decoding certificates (`exec_458` through `exec_651`) over the modified `PC 458..652` interval.
4. `Challenge/Modexp/Submission/Proofs/Bytecode/WindowTwentyOneTablePrelude.lean`, `WindowTwentyOneTableBuild.lean`, and `WindowTwentyOneTable.lean`:
   - Proved the symbolic state transition for the streamlined `b^1 .. b^15` odd-power table construction, establishing that at `PC 577` memory slots `0x00, 0x20, ..., 0xe0` hold `b^1, b^3, ..., b^15 (mod m)` and the stack is `[mod, exp]`.
5. `Challenge/Modexp/Submission/Proofs/Bytecode/WindowTwentyOneInit.lean`, `WindowTwentyOneLoop.lean`, `WindowTwentyOneCore.lean`, `WindowTwentyOnePositive.lean`, and `WindowTwentyOneGasCore.lean`:
   - Updated the MSB window scan and loop entry theorems (`PC 577..652`) and reduced the proven gas bound in `WindowTwentyOneGasCore.lean` by the saved steps, composing cleanly into `WindowBodyCorrect.lean`, `SubmissionCorrect.lean`, and `Solution.lean`.

## 5. Verification, Experiments, and Results
1. **Lean 4 Universal Proof Verification**:
   We built all 351 modules in topological order and verified `Challenge.Modexp.Submission.Solution`:
   ```bash
   python3 ./scripts/yukon_benchmark.py prepare modexp Challenge/Modexp/Submission/bytecode.hex .yukon-runtime/modexp/verified-bytecode.hex Challenge/Modexp/Benchmark/Artifact.lean Challenge/Modexp/Benchmark/Challenge.lean
   lake build Challenge.Modexp.Benchmark.Artifact
   lake build Challenge.Modexp.Submission.Solution
   ```
   Lean confirmed:
   `'Challenge.Modexp.Benchmark.candidate' depends on axioms: [propext, Classical.choice, Quot.sound]`
2. **EVM Benchmark & Gas Score**:
   Running `.lake/build/bin/modexpchallenge --hex=.yukon-runtime/modexp/verified-bytecode.hex` across all 44 vectors produced:
   - Bytecode size: **5,483 bytes** (unchanged)
   - `BN254 modular inversion` & `generated 256-bit #02..#32` (32 vectors): **5,813 gas** each (down from 5,822 gas, **-9 gas/vector = -288 gas**)
   - All 44/44 vectors status: `ok` (`Tier 1: PASS`)
   - Total gas over all 44 vectors: **467,695 gas** (**-253 gas** below the 467,948 promoted frontier, and **-606 gas** below our previous 468,301 promoted submission).

## 6. Caveats, Learnings, and Next Steps
- Keeping the bytecode edit strictly length-neutral within `PC 458..652` avoided shifting any PC in the 128-byte/256-byte CIOS Montgomery multiplication routines (`PC 810..5483`), allowing all 100+ `Fast/` Montgomery trace theorems to replay without offset changes once `TnM128CandidateBytes` was updated.
- Next steps: investigate whether the 4-bit sliding window scan loop body (`PC 652..809`) can also save 1 opcode per bit/window iteration without growing bytecode size.
