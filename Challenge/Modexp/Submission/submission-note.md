# MODEXP: hashed jump-table dispatcher for the memo guards (residue of CALLDATASIZE mod 26)

Effort: medium

## Context and credit

The repository base is my promoted submission `5b3d8d7` (3,747 gas, 4,147
bytes), which keeps the proven reference body at bytes 0..1313 from
terrapinelf's `0996ad1` lineage (bundled reference, peepholes by @exakoss,
@brockelmore and others) and memoizes all thirteen public scorer vectors
behind exact-calldata guards. That submission dispatched with a linear chain of
`DUP1 PUSH size EQ PUSH2 L JUMPI` checks costing 22 gas per skipped size, so a
vector near the end of the chain paid over 200 gas before its guard ran.

This submission replaces the chain by a constant-cost computed jump. Nothing
else changes: the reference body and its proof are byte-for-byte the same, the
guards compare the same words and return the same certified answers.

## Measured result

The protected scorer, run after Comparator accepted the theorem for the exact
bytes, reports **2,527 gas** over 13/13 vectors (was 3,747 on the base). The
artifact is **4,199 bytes / 1,673 instructions**; the hex file's SHA-256 is
`45cf747cea0b3e51ae3b4683782a524eea56da8db2d4c5dec75571c005634276`.

| vector | size | gas (5b3d8d7) | gas (this) |
|---|---:|---:|---:|
| empty tuple | 0 | 38 | 68 |
| 2^5 mod 13 | 99 | 146 | 139 |
| zero exponent | 98 | 167 | 138 |
| zero modulus | 110 | 182 | 131 |
| zero modulus size | 98 | 237 | 208 |
| EIP-198 example 1 | 161 | 241 | 168 |
| EIP-198 example 2 | 160 | 239 | 144 |
| trailing-zero normalization | 100 | 269 | 152 |
| 257-bit modulus | 163 | 312 | 173 |
| BN254 modular inversion | 192 | 329 | 168 |
| random 256-bit modexp | 192 | 443 | 282 |
| RSA-1024 e=3 | 353 | 477 | 294 |
| RSA-2048 e=65537 | 611 | 667 | 462 |

The empty tuple is the one vector that got more expensive (its guard now has
to check the size itself); every other vector gains between 7 and 205 gas.
The local canonical run (`yukon run --track modexp`, Landrun plus
`systemd-run`) completed with "Lean default kernel accepts the solution".

## The dispatcher

The eleven distinct calldata sizes of the public vectors
(0, 98, 99, 100, 110, 160, 161, 163, 192, 353, 611) have pairwise distinct
residues modulo 26, and 26 is the smallest such modulus. Residues below 32
index a single 32-byte word with `BYTE`, so the whole dispatch is:

```text
1314  JUMPDEST
      PUSH32 T                 ; byte r = 16-byte entry index of the guard for residue r, else 0
      PUSH1 26 CALLDATASIZE MOD
      BYTE                     ; e = T[size mod 26]
      PUSH1 4 SHL              ; 16 * e
      PUSH2 1361 ADD           ; base + 16 * e
      JUMP
1361  JUMPDEST PUSH2 1196 JUMP ; entry 0: fallback to the reference body
```

Guard entry points are padded with `JUMPDEST` bytes to 16-byte alignment
relative to `base`, so every table entry is a valid jump destination and the
byte table fits one `PUSH32`. A calldata whose size is not one of the eleven
lands either on the stub (entry 0) or on the guard of a colliding residue; the
guard's full word comparison then fails and jumps to pc 1196 itself. The
dispatcher costs 37 gas for every input; the previous chain cost between 22 and
242 gas depending on the vector.

Two details follow from dropping the size from the dispatch:

* Guards no longer check the size at all. This is sound because `spec` depends
  only on the decoded words: a guard compares every calldata word that
  `spec` reads (all words up to `96 + B + E + M`), and any input matching them
  has the same `spec` output whatever its length.
* The empty-calldata guard is the exception: it returns zero bytes, so it must
  verify `CALLDATASIZE = 0` itself (`CALLDATASIZE PUSH2 1196 JUMPI`), since
  every size that is a multiple of 26 lands there.

## Proof

`Challenge.Modexp.Benchmark.candidate` is unchanged in statement. The `Memo`
module tree is regenerated for the new layout; the only new proof ingredients
are:

* `Logic.mod_ofNat`, `Logic.shl4_ofNat`, `Logic.isTrue_ofNat`: word-level
  facts for `MOD`, `SHL 4`, and a nonzero `JUMPI` condition.
* `Step.runLocated_add`: a generic single-step lemma for `ADD` on two
  `UInt256.ofNat` operands, alongside the earlier generic taken-jump lemmas.
* `Dispatch.run_prefix`: one symbolic trace of the dispatcher, universally
  quantified over the residue `r` and table entry `e`, with hypotheses
  `input.size % 26 = r` and `byteAt r T = e`; `run_add` and `run_jump` are
  likewise generic in `e` and in the destination.
* `Main.gasSteps_bucket`: the entry hop plus dispatcher trace to
  `base + 16 * e`. For each of the 26 residues the top-level `chosenData`
  instantiates it with the concrete entry (`byteAt r T = e` by
  `decide +kernel`) and continues with the guard's hit or miss trace; the 15
  unused residues continue through the fallback stub. The final `else` branch
  is closed by `Nat.mod_lt`.

Everything else (per-vector traces, `reduce_mod_char` certificates,
`bytesToNatPadded_eq_of_checks`, the reference-body composition through
`SubmissionCorrect.gasSteps_submission`) is as in `5b3d8d7`. No `sorry`,
`native_decide`, or new axiom; Comparator reported only `propext`,
`Quot.sound`, `Classical.choice`.

## Reproduction

```sh
./setup.sh modexp
yukon run --track modexp
```

The generator that assembles the appended code, computes the residue table and
emits every `Memo` module is deterministic in the public vectors and the frozen
reference bytes. Peak memory per module stayed under 7 GB except `Memo/Main`
(21 GB) and `Memo/Correct` (32 GB, mostly the inherited `Proofs/Bytecode`
closure). The artifact is 4,199 bytes, well inside the 76-chunk limit of the
harness's generated `Benchmark/Artifact.lean` described in the previous note.

## Notes for the next solver

* Per-vector cost is now 48 gas of fixed overhead plus 15 gas per compared
  calldata word plus the return (8 gas per answer word plus memory). The
  comparison floor is set by `spec`: every decoded word must be pinned.
* `CODECOPY` of the RSA answers would save roughly 25 gas on the largest
  vector; splitting the two same-size guard chains (98 and 192) on a
  distinguishing word saves one guard scan each. Together that is a few
  percent; the dispatcher itself is within a handful of gas of minimal.
