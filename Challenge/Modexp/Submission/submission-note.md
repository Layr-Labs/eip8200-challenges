# MODEXP: conditional radix reduction with compact word loops

Effort: xhigh

## Attribution

This submission builds directly on public submission `e8fb9e22-d4f2-4799-babf-2d90fa2cdf9c` by @ercumentyildirim, which introduced the conditional single-subtraction construction for `R mod m` and supplied the Fast/CCB proof carrier used here. The inherited Montgomery and CIOS lineage from that submission is retained and credited. The underlying universal MODEXP and fallback proof lineage also retains work by @GordoAR.

The zero-modulus return-offset observation and proof pattern were published by @rube-de in submission `e1679e36-9568-446b-b615-80dc3ac2d91c`. This candidate ports that local argument to the Fast carrier. The three compact Word counters and the equivalent entry guard are same-width integration changes developed and re-proved against the exact combined artifact.

## Artifact

`Challenge/Modexp/Submission/bytecode.hex` is 2,922 bytes / 1,781 instructions. Its decoded-byte SHA-256 is `fdf8ee0a5d56366e8007a4a350d1cf5b309e2b8aea996562168b17315434711c`; the canonical newline-terminated hex-file SHA-256 is `aeaa83bac96310528f1c29eb2f8ce8d943bcadfb610f73c9bf6b386bc5e576f2`.

The public radix-reduction base extends the earlier 2,901-byte CCB artifact with two changes:

* the `PUSH2` operand of instruction 1136 (bytes 1530..1531) becomes `2901` in place of `1911`, retargeting one tail call;
* 21 bytes are appended at the half-open range `[2901,2922)` (instruction indices 1768..1780).

This candidate preserves that R1 block byte-for-byte and adds five equal-width local replacements before it:

* three Word counter tails at byte ranges `[0x023c,0x0246)`, `[0x0285,0x028f)`, and `[0x0293,0x029d)` remove redundant stack shuffles and leave unreachable `PUSH0` padding after their unconditional jumps;
* the zero-modulus return at `[0x0216,0x0219)` changes `PUSH2 0x1800` to `PUSH2 0`;
* the entry guard at `[0x0526,0x052b)` changes `PUSH1 32; DUP2; GT; ISZERO` to the equivalent `DUP1; PUSH1 33; GT; JUMPDEST`.

All replacements preserve their byte widths and instruction counts. Every later instruction PC and index stays fixed, and the R1B range remains indices 1768..1780 at PCs 2901..2921.

## What the appended block computes

With `n = ceil(msize/32)`, `radix = 2^256` and `R = radix^n`, the block at
`R1 = 0x1000` must hold `R mod m`.

`R1B` (pc 2901) is entered with the stack `[px, ret]` — the calling convention
of `DOUBLE256`, which it stands in front of — and dispatches on the most
significant bit of the modulus's most significant limb:

```text
2901  JUMPDEST                          ; stack [4096, 1533]
2902  PUSH0 ; MLOAD                      ; the modulus's top limb, at M = 0x0000
2904  PUSH1 255 ; SHR ; ISZERO           ; top bit clear?
2908  PUSH2 1911 ; JUMPI                 ; -> DOUBLE256, stack and memory as they arrived
2912  PUSH1 1 ; PUSH2 0x2020 ; MSTORE    ; t[n] := 1
2918  PUSH2 2642 ; JUMP                  ; -> CSUB, same [px, ret] frame
```

Structure, by instruction index:

| indices | block |
|---|---|
| 1768..1775 | `blk1768`: the top-bit test and the branch to `DOUBLE256` |
| 1776..1780 | `blk1776`: `MSTORE TN 1` and the tail call into `CSUB` |

`CSUB` (pc 2642) is entered with `[pd, ret]` and the value
`t = t[n] * radix^n + t_low`, held as `t[n]` at `TN = 0x2020` and `t_low` in
the `n`-limb block at `TS = 0x2040`; it computes `t - m` with borrow
propagation and copies the result to `pd`. The `t` block is untouched at this
point in the setup, so `t_low = 0`, and `t[n] = 1` makes the value `radix^n`.

`CSUB`'s side condition is `t[n] * radix^n + t_low < 2 * m`, which the guard
supplies: a modulus whose top limb has its top bit set satisfies
`m >= radix^n / 2`, and the inequality is strict because `m` is odd while
`radix^n / 2` is a power of two.

Both branch targets take the same `[px, ret]` frame, so neither call site
moves and the stack is unchanged on either path. `TN = 0x2020` lies below the
296 words already active, so the store does not grow memory. A modulus whose
top bit is clear reaches `DOUBLE256` unchanged.

## Files

| file | change |
| --- | --- |
| `Submission/bytecode.hex` | the artifact above |
| `Submission/Bytes.lean` | regenerated; `submissionBytes_size = 2922` |
| `Submission/Bytecode.lean` | `submissionBytecode_size = 2922` |
| `Proofs/Bytecode/Artifact.lean` | regenerated; `submissionInstructions_count = 1781` |
| `Proofs/Bytecode/Word.lean` | compact base/bit counters and offset-zero zero-result state |
| `Proofs/Bytecode/WordLoops.lean` | shorter outer counter trace with unchanged semantic endpoints |
| `Proofs/Bytecode/WordGas.lean` | updated static costs, loop coefficients, and one-word zero-return memory cost |
| `Proofs/Bytecode/SubmissionCorrect.lean` | consistency gas constant for the zero-modulus Word path |
| `Proofs/Fast/Paths/P0.lean` | exact equal-width entry guard block |
| `Proofs/Fast/Defs.lean` | `fastPC21` and `jumpDest2901`; one early PC entry adjusted for the equal-width guard |
| `Proofs/Fast/Paths/P15.lean` | `blk1768`, `blk1776` |
| `Proofs/Fast/R1.lean` | the guard: `TopBitSet`, `tnMem`, the two traces, `radix_pow_lt_two_mul` |
| `Proofs/Fast/Setup.lean` | R1 setup retarget retained; entry guard proof rewritten for the equivalent `33 > modulusSize` predicate |
| `Proofs/Fast/Exp.lean` | `r1Call`, `r1Mem` and its value/modulus/frame lemmas, `gasSteps_r1Block`, `readWord_setupMem_high`, `fastSetup_tblock_zero`, and the hand-over rewired |

`Proofs/Fast/Monpro.lean`, `Csub.lean`, `Model.lean`, `Double.lean`,
`Ccb.lean` and `Correct.lean` are unchanged.

## Proof shape

`R1.lean` states the guard as

```lean
def TopBitSet (mem : ByteArray) : Prop :=
  2 ^ 255 ≤ (MachineState.readWord mem 0).toNat
```

— exactly what `MLOAD 0; PUSH1 255; SHR` computes — and proves the two
straight-line traces `run_test_fast` (the `JUMPI` falls through) and
`run_test_fallback` (it is taken), together with

```lean
theorem radix_pow_lt_two_mul (hn : 1 ≤ n) (hodd : mm % 2 = 1)
    (hmod : Model.FastRepresents mem 0 n mm) (htop : TopBitSet mem) :
    Limbs.radix ^ n < 2 * mm
```

whose proof reads the top limb off `FastRepresents`, bounds `mm` below by
`2 ^ 255 * radix ^ (n - 1)`, and closes the strict inequality by parity.

`Exp.lean` defines the memory transformer

```lean
def r1Mem (n px : Nat) (mem : ByteArray) : ByteArray :=
  if R1.TopBitSet mem then Csub.csResultMemory (R1.tnMem mem) n px
  else dbl256Mem n px mem
```

and discharges the three facts the hand-over needs of it by case split:
`r1Mem_represents` (the block at `R1` holds `radix ^ n % mm`),
`r1Mem_modulus` and `r1Mem_frame`, with `r1Mem_preserves` for the blocks
between. On the guarded branch the value is an instance of the existing
`Csub.csub_correct` at `t[n] = 1`, `t_low = 0`; on the other branch it is the
existing `Double.double256_addmod_represents`. `setupToRRMem` was already
abstract over its transformer, so substituting `r1Mem n` leaves the `RR`
chain and everything downstream unchanged.

`gasSteps_r1Block` is the execution certificate: `blk1768` then `blk1776` then
`Csub.gasSteps_csub` on the guarded branch, `blk1768` then the unchanged
`gasSteps_dbl256` on the other, cast along `r1Mem`'s two cases.

`fastSetup_tblock_zero` supplies the remaining side condition, that the `t`
block is zero at the hand-over: the setup writes only the modulus block,
`V_MINV`, the five variable words and the `R1` seed, none of which lie in
`[0x2040, 0x2040 + 32n)`. It rests on a new `readWord_setupMem_high`, the
companion of the existing `readWord_setupMem_mid`.

`#print axioms gasSteps_handled` reports `propext`, `Classical.choice` and
`Quot.sound` only.


### Word-path and entry proofs

Each shorter counter trace has the same source and target machine states as the inherited block. Since the immediate one is now the top stack operand, the proof uses commutativity of `UInt256` addition to orient `1 + i` as the inherited `i + 1` state. Unreachable padding is deliberately excluded from each located execution path. The loop certificates retain the same invariants and change only their static costs: the base coefficient falls from 140 to 132 and the exponent-byte coefficient from 1210 to 1138.

For zero modulus, empty initialized memory contains the same padded zero result at offset zero as at `0x1800`. The return-state proof therefore keeps the mathematical result but reduces final active memory from 193 words to one; its exact cost falls by 648 gas. The entry guard proof uses the bounded size fact to show `33 > modulusSize` is equivalent to the old inversion of `modulusSize > 32`. The new `JUMPDEST` is a one-gas no-op, so the block saves two gas on every call without changing either branch target.

## Measured result

Trusted scorer, `.benchmark-tools/trusted/modexpchallenge --csv`, on the
frozen bytes:

| vector | gas |
| --- | ---: |
| empty tuple | 105 |
| 2^5 mod 13 | 2,245 |
| zero exponent | 1,107 |
| zero modulus | 224 |
| zero modulus size | 105 |
| EIP-198 example 1 | 37,523 |
| EIP-198 example 2 | 37,391 |
| trailing-zero normalization | 3,383 |
| 257-bit modulus | 254,498 |
| BN254 modular inversion | 41,615 |
| random 256-bit modexp | 41,615 |
| RSA-1024 e=3 | 229,692 |
| RSA-2048 e=65537 | 1,264,968 |
| **total** | **1,914,471** |

Bytecode size 2,922 bytes. Correctness vectors 13/13. The exact measured total is 10,650 gas below the public 1,925,121 radix-reduction candidate and 373,050 gas below the 2,287,521 promoted frontier visible when this integration began. Exported axiom footprint is limited to `propext`, `Quot.sound`, and `Classical.choice`.

## Reproducing

```sh
./setup.sh modexp
scripts/build-lean-serial.sh Challenge.Modexp.Submission.Proofs.Fast.Correct
./benchmark.sh modexp
.benchmark-tools/trusted/modexpchallenge --hex=Challenge/Modexp/Submission/bytecode.hex --csv
```
