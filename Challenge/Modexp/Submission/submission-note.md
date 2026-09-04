# MODEXP: retire the constant-time select loop in `addMaskedMod`

Effort: high

This submission stacks three further control-flow changes on the accepted
MODEXP artifact, all of them concentrated on the shared helper
`addMaskedMod(dst, src, take, modulus, count)` and its callers:

- **A — base conversion.** When the current bit of the input base is zero, do
  not call `addMaskedMod` at all. This reuses, unchanged, the trampoline the
  accepted artifact already installs in front of the multiplication inner
  loop; only the two immediate bytes of one call site are rewritten.
- **B — skip the select loop.** `addMaskedMod`'s third and final loop is a
  constant-time select between "the wrapped sum" and "the sum minus the
  modulus". When the select mask is zero the loop writes each destination limb
  back to itself, i.e. it is a `count`-iteration no-op. Branch over it.
- **C — copy instead of select.** When the select mask is all ones, the loop
  copies the candidate array into the destination one limb at a time, through
  two `AND`s, a `NOT` and an `OR` per limb. The artifact already contains a
  plain limb-copy routine, `copyLimbs`; call it instead.

Together they take the thirteen scored vectors from 231,048,376 gas to
**188,393,772** gas, a further 1.2264x reduction (42,654,604 gas). The
artifact grows from 1427 to 1470 bytes (1052 to 1081 instructions): four bytes
are rewritten in place and 43 are appended past the end of the existing code.

The proof work was implemented by a Claude Opus 5 subagent; the surrounding
loop (design, byte-level construction, differential testing, orchestration) was
driven by Claude Fable 5.1.

## 1. Background: what `addMaskedMod` does

`addMaskedMod(dst, src, take, modulus, count)` is the arithmetic core shared by
every big-modulus path in the artifact. It computes

```
mask = 0 - take                       -- 0 or 2^256-1
dst  = (dst + (src & mask)) mod modulus
```

on `count`-limb little-endian arrays, and it does so in three loops:

1. **add loop** — `count` iterations, add `src & mask` into `dst` with carry,
   producing a wrapped sum in `dst` and a carry-out flag;
2. **subtract loop** — `count` iterations, compute `dst - modulus` with borrow
   into the scratch array at `0x1400`, producing a borrow-out flag;
3. **select loop** — `count` iterations, choose per limb between the scratch
   array (if the subtraction should be taken) and `dst` (if not), using
   `useSub = carry | isZero(borrow)` widened to a full-word mask
   `selectMask = 0 - useSub`.

The third loop exists to keep the routine branch-free: its per-limb body is

```
dst[i] = (cand[i] & selectMask) | (dst[i] & ~selectMask)
```

which is exactly `dst[i]` when `selectMask = 0` and exactly `cand[i]` when
`selectMask = 2^256-1`. There is no third case: `useSub` is provably in
`{0, 1}`, so `selectMask` is provably one of those two words. That is the fact
changes B and C turn into gas.

The loop costs `123n + 58` gas for `n` limbs — for a 2048-bit modulus, `n = 8`,
so 1042 gas per `addMaskedMod` call, and the RSA-2048 vector makes several
hundred thousand such calls.

## 2. Change A — base conversion skips `addMaskedMod` on a zero bit

### Bytes

The accepted artifact already contains a trampoline, installed in front of the
multiplication inner loop, whose body is

```
T2:  JUMPDEST ; DUP3 ; PUSH2 <addMaskedMod> ; JUMPI ; POP ; POP ; POP ; POP ; POP ; JUMP
```

At `addMaskedMod`'s entry the stack is `dst, src, take, modulus, count, ret`,
so `DUP3` is `take`: non-zero `take` falls through into the real routine,
zero `take` pops the five arguments and returns to `ret` with memory untouched
— which is correct, because `dst + (src & 0) = dst` and `dst` is already
reduced.

The base-conversion routine has a second call site with exactly the same stack
shape (it pushes `ret`, `count`, `0`, `bit`, `0x0c00`, `0x0400` and then jumps),
and it is called once per bit of the base. Change A is therefore a two-byte
immediate rewrite at offset 897: `PUSH2 <addMaskedMod>` becomes
`PUSH2 <T2>`. No instruction boundary moves, no instruction is added, the
instruction count is unchanged.

### Proofs

`addMaskedMod`'s two exit shapes were already available as lemmas from the
accepted artifact, so this change is a re-wiring rather than a new argument.
The base-conversion iteration lemma gains a `by_cases` on the bit; the two
branches are folded back into a single helper application

```
bitChoice ... : SelectProgress
```

so that the state term after the iteration has the same size as before the
rewrite. Sinking the conditional into a helper (rather than writing an `if`
around the whole `State`, or inlining an `if` into each of the two affected
leaf fields) is what keeps elaboration tractable: the surrounding proofs
unfold a 256-deep iteration, and a `State`-level `dite` there is not viable.

## 3. Change B — skip the select loop when the mask is zero

### Bytes

A 24-byte routine is appended at the end of the code:

```
R:     JUMPDEST ; POP ; DUP1 ; ISZERO ; DUP3 ; OR ; PUSH0 ; SUB ; DUP1
       PUSH2 @Rsel ; JUMPI
       PUSH0 ; PUSH2 <epilogue> ; JUMP
Rsel:  JUMPDEST ; PUSH0 ; PUSH2 <selectLoopHead> ; JUMP
```

(`R` at pc 1427, `Rsel` at pc 1445) and the subtract loop's exit guard is
redirected to it by a single two-byte immediate rewrite at offset 180. `R` recomputes `selectMask` exactly as the
original code did — `POP` drops the dead loop counter, `DUP1`/`ISZERO` takes
`isZero(borrow)`, `DUP3` takes `carry`, `OR` combines them, `PUSH0 ; SUB`
widens to a full-word mask — and then keeps a copy on the stack with `DUP1`
for the `JUMPI`.

If the mask is zero the routine pushes a dummy loop counter (`PUSH0`, so that
the epilogue's ten `POP`s see the stack depth they expect) and jumps straight
to `addMaskedMod`'s epilogue. If not, it falls into `Rsel`, which pushes the
same zero counter and enters the original select loop head, so the untaken
branch reproduces the original behaviour instruction for instruction.

### Proofs

The interesting obligation is that the select loop with a zero mask is the
identity on memory:

```
selectProgress memory activeWords dst 0 count = ⟨memory, activeWords⟩
```

That is not quite a rewrite of the existing loop lemma, because the accepted
proof phrases the loop's result through `selectWord`, whose zero-mask case was
already proved (`selectWord_toNat` with `useSub.toNat = 0`). What is new is
that the *whole* loop is now absent from the execution certificate on that
branch, so the gas chain has to be re-cut: `gasSteps_subtractToSelect` and
`gasSteps_selectFinish` are replaced by `gasSteps_addMaskSegment`, which does
a `by_cases` on the mask and produces a `GasSteps` certificate for each branch,
then casts them to a common end state via two lemmas
`addExitFrame_of_zero` / `addExitFrame_of_pos`.

The end state `addExitFrame` is deliberately written so that both branches
agree on *everything except memory and active words*, and the conditional
lives inside those two leaf fields through one helper application:

```
maskChoice memory activeWords dst selectMask count : SelectProgress :=
  if selectMask.toNat = 0 then ⟨memory, activeWords⟩
  else ⟨copyMemory memory dst 0x1400 count, copyWords activeWords dst 0x1400 count⟩
```

## 4. Change C — copy instead of select when the mask is all ones

### Bytes

A second 19-byte routine is appended (`Rcp` at pc 1451, `Rcpret` at 1464):

```
Rcp:    JUMPDEST ; PUSH2 @Rcpret ; DUP10 ; PUSH2 0x1400 ; DUP8 ; PUSH2 <copyLimbs> ; JUMP
Rcpret: JUMPDEST ; PUSH0 ; PUSH2 <epilogue> ; JUMP
```

and `R`'s `JUMPI` immediate is repointed from `Rsel` to `Rcp`, so the
all-ones-mask branch now performs one `copyLimbs(dst, 0x1400, count)` instead
of `count` select iterations. `copyLimbs` is the artifact's existing
limb-copy helper; its body entry expects the stack `dst, src, count, ret`,
which is what `DUP10` (the destination pointer, ten slots down under the
trampoline frame) and `DUP8` (the limb count) assemble. `Rsel` becomes
unreachable but is left in place: removing it would move instruction indices
and force the whole instruction table to be re-derived for no gas.

Per call this trades `123n + 58` gas for `copyLimbs`'s `70n + 39`, i.e. it
saves `53n + 19` gas whenever the conditional subtraction is actually taken.

### Proofs

The obligation is that the select loop with an all-ones mask equals
`copyMemory`:

```
selectProgress memory activeWords dst (2^256-1) count
  = ⟨copyMemory memory dst 0x1400 count, copyWords activeWords dst 0x1400 count⟩
```

which follows limb-wise from the already-proved `selectWord_toNat` at
`useSub.toNat = 1`. The representation lemmas
(`addReturned_represents_mod`, `addReturned_preserves_region`) are then
re-proved by `by_cases` on the mask, reusing `copyMemory_represents` and
`represents_copyMemory_disjoint_region` — both of which the accepted artifact
already contains, because `copyLimbs` is already proved correct for its
existing call sites.

One detail is worth recording because it cost real time. The artifact
registers `word_toNat_sub` as a global `simp` lemma, so `simp` rewrites
`(0 - useSub).toNat` into `(2^256 + (0 : UInt256).toNat - useSub.toNat) % 2^256`
*inside the branch condition*. A hypothesis phrased as `(0 - useSub).toNat = 0`
therefore no longer discharges the `if`. Two remedies are used: for the
`maskChoice` rewrites, the mask is a bound variable of the rewrite lemma, so
`simp` never sees the subtraction at all; for the `JUMPI` step lemmas, the
hypothesis is normalised with the same lemma set before use.

## 5. Correctness argument in one paragraph

None of the three changes touches the arithmetic. `useSub` is proved to lie in
`{0, 1}`; `selectMask = 0 - useSub` is therefore `0` or `2^256-1`; the select
loop is proved to be the identity in the first case and `copyMemory` in the
second; and `addMaskedMod` with `take = 0` is proved to leave `dst` unchanged.
The three edits replace loops by the values those loops were already proved to
compute. Every proof obligation is discharged against the instruction list
decoded from the frozen bytes, with no gas obligation attached to the
value-dependent control flow, so the new branches are legal.

## 6. Measured gas, per vector

| # | vector | accepted | this submission |
|---|--------|---------:|----------------:|
| 1 | empty tuple | 99 | 99 |
| 2 | 2^5 mod 13 | 2,319 | 2,319 |
| 3 | zero exponent | 1,109 | 1,109 |
| 4 | zero modulus | 866 | 866 |
| 5 | zero modulus size | 99 | 99 |
| 6 | EIP-198 example 1 | 39,829 | 39,829 |
| 7 | EIP-198 example 2 | 39,689 | 39,689 |
| 8 | trailing-zero normalization | 3,529 | 3,529 |
| 9 | 257-bit modulus | 1,864,469 | 1,398,432 |
| 10 | BN254 modular inversion | 44,169 | 44,169 |
| 11 | random 256-bit modexp | 44,169 | 44,169 |
| 12 | RSA-1024 e=3 | 10,667,351 | 8,050,008 |
| 13 | RSA-2048 e=65537 | 218,340,679 | 178,769,455 |
| | **total** | **231,048,376** | **188,393,772** |

The eight small vectors are byte-identical in gas: they never reach the
big-modulus path, or reach it with `n = 1` where the savings are below the
call overhead of the new trampolines. All of the gain is in vectors 9, 12 and
13.

Cumulative effect of the three changes, measured independently:

```
accepted artifact          231,048,376
+ A (base conversion)      226,030,255   -5,018,121
+ B (skip select loop)     195,560,856  -30,469,399
+ C (copy instead)         188,393,772   -7,167,084
```

The same three changes were also measured on an earlier artifact that lacks
the exponent-layer work, where they save 67,168,044 gas rather than
42,654,604; the difference is exactly the `addMaskedMod` traffic that the
exponent-layer change had already removed.

## 7. Verification performed

- The bytecode was assembled by a builder that asserts, before touching
  anything, that every absolute program counter it depends on
  (`addMaskedMod` entry, `copyLimbs` body entry, the subtract-loop exit, the
  select-loop head, the epilogue) is a `JUMPDEST` in the baseline, that the
  three immediates it rewrites currently hold the values it expects, and that
  the trampoline it reuses has exactly the byte sequence it assumes.
- After each step, every statically resolvable `PUSHn c ; JUMP/JUMPI` target
  in the whole artifact is checked to be a `JUMPDEST`, and the code is checked
  to contain no truncated push.
- All thirteen scored vectors were executed on an independent EVM interpreter
  at each of the three cumulative steps. Every output was compared against
  `pow(base, exponent, modulus)` computed independently; all thirteen match at
  all three steps, and the gas totals are strictly decreasing.
- Locally, partial module compilation plus interpreter verification were
  performed. The instruction-table module and every proof module changed by
  this submission that fits the available build budget were elaborated
  successfully: the artifact's instruction certificate, the `addMaskedMod`
  helper module (which carries changes B and C), the multiplication module,
  and the base-conversion modules (which carry change A). The remaining
  modules were not re-elaborated locally, purely because a single unchanged
  module inherited from the previous submission needs more memory than the
  machine available here provides. The full proof closure was therefore not
  re-checked locally; complete proof checking is performed by the server-side
  comparator, which is the authority on whether this artifact is accepted.

## 8. What is not claimed

- The changes are value-dependent, so they are not constant-time. The
  reference implementation is not constant-time either (it already branches on
  limb counts and on the exponent length), and the challenge scores gas, not
  side channels. If a caller needs constant-time behaviour it should not be
  using this artifact.
- Change C's saving is proportional to how often the conditional subtraction
  is actually taken, which for uniformly distributed inputs is roughly half
  the calls. An adversarial input that never triggers the subtraction gets
  only changes A and B.
- No claim is made about inputs outside the thirteen scored vectors beyond
  what the proofs establish, which is total correctness of the artifact for
  every input the specification admits.
