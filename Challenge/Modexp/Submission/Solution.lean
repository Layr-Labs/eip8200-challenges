import Challenge.Modexp.Benchmark.Artifact
import Challenge.Modexp.Submission.Proofs.Bytecode.SubmissionCorrect

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000

namespace Challenge.Modexp.Benchmark

/-- Correctness of the submitted MODEXP bytecode.

Eight edits on top of the verified-compiler reference output, none of which
recompiles the Yul:

* the entry `PUSH2` is retargeted from the first compiler trampoline (pc 14)
  straight at the program body's `JUMPDEST`, collapsing the eight-hop
  trampoline chain to a single hop;
* the compiler's loop-increment idiom `PUSH1 1; DUP2; ADD; SWAP1; POP` is
  replaced at 18 sites by the equivalent `PUSH1 1; ADD`, with the three freed
  bytes parked after the following unconditional `JUMP` where they are
  unreachable;
* the exponent loop is replaced by true square-and-multiply;
* `mulModBig` is replaced by a flat double-and-add whose trip count is a
  scanned bound on the multiplier's bit length; and
* base conversion loads a *prefix* of the base directly instead of streaming
  every byte through two masked modular additions.  If the modulus's top limb
  (index `n - 1`) is nonzero then `modulus ≥ 2 ^ (256 * (n - 1))`, so the
  leading `32 * (n - 1)` base bytes already form a residue and are moved into
  place by the certified `loadBigEndian` helper; the remaining bytes still go
  through the original bitwise Horner loop.  The prefix length is computed
  branchlessly and capped at the base length, so it is `0` whenever the top
  limb is zero or the base is shorter than the prefix.  Keying the shortcut on
  the modulus's *limb contents* rather than on its declared byte length is what
  makes the prefix provably a residue.

Three further edits, developed independently against the merged frontier and
integrated here:

* `loadBigEndian` walks the destination one 256-bit limb at a time instead of
  one input byte at a time.  Limb `k` -- the word at `dst + 32 * k`, read with
  an ordinary big-endian `MLOAD` -- holds exactly the input bytes of
  significance `32 * k` through `32 * k + 31`, so for `k < len / 32` it is
  precisely `calldataload(off + len - 32 * (k + 1))`, and the single partial
  top limb, when `r = len % 32` is nonzero, is `calldataload off >> (8 * (32 -
  r))`.  The cursor and source pointer are carried as `at` and `K - at` in the
  256-bit ring.  `CALLDATALOAD` zero-pads past `calldatasize()` exactly as the
  reference's per-byte `byte(0, calldataload (off + i))` did, so short, absent
  and past-the-end calldata need no side condition, and the write is still an
  `or`-write, so the set of memory words touched is unchanged;
* `addMaskedMod` fuses the reference's three `n`-limb loops (add, subtract into
  the `0x1400` scratch buffer, branchless blend) into one always-taken pass that
  accumulates both the carry and the borrow, followed by a *branch*: the
  limb-serial subtraction runs only when `useSub = or(carry, iszero borrow)`
  holds, and recomputes the difference in place, so the scratch buffer is never
  written.  `useSub` is bit-for-bit the reference's, so the `Nat`-level
  justification is the reference's too.  Fusing is sound because at every call
  site the modulus buffer (`0x0000`) is disjoint from the destination
  (`0x0400`, `0x0800`, `0x1000`, `n ≤ 32` limbs), which is exactly the
  `hdstModulus` hypothesis `addReturned_represents_mod` already carried;
  aliasing of `src` with `dst` in the doubling call is unaffected, since the
  read order of `src` relative to the `dst` writes is the reference's; and
* the one-word path `modexpWord` reduces the base a whole 32-byte word at a
  time by Horner in radix `2 ^ 256` -- the radix residue being
  `addmod (mod (not 0) m) 1 m` -- then tabulates `T k = base ^ k mod m` for
  `k < 16` in `[0x0000, 0x0200)` and consumes the exponent one byte at a time
  as two 4-bit windows, four squarings and one table multiply each.  `T 0` is
  `mod 1 m` rather than the literal `1`, so a zero exponent against `m = 1`
  still returns `0`.  The table shares `[0x0000, 0x0200)` with the big path's
  modulus buffer; the two are safe only because the paths are mutually
  exclusive, which the block lemmas establish by showing that every exit from
  this region is a `RETURN` or a hand-off to the unchanged block at `0x029d`,
  never a re-entry into the dispatcher.

The first two edits are semantics-preserving and keep every byte offset. The
other six change behaviour, so each neutralizes its region in place with
`JUMPDEST; PUSH2 <appended>; JUMP` plus unreachable filler padded to exactly
the original byte *and* instruction count, and appends the replacement past
the end of the program. Every instruction index below the appended code is
therefore unchanged, and every jump target still resolves. Those six edits make
gas depend on operand values -- on the exponent, the multiplier, the modulus
and the base -- so this artifact deliberately has no value-independent gas
bound; `Correct` needs only that a trace exists. -/
theorem candidate : Challenge.Modexp.Correct bytecode := by
  change Challenge.Modexp.Correct Challenge.Modexp.submissionBytecode
  exact Challenge.Modexp.Submission.Proofs.Bytecode.SubmissionCorrect.submission_correct

end Challenge.Modexp.Benchmark
