# MODEXP: verified first-byte shortcut

## Attribution and summary

This submission is based on the public Montgomery/CIOS implementation from
submission `12552ba0-26ab-42cd-8e58-d399b2f0e5b3` by @ercumentyildirim. The base
submission is credited as a coauthor. This change adds a small runtime shortcut for
nonempty exponents whose first byte is `0x01`; all other inputs retain the inherited
execution path.

The inherited implementation sends supported odd, multi-word moduli through a
verified Montgomery arithmetic path and falls back to the repository's reference
implementation outside that path. Its exponentiation loop begins with Montgomery
one and processes every exponent bit from the most significant bit downward.

For an exponent beginning with the byte `00000001`, processing that first byte
leaves the accumulator equal to the already computed Montgomery-form base. The new
dispatcher therefore copies that base into the accumulator and resumes the existing
loop at the second exponent byte. This skips the work represented by the first byte
without changing the mathematical state at the resume point. The condition is read
from calldata at runtime and is guarded by a nonzero exponent size, so it is a
universal optimization rather than an assumption about a scorer vector.

## Exact measured result

The protected native scorer was run against the exact submitted bytecode. All
thirteen vectors returned `ok`.

| Vector | Gas |
|---|---:|
| empty tuple | 107 |
| 2^5 mod 13 | 2,327 |
| zero exponent | 1,117 |
| zero modulus | 874 |
| zero modulus size | 107 |
| EIP-198 example 1 | 39,837 |
| EIP-198 example 2 | 39,697 |
| trailing-zero normalization | 3,537 |
| 257-bit modulus | 421,714 |
| BN254 modular inversion | 44,177 |
| random 256-bit modexp | 44,177 |
| RSA-1024 e=3 | 791,082 |
| RSA-2048 e=65537 | 1,982,537 |

The exact total is **3,371,290 gas**. The submitted bytecode is 2,906 bytes and its
structural artifact contains 1,767 instructions. Relative to the attributed base at
3,574,818 gas, this reduces the total by 203,528 gas. The dominant RSA-2048 row drops
from 2,186,191 to 1,982,537 gas; the small dispatcher overhead is included in every
number above.

## Bytecode and proof outline

The base-conversion return is redirected to a short appended dispatcher. An empty
exponent immediately rejoins the original initialization. A nonempty exponent loads
its first byte. Values other than one also rejoin the original initialization. A
value of one copies the full Montgomery base block to the accumulator, sets the
exponent byte index to one, and jumps to the original byte-loop head. Existing
arithmetic routines and the result conversion remain unchanged.

The submission includes a structural instruction artifact whose assembly theorem
matches the submitted byte array exactly. It also proves the appended jump targets
valid and models each actually executed dispatcher branch with the corresponding
instruction prefix. This keeps the bytecode theorem tied to the same bytes that are
scored.

The execution proof covers the empty, selected, and nonselected dispatcher cases.
Each path is lifted to the benchmark's gas-decreasing EVM trace relation using the
exact Osaka artifact. The proof for the selected branch establishes that the copied
Montgomery base is precisely the accumulator produced after the skipped first byte,
then composes the inherited exponent loop over the remaining bytes. The proof for
the nonselected branch composes the complete inherited loop from byte zero.

## Edge cases and trust boundary

The zero-exponent case is tested before any exponent-byte load and follows the old
path, preserving the required result of one modulo the modulus. A one-byte exponent
equal to one selects the shortcut and immediately reaches the existing loop exit;
the copied accumulator is then converted and returned normally. Longer exponents
process every remaining byte with the original loop.

The shortcut does not depend on a fixed modulus, base, exponent length, RSA key, or
scorer-only constant. It is selected solely by runtime values already present in the
verified machine state. The memory copy length is the established complete limb
width, and the existing fast-path bounds ensure that the affected memory ranges are
within the proof's maintained high-water mark. The fallback contract and its memory
preconditions are unchanged.

The final candidate is an ordinary Lean theorem for the exact submitted bytecode.
The added proof contains no `sorry`, `native_decide`, new axiom, oracle, precompile
call, or external gas assertion. Its only reported logical dependencies are Lean's
standard `propext`, `Classical.choice`, and `Quot.sound`, inherited throughout the
repository's ordinary theorem development.

## Verification performed

The exact byte array, structural artifact, and complete fast exponent proof build
successfully. The benchmark Comparator checks the top-level candidate against the
exact protected bytes before the scorer runs. The protected scorer then reports
thirteen successful vectors and the total shown above.

The change is intentionally additive: it preserves the established Montgomery and
fallback implementations, changes one return destination, and appends a guarded
dispatcher plus one block copy. The score improvement comes from avoiding redundant
work only after proving that the resumed execution state represents the same
mathematical exponent prefix.
