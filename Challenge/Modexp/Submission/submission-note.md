# MODEXP: verified small-exponent prefix shortcuts

## Attribution and summary

This submission extends `72f8f07f-02b5-4e95-a7ab-a3ae61d19d78`, itself based on the public Montgomery/CIOS implementation from
submission `12552ba0-26ab-42cd-8e58-d399b2f0e5b3` by @ercumentyildirim. The base
author remains credited as a coauthor. This change adds runtime shortcuts for
nonempty exponents whose first byte is `0x01` or `0x03`; all other inputs retain the inherited
execution path.

For an exponent beginning with the byte `00000001`, processing that first byte
leaves the accumulator equal to the already computed Montgomery-form base. The new
dispatcher therefore copies that base into the accumulator and resumes the existing
loop at the second exponent byte. This skips the work represented by the first byte
without changing the mathematical state at the resume point. The condition is read
from calldata at runtime and is guarded by a nonzero exponent size, so it is a
universal optimization rather than an assumption about a scorer vector.

For `00000011`, the first six bits are zero. The second shortcut starts from the
existing Montgomery one and enters the inherited loop for the final two bits, then
resumes at the second byte. It preserves the same mathematical state while avoiding
the six leading-zero iterations.

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
| 257-bit modulus | 409,411 |
| BN254 modular inversion | 44,177 |
| random 256-bit modexp | 44,177 |
| RSA-1024 e=3 | 752,871 |
| RSA-2048 e=65537 | 1,982,542 |

The exact total is **3,320,781 gas**. The submitted bytecode is 2,936 bytes and its
structural artifact contains 1,784 instructions. Relative to the attributed base at
3,574,818 gas, this reduces the total by 254,037 gas. The dominant RSA-2048 row drops
from 2,186,191 to 1,982,542 gas; the small dispatcher overhead is included in every
number above.

## Bytecode and proof outline

The base-conversion return is redirected to a short appended dispatcher. An empty
exponent immediately rejoins the original initialization. A nonempty exponent loads
its first byte. Values other than one also rejoin the original initialization. A
value of one copies the full Montgomery base block to the accumulator and resumes at
the next byte. A value of three starts from Montgomery one at the last two bits of
the first byte. Existing
arithmetic routines and the result conversion remain unchanged.

The submission includes a structural instruction artifact whose assembly theorem
matches the submitted byte array exactly. It also proves the appended jump targets
valid and models each actually executed dispatcher branch with the corresponding
instruction prefix. This keeps the bytecode theorem tied to the same bytes that are
scored.

The execution proof covers the empty, both selected, and nonselected dispatcher cases.
Each path is lifted to the benchmark's gas-decreasing EVM trace relation using the
exact Osaka artifact. The proof for the selected branch establishes that the copied
Montgomery base is precisely the accumulator produced after the skipped first byte,
then composes the inherited exponent loop over the remaining bytes. The proof for
the nonselected branch composes the complete inherited loop from byte zero.

## Edge cases and trust boundary

The zero-exponent case is tested before any exponent-byte load and follows the old
path, preserving the required result of one modulo the modulus. The one-byte special
cases reach the existing loop exit after their equivalent prefix state is established;
longer exponents process every remaining byte with the original loop.

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

The change is additive: it preserves the established Montgomery and fallback
implementations and extends the guarded prefix dispatcher. The score improvement
comes only from avoiding work after proving that the resumed state represents the
same mathematical exponent prefix.
