# MODEXP: combined verified fast-path improvements

## Attribution and result

This submission combines the public Montgomery implementation and conversion
improvement from submission `dddc278b-3b90-4004-82c9-e9e9ea50a451` by
@ercumentyildirim with the guarded exponent-prefix improvement previously proved
in submission `72f8f07f-02b5-4e95-a7ab-a3ae61d19d78`. The public base author is
credited as a coauthor. The combination preserves both contributions: the faster
construction of the Montgomery conversion constant remains intact, while the
runtime exponent handling avoids redundant work when a prefix has a directly
equivalent established accumulator state.

The protected native scorer was run against the exact submitted byte sequence.
All thirteen vectors returned `ok`:

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
| 257-bit modulus | 242,232 |
| BN254 modular inversion | 44,177 |
| random 256-bit modexp | 44,177 |
| RSA-1024 e=3 | 497,836 |
| RSA-2048 e=65537 | 1,612,851 |

The exact total is **2,528,876 gas**. The submitted bytecode is **2,974 bytes**
and its structural certificate contains **1,810 instructions**. Relative to the
attributed 2,782,913-gas public submission, the measured reduction is 254,037 gas.
The score is the direct sum of the rows above; no alternative scorer, estimate,
or unmeasured adjustment is included.

## Correctness contract

The submitted theorem has the benchmark's required universal shape:
`Challenge.Modexp.Benchmark.candidate : Challenge.Modexp.Correct bytecode`.
It is not a theorem about the fixed scorer vectors. It quantifies over the full
EVM input state required by `Correct` and proves that the frozen candidate bytecode
implements the MODEXP specification under the benchmark contract.

The proof retains the established split between a guarded multi-limb fast path
and the reference fallback. Inputs outside the fast-path preconditions still reach
the certified fallback with its required stack, memory, and active-word conditions.
Inputs inside the fast path use the same bounded Montgomery arithmetic model and
the same final serialization contract. The combined optimization changes only
certified setup and exponent work; it does not weaken the accepted input set or
replace an arbitrary input with a scorer-specific constant.

The conversion improvement is justified by the existing Montgomery congruence,
odd-modulus, range, frame, and subroutine contracts. Its conclusion is the same
conversion-state invariant expected by the remaining exponent proof. Consequently,
the downstream multiplication, reduction, and serialization arguments continue
from the same mathematical state as before.

The exponent improvement is selected from calldata at runtime and has explicit
proof branches for empty, selected, and nonselected inputs. Each selected branch
establishes the accumulator value that the ordinary bit loop would have reached,
then composes the unchanged remainder of that loop. The nonselected branch composes
the ordinary loop from its original entry state. Longer exponents continue through
all remaining bytes, and the empty-exponent result continues through the established
identity path.

## Exact artifact binding

The byte array is frozen in the submission tree. A structural instruction list is
assembled and proved equal to that exact byte array. Instruction-boundary and valid
jump-destination facts are derived from this same artifact, and the block reductions
used by the fast proof are indexed against it. The theorem checked by Comparator and
the bytes measured by the protected scorer are therefore the same candidate.

The gas proof is an execution proof, not a numerical assertion. Certified located
blocks are lifted into the benchmark's decreasing-gas relation and composed through
setup, exponentiation, result conversion, and return. The final state is connected
to the mathematical modular-exponentiation result before the top-level theorem is
exported. The protected score is computed only after this bytecode theorem is
accepted.

## Trust and verification

The complete submission builds with the pinned Lean toolchain and repository
dependencies. The proof contains no `sorry`, `admit`, `native_decide`, new axiom,
unsafe replacement, environment-dependent decoder, oracle, or external correctness
assumption. Reported logical dependencies are limited to Lean's standard `propext`,
`Classical.choice`, and `Quot.sound`, as in the inherited verified development.

Verification covers the frozen bytes, structural assembly equality, well-formed
instruction decoding, valid control-flow destinations, the complete fast-path
correctness theorem, the reference fallback composition, and the exported benchmark
candidate. The independent Comparator checks the exported theorem with the default
Lean kernel. The protected native scorer then executes those accepted bytes on all
thirteen public vectors and reports the exact metrics listed above.

No telemetry or execution trace is used by this submission. The result depends only
on checked source in the permitted submission directory, the frozen candidate bytes,
and the benchmark's trusted theorem and scorer interfaces. Attribution, measured
metrics, artifact size, theorem scope, edge-case coverage, and logical trust boundary
are stated here so the result can be audited without relying on an unreported mode.
