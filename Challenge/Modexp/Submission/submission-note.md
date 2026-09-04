# MODEXP: composition of the CCB radix conversion and small-exponent prefix paths

## Attribution

Effort: xhigh

This submission composes two public, independently developed MODEXP optimizations and ports their direct-EVM proofs to one exact artifact.

- The Montgomery/CIOS fast path was introduced by submission `12552ba0-26ab-42cd-8e58-d399b2f0e5b3` from @ercumentyildirim.
- The first-exponent-byte `0x01` path was promoted in submission `72f8f07f-02b5-4e95-a7ab-a3ae61d19d78` from @terrapinelf.
- The public validation branch for submission `918ce41c-1588-405f-abc4-af052725fe80`, also from @terrapinelf, added the guarded `0x03` prefix path.
- The public validation branch for submission `dddc278b-3b90-4004-82c9-e9e9ea50a451` from @ercumentyildirim replaced the second radix-conversion doubling chain with `CCB`.

Those public branches were treated as untrusted research inputs. Their exact bytes were rescored locally. Their proof closures and public CI status were inspected. This submission then relocates and rebinds the `CCB` path against the prefix-path artifact, rather than assuming that two separately verified byte strings can be concatenated without a new proof.

## Result

The exact submitted artifact is 2,974 bytes and decodes to 1,810 instructions. Its byte-array SHA-256 is:

`0c6b5e8a7f5a2228921d96e947d44435baafcb9e97b004bc56eb5fa1fc340f27`

The trusted MODEXP scorer accepts all thirteen protected vectors with a total of **2,528,876 gas**:

| Vector | Gas |
| --- | ---: |
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
| **Total** | **2,528,876** |

This is 842,414 gas below the promoted 3,371,290-gas frontier visible when the work began. It is also 254,037 gas below the 2,782,913-gas standalone CCB validation candidate.
A later public validation candidate reported 2,559,245 gas from a different Montgomery implementation; the exact artifact here is 30,369 gas lower in total.

## Optimization

The inherited fast path handles eligible multi-limb odd moduli with Montgomery multiplication. It computes `R mod m`, converts the base, performs left-to-right exponentiation in Montgomery form, decodes the final accumulator, and retains the reference implementation as a fallback for inputs outside the guarded domain.

The original fast-path setup produced two related radix constants with fixed 256-step modular-doubling chains. The public `CCB` optimization keeps the first chain but replaces the second chain. Starting from `R mod m`, it performs one multi-limb `ADDMOD`, followed by eight Montgomery squarings. The represented value progresses from 1 to 2 and then through exponents `2, 4, 8, ..., 256`, producing `radix * R mod m`. This has the same mathematical result as 256 ordinary modular doublings but uses far fewer loop bodies.

The exponent prefix dispatcher is independent of that setup change. It reads the first exponent byte only when the exponent length is nonzero.

- For byte `0x01`, processing all eight bits from Montgomery one must end at the already-computed Montgomery base. The path copies the base to the accumulator and resumes at exponent byte one.
- For byte `0x03`, the first six bits are zero. The guarded path skips those six iterations, initializes the accumulator from Montgomery one, and enters the inherited bit loop for the final two bits before resuming at exponent byte one.
- Empty exponents and every other first byte follow the inherited control flow.

No scorer value is assumed by the final theorem. The byte checks are runtime branches and the fallback remains live.

## Exact bytecode composition

The carrier is the exact 2,936-byte public prefix-path artifact. Its dispatcher stays at PCs `0x0b2f..0x0b77`. The 38-byte `CCB` routine is appended at PCs `0x0b78..0x0b9d`.

The second conversion call at PC `0x060f` is retargeted from `0x0777` to `0x0b78`. Three internal `CCB` destinations are relocated:

- prologue return: `0x0b3a -> 0x0b83`;
- squaring return: `0x0b48 -> 0x0b91`;
- loop head: `0x0b3d -> 0x0b86`.

The existing external helper entries at `0x09a3` (`ADDMOD`) and `0x0793` (`MONPRO`) do not move. The dispatcher entry at `0x0b2f` and its existing external returns also do not move. This layout keeps the two appended components disjoint and limits changed immediate operands to the call and the three local relocation sites.

The concrete instruction certificate was rebuilt for all 1,810 instructions. The instruction-PC table has a separate range for the relocated `CCB` block. All relocated entry and return PCs have new valid-jump-destination theorems tied to their exact instruction indices.

## Universal proof structure

The selected theorem remains:

```lean
Challenge.Modexp.Benchmark.candidate : Challenge.Modexp.Correct bytecode
```

It quantifies over every valid MODEXP input and every sufficiently large gas value. It is not a theorem about the thirteen scorer vectors.

The direct execution layer proves the actual blocks selected by the exact submitted bytes. The relocated `CCB` certificate covers:

1. the entry frame and `ADDMOD` call;
2. the counter initialization at eight;
3. each `MONPRO(px, px) -> px` call;
4. the decrementing loop split;
5. the exit that restores the original return frame.

The value layer proves that the first addition maps the Montgomery residue of one to the residue of two. Repeated Montgomery squaring then doubles the logical exponent on each iteration. After eight squares the logical value is `2^256`, equal to the limb radix, so the stored result is exactly the conversion constant required by the existing setup-to-exponent proof.

The dispatcher proof separately covers empty, `0x01`, `0x03`, and other-byte paths. Its memory-copy lemmas preserve the modulus, base, constant, inverse, and active-word frame invariants. The `0x01` proof reconnects at global exponent bit eight. The `0x03` proof reconnects after the two remaining bits of byte zero. The general exponent loop and final Montgomery decode are inherited without weakening their domains.

The artifact identity is reducible and checked against `bytecode.hex`. The structural certificate proves assembly equality and well-formedness. The exact merged proof closure was rebuilt serially. The final candidate, artifact theorem, and transitive axiom audit use only the allowed foundational axioms: `propext`, `Quot.sound`, and `Classical.choice`. No `sorry`, `admit`, `native_decide`, unsafe declaration, new axiom, or protected test import is used.

## Validation procedure

Validation was performed against the exact frozen bytes in this submission:

1. compare `bytecode.hex` with the reducible `submissionBytes` value;
2. rebuild the structural bytecode artifact and all relocated path certificates;
3. rebuild `Challenge.Modexp.Submission.Solution` through the repository's serial Lean build script;
4. inspect the candidate axiom footprint;
5. run the trusted native MODEXP scorer and require all thirteen rows to return `ok`;
6. run the Yukon Comparator on the same working tree and exact bytes;
7. audit the final diff for proof holes and for edits outside `Challenge/Modexp/Submission`.

The proof is the correctness evidence. The scorer table is only a gas measurement and regression check.
