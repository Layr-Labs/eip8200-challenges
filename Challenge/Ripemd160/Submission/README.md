# RIPEMD-160: compact Source32 with a length guard

The exact runtime is **5,233 bytes**, with **3,789 executable instructions**
and an unchanged 280-byte digest payload. Raw SHA-256:
`ff5b157dc2a1c565f3b6007f650d126c15ea501354615d06b051d4fbda8a28c4`.

This candidate extends the compact Source32 artifact `24c55f44…`. The only
runtime edit changes the five-byte padding guard at PCs 4799–4803 to test
whether calldata length is below 65535. Accepted lengths have zero high lanes;
rejected lengths execute the existing unconditional high stores. All byte PCs
and bytes outside that window stay fixed. Subsequent instruction indices fall
by one. The packed length lookup, Source32 constructor and compression
arithmetic are retained.

The predicted fixed-corpus score is **673,650 gas**, 63 below compact Source32's
673,713. This package's proof lane did not run the trusted scorer or independent
EVM branch controls. Runtime receipts and official acceptance are recorded
separately; the prediction is not an official score or an all-input gas claim.

Validation uses the pinned Lean 4.31.0 toolchain and unchanged protected
preparation script. The exact protected literal compiles at the default
recursion settings. The complete Solution build, fresh committed no-build,
exact candidate type and named axiom audit pass. The candidate proves
`Challenge.Ripemd160.Correct Challenge.Ripemd160.Benchmark.bytecode` and uses
exactly `propext`, `Classical.choice` and `Quot.sound`.

The certificate retains typed instructions, assembly witnesses, raw templates,
physical PC facts and exact guard index links. Both guard branches and the
low/high store semantics are checked universally, including the execution
state at each seam. Changes are confined to `Challenge/Ripemd160/Submission`.

Inherited arithmetic and proof contributions retain their original attribution.
In particular, the earlier startup-modulus improvement originated in fkiene's
public submissions `8c5a1372-55ad-4d56-b2f0-4fd531dbde69` and
`74a1020d-ba24-4150-9c29-a4e5006a17a1`. Earlier round-13 literals, paired rotations,
physical keys, Euler memory layout and padding skip remain represented by
their existing proofs and attribution. The public release note supplies the
additional promoted-source acknowledgment for this guard adaptation.
