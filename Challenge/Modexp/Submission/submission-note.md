# MODEXP: restore public PR #421 leading-set-bit initialization

Base: `7d31b5f1254c37e2da591460c9727007594bd9fe` (official score 1,819,772).
Donor: public PR #421, commit `df871a4552cc1c7fbcaa227ba01b3359c707830e`.
This is a selective donor restoration, not an original algorithmic discovery.
Implemented using Hermes Agent / OpenAI gpt-6-astra.

For the first exponent byte when nonzero, the existing LZ routine locates its
leading set bit. Instead of squaring Montgomery one and multiplying by BASE,
the restored block copies BASE onto ACC and resumes at the mask shift. A zero
first byte retains the old bit-loop route. Later exponent bytes are unchanged.
The mathematical memory model and gas-step composition are ported from the
accepted donor, including the zero-byte branch and last-bit special case.

The donor helper is relocated to pc 3695..3721, instruction indices 2414..2428.
The only changes to existing executable bytes are the two bytes of the LZ
jump immediate at offsets 2968 and 2969. All other base bytes, including the
newer fused-window PR #533, RR leading initialization, and full/raw-base
conversion, are preserved. CCB is untouched. No donor in-place padding edit
or older unrelated source was restored.

Canonical artifact: 3,722 bytes, 2,429 instructions.
SHA-256: `13347aec602b91972119748a613e2fa2531e3200c8228e92047fb9aa5f145c8d`.
Bytes.lean, Bytecode.lean, instruction assembly, located paths, PC facts,
jump-destination facts, Lz states, Exp memory/invariant and execution proofs
are updated together. Solution.lean continues to export the universal
candidate theorem via the existing integrated proof chain. No proof escape
was added.

Local evidence (light Python only):
- RED: incumbent actual-bytecode seam returned pc 1789 for nonzero byte 1.
- GREEN: 1,024 actual-bytecode seam cases (all 256 first-byte values at
  n=2,4,8,32), with exact stack, destination-memory output, unchanged memory
  outside ACC, and zero/nonzero route assertions.
- Independently reassembled all 2,429 instruction-source entries and compared
  them with bytecode.hex and Bytes.lean; exact match. Checked new PC bindings
  and that only the two declared preexisting byte offsets changed.
- Static canonical-bytecode / proof-escape audit and git diff whitespace check
  passed. Candidate-local imports all resolve, including the new helper.

These are bounded component and source-binding checks, NOT full MODEXP
execution, aggregate scoring, Lean elaboration, or Comparator acceptance.
Local heavy computation was prohibited; the universal proof source has not
been compiled locally. Hosted proof and functional validation remain required.
No official submission was made by the implementer.

The remaining estimated aggregate upside is 113,360 gas against the pinned
base (two avoided MonPro calls per affected wide row, less control/copy
reserve); this is a hypothesis, not a measured candidate score.
