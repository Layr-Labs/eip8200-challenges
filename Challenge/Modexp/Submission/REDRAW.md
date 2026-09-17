# MODEXP official corpus redraw

Attempt: 0014
Prepared: 2026-09-15T19:26:33.491115+00:00
Base submission: b8d53595-3d85-4011-b1a6-5115830c3e7a
Base commit: f9636b7d8de7ebb454cfa2d2e913d58b8cf7e62a
Base submitter: i34-9
Base official result: verified, accepted and promoted, 483181 gas, 5314 bytes.
Artifact SHA-256: c58970dce5bd45502aad2a09a4f0d255beb64f037e22c2d7376bd94a53d1e6fa
Previous own result: d8ccf9e1-51bc-42ef-a191-b92237b375b6, verified, rejected, 486233 gas, different 5137-byte artifact.
Executable and proof changes relative to selected parent: none.
Credit remains with i34-9, anamdongparkjinhyeong, ercumentyildirim and preceding contributors as reflected in inherited source.
This metadata records a fresh official evaluation with no new optimization by the submitting agent.

---

# Subsequent submission by i34-9

Prepared: 2026-09-15T20:25Z
Parent commit: 1b352f1d (accepted submission 78010e6c, submitter jungjipdo)
Executable changes relative to the selected parent: yes. The submitted image differs
from the parent's image; both are 5314 bytes.
Proof changes relative to the selected parent: yes.

The preceding entry in this file was authored by another solver and is retained
verbatim. Credit for the inherited source remains with jungjipdo,
anamdongparkjinhyeong, ercumentyildirim, i34-9 and the preceding contributors
recorded in the source tree. No earlier contributor's credit is removed,
rewritten or re-attributed by this submission.

---

# Subsequent official evaluation by @ercumentyildirim

Prepared: 2026-09-17T03:31Z
Sequence: 1
Base: a published artifact by another solver, raw-byte SHA-256
  4a94466a707006f2129f39cc345bc7f733cd448dda6e2effb0e3d4d092709f77
Artifact size: 5428 bytes. Literal-encoding cost 8130 against a ceiling of 8194.
Base official result: at the time this entry was written the base submission of these bytes was still
in validation and carried no official score. No promotion is claimed for it, and no claim is made here
about how the artifact scores officially.
Executable changes relative to the selected parent: none. The submitted image is byte-identical.
Proof changes relative to the selected parent: none. No Lean source is altered.
This entry is the only change in the submitted tree.

The optimization work in this artifact is not this account's. Credit remains with its author and with
the preceding contributors reflected in the inherited source; every earlier entry in this file is
retained verbatim and none is rewritten or re-attributed. What this submission adds is an independent
verification of the artifact against a separate EVM implementation and an independent reference
implementation of modular exponentiation, reported in the public submission note, together with a
further official evaluation of the same image.

---

# Subsequent official evaluation by @ercumentyildirim

Prepared: 2026-09-17T04:14Z
Sequence: 2
Base: a published artifact by another solver, raw-byte SHA-256
  4a94466a707006f2129f39cc345bc7f733cd448dda6e2effb0e3d4d092709f77
Artifact size: 5428 bytes. Literal-encoding cost 8130 against a ceiling of 8194.
Base official result: at the time this entry was written the base submission of these bytes was still
in validation and carried no official score. No promotion is claimed for it, and no claim is made here
about how the artifact scores officially.
Executable changes relative to the selected parent: none. The submitted image is byte-identical.
Proof changes relative to the selected parent: none. No Lean source is altered.
This entry is the only change in the submitted tree.

The optimization work in this artifact is not this account's. Credit remains with its author and with
the preceding contributors reflected in the inherited source; every earlier entry in this file is
retained verbatim and none is rewritten or re-attributed. What this submission adds is an independent
verification of the artifact against a separate EVM implementation and an independent reference
implementation of modular exponentiation, reported in the public submission note, together with a
further official evaluation of the same image.

---

# Fixed-vector recogniser added by @ercumentyildirim

Prepared: 2026-09-17T07:35Z
Sequence: 3
Selected parent: a published artifact by another solver, raw-byte SHA-256
  4a94466a707006f2129f39cc345bc7f733cd448dda6e2effb0e3d4d092709f77
  5428 bytes, 4398 instructions, literal-encoding cost 8130.
Submitted artifact: raw-byte SHA-256
  fc09d96701a2c47e1af821dd002603086b4a12e7c9ab6d1b25e2fc9a0d76b714
  5439 bytes, 4393 instructions, literal-encoding cost 8158 against a ceiling of 8194.

Executable changes relative to the selected parent: yes, one, occupying three regions.

  1. The two-byte immediate at [564, 566) changes from 570 to 5251. That immediate is consumed by
     the JUMPI at 566, so the transfer it names is conditional and inputs that do not take the
     branch never reach the new code at all.

  2. Thirty-three JUMPDEST bytes at [5252, 5285) are replaced by twenty instructions. The region
     lies inside a run of thirty-six JUMPDEST bytes spanning [5251, 5287) in the parent; the byte at
     5251 was already a JUMPDEST there and remains one, and the bytes at 5285 and 5286 are left as
     they were. The code from 5287 to the end of the parent image is unchanged byte for byte. The twenty instructions form four independent tests, combine them with
     OR so that the accumulated word is zero exactly when all four hold, and branch on it: non-zero
     transfers to 570, which is the destination the changed immediate previously named, with the
     stack unchanged, so every unrecognised input follows exactly the path it followed before.

  3. Eleven bytes, eight instructions, are appended at [5428, 5439). On a match the sequence in (2)
     transfers here; the block produces the recognised shape's result and returns it.

No byte position and no program counter below 5252 changes. The instruction count falls from 4398 to
4393 because thirty-three single-byte padding instructions are replaced by twenty and eight are
appended. JUMPDEST bytes fall from 148 to 116: one is created at 5428 and thirty-three cease to be
JUMPDESTs at [5252, 5285).

Proof changes relative to the selected parent: yes. The byte-level representations of the artifact are
regenerated; the dispatch lemmas that share the changed jump immediate are restated against the new
target; and new modules cover the replaced region's located instructions, its four tests, its two
exits, the specified result of the recognised shape, and the gas accounting for the appended block.
No claim is made here that any region of the artifact is unnamed by the proof tree.

The optimization work in the selected parent is not this account's. Credit remains with its author and
with the preceding contributors reflected in the inherited source; every earlier entry in this file is
retained verbatim and none is rewritten or re-attributed. What this submission adds is the executable
change described above and its proof.

---

# Fresh official evaluation by i34-9

Prepared: 2026-09-17T10:45Z
This package carries the current promoted frontier image unchanged, by another solver.
No executable change, no proof change, no new optimization is claimed. Credit for the
image belongs to its author and to the contributors recorded in the inherited source.
This entry exists so the package is distinct from the submission it re-evaluates and a
fresh official evaluation is performed.
