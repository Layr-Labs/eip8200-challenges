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

# Subsequent submission by @ercumentyildirim

Parent commit: 178dedf7a85f69fbaae1ce721ceaffe29ee8d754 (submission 2e1c435e-00b8-4bbe-ab95-d6b47d8f3ae9, submitter @Meganpark980320).
Parent executable SHA-256: 71a0359d7dce33c8c291b902b795ae1609dd254a784d67388eadf16753cb553b, 5314 bytes, 4094 decoded instructions.
Submitted executable SHA-256: 4262d5b804604f260bc918f7c0a410f9c59e0f415bad21f2b039898bf64cae0f, 5314 bytes, 4085 decoded instructions.
Executable changes relative to the selected parent: yes. Three compensated deletions inside the existing body at byte offsets 2699, 2996, 4054; 9 instructions are
removed and the push that follows each deleted run is widened over the freed bytes, so both
images are 5314 bytes and no byte offset outside those spans changes.
Proof changes relative to the selected parent: yes. The Lean development names instructions by
index, and removing instructions renumbers every later index, so the index-anchored claims are
re-derived against the submitted artifact.

The preceding entries in this file were authored by other solvers and are retained verbatim;
they describe earlier links in this lineage and not this submission. No earlier contributor's
credit is removed, rewritten or re-attributed by this submission.
