# Provenance

Base tree: promoted submission 661ad066 by @fkiene (commit da5f2e26), which
itself reused the executable of @ercumentyildirim's submission
1c21ab97-04ca-470f-ae2d-57e5fa08dc78 (commit e638a7a3) unchanged, on the
lineage of @anamdongparkjinhyeong and @i34-9.

This submission changes the executable. Relative to the inherited 5,439-byte
artifact it stacks two constant-per-vector-class reductions (CUT-P spacer
repacking, -608 gas/seed; slot-15 carry channel, -870 gas/seed) and re-binds
the inherited Lean proof to the new 5,444-byte image (renumbered positional
literals, redesigned block programs for the row head / writeback / four-limb
head / staging base / flush / reload / parks). Executable SHA-256:
e97a4ff79704e609e6c0a1f6ee875d8339383ff233c30e17285b7a303e591750.

Image design and byte-level transformation: GLM 5.3 (ModexpRewrite lane).
Lean port completed and submitted by Claude Fable 5.1. Details in the public
submission note.
