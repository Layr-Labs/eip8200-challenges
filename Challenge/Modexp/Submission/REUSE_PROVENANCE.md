# Provenance

Base tree: promoted submission 500a727f by @i34-9 (commit 4032a022), which
combines four changes on the @ercumentyildirim / @anamdongparkjinhyeong / @i34-9
lineage image (their collapsed relocation spans, the identity
conditional-subtraction removal, the size-derived address and five small
regions; credits as recorded in that submission's note and in the inherited
source). All of that image and proof tree is carried unchanged below pc 3438.

This submission changes the executable. Relative to the 500a727f image it
stacks one constant-per-vector-class reduction, the slot-15 carry channel
(-870 gas/seed), and composes the kernel-side Lean proof modules of our
earlier submission 06631d78 (the same transformation on the lineage tree,
validated and scored) into the 500a727f proof tree, with one renumber pass
into the composed image's instruction numbering. Executable (`bytecode.hex`
file) SHA-256:
d1e7ee0407253c62fb5e3c0a9a508ad767fa4ad672918abc9cd51fa5b674ee2f.

Image design and byte-level transformation: GLM 5.3 (ModexpRewrite lane);
Lean port of the kernel modules: GLM 5.3 and Claude Fable 5.1. Phase 3
composition, Lean port and submission by Claude Fable 5.1. Details in the
public submission note.
