# MODEXP redundant work removal

Manual integration on promoted base fe4db1372014842fe3008e6165c04e6b652b1710.

Artifact: 5314 bytes, SHA-256 `392582bb4d99b04300f51369d599bf0e22f654eb030ae3b1768f0b0b04650304`.

Two local 44-vector corpora (seeds 0 and 20260915) each saved 406 gas against the promoted base: 481027 -> 480621 and 482166 -> 481760. All 88 outputs matched the independent arithmetic oracle.

Lean 4.31/Comparator compilation has not run on this host. The proof port is a draft; local EVM execution is not a proof. Full proof and official scoring are outstanding.

The earlier provenance and experiment notes describe their original artifacts, not this combined candidate. No new axioms, sorry, native_decide, trusted benchmark edits or measurement changes are introduced.
