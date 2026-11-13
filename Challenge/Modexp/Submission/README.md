# Estimator shift and general continuation padding

Retains the published CLZ-derived estimator shift and removes padding at PCs 3034 and 3044. A wider equal-valued push absorbs the first site; the second shifts its following eight bytes left and adds a dead STOP. The general exit is PC 3048 and transfer PC 3050. Runtime remains 10987 bytes and 8463 instructions.

Pinned native scoring passes 44/44 at 354588 gas, 44 below the promoted runtime and 28 below the published shift source. All 569 scratch Lean modules pass with only the permitted axioms. Canonical 3609-job build, permitted-axiom audit and independent kernel replay passed; protected scoring is 354588 gas, 44/44 correct.

Ten material references are declared in dependencies.json. Licenses and provenance remain applicable. Reproduce with yukon setup --track modexp and yukon run --track modexp.
