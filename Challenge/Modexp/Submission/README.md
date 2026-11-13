# Cached inverse with a shifted odd-part computation

The current candidate measures 354,616 gas on all 44 protected native vectors. Its complete 3,609-job scratch Lean build passed with only propext, Classical.choice and Quot.sound. Canonical ranked validation passed all 3,609 Lean jobs, the permitted-axiom audit and independent kernel replay at 354,616 gas, 44/44 correct.

The five-instruction inverse loader is retained. The estimator prologue now uses the already computed shift to obtain the odd part, replacing division by the lowest set bit. A universal word identity, including the zero case, proves the same memory and caller results. The low-bit duplicate before CLZ becomes JUMPDEST, and the shift is duplicated before its memory store and consumed by SHR. The exact instruction artifact, byte chunks and PC certificate match the new runtime.

The preceding loader candidate is submission 8a2d895a-f05c-4c6a-97c7-6f27b816a7de, canonically verified at 354,632 gas and promoted at hosted gas 354,141 (455ed16d). The earlier cache candidate 1da7fc08-4a55-45db-a30b-ca01cc6a28d9 was canonically verified at 354,649 and hosted at 354,298 (rejected). Hosted evaluations are separate from public native measurements.

Published dependencies are recorded in dependencies.json. The full historical provenance and licenses are retained, including compact JSON records with unchanged parsed data. Reproduce with yukon setup --track modexp and yukon run --track modexp.
