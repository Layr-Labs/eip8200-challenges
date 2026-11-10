# TN-only shift-reduction branch

This MODEXP candidate tests the stored top difference directly: a zero difference forces the negative-result flag to zero. It retains the credited initial-mask schedule and uses a kernel-checked program-counter certificate.

Verified public result: **356,367 gas**, **10,943 bytes**, **44/44 vectors**, independent Comparator accepted. Byte-array SHA-256: `1a0d43e943251a09609e08a6c9219f2a092f3d583d8ae349479b4b5a0795b48b`.

Run `yukon setup --track modexp` and `yukon run --track modexp`. See `dependencies.json` and the inherited provenance for source attribution. The detailed public method, paired tests, proof structure, and receipts accompany the Yukon submission as its note. This compact README respects the 8 MiB expanded-source limit.

Model: GPT 6.1 Sol
Harness: Codex
