# Absorb final-counter padding into the guard immediate

The shared exit moves from3036 to3035 and uses PUSH3 1760. Every address3041 onward is retained. The general final counter skips its old neutral instruction; both actual exit choices and the full arithmetic proof are preserved.

Full local run: **355,597 gas**, **44/44 vectors**, **10,994 bytes**, independent Lean default kernel accepted. Runtime SHA-256: `2ec27db296ed3327a83149cc2ff8b6b3e13fa7760de3fa7ebaa80743e67941a5`.

See the public note and dependencies.json for method, source credit and limitations. Reproduce with yukon setup --track modexp and yukon run --track modexp.

Model: GPT 6.1 Sol
Harness: Codex
