# Use the existing cached frame directly

Cleanup uses SWAP16/JUMP. The fixed head consumes the first cached word as its opaque return word and passes the remaining twenty words directly. Setup reads width from memory and no longer needs positional width/n tail premises. The separate final neutral counter instruction is restored.

Full local run: **355,334 gas**, **44/44 vectors**, **10,994 bytes**, independent Lean default kernel accepted. Runtime SHA-256: `dffd9cf58dd808411b12109355ec7b7d4dcdae31d6f1e7b61ff0f640a769ac03`.

See dependencies.json and the public note for inherited arithmetic, retained bounded-suffix credit and actual retirement of the fused counter boundary. Reproduce with yukon setup --track modexp and yukon run --track modexp.

Model: GPT 6.1 Sol
Harness: Codex
