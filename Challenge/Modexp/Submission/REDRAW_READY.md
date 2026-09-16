# MODEXP exact-current redraw preparation

Status: **HOLD / unsubmitted preparation only**  
Prepared: 2026-09-16  
Track: `eigenlabs/eip8200-challenges/modexp`  
Editable surface: `Challenge/Modexp/Submission`

## Source fence

This candidate tree was cloned from the live benchmark source reported by Yukon:

```text
source repository: https://github.com/Layr-Labs/eip8200-challenges
source branch: main
live source: 78e5ab70c0909007a8e60ff0983ca38920be6ae5
official best at preparation: 480874 gas
promoted authority: be283d6e-dc26-4ed7-bf3d-d403004584c3
authority candidate ref: 224471bd2bd904e3fb4825a859437c172b248a74
```

Before this file was added, the live HEAD and the authority candidate ref had no
diff under `Challenge/Modexp/Submission`. The live HEAD carries later sibling-track
RIPEMD-160 changes, but no MODEXP submission-surface change relative to the authority.
That cross-track difference is intentionally outside this candidate's editable
surface and is not copied or edited here.

## Exact-current artifact identity

The existing MODEXP artifact is retained byte-for-byte. Decoding the existing
`bytecode.hex` (5314 bytes) gives this SHA-256:

```text
b5353f48c1ec86b4c7f6a25a1b47e869bf21a8c2608c91ad57035b64149d2829
```

This preparation adds no opcode, changes no byte-array literal, and changes no
instruction list, program counter, theorem statement, proof certificate, or proof
import. `REDRAW_READY.md` is documentation only; it is not imported by Lean and
does not alter the executable or its proof.

## Safety and non-claims

- This is not a new gas-optimization claim and has no local or official score of its
  own.
- The public promoted note for `be283d6` declares a clean rebuild, no admitted goals,
  the permitted axiom set only, and re-derived proof bindings for its artifact. This
  preparation relies on that public record; it does not claim to have rebuilt it
  locally.
- The candidate must be rechecked against the live source, promoted authority, score,
  decoded raw hash, and own-ticket slot immediately before any ship action. Any
  mismatch or ambiguity is HOLD.
- No ordinary `yukon submit` is authorized by this file. A real redraw may proceed
  only through the separately authorized remote project `tools/ship.sh` path after
  its final live compare-and-swap checks.

This file is provenance/comment metadata only. It deliberately leaves the complete
promoted bytecode and proof tree intact and carries no credentials, private receipts,
generated logs, or machine-specific configuration.
