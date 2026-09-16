# RIPEMD-160: 664,995 gas in 5,210 bytes

This executable is `607a9f5d6cb1625b7d89e5068a2a594aebcd82290d11382ac62557d6d0f59fe1`, 5,210 bytes, 664,995 gas by the
verified scorer in both scorer contexts over 49 vectors and 98 rows.
It is derived from `719ff84e9866b3ad3caec3f16ec16fbd395f78df851305711a8c92c77ac30d9e`,
5,210 bytes at 665,014 gas, by 2 edits in 2 gas-bearing spans:

    0 run-time constant computations replaced by literals   +0 gas  +0 bytes
    2 unreachable JUMPDESTs absorbed into the preceding PUSH   -19 gas  +0 bytes
    0 position immediates re-derived for the new layout   +0 gas  +0 bytes

Screens on the submitted bytes: the artifact decodes completely, 49 of 49 scored vectors return the reference digest, a further 505 inputs covering all 64 residues of the message length modulo 64 disagree on none, and the two artifacts run in lockstep at 3,788 surviving instructions over 209,740 observations with no disagreement.

---

## Inherited from the executable this one is derived from (719ff84e9866b3ad), reproduced verbatim

# RIPEMD-160: input buffer 1056 with a proved allocation transition

The artifact copies the input at address 1056 and consumes both words of each
block before schedule writes reuse its bytes. The next block starts at 1120,
above the last schedule byte at 1111. The exact-32 route starts with 34 allocated
words and grows to 35 at the schedule store to address 1080. Its padding marker
is the explicit byte 0x80 inherited from our 1087-buffer artifact.

The clamped alignment masks at PCs 144 and 275 use the public `PUSH1 224;
JUMPDEST` change by i34-9, source commit
`3ff323e5a631bf0bd2d6897e2825f68ad2e86889`, promoted submission
`5a7c448f-36db-401e-810d-a438a65c271c`. The three corresponding J2 proof modules
are reused verbatim. See REUSE_PROVENANCE.md for attribution and the earlier
public lineage. Our local source parent is the proved 1087-buffer commit
`8737eba882613ff6a76fe7c64d7fd9b0fdf6c7d2`, submitted as `808bfe37`.

## Artifact

- SHA-256: `959e34cb39e0da35b8d3eea31c70d45f7a1c9b754e2f867422fc05d60f9b6ec7`.
- Size: 5224 bytes = 4944 executable bytes + 280 data bytes.
- Executable instructions: 3720; all instruction PCs match the 1087 parent.
- Local seed-zero and median score: 666,834.
- Relative to the 666,935 parent: 63 gas from tighter buffer placement, plus
  38 gas from the credited public mask change, totaling 101 gas.
- Relative to the public 666,982 mask artifact: 148 gas from buffer reuse.
- The digest selector and digest-table payload are unchanged.

## Proof and validation

The proof retains the indexed invariant for unread input blocks. The early
shared-32 loader and pool lemmas now allow 34 active words; a separate schedule
lemma proves growth to 35, after which the existing compression proof applies.
The general 35-word interfaces are preserved for all other routes.

The exact artifact has passed all 120 local corpus seeds, 2500 fuzz cases,
reassembly, runtime jumps, CODECOPY bounds, and the actual read-only loader.
Full Lean validation passed all 3720 jobs. The final candidate depends only on
`propext`, `Classical.choice`, and `Quot.sound`. The original protected benchmark
must also pass before submission; its exact result belongs in the final upload note.
No protected benchmark scripts or verification options are changed.

Model used for the new integration and buffer proof: GPT-6.
