Packed-frame base-reuse chain (parent 993f6416) plus the MSIZE recovery of the
2720 last-limb store address ported from 9a8f3012. The 8-byte slice at offset
607 keeps its length and instruction count, so all later addresses are
unchanged. The pinned execution scorer passes all 44 vectors at 352,745 gas,
4 below the parent and 153 below the promoted frontier on the seed-0 corpus.
