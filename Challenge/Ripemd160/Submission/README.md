# RIPEMD-160: build the schedule fan's second lane by placement instead of multiplication

The submitted runtime uses 667669 gas on the original 49-vector clean corpus and the same total on the corresponding dirty-frame corpus. It is 5219 bytes: 4939 executable bytes followed by the unchanged 280-byte digest payload. The source base is the public source `acfddfd4ab8d558fe6c5c129d19a1dbd6af9e57a`, whose bytecode (5219 bytes, raw-byte SHA-256 `badd23b793ab2679687d8edd0ca88ad90bf85f69912e17f6780d8df469f87aac`) uses 669769 gas on the same corpus. The submitted bytecode has raw-byte SHA-256 `beabbf1aa1da08e39ca1fd986a9f31cefd8ed775181d45bb2012a41fdc8c14a2`.

## Schedule fan change

The fan prepares the sixteen message words in the packed two-lane form the round body reads. The base artifact writes each byte-swapped half to scratch once and then derives the second lane arithmetically, multiplying every word that the schedule needs in both lanes by a broadcast constant.

This version produces the second lane by placement. Each swapped half is written to scratch twice, the second copy eighteen bytes above the first, and the upper half is duplicated by two sixteen-byte MCOPY instructions. One load at the right offset then returns a word already holding the value in both lanes, and a single wide immediate mask clears the bytes between them. The broadcast constant and its multiplies are gone.

Over the changed region the fan loses 13 of its 17 multiplies and 9 of its 72 stack copies and gains 2 MCOPY instructions, one shift and one OR. The scheduled words are stored in a different order; that order never reverses two writes whose 32-byte windows overlap, so the scratch image is unchanged. The fan occupies the same 572 bytes as before.

The two artifacts differ only at byte offsets 326 to 897. Every byte from 899 onward is identical, which covers the whole compression body, the tail and the digest payload; all 15 jump destinations are unchanged; and the executable instruction count goes from 3734 to 3724. The compression body therefore executes the same instructions at the same program counters for the same gas, and none of the reduction comes from it.

## Proof

The fan's raw execution theorems are restated for the new instruction slice: the two scratch stores and their addresses, the packed-load stage with its mask and its two MCOPY copies, and the store stage in its new order, whose write sequence is proved to leave the same scratch image because reordering writes to non-overlapping windows cannot change memory. The round driver and the table layout are unchanged, every instruction index that moved is relocated in the remaining located proofs, and the compression body's proofs are untouched. The straight-line advance check used by the located-block lifts is extended to cover MCOPY, discharged from the stepper's own MCOPY step.

## Verification

The original native scorer passed all 98 clean and dirty runs, totalling 667669 gas in each frame: 50 gas less for each of the 42 executions of the fan across the corpus. A memory-image differential over 442 inputs compared the full memory image and the whole stack at every one of the 1345 compression entries against the base artifact and found them identical on every entry, with 0 disagreements and 0 abnormal halts.

## Scope

Only Challenge/Ripemd160/Submission is changed. The original specification, EVM semantics, protected scorer and artifact generator, compiler and Lean kernel, dependency pins and benchmark settings are used as supplied. No axiom, no `sorry`, and no increased verification option.
