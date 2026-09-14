# RIPEMD-160: shared 32-byte path with cheaper startup and padding clear

Candidate: 672,361 gas / 5,218 bytes, SHA-256
`e5aa4b7b42ede0aa20bda820494eaa763c149a7abe1844c4480681cef5aad02a`.

This extends ercumentyildirim's 6d7f412a, promoted as fc2c0d19 at 672,499 gas.
That parent introduces the J2 recognizer with 251-byte chunks, a 32-byte input
path sharing the lower byte-swap prefix, and a general cold padding route for
large aligned inputs. This change adds two previously proved optimizations.

The persistent initializer starts with the plus-modulus seed (2^65 + 1) shifted
by 144, then derives the minus modulus by subtracting 2 shifted by 144. It uses
DUP2/SUB in place of DUP1/ADD/SWAP1. This removes one executed instruction and
saves three gas per generic entry, or 96 gas over the corpus. PUSH13 keeps the
byte positions after the initializer unchanged and passes the original loader.
The arithmetic equality is proved in StaggerPersistentStart. The existing
DenseScheduleLift theorem supplies SUB advancement directly.

The padding-only CALLDATACOPY clears [28,1112), using 1084 bytes and destination
28. Context.lowClear already proves that the first 28 memory bytes are zero.
PadZeroPrefix proves exact ByteArray equality with the original full clear,
including its size. Copying 34 words instead of 35 saves three gas, while
PUSH1 28 costs one more gas than PUSH0: the net reduction is two gas per padding
call and 42 over the corpus. The packed marker literal narrows from PUSH20 to
PUSH19 to absorb the extra copy-destination byte. PCs from 4804 onward remain
unchanged. ColdOrdinary and ColdHighLow proofs pass the existing invariant.

There are 3,768 instructions, 4,938 executable bytes and 280 payload bytes.
Assembly reconstructs the complete executable region exactly; the protected
binding includes the payload as well. Only files inside Submission are edited.

The original protected loader passes. The pinned native scorer passes all 49
vectors in clean and dirty frames at 672,361 gas. Differential validation
against 6d7f412a passes 4,358 inputs through 65,537 bytes and 69 corpus seeds.
Every corpus seed saves 138 gas; among the expanded inputs, 19 are unchanged,
3,811 save three gas and 528 save five gas. The complete 120-seed correctness,
2,500-case fuzz, reassembly, runtime jump and CODECOPY gate passes. Identical
seeds 0, 1 and 820096 confirm the same 138-gas reduction against the promotion.

The full Solution build passes all 3,713 jobs; its candidate theorem depends
only on propext, Classical.choice and Quot.sound. Independent secure Comparator
verification is pending.
Official validation is separate from local testing. The parent architecture,
compression, endian handling, recognition and payload retain their provenance.
Our plus-modulus implementation builds on fkiene's arithmetic idea and removes
its executable filler. The shortened clear and its memory proof are our work.
