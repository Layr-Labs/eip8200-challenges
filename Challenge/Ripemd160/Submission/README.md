# RIPEMD-160: CODESIZE bound for the upper padding word

Candidate: 673,654 gas / 5,233 bytes, SHA-256
`4f47a363ffaa302f3f7790bb06f899937e8258ea03dee344d6b8024a122a316f`.

The padding-only block tests whether calldata length is below the exact code
size, 5,233. This is sufficient to prove its upper bit-length word is zero.
Accepted lengths skip the existing high-word stores; other lengths execute
those stores with the exact high word. The universal proof establishes the
sufficient implication for every UInt256 length and retains both paths.

`CODESIZE CALLDATASIZE LT` replaces the eleven-gas shift/zero test with a
seven-gas comparison. Twenty-one corpus paths save four gas each, reducing
our submitted direct-footer/shifted-answer artifact from 673,738 to 673,654.
The branch destination uses PUSH4 with two leading zero bytes, preserving
all subsequent physical byte positions without an executable filler. The
digest selector is 2020082812; its fourteen payload records are permuted
consistently. Bytecode contains 3,793 instructions and 280 payload bytes.

The original protected loader passes. The pinned native scorer passes all
49 vectors in clean and dirty frames. Differential validation against our
submitted parent passes 4,358 inputs and 69 corpus seeds; all corpus seeds
save exactly 84 gas. Boundary cases include lengths around 5,233, 32 KiB
and 64 KiB. Rejected larger lengths may execute zero-valued upper stores,
costing 57 additional gas on that path while preserving the exact digest.
The 120-seed gate passes with minimum/median 673,654 and maximum 674,177.

This extends i34-9's Source32Footer implementation and the sufficient
upper-length guard from fkiene's bacc0bbf submission. Our shifted-answer
method comes from promoted submission 478b8a1d. Inherited implementation
and proof contributions retain their existing attribution. Changes are
confined to the permitted Submission tree. Full proof and secure benchmark
results are recorded separately in the submission note.

The full Solution build passes all 3,678 jobs. Its universal candidate theorem
uses only propext, Classical.choice and Quot.sound. Independent secure
Comparator verification is in progress; official acceptance is separate.
