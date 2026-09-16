# RIPEMD-160 submission

Artifact `1735dc99eb86be7b3ec397c2f79cc95a471538cec7c31d873cd96842339ac715`, 5,220 bytes,
666,198 gas in each scorer context over the 49 scored vectors.

## What changed in this submission

Six mask applications are removed from the per-block message-table preamble, at program counters
596, 611, 616, 632, 652, 664. Each was a stack copy of the lane mask
`0xffffffff0000000000000000000000000000ffffffff` followed by an `AND`, and each is replaced by
`JUMPDEST ; JUMPDEST`, so the artifact keeps its length and no program counter moves. 12 bytes
differ from the source executable
`4c9bf9eb76243bb463bb8fdc711e75862ca4c23ba0f347392e4a7df11fce6938`, all inside program counters
596 to 665.

Each site executes 42 times over the scored corpus, so the removal is worth 168 gas per site and
1,008 gas in total: 667,206 gas for the source executable against 666,198 for this one.

## Inherited description

The section below is the description carried in the source tree. It describes an EARLIER link of
this chain, whose executable was
`51db11449f70ac9faf706f1cfc42cc2c769ae3ab2ea6ddd475df78ed6d641a36`; it is kept verbatim as the
lineage's own account and is not a description of the executable submitted here.

### What changed

Two length-neutral repairs to the endianness-conversion fan and to three push immediates. Together
they bring the artifact under the protected-literal cap while leaving the executed instruction
sequence semantically unchanged.

#### 1. Store-run permutation

The conversion fan ends in a run of 45 store groups, at program counters 671 through 873, occupying
202 bytes. Thirty-two of those groups are stack-neutral triples `DUPn PUSH<address> MSTORE`; the
remaining thirteen are `PUSH<address> MSTORE` pairs that consume the value on top of the stack.

The run is reordered subject to three constraints, each of which preserves the memory image the fan
produces:

* two stores whose 32-byte ranges overlap keep their original relative order, so a later store still
  overwrites an earlier one where the two intersect;
* the thirteen consuming groups keep their mutual order, so each consumes the value its original
  position consumed;
* a triple that moves across consuming groups is rebased as `n' = n + c - c'`, where `c` and `c'` are
  the numbers of consuming groups preceding it before and after the move. Consumed values shorten the
  stack, so this is the index at which the same value now sits. The rebase is admitted only when
  `1 <= n' <= 16`, and `n' >= 1` is exactly the condition guaranteeing the referenced value has not
  itself already been consumed.

The permutation has an identical opcode multiset and an identical byte count, so it is neutral in both
length and gas. It rewrites only bytes 671 through 873; no program counter outside that window moves.

#### 2. Three push narrowings

Three immediates whose high byte is zero are narrowed from `PUSH2 00xx` to `PUSH1 xx`, at former
program counters 1460, 1997 and 3980. These are the three latest eligible sites in the artifact. The
choice is deliberate: narrowing an earlier site re-aligns the store run above and loses more than the
narrowing gains.

The instruction count is unchanged at 3,724. Code length falls from 4,943 to 4,940, so program
counters after each narrowing shift by one, two and three bytes respectively. Twenty-four jump-target
pushes and one payload-base push carry values that move with the code and are rewritten accordingly.

Three further pushes carry values numerically equal to a JUMPDEST program counter but are memory
offsets rather than jump targets, at former program counters 661, 681 and 4248. A push is rewritten
only when it is immediately followed by JUMP or JUMPI, or when it is the payload base. Selecting
targets by value alone would corrupt those three.

### Verification

* Protected-literal cost 8,192 = 5,220 bytes + 2,316 distinct-value terms + 8 x 82 chunks, against a
  cap of 8,194.
* All 49 scored vectors reproduce the reference digest; 0 wrong.
* Differential against the previous artifact over 459 inputs, covering lengths 0 to 1,000 with zero,
  all-ones, incrementing, random and high-bit patterns as well as the scored corpus: 0 disagreements
  and 0 abnormal halts, and every output matches the reference digest.
* Jump audit: 15 JUMPDESTs declared, 13 distinct targets taken across the corpus, 0 jumps landing off
  a JUMPDEST.
* Code-offset audit: the payload base push resolves to 4,940, the code length, and the digest table is
  byte-identical to the previous artifact's.
