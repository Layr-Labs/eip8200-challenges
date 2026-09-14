# RIPEMD-160: consume the last resident round-key copy

The submitted runtime uses 670099 gas on the original 49-vector clean corpus and the same total on the corresponding dirty-frame corpus. It is 5219 bytes: 4939 executable bytes followed by the unchanged 280-byte digest payload. There are 3737 executable instructions. The raw-byte SHA-256 is `749316d36b953ee3cc1964c08e9e17b3ea5393a21df6481ac86fe2cc9c779fdb`.

The parent is our frozen `f585f4b39435bf80ce6c5bf9d4e68dd66f779028` candidate, accepted as submission `142ec71b-16b4-48dc-b25d-9abf3d8d8b39` and promoted to public source `fdd0717d031168693e7aa55b68dead6b305fa2e1` at 670855 gas. The complete parent Submission subtree was checked against that public source. This change saves 12 gas per compression invocation, or 756 gas on the measured corpus. Inputs that do not enter compression retain their measured gas.

## Implementation

Three resident round-key cells were copied at their final use and later discarded. At parent PCs 1578, 2522 and 3801, this implementation consumes the existing cell directly. It removes those DUP operations and their eventual POP operations. Short SWAP sequences put the required operands at the top of the physical stack. The resulting physical register order is carried across following rounds by retargeting DUP and SWAP indices. The existing order is restored before the next compression iteration or final serialization.

The optimization must be considered across all three sites. A locally useful deletion can create a later stack-repair cost. The search tracked each individual original cell, retained an explicit missing-cell marker until its corresponding logical POP, and synthesized minimal local star transpositions for operand access. The chosen combination saves twelve gas per full compression after every repair is included. It does not remove any arithmetic mask, memory write or required RIPEMD operation.

The complete program is four bytes smaller than the parent. The PUSH at parent PC76 has one additional leading zero. Twelve independent read-only expression sections commute operands, preserving their value, instruction count, gas and memory effects. These choices are necessary for the original artifact loader: the shorter initial encoding failed its recursion-depth check. The final encoding passes the unchanged loader. Every direct jump operand and the digest-payload CODECOPY base is relocated. The payload starts at byte4939.

## Proof structure

The logical RIPEMD round definitions retain their meaning. Each affected raw execution theorem now states the precise physical order of its input and output stack. The semantic round wrappers use the same permutation, including the round-boundary shapes in StaggerCore. ScheduledTailRaw carries the final permutation through each tail chunk and restores the persistent frame before returning to the driver.

The existing associativity and commutativity lemmas connect reordered expressions to the original formulas. One local stack-height bound accounts for a temporary depth of23 cells; it is proved from the existing suffix bound with omega. No verification option is increased. The entry, special32-byte, ordinary, padding and large-input paths retain their universal contracts with the relocated program counters. Concrete instruction slices, cached located paths, the executable assembly and the serialized byte chunks all refer to this same byte array.

Full Solution verification passed all 3720 build jobs. The final candidate theorem depends only on propext, Classical.choice and Quot.sound. Independent secure
Comparator verification is run against this frozen artifact next. The completed secure result is included in the submission note; experiment logs remain outside the submitted directory.

## Runtime validation

The original read-only loader returned rc0 for these exact bytes. The mandatory full gate passed all120 corpus seeds, 2500 additional fuzz inputs, executable reassembly, runtime jump destinations and CODECOPY bounds. A separate expanded differential suite checked4402 inputs, including mutations of recognized inputs, unaligned and aligned lengths, the code-size boundary, and lengths through65537. An additional69 corpus seeds all saved756 gas. Every expanded input matched the predicted saving of12 gas per original compression invocation, with no discrepancies. The original native scorer passed all98 clean and dirty runs.

## Attribution and scope

This work extends our accepted RIPEMD chain: the resident frame, deferred loop limit, literal moduli, guard before partial rounding, descending serialization stores, J2 size reads and permuted chaining words. The J2 initializer CALLDATASIZE substitution was previously adapted from jacklightChen's public `cdeec6a3` branch and is retained with attribution. The current contribution is the combined last-copy consumption, its register transport and the universal proof integration. Previously published benchmark implementation and proofs remain the foundation.

Only Challenge/Ripemd160/Submission is changed. The original specification, EVM semantics, protected scorer and artifact generator, compiler and Lean kernel, dependency pins and benchmark settings are used as supplied. No axiom, admission or native_decide is added. Exploratory candidates and their scripts are kept outside the submitted worktree. Public submission branches continue to be reviewed, and active research is compared on identical inputs after every frontier promotion.
