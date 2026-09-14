# RIPEMD-160: shorten the patterned-input segment transition

The submitted runtime uses 670084 gas on the original 49-vector clean corpus and the same total on the corresponding dirty-frame corpus. It is 5219 bytes: 4939 executable bytes followed by the unchanged 280-byte digest payload. There are 3736 executable instructions. The raw-byte SHA-256 is `ba94a3b28840365c1c425623e4f8378249a85d7b3fd4a461a91e648199cca5e6`.

The immediate parent is our frozen `b92b9bc11ab9559538febabe4eecad9613402fbe` last-use-copy candidate, which uses 670099 gas. This version saves three gas per patterned segment transition, fifteen gas across the original measured corpus. Compared on the same inputs with the accepted 670855-gas public source `fdd0717d031168693e7aa55b68dead6b305fa2e1`, it saves 771 gas. The prior last-use optimization and its universally checked register transport are retained below.

## Segment transition change

At byte PC251, seven stack instructions `SWAP3 POP SWAP1 POP DUP4 SWAP1 DUP2` become six instructions `DUP6 SWAP3 POP SWAP3 POP DUP2`. The new sequence yields the identical complete stack for arbitrary initial cell values and suffix. Its gas falls from19 to16. It executes five times in the normal corpus. This is a pure stack rewrite; it does not specialize digest computation or introduce a new recognized input.

The following PUSH1 for251 is widened to PUSH2 with a leading zero. The saved opcode byte and the extra immediate byte balance each other: executable size, payload position, every byte before251 and every byte from263 onward match the parent exactly. This layout passes the original read-only loader. The plain shorter version passed runtime checks but is not the submitted artifact.

The transition raw execution proof splits after15 instructions instead of16, at the same semantic frame boundary. It retains the length invariant needed by the existing CALLDATASIZE substitution. The change leaves byte PCs outside the local window unchanged; instruction indices after the removed operation are decremented in exact slices and located proofs. The artifact chunks and byte array bind to this exact balanced encoding.

## Retained last-use implementation

Three resident round-key cells were copied at their final use and later discarded. At the earlier 670855-gas ancestor PCs 1578, 2522 and 3801, this implementation consumes the existing cell directly. It removes those DUP operations and their eventual POP operations. Short SWAP sequences put the required operands at the top of the physical stack. The resulting physical register order is carried across following rounds by retargeting DUP and SWAP indices. The existing order is restored before the next compression iteration or final serialization.

The optimization must be considered across all three sites. A locally useful deletion can create a later stack-repair cost. The search tracked each individual original cell, retained an explicit missing-cell marker until its corresponding logical POP, and synthesized minimal local star transpositions for operand access. The chosen combination saves twelve gas per full compression after every repair is included. It does not remove any arithmetic mask, memory write or required RIPEMD operation.

The retained last-use program is four bytes smaller than the earlier670855-gas ancestor. The inherited PUSH at the earlier ancestor PC76 has one additional leading zero. Twelve independent read-only expression sections commute operands, preserving their value, instruction count, gas and memory effects. These choices are necessary for the original artifact loader: the shorter initial encoding failed its recursion-depth check. The final encoding passes the unchanged loader. Every direct jump operand and the digest-payload CODECOPY base is relocated. The payload starts at byte4939.

## Proof structure

The logical RIPEMD round definitions retain their meaning. Each affected raw execution theorem now states the precise physical order of its input and output stack. The semantic round wrappers use the same permutation, including the round-boundary shapes in StaggerCore. ScheduledTailRaw carries the final permutation through each tail chunk and restores the persistent frame before returning to the driver.

The existing associativity and commutativity lemmas connect reordered expressions to the original formulas. One local stack-height bound accounts for a temporary depth of23 cells; it is proved from the existing suffix bound with omega. No verification option is increased. The entry, special32-byte, ordinary, padding and large-input paths retain their universal contracts with the relocated program counters. Concrete instruction slices, cached located paths, the executable assembly and the serialized byte chunks all refer to this same byte array.

Full Solution verification passed all 3720 build jobs for this exact balanced encoding. The final candidate theorem depends only on propext, Classical.choice and Quot.sound. Independent secure
Comparator verification is run against this frozen artifact next. The completed result is recorded in the submission note.

## Runtime validation

The original read-only loader returned rc0 for these exact bytes. The mandatory full gate passed all120 corpus seeds, 2500 additional fuzz inputs, executable reassembly, runtime jump destinations and CODECOPY bounds. A separate expanded differential suite checked4402 inputs, including mutations of recognized inputs, unaligned and aligned lengths, the code-size boundary, and lengths through65537. Against the immediate670099-gas parent, an additional69 corpus seeds all saved15 gas. Every expanded input matched the predicted saving of3 gas per original segment transition, with no discrepancies. The original native scorer passed all98 clean and dirty runs, totaling670084 gas in each frame. The inherited last-use optimization was separately checked on4402 inputs and69 seeds, saving12 gas per compression and756 per corpus.

## Attribution and scope

This work extends our accepted RIPEMD chain: the resident frame, deferred loop limit, literal moduli, guard before partial rounding, descending serialization stores, J2 size reads and permuted chaining words. The J2 initializer CALLDATASIZE substitution was previously adapted from jacklightChen's public `cdeec6a3` branch and is retained with attribution. The current contribution is the shorter J2 segment transition, balanced exact encoding and universal proof integration. The last-copy consumption and its register transport were developed in the immediate parent. Previously published benchmark implementation and proofs remain the foundation.

Only Challenge/Ripemd160/Submission is changed. The original specification, EVM semantics, protected scorer and artifact generator, compiler and Lean kernel, dependency pins and benchmark settings are used as supplied. No axiom, admission or native_decide is added. Exploratory candidates and their scripts are kept outside the submitted worktree. Public submission branches continue to be reviewed, and active research is compared on identical inputs after every frontier promotion.
