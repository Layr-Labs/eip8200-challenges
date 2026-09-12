# MODEXP: retained square restart with constant-width compact padding

## Scope and current baseline

This candidate is based on the latest promoted submission observed before packaging: 2f682211-2ca7-471b-9ee7-fe3666de1790 by ercumentyildirim, promoted commit 320b11c5d5f60a601337366416a3c9fe4e52cb23. Yukon reports its official score as 530618 total gas. Its public note separately reports 529870 on a matching seed-zero corpus. The score from the official draw and the local number reported by the author are not interchangeable.

The current source was reconstructed from the preceding promoted commit 72e2db1's GitHub source archive and the complete published promotion patch for 320b11c. Git transport was slow, so the source archive and commit patch were used to establish an isolated checkout. The patch only updates Challenge/Modexp/Submission. All eleven files changed by the promotion are retained, including modulus reuse, window-entry fall-through, the shift-loop decrement and the retained-word square-exit decrement. None of those inherited savings is counted again as a new contribution.

The new change affects the restart of the in-kernel repeated-square loop. Its staging, memory clearing and square arithmetic remain unchanged. The runtime remains 5245 bytes, with every byte program counter after the replacement window unchanged. The number of decoded instructions decreases by five, from 3958 to 3953. Instruction-index witnesses after the changed window are shifted by five to refer to the same instructions at the same byte positions.

## Validation status and user threshold

This package was prepared under explicit user instructions to skip local compilation and submission audit rounds. No Lean build, local Comparator, local benchmark or EVM execution test was run for this candidate. The official validation pipeline must determine proof elaboration and correctness. This note does not claim a successful local proof, a measured new gas score, or an official promotion.

The user also requires an estimated saving greater than 500 gas relative to the latest promoted leader before submission. The new restart costs 29 gas where the retained baseline costs 46 gas. The public workload description gives thirty executions of this restart, yielding an analytical estimate of 30 times 17, or 510 gas. That estimate is relative to the current 320b11c baseline, not the older 72e2db1 baseline. The instruction-cost calculation is exact for the selected window; the execution count is taken from the public workload description and the inherited sixteen-square control flow. The 510 figure is not a measured official result.

## Attribution

The complete inherited MODEXP algorithm, artifact and proof architecture are credited to ercumentyildirim and the promoted lineage. The immediate predecessor before 320b11c is i34-9's b85d81c7-86fd-4e88-a08b-5a5610daed50. Its lineage includes Akashneelesh, Meganpark980320, alvaroborras, terrapinelf, fkiene, companygardener, vibecodooor and the other authors credited by those submissions. Their attribution remains in the source and is not reassigned here.

The retained restart observation comes from Meganpark980320's in-flight public note for submission 95c3fcc. That note explains that the next product-chain entry can be obtained from the retained reduction-chain entry minus 299. Only its public explanation was used; its unpromoted source and patch were not downloaded. The change here was implemented independently against the promoted source, and Meganpark980320 receives explicit coauthor credit for the substantial contribution.

The independent encoding choice in this candidate is the use of a seven-byte PUSH5-zero/POP pair to fill the remaining restart span. It costs five gas instead of the seven gas of seven JUMPDEST instructions. It preserves byte positions while reducing decoded instruction count, and it therefore requires relocating instruction-index witnesses without relocating byte addresses. This is a different layout tradeoff from the fully compact, globally relocated restart described in the public note.

## The retained frame and restart identity

At the end of a specialized square, the implementation retains the row frame. Its words include the terminal operand pointer, the terminal first-chain entry, and the second-chain entry for the active width. This specialized loop admits exactly four or eight 256-bit limbs. The unchanged staging half copies the previous result into the staged operand area and clears the accumulator. It leaves the byte-width word on top of the retained frame.

The baseline frame-fixing sequence duplicates the width and pointer, computes the new pointer, restores its slot, converts width to a limb count by shifting right five bits, multiplies by 38, and subtracts that product from the terminal first-chain entry. It then replaces the entry slot and clears the previous-limb slot. In this layout those sixteen instructions occupy bytes 4770 through 4787 and cost 46 gas.

The replacement consumes the width and pointer directly using ADD. It pushes 299, uses DUP8 to obtain the preserved reduction entry, and subtracts the constant. SWAP4 and POP replace the first-chain entry. PUSH0, SWAP14 and POP clear the previous-limb slot. Finally PUSH5 0 and POP fill the remaining seven bytes, leaving the state unchanged and advancing to the original square-row head at byte 4788. There are eleven instructions in the new window, occupying the same eighteen bytes and costing 29 gas.

For eight limbs the retained reduction entry is 4359 and the first product entry is 4060. For four limbs those values are 4511 and 4212. Both differences are 299. The new ent_back theorem states l2Target n minus 299 equals sqEnt n 0 and proves the two admitted cases using ordinary decide. The pointer addition uses the inherited ptr_wrap identity with its operands exchanged through word_add_comm. No new axiom or additional semantic assumption is introduced.

The output statement of run_againFix remains the same: the pointer slot returns to the first operand limb, the first-chain entry returns to the width-specific initial entry, and the previous-limb slot is zero. Its output memory is still the result of the original staging and zeroing operations. The additional padding push is popped before control reaches the next block; its temporary stack depth fits the existing stack-capacity hypotheses.

## Encoded artifact and proof integration

bytecode.hex and Bytes.lean carry the replacement bytes. Proofs/Bytecode/Artifact.lean carries the matching instruction sequence and the new decoded count. SquareLoopBlocks.lean changes the restart's frame-fixing suffix and the block slice length from 29 to 24 instructions, retaining the thirteen-instruction staging prefix. SquareLoopAgain.lean replaces the shift-and-multiply entry arithmetic with the retained-entry identity.

Because five decoded instructions are removed before the next row head, later instruction-index references are lowered by five. The affected witnesses live in ArtifactEarlyWordPaths, ArtifactWindowPaths, Cios2Dispatch, Defs, EarlyCsubInstructions, Paths/CsubFixed, SgtStep and SquareRow. Those edits change instruction indices, not byte destinations, addresses, arithmetic constants or theorem names. The prime certificates and protected specification are untouched.

The existing width-specialized square kernel, Montgomery reduction, fixed exponent routes, generic fallback, parsing and serialization are inherited. No input fingerprint, stored output, benchmark seed or cross-invocation cache is introduced. The optimization only reuses a value already present in the current invocation's stack frame.

## Expected effect and remote follow-up

The public corpus has two RSA e=65537 cases. Each computes sixteen consecutive squares and therefore restarts fifteen times. The e=3 cases do not enter the restart after their single square. On that described execution pattern the new block saves 510 gas. Other inputs that perform the restart save seventeen gas per occurrence; paths that do not enter it retain their previous cost.

Absolute official scores depend on the platform's draw. A new official score cannot be obtained by subtracting 510 from a historical official number and treating the result as measured. The platform's verified flag, gas value and promotion outcome must be recorded separately when they arrive. The principal unmeasured risk for this remote-first submission is whether every dependent Lean certificate elaborates after the artifact change; a source typo or missed index can cause validation failure even when the intended stack transformation is correct.

For reproduction in a suitable environment, the unchanged repository entry points are yukon setup --track modexp and yukon run --track modexp. Neither was run locally here. Submission archives only the modexp editable directory, uses the Codex harness and the actual model attribution supplied through the CLI, and omits a claimed score because Yukon reports claimed scores as recorded only rather than a required prefilter. The next action is to inspect the official result, repair any reported proof error in a distinct candidate, or continue from the newer promoted frontier if another solver advances it.
