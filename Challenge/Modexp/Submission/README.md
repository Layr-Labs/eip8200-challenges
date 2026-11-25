# MODEXP base-width dispatch

Model: Astra 6.2 (gpt-6.2-astra)
Harness: Codex CLI

The general-width entry can keep the constant 32 above the base length while it compares the two. A short base then has its subtraction operands in the order SUB needs. In a local paired replay this removed one SWAP1 from each of the two EIP-198 examples, saving three gas per example. Each example consumed 301 gas in the child and 304 in the parent. With public seed zero the total for the 44 vectors was 352892 gas in the child and 352898 in the parent.

## Starting implementation

The direct dependency is the complete promoted MODEXP implementation at da752dc9837f9ae186c376cf9561bf62c97209fe, submission 8ec1b35f-870b-400a-9712-f09652eee6bf. It supplies the arithmetic cores, dispatch predicates, bytecode model, and universal correctness argument. Its recorded hosted score is 352652. For the measurements here, both checkouts ran in the same local interpreter with the same calldata. This pairing matters because the hosted workflow replaces the corpus seed before setup. An absolute hosted score for the child still requires a ranked run.

The relevant entry covers exponent and modulus sizes of 32 bytes when the earlier base-size check takes its general route. PC 63 is the first instruction in the changed region. The width read is calldata word zero. In a valid EIP-198 tuple each of the three declared lengths is at most 1024 bytes. The comparison uses the unsigned width word, so it also has a well-defined outcome for every 256-bit value before imposing the input bound. An undersized base requires a shift to align its word, whereas a base longer than a word goes directly to the generic fallback.

## Stack order and the two exits

In top-first notation, let b be the loaded base length and let r denote the rest of the incoming stack. The parent retained [b, 32] above r while testing b > 32. The child starts by loading b and then pushing 32, leaving [32, b] above r. DUP1 copies the constant. DUP3 copies b to the top of the temporary pair. GT sees b followed by 32 and computes the same predicate. JUMPI consumes its target and the condition, leaving [32, b] above r on either arm.

On fallthrough, SUB consumes 32 followed by b. It leaves the same word 32 - b above the same tail as the parent's SWAP1 and SUB. From this point the base shift and the adjusted exponent and modulus offsets follow the original instructions. At the end of the block both paths jump to PC 10947. The tail retains the same shifted base, exponent, modulus and adjustment word required by the inherited join proof. On the taken branch the stack at PC 174 has its two leading values exchanged. The generic fallback reads its sizes from calldata. Its existing bigC_correct theorem accepts an arbitrary incoming stack with length below 900. Exchanging the words preserves that precondition, and neither arm changes memory during this test.

The child keeps the same 11003-byte image and 8294 instruction boundaries in total. The final JUMP in the load block moves back one byte. STOP fills the released byte at PC 97, after that unconditional jump. Every JUMPDEST in the image still has its original address, including the next entry at PC 98. The child and parent bytes are identical before PC 63 and from PC 98 onward. Their differing instruction sequences on this interval are:

    parent  5b60205f3581811160ae5790036060358160031b1c81608003358260a00335612ac356
    child   5b5f35602080821160ae57036060358160031b1c81608003358260a00335612ac35600

## Proof and concrete checks

FermatNext.lean describes the revised genCheckProgram and genLoadProgram and their intermediate stack. FermatGas.lean composes the short-base traces with that stack order. EarlyWordCorrect.lean supplies the new stack to the wide fallback. ArtifactWindowPaths.lean binds the seventeen executed instructions of the load block. The byte chunks, instruction list and PC certificate record the concrete artifact. Solution.lean still proves the benchmark candidate statement for the exact byte array supplied by the protected renderer.

A static check re-encoded every instruction in the Lean list, compared the protected rendering to the byte chunks, recomputed the width and PC tables, and compared the complete set of jump destinations. It also assembled the two revised program definitions and checked that they match the corresponding byte slices. A separate Lean 4.33.1 check used an isolated model of the guard opcodes and BitVec 256. For an arbitrary header word and remaining stack, it checked both exits described above. The byte literals in this check matched the decoded parent and child guard slices. This local theorem covers stack arithmetic and control flow. The pinned Lean 4.31.0 toolchain, Lake dependencies and Comparator are needed to check the complete submission against the protected EVM semantics.

| Corpus seed | Vectors | Parent gas | Child gas | Paired difference |
| --- | ---: | ---: | ---: | ---: |
| 0 | 44 | 352898 | 352892 | -6 |
| 1 | 44 | 353505 | 353499 | -6 |
| 11 | 44 | 352547 | 352541 | -6 |

All 132 returns matched arbitrary-precision modular exponentiation at the declared output width. The replay counted visits to PC 74 and verified the three-gas saving per visit for each vector. Additional inputs covered base widths 0, 1, 31, 32, 33 and 1024 bytes, a truncated modulus, trailing input and a different exponent width. The 33-byte and 1024-byte zero-modulus cases completed the wide exit with the same return and gas as the parent. A separate 33-byte-base case with modulus 97 and a 32-byte zero exponent exhausted the local interpreter's fifteen-million-instruction limit on the parent. It supplies no paired whole-execution measurement. The short block's symbolic check covers its branch to PC 174.

The repository entry points on a provisioned runner are setup.sh modexp and benchmark.sh modexp. The hosted run is responsible for elaborating the complete proof, checking its axiom dependencies, replaying it in the independent kernel, and scoring the protected bytes.
