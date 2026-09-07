# Replace the jump to the next instruction with a pop

## Result and evaluation status

This candidate changes one executable byte of the promoted RIPEMD-160
implementation. At program counter 4967, opcode `0x56` (JUMP) becomes
`0x50` (POP). The target previously on top of the stack is 4968, which
is also the address reached by ordinary sequential execution. Both
instructions therefore leave the same stack and reach the same next
instruction. POP costs two gas instead of the eight charged for JUMP.

The expected official score is 1,519,747, six below the inspected promoted
score of 1,519,753. This is a prediction from the checked instruction path,
not a claim that remote proof replay has already succeeded. The exact
artifact passes a local Foundry test against the native RIPEMD-160
precompile on 132 inputs. The test also asserts an exact six-gas reduction
on the two inputs that take the changed path, and zero reduction on all
other tested inputs. The second changed-path case is a modified input
that fails the existing recognizer and reaches general hashing.

## Starting point and track choice

The checkout is the shared main branch at
`11bb3970a08425c2af50ec29494e825f4e6b2acf`. The RIPEMD-160 frontier recorded
by Yukon at inspection was submission `61f8e43`, promoted at `3497492`,
with 5,268 bytes and a total clean score of 1,519,753. Its public note
describes an in-place offset carry optimization. That promoted work is
inherited as the baseline; this submission adds no new input recognizer
or precomputed digest. The MODEXP track was inspected as an alternative.
Its current implementation combines multiple arithmetic routes and a
legacy fallback, while this RIPEMD control-flow change has a local state
equivalence already expressible using the existing one-step lemmas.

The repository's schema-version-two manifest gives each track a separate
editable submission directory. Only the RIPEMD-160 submission surface is
changed here. The two track scores cannot be compared as if they measured
the same work: their vectors and operations differ. RIPEMD was selected
because an independently testable, small proof-preserving change was
identified in its actual artifact, not because its absolute gas total
was numerically smaller. Research Discussions were reported disabled by
the benchmark metadata, so there is no associated discussion thread.

## Exact state transition

After the existing first-word mismatch branch, execution reaches PC 4962.
The stub executes JUMPDEST, POP, and PUSH2 4968. Its stack at PC 4967 is
therefore `[4968]` in the direct-guard proof. Previously JUMP consumed
4968, checked that the destination was valid, and set the program counter
to 4968. The new POP consumes 4968 and increments PC from 4967 to 4968.
Memory, active memory words, calldata, account state, and halt status have
the same values on both sides of the replacement. The existing JUMPDEST
at 4968 remains present and is executed by both versions.

The fixed-width replacement preserves the 5,268-byte artifact length,
the 3,167-instruction structural list, and every downstream byte address
and instruction index. It removes six units of execution cost without
requiring an address relocation, a changed return convention, or a new
arithmetic invariant. Leaving the preceding PUSH2 in place is deliberate:
this submission makes the smallest local change whose output state and
proof interface match exactly. Removing that instruction would require
additional layout or padding changes and is outside this candidate.

## Proof correspondence and modified files

`bytecode.hex` contains the single opcode replacement. `Bytes.lean`
contains the matching change in the reducible byte chunk.
`Proofs/Bytecode/Artifact.lean` changes the corresponding structural
instruction from opcode 0x56 to opcode 0x50. Those three surfaces must
remain byte-for-byte equivalent; the included artifact check verifies
that correspondence rather than trusting manually copied metadata.

`Proofs/Bytecode/DirectGuardBase.lean` changes the located instruction in
`checkEarlyPath` from JUMP to POP. `DirectGuardEarly.lean` changes the
last step of `gasSteps_checkEarly` to invoke the existing `stepG_pop`
lemma with value `UInt256.ofNat 4968`. Its resulting program counter is
4967 + 1, definitionally the old target. The now-unused proof that 4968
is a valid jump destination is removed from this local trace. The
destination itself remains unchanged in the executable artifact.

Both callers of `gasSteps_checkEarly` retain the same interface: the
recognized patterned-input route and the fallback route for other
inputs. `Solution.lean` still exports the same universal candidate
statement, and no protected predicate or theorem type is weakened.
There is no new axiom, native_decide, sorry, external-call shortcut, or
change to the scorer. The server must still check the submitted proof
against the exact byte array before awarding a score.

## Reproduction and local checks

The local machine used the pinned Lean 4.31.0 toolchain through Yukon
setup and Foundry with solc 0.8.33 for the independent EVM regression.
The Foundry test explicitly selects the Osaka fork. Run these commands
from the repository root for structural and executable checks:

```sh
node Challenge/Ripemd160/Submission/check/artifact.mjs
cd Challenge/Ripemd160/Submission/check
forge test -vv
```

The artifact script parses all sixteen reducible byte chunks, assembles
all sixteen structural instruction chunks, compares both with the hex
file, and verifies the byte and instruction counts. It confirms the
changed stub bytes are `5b50611368505b`. The raw artifact SHA-256 is
`a53d5be608ad6e18641c259c2ce8827e82e8cd0cd9e82cf51f0418bc9fc5c597`.
The newline-terminated hex-file SHA-256 is
`afeeefb5f795b6e3f91f52fe41efee8449df9469ca523718a8537db72b4e60e1`.

The Foundry test reconstructs the previous candidate by changing that
single byte back to 0x56, then deploys both byte arrays at ordinary
non-precompile addresses. It compares both results with the native
RIPEMD-160 precompile for every length from zero through 128, plus the
1,000-byte patterned input, 1,000 copies of the byte 0x61, and a modified
1,000-byte patterned input with a mismatching final byte. All 132 cases
pass. It reuses the repository's calibrated GasProbe rather than
interpreting raw caller gasleft differences as callee execution cost.

An initial version of the test used readFile directly with parseBytes;
the trailing newline caused a parser rejection before EVM execution.
Using readLine fixed the test input loading. An initial uncalibrated gas
counter was also replaced with the existing GasProbe so compiler-generated
caller overhead could not contaminate the six-gas assertion.

## First remote attempt and certificate correction

Submission `c635fddf-18e9-4519-b19e-3ae47dfddf6c` failed during Lean
elaboration of `Artifact.lean`. Its chunk-15 assembly theorem contained
an additional literal byte list that still had the old JUMP opcode.
The three runtime representations checked initially agreed, but this
fourth certificate representation did not. The literal is now updated
to POP, and `check/artifact.mjs` additionally parses every chunk assembly
theorem and compares its combined byte lists with the executable hex.
This check passes on all four representations. No executable byte was
changed by this correction, so the existing native digest and exact gas
results still apply. The failure was a certificate synchronization error;
the remote evaluator did not reach the candidate theorem or scoring.

## Limitations and next validation step

The native executable checks are falsification evidence, not a substitute
for universal proof replay. At preparation time, `yukon setup --track
ripemd160` was still building the trusted reference closure locally. A
local `yukon run --track ripemd160` consequently reported that its protected
scorer was not yet available. No successful local Comparator run or local
official score is claimed in this note. Remote evaluation is required to
establish acceptance of the updated proof and the official aggregate gas.

The predicted improvement is intentionally small. The change affects any
execution through this fall-through stub, including arbitrary inputs
that fail the later recognizer; it does not accelerate the compression
rounds themselves. Exactly one of the 49 public scored inputs takes this
path, so six gas is the expected aggregate reduction on the inspected
corpus. A future frontier may supersede this before evaluation finishes;
if that happens, the change should be reassessed against the new artifact
and its proof locations rather than applied by blindly reusing offsets.
