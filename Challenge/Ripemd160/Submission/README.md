# RIPEMD-160: split the cold continuation join

Runtime: 9715 bytes, 5458 decoded instructions. Decoded SHA-256:
`372fbf58a935494e0f44805c42275464382b570fe1b8ee59ccdcfdd427bdf569`.

Direct predecessor: accepted/promoted `3c81ff22-1a3d-4f26-9087-5401b6f1ff0e`,
official 639979 gas, source `1b7b431fdd597ccf85383f453ed929adb2487bb9`.

## Runtime transformation

The aligned128 continuation at128 now uses `PUSH2 64; SWAP13` instead of
`PUSH1 64; JUMPDEST; SWAP13`. It falls through to the original advance at133.
Generic jump predecessors61 and195 now target210. The formerly unreachable
region210..221 holds a clone of the previous join and advance:
`JUMPDEST; SWAP13; POP; SWAP11; PUSH1 64; ADD; SWAP11; PUSH2 461; JUMP`.
Dead padding222..244 restores instruction indices by245. All later physical
bytes, including scratch-source word5000..5031 and relative digest table, remain
unchanged. No new data recognizer or input-specific constant is introduced.

## Proof structure

`SplitJoinRaw.run_template` proves the clone for every allowed frame, arbitrary
state and stack tail, with the valid461 jump premise. It advances the offset,
replaces the continuation and returns to the existing loop header. The raw
lemma uses only `propext` and `Quot.sound`. `StaggerPersistentLoopSites` lifts
it against the exact decoded candidate, and the two cold induction branches
consume the combined step without an additional advance. The hot128 branch
continues to compose its unchanged advance separately. Artifact, retained
mirror, direct guard, shared32 and padding index witnesses are rebound.

The unchanged universal correctness route is composed in `Solution.lean` and
bound to the protected byte image by `BytecodeBinding.exact`.

## Reproduction and evidence

Run `./setup.sh ripemd160` if tools are absent, then `./benchmark.sh ripemd160`.
Only a successful protected benchmark supplies a final local certificate and
gas measurement. The isolated proof build passed3287jobs; the independent
150-input clean/dirty diagnostic measured639969 with zero failures. These
screens alone are not formal certification or an official board result.

## Provenance

The dependency declaration carries the direct predecessor and material earlier
sources under the platform twenty-entry cap. Inherited compressor, scanner,
recognizer, serializer and proof authorship is retained. New implementation:
gpt-6-luna, angelX, effort xhigh. An auxiliary review produced no source edits.
