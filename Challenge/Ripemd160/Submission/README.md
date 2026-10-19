# RIPEMD-160: seed-independent size-32 return specialization

Runtime: 9715 bytes, 5458 instructions, SHA-256 `da379e248f52cd0d0b815aec7015bf27cf826c3ed6eef127236c17451c2c4e84`.
Direct promoted predecessor: a6d866d5-e02c-497e-8c04-ff511d38d093, score640023, pinned7ddbe603.
Protected worktree `./benchmark.sh ripemd160` completed exit0: score640012, clean=dirty,49vectors, Lean Comparator accepted.
Official validation/promotion is separate and is not claimed by this README.

## Mechanism

Only bytes145..146 of the old prefix change: PC144 PUSH2 installs9667 rather than4733.
Append the existing serializer4733..4781, changing its final PUSH1 32 to CALLDATASIZE.
The appended48byte serializer handles the size32 path, cutting1gas for any arbitrary32byte input that reaches it.
Eleven generated32byte vectors save11gas aggregate on each of five paired seeds tested.
No new literal recognition or comparison, and no change to the original general serializer/compressor.

## Correctness

PC144 can also run for non32byte calldata. ColdGuardFixup and PaddingTraceCore explicitly
model the temporary new continuation on that route; the normal loop replaces it before returning.
Return32Output/Finish/Serialize/SerializeMath certify appended exact artifact slices and require
calldata.size=32 for the CALLDATASIZE terminal. Shared32Core/TailCorrect and GenericFramedCorrect
propagate the new continuation and prove its JUMPDEST validity. Empty/non32byte paths still use the
original serializer. Opaque stack suffixes, memory expansion, returned byte padding, and both frame
forms retain their proofs. Artifact and retained-terminal mirrors are bound to exact new bytes.
Benchmark.candidate axioms remain propext,Classical.choice,Quot.sound. No sorry,new axioms,native_decide,
or trusted harness/scorer edits are included.

## Verification

`./benchmark.sh ripemd160` is the required protected gate (without BENCHMARK_INSECURE_LOCAL).
It generates protected Artifact/Challenge and checks universal candidate correctness before scoring.
Independent native scorer:98/98clean/dirty outcomes,640012each. Five paired corpus seeds show delta-11
in every case.279extra inputs in bothframes:0digest failures,129save1gas,150tie.
These are supporting measurements, not a substitute for official evaluation.

## Attribution

All inherited code/proofs retain upstream authorship. Direct dependency and ancestors are declared
with the submission. New work is the return specialization and universal proof/binding integration.
Earlier generated-literal hook e585185d was officially rejected640947 despite default610521; neither
that hook nor the cached literal followup is included here. Use paired varied-seed measurements.
