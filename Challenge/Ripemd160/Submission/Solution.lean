import Challenge.Ripemd160.Benchmark.Artifact
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionCorrect

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000

namespace Challenge.Ripemd160.Benchmark

/-- Exact-bytecode correctness for the direct stack-resident compressor. -/
theorem candidate : Challenge.Ripemd160.Correct bytecode := by
  change Challenge.Ripemd160.Correct Challenge.Ripemd160.submissionBytecode
  exact Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard.correct_of_recognition
    Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionCorrect.from_entry

end Challenge.Ripemd160.Benchmark

#print axioms Challenge.Ripemd160.Benchmark.candidate
-- redraw marker 2026-09-15T09:15:23Z
-- Yukon reuse by @i34-9: source @ercumentyildirim, submission b6cd6b15-6fe8-48e2-bf2d-18d7d4b77aa9, commit ef17a52c1.
-- provenance marker RIPC0-30e4ab42-v1
-- base is NOT our work: submission b6cd6b15-6fe8-48e2-bf2d-18d7d4b77aa9, executable cf3e0c0d3449e0ea4304b0807ab90cf3a11e8e690d1dcbafc94c00ce7c975004, 5212 bytes, 664022 gas.
-- predecessor cf3e0c0d3449e0ea4304b0807ab90cf3a11e8e690d1dcbafc94c00ce7c975004, 5212 bytes, 664022 gas.
-- executable 30e4ab4256a50425c21370d99efee74f8f942e1265fa23a0c751b68f4cf39189, 5212 bytes, 664008 gas, 8187 units of the 8194 budget, derived from cf3e0c0d3449e0ea4304b0807ab90cf3a11e8e690d1dcbafc94c00ce7c975004 at 664022 gas by a single change. The predecessor line deletes an eagerly-built recogniser constant and leaves a one-byte JUMPDEST at offset 138 as padding; that JUMPDEST is dead. No PUSH immediate names offset 138, and every JUMP and JUMPI in the artifact is immediately preceded by a literal PUSH, so the set of reachable jump targets is statically complete and does not contain it. It is therefore pure fall-through cost, one gas on each of the fourteen scored vectors that reach the ordinary path. Deleting it frees one byte, which is returned by widening the PUSH2 0x00fb at offset 141 to PUSH3 0x0000fb: a PUSH costs three gas at every width and the pushed value is unchanged. The length stays 5212, so the digest table keeps its CODESIZE-relative position, and every instruction from offset 144 onward keeps its exact program counter. Three bytes differ from the predecessor.
-- model Claude Opus 5 (1M context), harness Claude Code.
