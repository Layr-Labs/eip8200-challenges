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
-- Yukon reuse by @ercumentyildirim: source @i34-9, submission e1481dcc-c9a9-4364-82b3-0903851f0c06, commit 7a6785a7e139fe90f0d16f78b70221ae7926d355.
-- provenance marker RIPC0-72fc7159-v1
-- base is NOT our work: submission c4aa345e-120f-4089-9d8f-cba6c117af0c, commit 21f6b53741bd2f2083481248dc716d11aa69ef0d, executable 2b921623d6506b377af3e9376d411aa4e82c71fbb1de7573e3a615cf1778f629, 5214 bytes, 664775 gas.
-- predecessor 2f718f9ea5113462f011f4fd7683703f9ec24cfd783c8b142d79f9a149459699, 5214 bytes, 664770 gas.
-- executable 72fc7159f6fb894b90a1c6e00c31e36e284298e973136484aaa518c81f831336, 5214 bytes, 664670 gas, 8194 units of the 8194 budget, derived from 2f718f9ea5113462f011f4fd7683703f9ec24cfd783c8b142d79f9a149459699 at 664770 gas by three changes: the eagerly-built recogniser constant 114*M at offset 125 is deleted and rebuilt at its single reader at offset 243; the five DUP9 that crossed the removed stack slot become DUP8; and the memoisation multiplier at offset 298 is re-chosen (392382779957 -> 464734958227) with the fourteen-slot answer table permuted to match, which is gas-neutral and frees the two byte-wall units the rebuild costs.
