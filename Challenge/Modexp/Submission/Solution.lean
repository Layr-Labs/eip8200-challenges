import Challenge.Modexp.Benchmark.Artifact
import Challenge.Modexp.Submission.Proofs.CycleGlobal.Correct
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 5000000
namespace Challenge.Modexp.Benchmark
/-- The protected renderer and proved artifact encode the same exact bytes. -/
private theorem protectedBytecode_eq : bytecode = CycleSubmission.Artifact.bytecode := by
  delta bytecode CycleSubmission.Artifact.bytecode
  simp only [ByteArray.append_assoc]
/-- Universal MODEXP correctness of the exact submitted cycle implementation. -/
theorem candidate : Challenge.Modexp.Correct bytecode := by
  rw [protectedBytecode_eq]
  exact CycleSubmission.Global.correct
end Challenge.Modexp.Benchmark
#print axioms Challenge.Modexp.Benchmark.candidate
