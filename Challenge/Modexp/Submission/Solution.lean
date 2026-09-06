import Init.Data.ByteArray.Lemmas
import Challenge.Modexp.Benchmark.Artifact
import Challenge.Modexp.Submission.Proof.Top

set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace Challenge.Modexp.Benchmark
open Challenge.Modexp.Submission (correct_of_asm programAsm programInstrs)
open YulEvmCompiler (assemble assembleBytes)

open Challenge.Modexp.Submission.Proof.Top (hlow hsmall hcert hne program_correct)

/-!
# The MODEXP submission

`Proof.Top.program_correct` proves the full Asm-level run of `programAsm`
from the challenge's fixed initial state for every valid input, and
`Bridge.correct_of_asm` lifts that run — through the pinned compiler's
simulation theorem and the kernel-checked stack certificate — to
`Correct (assemble programInstrs)`.

The benchmark's `bytecode` is the chunked literal regenerated from
`Submission/bytecode.hex` by `scripts/yukon_benchmark.py prepare`; it is
the same 2187 bytes as `assemble programInstrs`. `artifact_eq` checks this
at the flat-list level (`Array.toList_inj` on `.data`, with core's
`toList_data_append` unfolding the chunk concatenation into plain list
appends), so the kernel never evaluates a byte-array append or an
elementwise array comparison.
-/

/-- The submitted artifact is exactly the assembled program. -/
theorem artifact_eq : bytecode = assemble programInstrs := by
  have h1 : bytecode.data.toList = assembleBytes programInstrs := by
    unfold bytecode
    simp only [ByteArray.toList_data_append]
    decide
  have h2 : bytecode.data = (assembleBytes programInstrs).toArray :=
    Array.toList_inj.mp (by rw [h1])
  exact ByteArray.ext h2

/-- Correctness of the submitted MODEXP bytecode. -/
theorem candidate : Challenge.Modexp.Correct bytecode := by
  rw [artifact_eq]
  exact correct_of_asm hlow hsmall hcert hne program_correct

end Challenge.Modexp.Benchmark
