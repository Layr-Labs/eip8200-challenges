import Challenge.Ripemd160.Submission.Proofs.Bytecode.CompressionRunTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.CompressionGasComposition
import Challenge.Ripemd160.Submission.Proofs.Bytecode.OuterGasTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.FinalCorrectness

set_option warningAsError true

/-!
# End-to-end correctness of the frozen RIPEMD-160 reference bytecode

This final layer installs the concrete compression run and the independently
proved compression and outer-trace gas facts in `FinalCorrectness`.  It exposes
both the exact closed gas schedule and the minimal challenge theorem without
additional hypotheses.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.ReferenceCorrect

open Challenge.Ripemd160

/-- The concrete direct-bytecode compression seam for a realizable input. -/
noncomputable def compressionSeam (input : ByteArray)
    (hfit : CalldataFits input) : DirectCorrect.CompressionSeam input :=
  CompressionSeamBridge.toCompressionSeam
    (CompressionRunTrace.compressionRun input hfit)

/-- The final compressor state reaches the exact memory high-water mark used
by the closed gas formula. -/
theorem compression_finalActiveWords (input : ByteArray)
    (hfit : CalldataFits input) :
    ((compressionSeam input hfit).states
        (DriverTrace.blockCount input)).activeWords.toNat =
      GasCost.finalActiveWords input.size := by
  change (CompressionRunTrace.states input
    (DriverTrace.blockCount input)).activeWords.toNat = _
  exact CompressionRunTrace.states_final_activeWords input hfit
    (OuterGasTrace.padReturned_activeWords input hfit)

/-- All formerly open facts of `FinalCorrectness`, supplied by the concrete
execution and gas traces. -/
noncomputable def referenceFacts : FinalCorrectness.RemainingFacts where
  run := CompressionRunTrace.compressionRun
  compressionCost := fun input hfit =>
    CompressionGasIntegration.compressionCostFacts input hfit
  outerCost := fun input hfit =>
    OuterGasTrace.outerCostFacts input hfit (compressionSeam input hfit)
      (compression_finalActiveWords input hfit)

/-- The exact reference gas formula suffices for every realizable calldata
input. -/
theorem reference_correctWithSchedule :
    GasCost.CorrectWithSchedule submissionBytecode
      GasCost.referenceGasForSize :=
  FinalCorrectness.correctWithSchedule referenceFacts

/-- End-to-end canonical challenge theorem for the frozen reference bytes. -/
theorem reference_correct : Correct submissionBytecode :=
  FinalCorrectness.correct referenceFacts

end Challenge.Ripemd160.Submission.Proofs.Bytecode.ReferenceCorrect
