import Challenge.Ripemd160.Reference.Proofs.Bytecode.CompressionSeamBridge
import Challenge.Ripemd160.Reference.Proofs.Bytecode.OutputResultBridge
import Challenge.Ripemd160.Reference.Proofs.Bytecode.ExactGasBridge

set_option warningAsError true

/-!
# Final RIPEMD-160 reference-bytecode theorem

This is the public aggregation layer for the direct EVM proof.  Functional
output serialization is closed by `OutputResultBridge`; exact cost arithmetic
is closed by `ExactGasBridge`.  The only remaining inputs are the concrete
compressor run and the two potential equations that still have to be obtained
from the compression and outer trace implementations.

In particular, there is no separate assumption about the returned digest:
`CompressionRun.hashWords` implies `CompressionSeam.finalWords`, and the output
bridge derives all 32 returned bytes from those five words.
-/

namespace Challenge.Ripemd160.Reference.Proofs.Bytecode.FinalCorrectness

open Challenge.Ripemd160
open Challenge.EvmProof

/-- The exact outstanding proof interface.

`run` contains one compiled compression trace per padded block and its
per-block hash-word invariant.  `compressionCost` states only the compressor's
memory-potential equation.  `outerCost` states the independently checkable
padding/framing costs and the two active-memory boundary values.

No result-byte equality, whole-program trace, or whole-program gas equality is
assumed here; all three are derived below. -/
structure RemainingFacts : Type where
  run : ∀ (input : ByteArray), CalldataFits input →
    CompressionSeamBridge.CompressionRun input
  compressionCost : ∀ (input : ByteArray) (hfit : CalldataFits input),
    ExactGasBridge.CompressionCostFacts input
      (CompressionSeamBridge.toCompressionSeam (run input hfit))
  outerCost : ∀ (input : ByteArray) (hfit : CalldataFits input),
    ExactGasBridge.OuterCostFacts input hfit
      (CompressionSeamBridge.toCompressionSeam (run input hfit))

/-- The `DirectCorrect` seam is derived, rather than independently assumed. -/
def seam (facts : RemainingFacts) (input : ByteArray)
    (hfit : CalldataFits input) :
    DirectCorrect.CompressionSeam input :=
  CompressionSeamBridge.toCompressionSeam (facts.run input hfit)

/-- Exact cost of the same end-to-end trace used for functional correctness. -/
theorem fullTrace_cost (facts : RemainingFacts) (input : ByteArray)
    (hfit : CalldataFits input) :
    (DirectCorrect.fullTrace input hfit (seam facts input hfit)).cost =
      GasCost.referenceGas input := by
  exact ExactGasBridge.fullTrace_cost input hfit (seam facts input hfit)
    (facts.compressionCost input hfit) (facts.outerCost input hfit)

/-- The reference bytecode is correct at the closed exact gas schedule.

The digest postcondition is supplied by `OutputResultBridge`, not by a field of
`RemainingFacts`. -/
theorem correctWithSchedule (facts : RemainingFacts) :
    GasCost.CorrectWithSchedule referenceBytecode
      GasCost.referenceGasForSize := by
  apply OutputResultBridge.correctWithSchedule_of_compression (seam facts)
  intro input hfit
  exact fullTrace_cost facts input hfit

/-- Final minimal challenge theorem. -/
theorem correct (facts : RemainingFacts) : Correct referenceBytecode :=
  GasCost.correct_of_schedule (correctWithSchedule facts)

end Challenge.Ripemd160.Reference.Proofs.Bytecode.FinalCorrectness
