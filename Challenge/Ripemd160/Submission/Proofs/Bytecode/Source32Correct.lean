import Challenge.Ripemd160.Submission.Proofs.Bytecode.Source32Trace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Source32FinalSemantics
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Source32Correct
open Challenge.Ripemd160 EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open PersistentStaggerFunctional StaggerPersistentFrame

theorem ready (input : ByteArray) (hfit : CalldataFits input) (h32 : input.size = 32) :
    StaggerMessage.Ready (tableState input).memory (PersistentStaggerTable.blockWords input 0) := by
  dsimp only [tableState, sourceState, PaddingTrace.source32Returned, Source32Physical.resultMemory,
    Source32Lower.lowerScratch]
  exact Source32Ready.ready input hfit h32

theorem final_hash (input : ByteArray) (hfit : CalldataFits input) (h32 : input.size = 32) :
    CompressionCorrect.hashArray (finalHash input) =
      CompressionSeamBridge.hashAfter input (DriverTrace.blockCount input) := by
  exact Source32FinalSemantics.hashAfter_of_ready (tableState input).memory input h32
    (ready input hfit h32)

theorem correct (input : ByteArray) (hfit : CalldataFits input) (h32 : input.size = 32)
    (entryPrefix : GasSteps (initialState submissionBytecode input 0) (Execution.atPC input 353)) :
    ∃ g₀ : Nat, ∀ gas : Nat, g₀ ≤ gas →
      Eval (initialState submissionBytecode input gas) (.returned (spec input)) := by
  have hr : (result input).halt = .Returned := rfl
  have hc : (result input).callStack = [] := rfl
  have hb : (result input).hReturn = spec input := by
    change (StaggerPersistentSerialize.result (tableState input) (finalHash input)
      (UInt256.ofNat 64) (UInt256.ofNat 64) maskRho).hReturn = spec input
    exact StaggerPersistentSerialize.returned_spec_of_hashArray (tableState input) input
      (UInt256.ofNat 64) (UInt256.ofNat 64) maskRho (finalHash input) (final_hash input hfit h32)
  exact Source32FinalSemantics.eval_of_return_trace submissionBytecode input (result input)
    (fullTrace input hfit h32 entryPrefix) hr hc hb

#print axioms ready
#print axioms final_hash
#print axioms correct
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Source32Correct
