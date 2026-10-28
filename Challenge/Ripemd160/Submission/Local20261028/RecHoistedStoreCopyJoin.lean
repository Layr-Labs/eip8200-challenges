import Challenge.Ripemd160.Submission.Local20261028.RecHoistedStoreAnchor
import Challenge.Ripemd160.Submission.Local20261028.ColdPaddingTrace
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.Control.HoistedStoreCopyJoin
open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM

/-- The missed hoisted scanner keeps exactly one harmless zero stack cell. -/
theorem copied_initial (input : ByteArray) (rho : List UInt256) :
    RetainedFallback114.copied (initialState Control.submissionBytecode input 0) rho =
      StackTail.append (Control.PaddingTrace.padCopied input) rho := by
  simp only [RetainedFallback114.copied, Control.PaddingTrace.padCopied,
    Control.PaddingTrace.padCopyDone, Control.PaddingTrace.padLengthReady,
    Control.PaddingTrace.padEntry, Control.Main.initializedState,
    StackTail.append]
  rfl

#print axioms copied_initial
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.Control.HoistedStoreCopyJoin
