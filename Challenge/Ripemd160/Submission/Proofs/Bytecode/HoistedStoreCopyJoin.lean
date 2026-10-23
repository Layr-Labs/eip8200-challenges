import Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedStoreAnchor
import Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.PaddingTrace
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedStoreCopyJoin
open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM

/-- The missed hoisted scanner keeps exactly one harmless zero stack cell. -/
theorem copied_initial (input : ByteArray) (rho : List UInt256) :
    RetainedFallback114.copied (initialState HoistedInherited.submissionBytecode input 0) rho =
      StackTail.append (HoistedInherited.PaddingTrace.padCopied input) rho := by
  simp only [RetainedFallback114.copied, HoistedInherited.PaddingTrace.padCopied,
    HoistedInherited.PaddingTrace.padCopyDone, HoistedInherited.PaddingTrace.padLengthReady,
    HoistedInherited.PaddingTrace.padEntry, HoistedInherited.Main.initializedState,
    StackTail.append]
  rfl

#print axioms copied_initial
end Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedStoreCopyJoin
