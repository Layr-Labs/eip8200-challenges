import Challenge.Modexp.Submission.Proofs.Fast.CarryRowTrace
import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedPointers

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.Proofs.Fast.CarryRowRun
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast
open Monpro CiosCached CiosCachedMacCore CarryRowModel CarryScratchAgreement
open CiosCachedMidMemory

theorem run_tail (s : State) (c f pbi pa pb flag cy ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1006) (hact : 88 ≤ s.activeWords.toNat)
    (htarget : Decode.isValidJumpDest s.executionEnv.code pa.toNat = true) :
    runInstructions CarryRowPrograms.tail
      (framed s (UInt256.ofNat 4039)
        ([c,f,pbi,pa,pb,flag,negative32,allOnes,cy,ret] ++ rest)) =
    some (framed {s with memory := tailMemS s.memory cy c}
      (if UInt256.isTrue (UInt256.gt (negative32+pbi) pb) then pa else UInt256.ofNat 4058)
      ([negative32+pbi,pa,pb,flag,negative32,allOnes,slotOverflow cy c + f,ret] ++ rest)) := by
  have h1 := CarryRowTrace.run_tailStore s c f pbi pa pb flag cy ret rest hcap hact
  have h2 := CiosCachedTailTest.run_test {s with memory := tailMemS s.memory cy c}
    pbi pa pb flag (slotOverflow cy c + f) ret rest hcap htarget
  have h := runInstructions_append_some _ _ _ _ _ h1 h2
  simpa only [CarryRowPrograms.tail, CiosCachedTailDefs.testProgram,
    CiosCachedTailDefs.tailLoopProgram, CiosCachedTailDefs.baseStack, List.drop_take] using h

end Challenge.Modexp.Submission.Proofs.Fast.CarryRowRun
