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

theorem run_tail (s : State) (c mu f pbi pa pb flag dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1006) (hact : 296 ≤ s.activeWords.toNat)
    (route : UInt256)
    (hroute : MachineState.readWord s.memory 9280 = route)
    (htarget : Decode.isValidJumpDest s.executionEnv.code route.toNat = true) :
    runInstructions CarryRowPrograms.tail
      (framed s (UInt256.ofNat 4765)
        ([c,mu,f,pbi,pa,pb,flag,negative32,allOnes,dst,ret] ++ rest)) =
    some (framed {s with memory := tailCarry s.memory c f}
      (if UInt256.isTrue (UInt256.gt (negative32+pbi) pb) then route else UInt256.ofNat 4794)
      ([negative32+pbi,pa,pb,flag,negative32,allOnes,dst,ret] ++ rest)) := by
  have h1 := CarryRowTrace.run_tailStore s c mu f pbi pa pb flag dst ret rest hcap hact
  have h2 := SquareRoute.run_test {s with memory := tailCarry s.memory c f}
    pbi pa pb flag dst ret route rest hcap hact
    ((readWord_tailCarry s.memory c f 9280 (Or.inr (by decide))).trans hroute) htarget
  exact runInstructions_append_some _ _ _ _ _ h1 h2

end Challenge.Modexp.Submission.Proofs.Fast.CarryRowRun
