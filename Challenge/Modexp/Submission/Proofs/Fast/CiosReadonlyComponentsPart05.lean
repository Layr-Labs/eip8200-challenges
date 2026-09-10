import Challenge.Modexp.Submission.Proofs.Fast.CiosReadonlyComponentsPart04

set_option warningAsError true
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.Proofs.Fast.CiosReadonly

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open WindowNibbleKernel CiosCachedMacCore CiosCached CiosCachedMidDefs
open Monpro
open CiosEndAroundCarry

theorem run_dropCache (s : State) (tl inv m0 aEnd m96 m64 m32 dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998) :
    runInstructions dropCache
      (framed s (UInt256.ofNat 4877) ([inv,m0,tl,m96,m64,m32,aEnd,dst,ret] ++ rest)) =
    some (framed s (UInt256.ofNat 4884) ([dst,ret] ++ rest)) := by
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  simp [dropCache, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    framed, hc3, hc4, hc5, hc6, hc7, hc8, hc9, Challenge.EvmProof.Word.succ_ofNat_mod]

end Challenge.Modexp.Submission.Proofs.Fast.CiosReadonly
