import Challenge.Modexp.Submission.Proofs.Fast.CiosReadonlyComponentsPart14

set_option warningAsError true
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.Proofs.Fast.CiosReadonly

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open WindowNibbleKernel CiosCachedMacCore CiosCached CiosCachedMidDefs
open Monpro
open CiosEndAroundCarry

theorem run_cachedFinishCarry (s : State)
    (bi pbi pa pb flag target2 tl inv m0 aEnd m96 m64 m32 dst ret mm mu t0 : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998) :
    runInstructions finishCarry
      (framed s (UInt256.ofNat 4572)
        ([mm,t0,mu] ++ cacheStack bi pbi pa pb flag target2 tl inv m0 aEnd m96 m64 m32 dst ret rest)) =
    some (framed s (UInt256.ofNat 4578)
      ([endCarry t0 mm,mu] ++ cacheStack bi pbi pa pb flag target2 tl inv m0 aEnd m96 m64 m32 dst ret rest)) := by
  have hc20 : rest.length + 20 < 1024 := by omega
  have hc21 : rest.length + 21 < 1024 := by omega
  simp [finishCarry,
    runInstructions, Challenge.EvmProof.Stepper.runInstr,
    framed, cacheStack, baseStack, Nat.add_assoc, hc20, hc21, endCarry,
    List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod]

end Challenge.Modexp.Submission.Proofs.Fast.CiosReadonly
