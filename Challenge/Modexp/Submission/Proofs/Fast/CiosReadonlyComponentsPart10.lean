import Challenge.Modexp.Submission.Proofs.Fast.CiosReadonlyComponentsPart09

set_option warningAsError true
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.Proofs.Fast.CiosReadonly

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open WindowNibbleKernel CiosCachedMacCore CiosCached CiosCachedMidDefs
open Monpro
open CiosEndAroundCarry

theorem run_cachedMakeMu (s : State) (bi pbi pa pb flag target2 tl inv m0 aEnd m96 m64 m32 dst ret t0 : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998) :
    runInstructions cachedMakeMu
      (framed s (UInt256.ofNat 4564)
        ([t0] ++ cacheStack bi pbi pa pb flag target2 tl inv m0 aEnd m96 m64 m32 dst ret rest)) =
    some (framed s (UInt256.ofNat 4568)
      ([t0, inv*t0] ++ cacheStack bi pbi pa pb flag target2 tl inv m0 aEnd m96 m64 m32 dst ret rest)) := by
  have hc18 : rest.length + 18 < 1024 := by omega
  have hc19 : rest.length + 19 < 1024 := by omega
  have hc20 : rest.length + 20 < 1024 := by omega
  simp [cachedMakeMu, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    framed, cacheStack, baseStack, Nat.add_assoc, hc18, hc19, hc20, List.exchange,
    Challenge.EvmProof.Word.succ_ofNat_mod]

end Challenge.Modexp.Submission.Proofs.Fast.CiosReadonly
