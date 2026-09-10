import Challenge.Modexp.Submission.Proofs.Fast.CiosReadonlyComponentsPart16

set_option warningAsError true
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.Proofs.Fast.CiosReadonly

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open WindowNibbleKernel CiosCachedMacCore CiosCached CiosCachedMidDefs
open Monpro
open CiosEndAroundCarry

theorem run_cachedProduct (s : State) (bi pbi pa pb flag target2 inv m0 aEnd m96 m64 m32 dst ret : UInt256)
    (n : Nat) (rest : List UInt256) (hcap : rest.length ≤ 998) (hn : n ≤ 32)
    (hact : 296 ≤ s.activeWords.toNat) :
    let tl := UInt256.ofNat (8224+32*n)
    let t0 := MachineState.readWord s.memory (8224+32*n)
    runInstructions cachedProduct
      (framed s (UInt256.ofNat 4562)
        (cacheStack bi pbi pa pb flag target2 tl inv m0 aEnd m96 m64 m32 dst ret rest)) =
    some (framed s (UInt256.ofNat 4578)
      ([endCarry t0 (UInt256.mulMod m0 (inv*t0) maxWord),inv*t0] ++
        cacheStack bi pbi pa pb flag target2 tl inv m0 aEnd m96 m64 m32 dst ret rest)) := by
  let tl := UInt256.ofNat (8224+32*n)
  let t0 := MachineState.readWord s.memory (8224+32*n)
  have h1 := run_cachedLoadLow s bi pbi pa pb flag target2 inv m0 aEnd m96 m64 m32 dst ret n rest hcap hn hact
  have h2 := run_cachedMakeMu s bi pbi pa pb flag target2 tl inv m0 aEnd m96 m64 m32 dst ret t0 rest hcap
  have h3 := run_cachedLoadMask s bi pbi pa pb flag target2 tl inv m0 aEnd m96 m64 m32 dst ret (inv*t0) t0 rest hcap
  have h4 := run_cachedMakeModProduct s bi pbi pa pb flag target2 tl inv m0 aEnd m96 m64 m32 dst ret (inv*t0) t0 rest hcap
  have h5 := run_cachedFinishCarry s bi pbi pa pb flag target2 tl inv m0 aEnd m96 m64 m32 dst ret
    (UInt256.mulMod m0 (inv*t0) maxWord) (inv*t0) t0 rest hcap
  have h12 := runInstructions_append_some _ _ _ _ _ h1 h2
  have h123 := runInstructions_append_some _ _ _ _ _ h12 h3
  have h1234 := runInstructions_append_some _ _ _ _ _ h123 h4
  exact runInstructions_append_some _ _ _ _ _ h1234 h5

end Challenge.Modexp.Submission.Proofs.Fast.CiosReadonly
