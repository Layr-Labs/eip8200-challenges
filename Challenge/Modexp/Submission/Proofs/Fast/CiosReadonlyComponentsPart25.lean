import Challenge.Modexp.Submission.Proofs.Fast.CiosReadonlyComponentsPart24

set_option warningAsError true
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.Proofs.Fast.CiosReadonly

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open WindowNibbleKernel CiosCachedMacCore CiosCached CiosCachedMidDefs
open Monpro
open CiosEndAroundCarry

theorem run_cachedProduct_model (s : State)
    (bi pbi pa pb flag target2 tl inv m0 aEnd m96 m64 m32 dst ret : UInt256)
    (n : Nat) (rest : List UInt256) (hcap : rest.length ≤ 998) (hn : n ≤ 32)
    (hact : 296 ≤ s.activeWords.toNat)
    (hc : ReadonlyCache s.memory n tl inv m0)
    (hminv : CiosCachedMidMemory.inverseInvariant s.memory n) :
    runInstructions cachedProduct
      (framed s (UInt256.ofNat 4562)
        (cacheStack bi pbi pa pb flag target2 tl inv m0 aEnd m96 m64 m32 dst ret rest)) =
    some (framed s (UInt256.ofNat 4578)
      ([rowC0 s.memory n,rowMu s.memory n] ++
        cacheStack bi pbi pa pb flag target2 tl inv m0 aEnd m96 m64 m32 dst ret rest)) := by
  rw [hc.lowAddress, hc.inverse, hc.modulusLow]
  have hr := run_cachedProduct s bi pbi pa pb flag target2
    (MachineState.readWord s.memory 9376) (MachineState.readWord s.memory (32*n-32))
    aEnd m96 m64 m32 dst ret n rest hcap hn hact
  have hcarry := row_carry_swapped (MachineState.readWord s.memory (32*n-32))
    (MachineState.readWord s.memory 9376) (MachineState.readWord s.memory (8224+32*n)) hminv
  simpa only [hcarry, rowC0, rowMu] using hr

end Challenge.Modexp.Submission.Proofs.Fast.CiosReadonly
