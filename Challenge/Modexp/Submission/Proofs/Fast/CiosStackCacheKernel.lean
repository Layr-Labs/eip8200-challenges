import Challenge.Modexp.Submission.Proofs.Fast.CiosStackCacheRows

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 400000

namespace Challenge.Modexp.Submission.Proofs.Fast.CiosStackCache.Gas

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs.Bytecode WindowTwentyOneBinding WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast.Monpro
open Challenge.Modexp.Submission.Proofs.Fast.CiosStackCacheMemory
open Challenge.Modexp.Submission.Proofs.Fast.CiosStackCacheModel
open Challenge.Modexp.Submission.Proofs.Fast.CiosStackCacheInit

/-- Full specialized CIOS call, including initialization and cache flush. The
block interface must be instantiated with the exact submitted artifact. -/
opaque kernel {art : ProgramArtifact} (s : State) (env : Environment art .Osaka s)
    (blocks : KernelBlocks art) (mem : ByteArray) (pa pb n : Nat)
    (dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 296 ≤ s.activeWords.toNat)
    (hw : n = 4 ∨ n = 8)
    (hpa : 32 ≤ pa) (hpaFit : pa+32*n ≤ 8192)
    (hpb : 32 ≤ pb) (hpbFit : pb+32*n ≤ 8192)
    (hcds : s.executionEnv.calldata.size < 2^256)
    (hs32 : MachineState.readWord mem 9344 = UInt256.ofNat (32*n))
    (htl : MachineState.readWord mem 9440 = UInt256.ofNat (8224+32*n))
    (hml : MachineState.readWord mem 9408 = UInt256.ofNat (32*n-32))
    (hminv : ((MachineState.readWord mem (32*n-32)).toNat *
      (MachineState.readWord mem 9376).toNat+1)%2^256 = 0) :
    GasSteps (Entry.artifactEntryState s mem pa pb dst ret rest)
      (mpCsubState s (rowsMem (mpZeroed s mem n) pa pb n n) dst ret rest) := by
  let c := initial s mem n
  let r := ReadOnlyCache.capture mem n
  have hr := rows s env blocks c r pa pb n dst ret rest hcap hact hw hpa hpaFit hpb hpbFit
    (ReadOnlyCache.capture_initial s mem n (by omega) (by omega)) htl hminv
  have he := Entry.run_entry s mem pa pb n dst ret rest hcap env.running hact
    (by omega) (by omega) hpa (by omega) hpb (by omega) hcds hs32 hml
  have he' : runInstructions CiosStackCachePrograms.entry
      (Entry.artifactEntryState s mem pa pb dst ret rest) = some (outAt s c r pa pb n 0 dst ret rest) := by
    simpa only [outAt, rowState, c, r, initial] using he
  have entrySteps := blocks.entry.steps
    (s := Entry.artifactEntryState s mem pa pb dst ret rest) (env.transfer rfl rfl) rfl he'
  have hall := entrySteps.trans hr
  simpa only [c, virtual_cacheRows, virtual_initial s mem n (by omega)] using hall

end Challenge.Modexp.Submission.Proofs.Fast.CiosStackCache.Gas

#print axioms Challenge.Modexp.Submission.Proofs.Fast.CiosStackCache.Gas.kernel
