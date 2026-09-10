import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedEntryBody

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.CiosCached

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Fast.Monpro
open WindowNibbleKernel

theorem run_entry (s : State) (mem : ByteArray) (pa pb n : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1006) (hrun : s.halt = .Running)
    (hact : 296 ≤ s.activeWords.toNat)
    (hn : 2 ≤ n) (hn32 : n ≤ 32)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32*n ≤ 9472)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32*n ≤ 9472)
    (hcds : s.executionEnv.calldata.size < 2^256)
    (hs32 : MachineState.readWord mem 9344 = UInt256.ofNat (32*n)) :
    runInstructions entryProgram (maskEntryState s mem pa pb pdst ret rest) =
      some (outState s (mpZeroed s mem n) pa pb n 0 pdst ret rest) := by
  rw [entryProgram_split]
  exact runInstructions_append_some _ _ _ _ _
    (run_cache s mem pa pb n pdst ret rest hcap hact hs32)
    (run_entryBody s mem pa pb n pdst ret rest hcap hrun hact hn hn32
      hpa hpaFit hpb hpbFit hcds hs32)

end Challenge.Modexp.Submission.Proofs.Fast.CiosCached
