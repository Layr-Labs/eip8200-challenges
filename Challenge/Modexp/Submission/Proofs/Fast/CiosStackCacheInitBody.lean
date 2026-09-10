import Challenge.Modexp.Submission.Proofs.Fast.CiosStackCacheInitBodyZero
import Challenge.Modexp.Submission.Proofs.Fast.CiosStackCacheInitBodyPointers

set_option warningAsError true
set_option maxHeartbeats 200000

namespace Challenge.Modexp.Submission.Proofs.Fast.CiosStackCacheInitBody

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Fast.Monpro
open Challenge.Modexp.Submission.Proofs.Fast.CiosCached

theorem run_entryBody (s : State) (mem : ByteArray) (pa pb n : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1006) (_hrun : s.halt = .Running)
    (hact : 296 ≤ s.activeWords.toNat)
    (_hn : 2 ≤ n) (hn32 : n ≤ 32)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32*n ≤ 9472)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32*n ≤ 9472)
    (hcds : s.executionEnv.calldata.size < 2^256)
    (hs32 : MachineState.readWord mem 9344 = UInt256.ofNat (32*n)) :
    runInstructions entryBodyProgram (cachedEntryState s mem pa pb n pdst ret rest) =
      some (outState s (mpZeroed s mem n) pa pb n 0 pdst ret rest) := by
  rw [entryBody_split]
  exact runInstructions_append_some _ _ _ _ _
    (run_zero s mem pa pb n pdst ret rest hcap hact hn32 hcds hs32)
    (run_pointers s mem pa pb n pdst ret rest hcap hpa hpaFit hpb hpbFit)

end Challenge.Modexp.Submission.Proofs.Fast.CiosStackCacheInitBody
