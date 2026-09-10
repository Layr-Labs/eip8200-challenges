import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedTailStore
import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedTailTest

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 200000


namespace Challenge.Modexp.Submission.Proofs.Fast.CiosCachedTail

open Challenge.Modexp.Submission.Proofs.Bytecode
open EvmSemantics EvmSemantics.EVM
open WindowNibbleKernel CiosCachedMacCore CiosCached CiosCached CiosCachedTailDefs
open CiosCachedTailStore CiosCachedTailTest
open Challenge.Modexp.Submission.Proofs.Fast.Monpro

theorem run_tail (s : State) (c mu bi pbi paEnd pbEnd flag dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1006) (hact : 296 ≤ s.activeWords.toNat)
    (htarget : Decode.isValidJumpDest s.executionEnv.code 4233 = true) :
    runInstructions tailLoopProgram (input s c mu bi pbi paEnd pbEnd flag dst ret rest) =
    some (result s c pbi paEnd pbEnd flag dst ret rest) := by
  rw [program_eq]
  exact runInstructions_append_some _ _ _ _ _
    (runInstructions_append_some _ _ _ _ _
      (run_cleanup s c mu bi pbi paEnd pbEnd flag dst ret rest hcap)
      (run_store s c pbi paEnd pbEnd flag dst ret rest hcap hact))
    (run_test { s with memory := tailMem s.memory c } pbi paEnd pbEnd flag dst ret rest hcap htarget)

end Challenge.Modexp.Submission.Proofs.Fast.CiosCachedTail
