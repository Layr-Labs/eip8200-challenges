import Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNTailStore
import Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNTailTest

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNTail

open EvmSemantics EvmSemantics.EVM
open WindowNibbleKernel MonproKNCache MonproKNRowPrograms MonproKNTailDefs
open MonproKNTailStore MonproKNTailTest
open Challenge.Modexp.Submission.Proofs.Fast.Monpro

theorem run_tail (s : State) (pmj ptj c mu bi pbi paEnd pbEnd dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1007) (hact : 296 ≤ s.activeWords.toNat)
    (htarget : Decode.isValidJumpDest s.executionEnv.code 1982 = true) :
    runInstructions tailProgram (input s pmj ptj c mu bi pbi paEnd pbEnd dst ret rest) =
    some (result s c pbi paEnd pbEnd dst ret rest) := by
  rw [program_eq]
  exact runInstructions_append_some _ _ _ _ _
    (runInstructions_append_some _ _ _ _ _
      (run_cleanup s pmj ptj c mu bi pbi paEnd pbEnd dst ret rest hcap)
      (run_store s c pbi paEnd pbEnd dst ret rest hcap hact))
    (run_test { s with memory := tailMem s.memory c } pbi paEnd pbEnd dst ret rest hcap htarget)

end Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNTail
