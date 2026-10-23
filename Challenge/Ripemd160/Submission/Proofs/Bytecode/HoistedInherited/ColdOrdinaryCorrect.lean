import Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.StaggerPersistentCorrect
import Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.ColdOrdinaryBlock
import Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.PersistentStaggerIteration
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.ColdOrdinaryCorrect
open Challenge.Ripemd160 EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open HoistedInherited.PersistentStaggerIteration HoistedInherited.StaggerPersistentLoopInduction

theorem correct (input : ByteArray) (hfit : CalldataFits input)
    (hpositive : 0 < input.size) (hn32 : input.size ≠ 32)
    (entryPrefix : GasSteps (initialState submissionBytecode input 0) (HoistedInherited.Execution.atPC input 246)) :
    ∃ g₀ : Nat, ∀ gas : Nat, g₀ ≤ gas →
      Eval (initialState submissionBytecode input gas) (.returned (spec input)) := by
  apply HoistedInherited.StaggerPersistentCorrect.correct_of_blocks input hfit hpositive hn32 (states input) (hashes input)
    (states_zero input) (hashes_zero input) ?_
    (fun hc i hi => states_last input hfit hpositive hc i hi) ?_
    (hashArray_hashes input hfit hpositive _ (Nat.le_refl _))
    (states_callStack input _) entryPrefix
  · intro i _
    exact ⟨states_code input i, states_fork input i, states_halt input i,
      states_noPrecompile input i, states_calldata input i⟩
  · intro i hi
    exact gasSteps_block input hfit hpositive i hi
      [DenseScheduleTemplate.mask8, DenseScheduleTemplate.mask16] (by decide) [] rfl
#print axioms correct
end Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.ColdOrdinaryCorrect
