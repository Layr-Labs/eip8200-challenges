import Challenge.Modexp.Submission.Proofs.Bytecode.WindowControlTrace
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitTableBuild
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitLoopBody
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitReturn

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 5000000

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitCorrect

open EvmSemantics EvmSemantics.EVM
open WindowHitStates

private theorem modulus_toNat (input : ByteArray) :
    (modulusWord input).toNat = WindowSpec.modulusValue input :=
  Challenge.EvmProof.Bytes.readWord_toNat input 160

/-- Exact successful guard, modulus case, table, loop and output composition. -/
def handled (input : ByteArray) (hmatch : WindowGuardLogic.Matches input) :
    WindowRoute.Handled input := by
  let guard := WindowControlTrace.gasSteps_hit input hmatch
  by_cases hzero : modulusWord input = 0
  · have hmodulus : WindowSpec.modulusValue input = 0 := by
      rw [← modulus_toNat, hzero]
      rfl
    let branch := WindowHitTableEntry.gasSteps_modulusZero input hzero
    let tail := WindowHitReturn.gasSteps_zeroReturn input
    exact ⟨zeroReturnedState input, ⟨(guard.trans branch).trans tail⟩,
      by rfl, WindowHitResult.zeroReturnedState_result input hmatch hmodulus⟩
  · have hnat : (modulusWord input).toNat ≠ 0 := by
      intro hz
      apply hzero
      apply Challenge.EvmProof.Word.word_ext
      exact hz
    have hmodulus : 0 < WindowSpec.modulusValue input := by
      rw [← modulus_toNat]
      omega
    let word := WindowHitLoopBody.loopAccumulator input 8
    have hword : word.toNat = WindowSpec.windowResult input :=
      WindowHitResult.completedWord_toNat input hmodulus
    let table := WindowHitTableBuild.gasSteps_tableBuild input hzero
    let loop := WindowHitLoopBody.gasSteps_loop input
    let tail := WindowHitReturn.gasSteps_normalReturn input word
    exact ⟨WindowHitReturn.normalReturnedState input word,
      ⟨((guard.trans table).trans loop).trans tail⟩,
      by rfl, WindowHitReturn.normalReturnedState_result input hmatch hmodulus word hword⟩

def route : WindowRoute.Route where
  toControl := WindowControlTrace.control
  hit := fun input _ _ _ hmatch => handled input hmatch

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitCorrect
