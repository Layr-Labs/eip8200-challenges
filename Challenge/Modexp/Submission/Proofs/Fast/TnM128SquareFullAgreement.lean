import Challenge.Modexp.Submission.Proofs.Fast.TnM128SquareScratchAgreement
import Challenge.Modexp.Submission.Proofs.Fast.TnM128SquareTailAgreement

set_option warningAsError true
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.TnM128SquareFullAgreement

open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Fast

/-- The eight cached rows agree with the cleared model outside the unused
scratch word at2048, even when the incoming scratch word is not zero. -/
theorem allRows_agree (s : State) (mem : ByteArray) :
    CarryScratchAgreement.Agree
      (TnCacheMemory.lift
        (TnM128SquareTailSteps.run (TnM128SquareFirstModel.first mem) 8 1 7).memory
        (TnM128SquareTailSteps.run (TnM128SquareFirstModel.first mem) 8 1 7).tn)
      (SquareResult.sqRowsCarry (Monpro.mpZeroed s mem 8) 8 8) := by
  have hfirst : CarryScratchAgreement.Agree
      (TnCacheMemory.lift (TnM128SquareFirstModel.first mem).memory
        (TnM128SquareFirstModel.first mem).tn)
      (SquareResult.sqRowsCarry (Monpro.mpZeroed s mem 8) 8 1) := by
    exact TnM128SquareScratchAgreement.firstRow_agree s mem
  exact TnM128SquareTailAgreement.run_agree
    (TnM128SquareFirstModel.first mem) (Monpro.mpZeroed s mem 8)
    8 1 (by decide) hfirst 7 (by decide)

/-- In particular, every materialized carry and result word is unchanged. -/
theorem readWord_allRows (s : State) (mem : ByteArray) (addr : Nat)
    (hout : addr + 32 ≤ 2048 ∨ 2080 ≤ addr) :
    MachineState.readWord
      (TnCacheMemory.lift
        (TnM128SquareTailSteps.run (TnM128SquareFirstModel.first mem) 8 1 7).memory
        (TnM128SquareTailSteps.run (TnM128SquareFirstModel.first mem) 8 1 7).tn) addr =
      MachineState.readWord
        (SquareResult.sqRowsCarry (Monpro.mpZeroed s mem 8) 8 8) addr :=
  CarryScratchAgreement.readWord_eq (allRows_agree s mem) addr hout

#print axioms allRows_agree
#print axioms readWord_allRows

end Challenge.Modexp.Submission.Proofs.Fast.TnM128SquareFullAgreement
