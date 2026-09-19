import Challenge.Modexp.Submission.Proofs.Fast.CarryScratchAgreement
import Challenge.Modexp.Submission.Proofs.Fast.SquareResult
import Challenge.Modexp.Submission.Proofs.Fast.TnCacheSquareModel
import Challenge.Modexp.Submission.Proofs.Fast.TnM128SquareTailSteps

set_option warningAsError true
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.TnM128SquareTailAgreement

open Challenge.Modexp.Submission.Proofs.Fast

theorem sqRow_carry_agree (a b : ByteArray)
    (h : CarryScratchAgreement.Agree a b) (n i : Nat)
    (hi : i < n) (hn : n ≤ 8) :
    CarryScratchAgreement.Agree
      (SquareResult.sqRowCarry a n i (SquareModel.sqTb a n i))
      (SquareResult.sqRowCarry b n i (SquareModel.sqTb b n i)) := by
  exact CarryScratchAgreement.trans
    (SquareResult.sqRow_agree a b h n i hi hn)
    (CarryScratchAgreement.symm
      (SquareResult.sqRow_agree b b (CarryScratchAgreement.refl b) n i hi hn))

theorem run_agree (z : TnCacheRowModel.CacheState) (mem : ByteArray) (n start : Nat)
    (hn : n ≤ 8)
    (h : CarryScratchAgreement.Agree
      (TnCacheMemory.lift z.memory z.tn) (SquareResult.sqRowsCarry mem n start)) :
    ∀ k, start + k ≤ n →
      CarryScratchAgreement.Agree
        (TnCacheMemory.lift
          (TnM128SquareTailSteps.run z n start k).memory
          (TnM128SquareTailSteps.run z n start k).tn)
        (SquareResult.sqRowsCarry mem n (start + k)) := by
  intro k
  induction k with
  | zero =>
      intro _
      exact h
  | succ k ih =>
      intro hk
      have hrow := sqRow_carry_agree
        (TnCacheMemory.lift
          (TnM128SquareTailSteps.run z n start k).memory
          (TnM128SquareTailSteps.run z n start k).tn)
        (SquareResult.sqRowsCarry mem n (start + k))
        (ih (by omega)) n (start + k) (by omega) hn
      rw [TnM128SquareTailSteps.run,
        ← TnCacheSquareModel.squareRow_lift
          (TnM128SquareTailSteps.run z n start k) n (start + k) (by omega) hn]
      exact hrow

#print axioms sqRow_carry_agree
#print axioms run_agree

end Challenge.Modexp.Submission.Proofs.Fast.TnM128SquareTailAgreement
