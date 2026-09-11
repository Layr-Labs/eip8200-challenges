import Challenge.Modexp.Submission.Proofs.Fast.SquarePrepared
import Challenge.Modexp.Submission.Proofs.Fast.SquareRowsModel

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 300000
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.Proofs.Fast.SquarePrepared
open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Fast Monpro

theorem square_spec (s : State) (mem : ByteArray) (pa pdst a m : Nat)
    (hpa : pa+256 ≤ 8192) (ha : Model.FastRepresents mem pa 8 a)
    (hm : Model.FastRepresents mem 0 8 m) (ham : a < m)
    (hinv : ((MachineState.readWord mem 224).toNat * (MachineState.readWord mem 9376).toNat+1) % 2^256 = 0) :
    (MachineState.readWord (SquareRowsModel.rows (prepared s mem pa pa 8) pa 8) 8224).toNat ≤ 1 ∧
    (m % 2 = 1 → Model.FastRepresents
      (Csub.csResultMemory (SquareRowsModel.rows (prepared s mem pa pa 8) pa 8) 8 pdst) pdst 8
      (Model.montMul m (Limbs.radix^8) a a)) := by
  have ha' := represents_prepared s mem pa pa 8 pa 8 a (by decide) (Or.inl hpa) ha
  have hm' := represents_prepared s mem pa pa 8 0 8 m (by decide) (Or.inl (by decide)) hm
  have hd := represents_double s mem pa a hpa ha
  have hz := tValue_zero s mem pa
  have hi : ((MachineState.readWord (prepared s mem pa pa 8) 224).toNat *
      (MachineState.readWord (prepared s mem pa pa 8) 9376).toNat+1) % 2^256 = 0 := by
    rw [read_prepared_outside s mem pa pa 8 224 (by decide) (Or.inl (by decide)),
      read_prepared_outside s mem pa pa 8 9376 (by decide) (Or.inr (by decide))]
    exact hinv
  exact ⟨SquareRowsModel.final_high_le_one _ pa a m (by omega) ha' hd hm' ham hz hi,
    fun hodd => SquareRowsModel.represents_result _ pa pdst a m (by omega) ha' hd hm' ham hodd hz hi⟩

end Challenge.Modexp.Submission.Proofs.Fast.SquarePrepared
