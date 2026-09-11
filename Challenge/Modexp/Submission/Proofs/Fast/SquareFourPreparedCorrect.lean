import Challenge.Modexp.Submission.Proofs.Fast.SquarePrepared
import Challenge.Modexp.Submission.Proofs.Fast.SquareFourRowsModel

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 500000
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.Proofs.Fast.SquarePrepared
open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Fast Monpro SquareInit StagedOperand

theorem represents_double_four (s : State) (mem : ByteArray) (pa a : Nat)
    (hpa : pa+128 ≤ 8192) (ha : Model.FastRepresents mem pa 4 a) :
    Model.FastRepresents (prepared s mem pa pa 4) 8928 5 (2*a) := by
  rw [prepared, if_neg (by simp : ¬(4=8 ∧ pa=pa)), if_pos ⟨rfl,rfl⟩]
  apply SquareFourInit.init_represents
  have hsel : Model.FastRepresents (selected mem pa pa 4) pa 4 a :=
    (Model.fastRepresents_congr (fun j hj => read_selected_outside mem pa pa 4 (pa+32*j) (by omega)) a).2 ha
  have hs := Csub.fastRepresents_mcopy (selected mem pa pa 4) pa 8960 4 a (by decide) hsel
  have hb : Model.FastRepresents (before mem pa pa 4) 8960 4 a := by
    simpa only [before, inputMemory, if_pos (show 4=4 ∨ 4=8 from Or.inl rfl), or_true, true_or, ite_true, stage] using hs
  exact (Model.fastRepresents_congr (fun j hj =>
    mpZeroed_readWord_outside s (before mem pa pa 4) 4 (8960+32*j) (Or.inr (by omega))) a).2 hb

theorem tValue_zero_four (s : State) (mem : ByteArray) (pa : Nat) :
    tValue (prepared s mem pa pa 4) 4 = 0 := by
  rw [prepared, if_neg (by simp : ¬(4=8 ∧ pa=pa)), if_pos ⟨rfl,rfl⟩, tValue, SquareFourInit.read_init_outside _ 8224 (Or.inl (by decide)), readWord_mpZeroed_tn]
  have hrep : Model.FastRepresents (SquareFourInit.initMemory (mpZeroed s (before mem pa pa 4) 4)) 8256 4 0 :=
    (Model.fastRepresents_congr (fun j hj => SquareFourInit.read_init_outside _ (8256+32*j) (Or.inl (by omega))) 0).2
      (fastRepresents_mpZeroed s (before mem pa pa 4) 4)
  have hlow := Model.fastRepresents_value_unique (Csub.fastRepresents_lowValue _ 8256 4) hrep
  rw [hlow]
  simp only [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.zero_mod, Nat.zero_mul, Nat.add_zero]

theorem init_high_clear_four (mem : ByteArray) :
    SquareWords.clearBit (MachineState.readWord (SquareFourInit.initMemory mem) 8928) = UInt256.ofNat 0 := by
  have ha := Csub.fastRepresents_lowValue mem 8960 4
  have hd := SquareFourInit.init_represents mem (Csub.lowValue mem 8960 4 4) ha
  have hc := SquareFourCoefficients.coefficient_high_le_one
    (SquareFourInit.initMemory mem) (Csub.lowValue mem 8960 4 4) (UInt256.ofNat 0) 0 hd ha.1 (by decide)
  simp only [SquareFourCoefficients.coefficient, Nat.reduceEqDiff, if_false,
    SquareFourCoefficients.dWord, Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd] at hc
  apply Challenge.EvmProof.Word.word_ext
  rw [SquareWords.clearBit_toNat]
  simp only [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.zero_mod]
  omega


theorem square_spec_four (s : State) (mem : ByteArray) (pa pdst a m : Nat)
    (hpa : pa+128 ≤ 8192) (ha : Model.FastRepresents mem pa 4 a)
    (hm : Model.FastRepresents mem 0 4 m) (ham : a < m)
    (hinv : ((MachineState.readWord mem 96).toNat * (MachineState.readWord mem 9376).toNat+1) % 2^256 = 0) :
    (MachineState.readWord (SquareFourRowsModel.rows (prepared s mem pa pa 4) pa 4) 8224).toNat ≤ 1 ∧
    (m % 2 = 1 → Model.FastRepresents
      (Csub.csResultMemory (SquareFourRowsModel.rows (prepared s mem pa pa 4) pa 4) 4 pdst) pdst 4
      (Model.montMul m (Limbs.radix^4) a a)) := by
  have ha' := represents_prepared s mem pa pa 4 pa 4 a (by decide) (Or.inl hpa) ha
  have hm' := represents_prepared s mem pa pa 4 0 4 m (by decide) (Or.inl (by decide)) hm
  have hd := represents_double_four s mem pa a hpa ha
  have hz := tValue_zero_four s mem pa
  have hi : ((MachineState.readWord (prepared s mem pa pa 4) 96).toNat *
      (MachineState.readWord (prepared s mem pa pa 4) 9376).toNat+1) % 2^256 = 0 := by
    rw [read_prepared_outside s mem pa pa 4 96 (by decide) (Or.inl (by decide)),
      read_prepared_outside s mem pa pa 4 9376 (by decide) (Or.inr (by decide))]
    exact hinv
  exact ⟨SquareFourRowsModel.final_high_le_one _ pa a m (by omega) ha' hd hm' ham hz hi,
    fun hodd => SquareFourRowsModel.represents_result _ pa pdst a m (by omega) ha' hd hm' ham hodd hz hi⟩


end Challenge.Modexp.Submission.Proofs.Fast.SquarePrepared
