import Challenge.Modexp.Submission.Proofs.Fast.CarryResult

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 500000
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.Proofs.Fast.CarryResult
open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Fast Monpro
attribute [local irreducible] SquarePrepared.prepared SquarePrepared.before SquareRowsModel.rows

theorem monpro_tn_le_one (s : State) (mem : ByteArray) (pa pb p a b mm : Nat)
    (hn32 : p+2 ≤ 8) (hpa : pa+32*(p+2) ≤ 2048) (hpb : pb+32*(p+2) ≤ 2048)
    (ha : Model.FastRepresents mem pa (p+2) a) (hb : Model.FastRepresents mem pb (p+2) b)
    (hm : Model.FastRepresents mem 0 (p+2) mm) (ham : a < mm) (hmpos : 0 < mm)
    (hinv : ((MachineState.readWord mem (32*(p+2)-32)).toNat *
      (MachineState.readWord mem 2816).toNat+1) % 2^256 = 0) :
    (MachineState.readWord (selectedRows (SquarePrepared.prepared s mem pa pb (p+2)) pa pb (p+2) (p+2)) 2080).toNat ≤ 1 := by
  by_cases hsq : p+2=8 ∧ pa=pb
  · have hp : p=6 := by omega
    subst p
    rcases hsq with ⟨_,rfl⟩
    rw [selectedRows, if_pos (show 6+2=8 ∧ pa=pa from ⟨rfl,rfl⟩)]
    exact (SquarePrepared.square_spec s mem pa 0 a mm hpa ha hm ham hinv).1
  rw [SquarePrepared.prepared, if_neg hsq]
  let input := SquarePrepared.before mem pa pb (p+2)
  have ha' := SquarePrepared.represents_before mem pa pb (p+2) pa (p+2) a (Or.inl hpa) ha
  have hb' := SquarePrepared.represents_before mem pa pb (p+2) pb (p+2) b (Or.inl hpb) hb
  have hm' := SquarePrepared.represents_before mem pa pb (p+2) 0 (p+2) mm (Or.inl (by omega)) hm
  have hi : ((MachineState.readWord input (32*(p+2)-32)).toNat *
      (MachineState.readWord input 2816).toNat+1) % 2^256 = 0 := by
    rw [SquarePrepared.read_before_outside mem pa pb (p+2) (32*(p+2)-32) (Or.inl (by omega)),
      SquarePrepared.read_before_outside mem pa pb (p+2) 2816 (Or.inr (by decide))]
    exact hinv
  have hr := selectedRows_agree (mpZeroed s input (p+2)) pa pb (p+2) (p+2)
    hpa hpb (by omega) hn32 (by omega) hsq
  rw [CarryScratchAgreement.readWord_eq hr 2080 (Or.inr (by decide))]
  exact Monpro.monpro_tn_le_one s input pa pb p a b mm hn32 hpa hpb ha' hb' hm' ham hmpos hi

end Challenge.Modexp.Submission.Proofs.Fast.CarryResult
