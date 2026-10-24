import Challenge.Modexp.Submission.Proofs.Fast.StagedMonpro
import Challenge.Modexp.Submission.Proofs.Fast.CarryResult

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace Challenge.Modexp.Submission.Proofs.Fast.StagedProduct
open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Fast
open Monpro CarryRowModel CarryScratchAgreement

theorem l1_agree (a b : ByteArray) (h : Agree a b) (bi : UInt256) (pa n j : Nat)
    (hpa : pa + 32*n ≤ 2048 ∨ 2368 ≤ pa) (hj : j ≤ n) :
    Agree (l1Step a bi pa n j).memory (l1Step b bi pa n j).memory ∧
      (l1Step a bi pa n j).carry = (l1Step b bi pa n j).carry := by
  induction j with
  | zero => exact ⟨h, rfl⟩
  | succ j ih =>
    have prev := ih (by omega)
    have hx := readWord_eq prev.1 (pa + 32*(n-1-j)) (by omega)
    have ht := readWord_eq prev.1 (2112 + 32*(n-1-j)) (Or.inr (by omega))
    simp only [l1Step, hx, ht, prev.2]
    exact ⟨write_same prev.1 _ _, True.intro⟩

theorem row_agree (a b : ByteArray) (h : Agree a b) (pa pb n i : Nat)
    (hpa : pa+32*n ≤ 2048 ∨ 2368 ≤ pa) (hpb : pb+32*n ≤ 2048)
    (_hn : 2 ≤ n) (hn32 : n ≤ 8) (hi : i < n) :
    Agree (rowCarry a pa pb n i) (rowMem b pa pb n i) := by
  have hbi : rowBi a pb n i = rowBi b pb n i := by
    unfold rowBi
    exact readWord_eq h _ (Or.inl (by omega))
  have hl1 : Agree (rowL1 a pa pb n i).memory (rowL1 b pa pb n i).memory ∧
      (rowL1 a pa pb n i).carry = (rowL1 b pa pb n i).carry := by
    simp only [rowL1, hbi]
    exact l1_agree a b h _ pa n n hpa (by omega)
  have hm := middle_agree (rowL1 a pa pb n i).memory (rowL1 b pa pb n i).memory hl1.1
    (rowL1 b pa pb n i).carry
  have hmu := rowMu_eq (rowL1 a pa pb n i).memory (rowL1 b pa pb n i).memory hl1.1 n
  have hc0 := rowC0_eq (rowL1 a pa pb n i).memory (rowL1 b pa pb n i).memory hl1.1 n hn32
  have hflag := overflow_eq (rowL1 a pa pb n i).memory (rowL1 b pa pb n i).memory hl1.1 (rowL1 b pa pb n i).carry
  have hl2 := l2_agree _ _ hm (rowMu (rowL1 b pa pb n i).memory n)
    (rowC0 (rowL1 b pa pb n i).memory n) n (n-1) hn32
  have hf : MachineState.readWord (rowL2 b pa pb n i).memory 2048 =
      overflow (rowL1 b pa pb n i).memory (rowL1 b pa pb n i).carry := by
    simp only [rowL2, rowMid]
    rw [readWord_l2Step_low _ _ _ n 2048 (n-1) (by decide), readWord_midMem_tnp]
    rfl
  simpa only [rowCarry, rowL2Carry, rowMem, rowL2, rowMid, hl1.2, hmu, hc0, hflag, hl2.2] using
    tail_agree _ _ hl2.1 _ _ hf

theorem rows_agree (mem : ByteArray) (pa pb n j : Nat)
    (hpa : pa+32*n ≤ 2048 ∨ 2368 ≤ pa) (hpb : pb+32*n ≤ 2048)
    (hn : 2 ≤ n) (hn32 : n ≤ 8) (hj : j ≤ n) :
    Agree (rowsCarry mem pa pb n j) (rowsMem mem pa pb n j) := by
  induction j with
  | zero => exact refl mem
  | succ j ih =>
    exact row_agree _ _ (ih (by omega)) pa pb n j hpa hpb hn hn32 (by omega)
/-- The fused final product starts with an already staged A, and skips entry copying. -/
def memory (s : State) (mem : ByteArray) (n : Nat) : ByteArray :=
  Csub.csResultMemory (rowsCarry (mpZeroed s mem n) 2368 256 n n) n 256

theorem rows_tn_le_one (s : State) (mem : ByteArray) (p a b mm : Nat)
    (hn : p + 2 ≤ 8)
    (ha : Model.FastRepresents mem 2368 (p + 2) a)
    (hb : Model.FastRepresents mem 256 (p + 2) b)
    (hm : Model.FastRepresents mem 0 (p + 2) mm) (ham : a < mm)
    (hminv : ((MachineState.readWord mem (32 * (p + 2) - 32)).toNat *
      (MachineState.readWord mem 2720).toNat + 1) % 2 ^ 256 = 0) :
    (MachineState.readWord (rowsCarry (mpZeroed s mem (p + 2)) 2368 256 (p + 2) (p + 2)) 2080).toNat ≤ 1 := by
  have hg := rows_agree (mpZeroed s mem (p + 2)) 2368 256 (p + 2) (p + 2)
    (by omega) (by omega) (by omega) hn (by omega)
  rw [CarryScratchAgreement.readWord_eq hg 2080 (Or.inr (by decide))]
  exact StagedMonpro.monpro_tn_le_one s mem 2368 256 p a b mm hn
    (by omega) (by omega) ha hb hm ham (by omega) hminv

theorem represents (s : State) (mem : ByteArray) (p a b mm : Nat)
    (hn : p + 2 ≤ 8)
    (ha : Model.FastRepresents mem 2368 (p + 2) a)
    (hb : Model.FastRepresents mem 256 (p + 2) b)
    (hm : Model.FastRepresents mem 0 (p + 2) mm)
    (hodd : mm % 2 = 1) (ham : a < mm)
    (hminv : ((MachineState.readWord mem (32 * (p + 2) - 32)).toNat *
      (MachineState.readWord mem 2720).toNat + 1) % 2 ^ 256 = 0) :
    Model.FastRepresents (memory s mem (p + 2)) 256 (p + 2)
      (Model.montMul mm (Limbs.radix ^ (p + 2)) a b) := by
  have hg := rows_agree (mpZeroed s mem (p + 2)) 2368 256 (p + 2) (p + 2)
    (by omega) (by omega) (by omega) hn (by omega)
  have ht := StagedMonpro.monpro_tn_le_one s mem 2368 256 p a b mm hn
    (by omega) (by omega) ha hb hm ham (by omega) hminv
  have hc := CarryRowModel.csResult_agree _ _ hg (p + 2) 256 (by omega) hn ht
  have hr := StagedMonpro.monpro_represents s mem 2368 256 p 256 a b mm hn
    (by omega) (by omega) ha hb hm hodd ham hminv
  exact (CarryRowModel.fastRepresents_iff _ _ hc 256 (p + 2) _ (Or.inl (by omega))).2 hr

#print axioms represents
end Challenge.Modexp.Submission.Proofs.Fast.StagedProduct
