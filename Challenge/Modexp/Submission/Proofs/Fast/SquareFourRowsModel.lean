import Challenge.Modexp.Submission.Proofs.Fast.SquareFourRowModel

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 500000
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.Proofs.Fast.SquareFourRowsModel
open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Fast
open Monpro SquareFourRowModel

def digit (mem : ByteArray) (pa i : Nat) : UInt256 :=
  MachineState.readWord mem (pa+32*(3-i))

def rows (mem : ByteArray) (pa : Nat) : Nat → ByteArray
  | 0 => mem
  | i+1 => row (rows mem pa i) (digit (rows mem pa i) pa i) i

theorem read_rows_outside (mem : ByteArray) (pa addr : Nat)
    (hd : addr+32 ≤ 8224 ∨ 8384 ≤ addr) :
    ∀ i, i ≤ 4 → MachineState.readWord (rows mem pa i) addr = MachineState.readWord mem addr := by
  intro i
  induction i with
  | zero => intro _; rfl
  | succ i ih =>
    intro hi
    rw [rows, read_row_outside _ _ _ _ (by omega) hd]
    exact ih (by omega)

theorem represents_rows (mem : ByteArray) (pa ptr count v : Nat)
    (hd : ptr+32*count ≤ 8224 ∨ 8384 ≤ ptr)
    (hr : Model.FastRepresents mem ptr count v) (i : Nat) (hi : i ≤ 4) :
    Model.FastRepresents (rows mem pa i) ptr count v := by
  refine (Model.fastRepresents_congr (a := rows mem pa i) (b := mem) ?_ v).2 hr
  intro j hj
  exact read_rows_outside _ _ _ (by omega) i hi

theorem row_step (mem : ByteArray) (pa a m i : Nat)
    (hpa : pa+128 ≤ 8224)
    (ha : Model.FastRepresents mem pa 4 a)
    (hd : Model.FastRepresents mem 8928 5 (2*a))
    (hm : Model.FastRepresents mem 0 4 m) (hi : i < 4)
    (hinv : ((MachineState.readWord mem 96).toNat *
      (MachineState.readWord mem 9376).toNat+1) % 2^256 = 0) :
    tValue (rows mem pa (i+1)) 4*Limbs.radix = tValue (rows mem pa i) 4 +
      SquareArithmetic.rowTerm Limbs.radix a i +
      (rowMu (mid (rows mem pa i) (digit (rows mem pa i) pa i) i) 4).toNat*m := by
  have ha' := represents_rows mem pa pa 4 a (Or.inl hpa) ha i (by omega)
  have hd' := represents_rows mem pa 8928 5 (2*a) (Or.inr (by decide)) hd i (by omega)
  have hm' := represents_rows mem pa 0 4 m (Or.inl (by decide)) hm i (by omega)
  have hiv : ((MachineState.readWord (rows mem pa i) 96).toNat *
      (MachineState.readWord (rows mem pa i) 9376).toNat+1) % 2^256 = 0 := by
    rw [read_rows_outside _ _ _ (Or.inl (by decide)) i (by omega),
      read_rows_outside _ _ _ (Or.inr (by decide)) i (by omega)]
    exact hinv
  exact row_equation (rows mem pa i) a m (digit (rows mem pa i) pa i) i
    hd' hm' ha.1
    (Model.readLimb_of_fastRepresents (memory := rows mem pa i) (ptr := pa)
      (count := 4) (value := a) (k := i) ha' hi) hi hiv

theorem final_equation (mem : ByteArray) (pa a m : Nat)
    (hpa : pa+128 ≤ 8224)
    (ha : Model.FastRepresents mem pa 4 a)
    (hd : Model.FastRepresents mem 8928 5 (2*a))
    (hm : Model.FastRepresents mem 0 4 m)
    (ht0 : tValue mem 4 = 0)
    (hinv : ((MachineState.readWord mem 96).toNat *
      (MachineState.readWord mem 9376).toNat+1) % 2^256 = 0) :
    ∃ Q, Q < Limbs.radix^4 ∧ tValue (rows mem pa 4) 4*Limbs.radix^4 = a*a+Q*m := by
  exact SquareArithmetic.final_quotient Limbs.radix a m 4 Limbs.radix_pos ha.1
    (fun i => tValue (rows mem pa i) 4)
    (fun i => (rowMu (mid (rows mem pa i) (digit (rows mem pa i) pa i) i) 4).toNat)
    ht0 (fun i hi => row_step mem pa a m i hpa ha hd hm hi hinv)
    (fun _ _ => word_lt_size _)

attribute [local irreducible] rows

theorem final_bound (mem : ByteArray) (pa a m : Nat)
    (hpa : pa+128 ≤ 8224)
    (ha : Model.FastRepresents mem pa 4 a)
    (hd : Model.FastRepresents mem 8928 5 (2*a))
    (hm : Model.FastRepresents mem 0 4 m) (ham : a < m)
    (ht0 : tValue mem 4 = 0)
    (hinv : ((MachineState.readWord mem 96).toNat *
      (MachineState.readWord mem 9376).toNat+1) % 2^256 = 0) :
    tValue (rows mem pa 4) 4 < 2*m := by
  obtain ⟨Q, hQ, he⟩ := final_equation mem pa a m hpa ha hd hm ht0 hinv
  have hp : 0 < Limbs.radix^4 := pow_pos Limbs.radix_pos 4
  have hdiv : tValue (rows mem pa 4) 4 = (a*a+Q*m)/Limbs.radix^4 := by
    rw [← he, Nat.mul_div_left _ hp]
  rw [hdiv]
  exact SquareArithmetic.final_bound hp ham hm.1 hQ

theorem final_high_le_one (mem : ByteArray) (pa a m : Nat)
    (hpa : pa+128 ≤ 8224)
    (ha : Model.FastRepresents mem pa 4 a)
    (hd : Model.FastRepresents mem 8928 5 (2*a))
    (hm : Model.FastRepresents mem 0 4 m) (ham : a < m)
    (ht0 : tValue mem 4 = 0)
    (hinv : ((MachineState.readWord mem 96).toNat *
      (MachineState.readWord mem 9376).toNat+1) % 2^256 = 0) :
    (MachineState.readWord (rows mem pa 4) 8224).toNat ≤ 1 := by
  have h := final_bound mem pa a m hpa ha hd hm ham ht0 hinv
  have hmR := hm.1
  simp only [tValue] at h
  nlinarith only [h, hmR]

theorem represents_result (mem : ByteArray) (pa pdst a m : Nat)
    (hpa : pa+128 ≤ 8224)
    (ha : Model.FastRepresents mem pa 4 a)
    (hd : Model.FastRepresents mem 8928 5 (2*a))
    (hm : Model.FastRepresents mem 0 4 m) (ham : a < m) (hodd : m % 2 = 1)
    (ht0 : tValue mem 4 = 0)
    (hinv : ((MachineState.readWord mem 96).toNat *
      (MachineState.readWord mem 9376).toNat+1) % 2^256 = 0) :
    Model.FastRepresents (Csub.csResultMemory (rows mem pa 4) 4 pdst)
      pdst 4 (Model.montMul m (Limbs.radix^4) a a) := by
  obtain ⟨Q, _, he⟩ := final_equation mem pa a m hpa ha hd hm ht0 hinv
  have hlt := final_bound mem pa a m hpa ha hd hm ham ht0 hinv
  have htn := final_high_le_one mem pa a m hpa ha hd hm ham ht0 hinv
  have hm' := represents_rows mem pa 0 4 m (Or.inl (by decide)) hm 4 (by decide)
  rw [Model.montMul_eq_mod_of_mul_eq (by omega) (Model.coprime_radix_pow_of_odd hodd 4) he]
  exact Csub.csub_correct (rows mem pa 4) 4 (Csub.lowValue (rows mem pa 4) 8256 4 4) m
    (MachineState.readWord (rows mem pa 4) 8224).toNat pdst (by decide) (by decide)
    (Csub.fastRepresents_lowValue (rows mem pa 4) 8256 4) hm' rfl htn (by omega) hlt

#print axioms represents_result
end Challenge.Modexp.Submission.Proofs.Fast.SquareFourRowsModel
