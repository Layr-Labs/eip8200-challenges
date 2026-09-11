import Challenge.Modexp.Submission.Proofs.Fast.SquareRowModel

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 500000
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.Proofs.Fast.SquareRowsModel
open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Fast
open Monpro SquareRowModel

def digit (mem : ByteArray) (pa i : Nat) : UInt256 :=
  MachineState.readWord mem (pa+32*(7-i))

def rows (mem : ByteArray) (pa : Nat) : Nat → ByteArray
  | 0 => mem
  | i+1 => row (rows mem pa i) (digit (rows mem pa i) pa i) i

theorem read_rows_outside (mem : ByteArray) (pa addr : Nat)
    (hd : addr+32 ≤ 8224 ∨ 8512 ≤ addr) :
    ∀ i, i ≤ 8 → MachineState.readWord (rows mem pa i) addr = MachineState.readWord mem addr := by
  intro i
  induction i with
  | zero => intro _; rfl
  | succ i ih =>
    intro hi
    rw [rows, read_row_outside _ _ _ _ (by omega) hd]
    exact ih (by omega)

theorem represents_rows (mem : ByteArray) (pa ptr count v : Nat)
    (hd : ptr+32*count ≤ 8224 ∨ 8512 ≤ ptr)
    (hr : Model.FastRepresents mem ptr count v) (i : Nat) (hi : i ≤ 8) :
    Model.FastRepresents (rows mem pa i) ptr count v := by
  refine (Model.fastRepresents_congr (a := rows mem pa i) (b := mem) ?_ v).2 hr
  intro j hj
  exact read_rows_outside _ _ _ (by omega) i hi

theorem row_step (mem : ByteArray) (pa a m i : Nat)
    (hpa : pa+256 ≤ 8224)
    (ha : Model.FastRepresents mem pa 8 a)
    (hd : Model.FastRepresents mem 8928 9 (2*a))
    (hm : Model.FastRepresents mem 0 8 m) (hi : i < 8)
    (hinv : ((MachineState.readWord mem 224).toNat *
      (MachineState.readWord mem 9376).toNat+1) % 2^256 = 0) :
    tValue (rows mem pa (i+1)) 8*Limbs.radix = tValue (rows mem pa i) 8 +
      SquareArithmetic.rowTerm Limbs.radix a i +
      (rowMu (mid (rows mem pa i) (digit (rows mem pa i) pa i) i) 8).toNat*m := by
  have ha' := represents_rows mem pa pa 8 a (Or.inl hpa) ha i (by omega)
  have hd' := represents_rows mem pa 8928 9 (2*a) (Or.inr (by decide)) hd i (by omega)
  have hm' := represents_rows mem pa 0 8 m (Or.inl (by decide)) hm i (by omega)
  have hiv : ((MachineState.readWord (rows mem pa i) 224).toNat *
      (MachineState.readWord (rows mem pa i) 9376).toNat+1) % 2^256 = 0 := by
    rw [read_rows_outside _ _ _ (Or.inl (by decide)) i (by omega),
      read_rows_outside _ _ _ (Or.inr (by decide)) i (by omega)]
    exact hinv
  exact row_equation (rows mem pa i) a m (digit (rows mem pa i) pa i) i
    hd' hm' ha.1
    (Model.readLimb_of_fastRepresents (memory := rows mem pa i) (ptr := pa)
      (count := 8) (value := a) (k := i) ha' hi) hi hiv

theorem final_equation (mem : ByteArray) (pa a m : Nat)
    (hpa : pa+256 ≤ 8224)
    (ha : Model.FastRepresents mem pa 8 a)
    (hd : Model.FastRepresents mem 8928 9 (2*a))
    (hm : Model.FastRepresents mem 0 8 m)
    (ht0 : tValue mem 8 = 0)
    (hinv : ((MachineState.readWord mem 224).toNat *
      (MachineState.readWord mem 9376).toNat+1) % 2^256 = 0) :
    ∃ Q, Q < Limbs.radix^8 ∧ tValue (rows mem pa 8) 8*Limbs.radix^8 = a*a+Q*m := by
  exact SquareArithmetic.final_quotient Limbs.radix a m 8 Limbs.radix_pos ha.1
    (fun i => tValue (rows mem pa i) 8)
    (fun i => (rowMu (mid (rows mem pa i) (digit (rows mem pa i) pa i) i) 8).toNat)
    ht0 (fun i hi => row_step mem pa a m i hpa ha hd hm hi hinv)
    (fun _ _ => word_lt_size _)

attribute [local irreducible] rows

theorem final_bound (mem : ByteArray) (pa a m : Nat)
    (hpa : pa+256 ≤ 8224)
    (ha : Model.FastRepresents mem pa 8 a)
    (hd : Model.FastRepresents mem 8928 9 (2*a))
    (hm : Model.FastRepresents mem 0 8 m) (ham : a < m)
    (ht0 : tValue mem 8 = 0)
    (hinv : ((MachineState.readWord mem 224).toNat *
      (MachineState.readWord mem 9376).toNat+1) % 2^256 = 0) :
    tValue (rows mem pa 8) 8 < 2*m := by
  obtain ⟨Q, hQ, he⟩ := final_equation mem pa a m hpa ha hd hm ht0 hinv
  have hp : 0 < Limbs.radix^8 := pow_pos Limbs.radix_pos 8
  have hdiv : tValue (rows mem pa 8) 8 = (a*a+Q*m)/Limbs.radix^8 := by
    rw [← he, Nat.mul_div_left _ hp]
  rw [hdiv]
  exact SquareArithmetic.final_bound hp ham hm.1 hQ

theorem final_high_le_one (mem : ByteArray) (pa a m : Nat)
    (hpa : pa+256 ≤ 8224)
    (ha : Model.FastRepresents mem pa 8 a)
    (hd : Model.FastRepresents mem 8928 9 (2*a))
    (hm : Model.FastRepresents mem 0 8 m) (ham : a < m)
    (ht0 : tValue mem 8 = 0)
    (hinv : ((MachineState.readWord mem 224).toNat *
      (MachineState.readWord mem 9376).toNat+1) % 2^256 = 0) :
    (MachineState.readWord (rows mem pa 8) 8224).toNat ≤ 1 := by
  have h := final_bound mem pa a m hpa ha hd hm ham ht0 hinv
  have hmR := hm.1
  simp only [tValue] at h
  nlinarith only [h, hmR]

theorem represents_result (mem : ByteArray) (pa pdst a m : Nat)
    (hpa : pa+256 ≤ 8224)
    (ha : Model.FastRepresents mem pa 8 a)
    (hd : Model.FastRepresents mem 8928 9 (2*a))
    (hm : Model.FastRepresents mem 0 8 m) (ham : a < m) (hodd : m % 2 = 1)
    (ht0 : tValue mem 8 = 0)
    (hinv : ((MachineState.readWord mem 224).toNat *
      (MachineState.readWord mem 9376).toNat+1) % 2^256 = 0) :
    Model.FastRepresents (Csub.csResultMemory (rows mem pa 8) 8 pdst)
      pdst 8 (Model.montMul m (Limbs.radix^8) a a) := by
  obtain ⟨Q, _, he⟩ := final_equation mem pa a m hpa ha hd hm ht0 hinv
  have hlt := final_bound mem pa a m hpa ha hd hm ham ht0 hinv
  have htn := final_high_le_one mem pa a m hpa ha hd hm ham ht0 hinv
  have hm' := represents_rows mem pa 0 8 m (Or.inl (by decide)) hm 8 (by decide)
  rw [Model.montMul_eq_mod_of_mul_eq (by omega) (Model.coprime_radix_pow_of_odd hodd 8) he]
  exact Csub.csub_correct (rows mem pa 8) 8 (Csub.lowValue (rows mem pa 8) 8256 8 8) m
    (MachineState.readWord (rows mem pa 8) 8224).toNat pdst (by decide) (by decide)
    (Csub.fastRepresents_lowValue (rows mem pa 8) 8256 8) hm' rfl htn (by omega) hlt

#print axioms represents_result
end Challenge.Modexp.Submission.Proofs.Fast.SquareRowsModel
