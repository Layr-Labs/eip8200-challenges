import Challenge.Modexp.Submission.Proofs.Fast.SquareTop
import Challenge.Modexp.Submission.Proofs.Fast.SquareCoefficients
import Challenge.Modexp.Submission.Proofs.Fast.SquareArithmetic

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 500000
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.Proofs.Fast.SquareRowModel
open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Fast
open Monpro SquareInit SquareProducts SquareCoefficients

def product (mem : ByteArray) (ai : UInt256) (i : Nat) : MacState :=
  products mem (coefficient mem ai i) ai i (8-i)

def extra (mem : ByteArray) (ai : UInt256) (i : Nat) : UInt256 :=
  ai * coefficient mem ai i 8

def mid (mem : ByteArray) (ai : UInt256) (i : Nat) : ByteArray :=
  SquareTop.memory (product mem ai i).memory (product mem ai i).carry (extra mem ai i)

def flag (mem : ByteArray) (ai : UInt256) (i : Nat) : UInt256 :=
  SquareTop.flag (product mem ai i).memory (product mem ai i).carry (extra mem ai i)

def row (mem : ByteArray) (ai : UInt256) (i : Nat) : ByteArray :=
  SquareReduce.reduction (mid mem ai i) (flag mem ai i)

theorem read_product_outside (mem : ByteArray) (ai : UInt256) (i addr : Nat)
    (hi : i ≤ 8) (hd : addr+32 ≤ 8256 ∨ 8512 ≤ addr) :
    MachineState.readWord (product mem ai i).memory addr = MachineState.readWord mem addr :=
  read_products_outside mem _ ai i addr hd (8-i) (by omega)

theorem read_mid_outside (mem : ByteArray) (ai : UInt256) (i addr : Nat)
    (hi : i ≤ 8) (hd : addr+32 ≤ 8224 ∨ 8512 ≤ addr) :
    MachineState.readWord (mid mem ai i) addr = MachineState.readWord mem addr := by
  rw [mid, SquareTop.memory, read_storeWord_outside _ _ _ _ (by omega),
    read_product_outside _ _ _ _ hi (by omega)]

theorem read_row_outside (mem : ByteArray) (ai : UInt256) (i addr : Nat)
    (hi : i ≤ 8) (hd : addr+32 ≤ 8224 ∨ 8512 ≤ addr) :
    MachineState.readWord (row mem ai i) addr = MachineState.readWord mem addr := by
  rw [row, SquareReduce.read_reduction_outside _ _ _ hd,
    read_mid_outside _ _ _ _ hi hd]

theorem represents_mid (mem : ByteArray) (ai : UInt256) (i ptr count v : Nat)
    (hi : i ≤ 8) (hd : ptr+32*count ≤ 8224 ∨ 8512 ≤ ptr)
    (hr : Model.FastRepresents mem ptr count v) :
    Model.FastRepresents (mid mem ai i) ptr count v := by
  refine (Model.fastRepresents_congr (a := mid mem ai i) (b := mem) ?_ v).2 hr
  intro j hj
  exact read_mid_outside _ _ _ _ hi (by omega)

theorem represents_row (mem : ByteArray) (ai : UInt256) (i ptr count v : Nat)
    (hi : i ≤ 8) (hd : ptr+32*count ≤ 8224 ∨ 8512 ≤ ptr)
    (hr : Model.FastRepresents mem ptr count v) :
    Model.FastRepresents (row mem ai i) ptr count v := by
  refine (Model.fastRepresents_congr (a := row mem ai i) (b := mem) ?_ v).2 hr
  intro j hj
  exact read_row_outside _ _ _ _ hi (by omega)

theorem low_mid (mem : ByteArray) (ai : UInt256) (i : Nat) :
    Csub.lowValue (mid mem ai i) 8256 8 8 = low (product mem ai i).memory := by
  rw [← limbSum_eq_lowValue]
  apply limbSum_congr
  intro k hk
  rw [mid, SquareTop.memory, read_storeWord_outside _ _ _ _ (Or.inr (by omega))]
  rfl

theorem extra_toNat (mem : ByteArray) (a : Nat) (ai : UInt256) (i : Nat)
    (hd : Model.FastRepresents mem 8928 9 (2*a)) (ha : a < Limbs.radix^8)
    (hi : i < 8) :
    (extra mem ai i).toNat = ai.toNat*(coefficient mem ai i 8).toNat := by
  have hc := coefficient_high_le_one mem a ai i hd ha hi
  have hw := word_lt_size ai
  rw [extra, word_toNat_mul, Nat.mod_eq_of_lt]
  exact lt_of_le_of_lt (by nlinarith only [hc]) hw

theorem row_equation (mem : ByteArray) (a m : Nat) (ai : UInt256) (i : Nat)
    (hd : Model.FastRepresents mem 8928 9 (2*a))
    (hm : Model.FastRepresents mem 0 8 m) (ha : a < Limbs.radix^8)
    (hai : ai.toNat = a / Limbs.radix^i % Limbs.radix) (hi : i < 8)
    (hinv : ((MachineState.readWord mem 224).toNat *
      (MachineState.readWord mem 9376).toNat+1) % 2^256 = 0) :
    tValue (row mem ai i) 8*Limbs.radix =
      tValue mem 8 + SquareArithmetic.rowTerm Limbs.radix a i +
        (rowMu (mid mem ai i) 8).toNat*m := by
  have hmid := represents_mid mem ai i 0 8 m (by omega) (Or.inl (by decide)) hm
  have hiv : ((MachineState.readWord (mid mem ai i) 224).toNat *
      (MachineState.readWord (mid mem ai i) 9376).toNat+1) % 2^256 = 0 := by
    rw [read_mid_outside _ _ _ _ (by omega) (Or.inl (by decide)),
      read_mid_outside _ _ _ _ (by omega) (Or.inr (by decide))]
    exact hinv
  have red := SquareReduce.reduction_equation (mid mem ai i) (flag mem ai i) m
    (SquareTop.flag_le_two _ _ _) hmid hiv
  have top := SquareTop.top_spec (product mem ai i).memory
    (product mem ai i).carry (extra mem ai i)
  rw [read_product_outside _ _ _ _ (by omega) (Or.inl (by decide)),
    extra_toNat mem a ai i hd ha hi] at top
  have prod := products_invariant mem (coefficient mem ai i) ai i (8-i) (by omega)
  have hlen : i+(8-i) = 8 := by omega
  change low (product mem ai i).memory + (product mem ai i).carry.toNat*Limbs.radix^(i+(8-i)) =
    low mem + ai.toNat*weighted (fun j => (coefficient mem ai i j).toNat) i (8-i) at prod
  rw [hlen] at prod
  have coeff := weighted_coefficient mem a ai i hd hi
  have hlen' : 9-i = (8-i)+1 := by omega
  rw [hlen', weighted, hlen] at coeff
  change tValue (row mem ai i) 8*Limbs.radix = _ at red
  rw [low_mid] at red
  have hhigh : (MachineState.readWord (mid mem ai i) 8224).toNat =
      (SquareTop.value (product mem ai i).memory (product mem ai i).carry (extra mem ai i)).toNat := by
    rw [mid, SquareTop.memory, read_storeWord]
  rw [hhigh] at red
  change (flag mem ai i).toNat*Limbs.radix +
      (SquareTop.value (product mem ai i).memory (product mem ai i).carry (extra mem ai i)).toNat = _ at top
  rw [top] at red
  have hlow : low mem = Csub.lowValue mem 8256 8 8 := limbSum_eq_lowValue mem 8256 8 8
  have heq : low (product mem ai i).memory +
      ((product mem ai i).carry.toNat + ai.toNat*(coefficient mem ai i 8).toNat)*Limbs.radix^8 =
      low mem + ai.toNat*(ai.toNat*Limbs.radix^i +
        2*(a/Limbs.radix^(i+1))*Limbs.radix^(i+1)) := by
    calc
      _ = (low (product mem ai i).memory+(product mem ai i).carry.toNat*Limbs.radix^8) +
        ai.toNat*(coefficient mem ai i 8).toNat*Limbs.radix^8 := by ring
      _ = low mem + ai.toNat*(weighted (fun j => (coefficient mem ai i j).toNat) i (8-i) +
          (coefficient mem ai i 8).toNat*Limbs.radix^8) := by rw [prod]; ring
      _ = _ := by rw [coeff]
  calc
    _ = (MachineState.readWord mem 8224).toNat*Limbs.radix^8 +
      (low (product mem ai i).memory +
       ((product mem ai i).carry.toNat + ai.toNat*(coefficient mem ai i 8).toNat)*Limbs.radix^8) +
      (rowMu (mid mem ai i) 8).toNat*m := by rw [red]; ring
    _ = _ := by rw [heq, hlow, hai]; simp only [tValue, SquareArithmetic.rowTerm]; ring

end Challenge.Modexp.Submission.Proofs.Fast.SquareRowModel
