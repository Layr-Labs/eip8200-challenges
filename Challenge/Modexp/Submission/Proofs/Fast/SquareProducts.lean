import Challenge.Modexp.Submission.Proofs.Fast.SquareInitMemory

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.Proofs.Fast.SquareProducts
open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Fast
open Monpro SquareInit

/-- The current value of the eight low accumulator words. -/
def low (mem : ByteArray) : Nat :=
  limbSum (fun k => (MachineState.readWord mem (tAddr 8 k)).toNat) 8

/-- Updating one radix digit, written without truncated subtraction. -/
theorem limbSum_replace (f : Nat → Nat) (n j v : Nat) (hj : j < n) :
    limbSum (fun k => if k = j then v else f k) n + f j*Limbs.radix^j =
      limbSum f n + v*Limbs.radix^j := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [limbSum_succ, limbSum_succ]
    by_cases he : j = n
    · subst j
      rw [if_pos rfl]
      have hkeep : limbSum (fun k => if k = n then v else f k) n = limbSum f n := by
        apply limbSum_congr
        intro k hk
        exact if_neg (by omega)
      rw [hkeep]
      omega
    · rw [if_neg (Ne.symm he)]
      have prev := ih (by omega)
      omega

theorem low_storeWord (mem : ByteArray) (j : Nat) (w : UInt256) (hj : j < 8) :
    low (storeWord mem (tAddr 8 j) w) +
        (MachineState.readWord mem (tAddr 8 j)).toNat*Limbs.radix^j =
      low mem + w.toNat*Limbs.radix^j := by
  have hsum : low (storeWord mem (tAddr 8 j) w) =
      limbSum (fun k => if k = j then w.toNat else
        (MachineState.readWord mem (tAddr 8 k)).toNat) 8 := by
    apply limbSum_congr
    intro k hk
    by_cases he : k = j
    · subst k; rw [if_pos rfl, read_storeWord]
    · rw [if_neg he, read_storeWord_outside]
      simp only [tAddr]
      omega
  rw [hsum]
  exact limbSum_replace _ 8 j w.toNat hj

/-- Multiply coefficients `x[i..]` by `y` and accumulate into the corresponding
    low words. The code skips the unchanged prefix below `i`. -/
def products (mem : ByteArray) (x : Nat → UInt256) (y : UInt256) (i : Nat) : Nat → MacState
  | 0 => ⟨mem, UInt256.ofNat 0⟩
  | k+1 =>
    let p := products mem x y i k
    let t := MachineState.readWord p.memory (tAddr 8 (i+k))
    ⟨storeWord p.memory (tAddr 8 (i+k)) (macSum (x (i+k)) y t p.carry),
     macCarry (x (i+k)) y t p.carry⟩

def weighted (x : Nat → Nat) (i : Nat) : Nat → Nat
  | 0 => 0
  | k+1 => weighted x i k + x (i+k)*Limbs.radix^(i+k)

/-- Exact product-and-carry invariant for the shared triangular limb chain. -/
theorem products_invariant (mem : ByteArray) (x : Nat → UInt256) (y : UInt256) (i : Nat) :
    ∀ k, i+k ≤ 8 →
      low (products mem x y i k).memory +
          (products mem x y i k).carry.toNat * Limbs.radix^(i+k) =
        low mem + y.toNat * weighted (fun j => (x j).toNat) i k := by
  intro k
  induction k with
  | zero => intro _; simp [products, weighted]
  | succ k ih =>
    intro hk
    have prev := ih (by omega)
    let p := products mem x y i k
    let t := MachineState.readWord p.memory (tAddr 8 (i+k))
    have hs := low_storeWord p.memory (i+k) (macSum (x (i+k)) y t p.carry) (by omega)
    have hm := macSpec (x (i+k)) y t p.carry
    change (macCarry (x (i+k)) y t p.carry).toNat*Limbs.radix +
      (macSum (x (i+k)) y t p.carry).toNat =
      t.toNat + (x (i+k)).toNat*y.toNat + p.carry.toNat at hm
    have hm' := congrArg (fun z : Nat => z*Limbs.radix^(i+k)) hm
    change low p.memory + p.carry.toNat*Limbs.radix^(i+k) =
      low mem + y.toNat*weighted (fun j => (x j).toNat) i k at prev
    change low (storeWord p.memory (tAddr 8 (i+k)) (macSum (x (i+k)) y t p.carry)) +
      t.toNat*Limbs.radix^(i+k) =
      low p.memory + (macSum (x (i+k)) y t p.carry).toNat*Limbs.radix^(i+k) at hs
    change low (storeWord p.memory (tAddr 8 (i+k)) (macSum (x (i+k)) y t p.carry)) +
      (macCarry (x (i+k)) y t p.carry).toNat*Limbs.radix^(i+(k+1)) = _
    rw [weighted, show i+(k+1) = (i+k)+1 by omega, pow_succ]
    nlinarith only [prev, hs, hm']

theorem read_products_outside (mem : ByteArray) (x : Nat → UInt256) (y : UInt256)
    (i addr : Nat) (hd : addr+32 ≤ 8256 ∨ 8512 ≤ addr) :
    ∀ k, i+k ≤ 8 →
      MachineState.readWord (products mem x y i k).memory addr = MachineState.readWord mem addr := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro hk
    simp only [products]
    rw [read_storeWord_outside]
    · exact ih (by omega)
    · simp only [tAddr]; omega

end Challenge.Modexp.Submission.Proofs.Fast.SquareProducts
