import Challenge.Modexp.Submission.Proofs.Fast.Monpro
import Challenge.Modexp.Submission.Proofs.Fast.SquareMath
import Challenge.Modexp.Submission.Proofs.Fast.SquareDiag

set_option warningAsError true
set_option maxHeartbeats 4000000

/-!
# The memory model of the square-by-entry CIOS rows

Row `i` of the square of the operand at `2048` (limb `k` of `a` at
`aAddr n k = 2048 + 32 * (n - 1 - k)`, `t[k]` at `tAddr n k`) runs

* the prologue `sqPro` (the new `sq_row` block): `x = a_i`, `tb = SGT 0 aprev`,
  `f = x + tb`, `b2 = f + x`, `lo = x * f`, `hi = diagHi x f`,
  `s = lo + t_i` stored at `tAddr n i`, carry `C = [s < lo] + hi`;
* the unchanged multiply chain for the steps `j = i+1 .. n-1` with multiplier
  `b2` and incoming carry `C` (`l1Run`, each step exactly `Monpro.l1Step`'s body);
* the unchanged middle / second loop / tail (`rowFrom`, Monpro style).

Everything here is independent of code addresses.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.SquareModel

open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Fast
open Monpro

/-! ## The first limb loop from an arbitrary step and carry -/

/-- One step (index `j`) of the first limb loop on any memory and carry:
`t[j] := macSum a[j] bi t[j] c`, `c := macCarry a[j] bi t[j] c`. -/
def l1StepOn (q : MacState) (bi : UInt256) (pa n j : Nat) : MacState :=
  let x := MachineState.readWord q.memory (pa + 32 * (n - 1 - j))
  let t := MachineState.readWord q.memory (8256 + 32 * (n - 1 - j))
  { memory := MachineState.writeBytes q.memory
      (Data.Bytes.natToBytesPadded (macSum x bi t q.carry).toNat 32) (8256 + 32 * (n - 1 - j))
    carry := macCarry x bi t q.carry }

/-- `k` steps of the first limb loop, starting at step `j0` from `q`. -/
def l1Run (q : MacState) (bi : UInt256) (pa n j0 : Nat) : Nat → MacState
  | 0 => q
  | k + 1 => l1StepOn (l1Run q bi pa n j0 k) bi pa n (j0 + k)

theorem l1Run_zero (q : MacState) (bi : UInt256) (pa n j0 : Nat) :
    l1Run q bi pa n j0 0 = q := rfl

theorem l1Run_succ (q : MacState) (bi : UInt256) (pa n j0 k : Nat) :
    l1Run q bi pa n j0 (k + 1) = l1StepOn (l1Run q bi pa n j0 k) bi pa n (j0 + k) := rfl

theorem l1Step_succ_eq (mem : ByteArray) (bi : UInt256) (pa n j : Nat) :
    l1Step mem bi pa n (j + 1) = l1StepOn (l1Step mem bi pa n j) bi pa n j := rfl

/-- `Monpro.l1Step` is the run from step `0` with carry `0`. -/
theorem l1Step_eq_l1Run (mem : ByteArray) (bi : UInt256) (pa n : Nat) :
    ∀ j, l1Step mem bi pa n j = l1Run ⟨mem, UInt256.ofNat 0⟩ bi pa n 0 j
  | 0 => rfl
  | j + 1 => by
      rw [l1Step_succ_eq, l1Step_eq_l1Run mem bi pa n j, l1Run_succ, Nat.zero_add]

/-! ### Where the loop writes -/

theorem readWord_l1StepOn_disj (q : MacState) (bi : UInt256) (pa n j addr : Nat)
    (haddr : addr + 32 ≤ 8256 + 32 * (n - 1 - j) ∨ 8256 + 32 * (n - 1 - j) + 32 ≤ addr) :
    MachineState.readWord (l1StepOn q bi pa n j).memory addr =
      MachineState.readWord q.memory addr := by
  apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
  rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  exact haddr

/-- Every step of a run that stays inside the `t` block writes only inside
`[8256, 8256 + 32 * n)`. -/
theorem readWord_l1Run (q : MacState) (bi : UInt256) (pa n j0 addr : Nat)
    (haddr : addr + 32 ≤ 8256 ∨ 8256 + 32 * n ≤ addr) :
    ∀ k, j0 + k ≤ n →
      MachineState.readWord (l1Run q bi pa n j0 k).memory addr =
        MachineState.readWord q.memory addr := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
      intro hk
      rw [l1Run_succ, readWord_l1StepOn_disj (l1Run q bi pa n j0 k) bi pa n (j0 + k) addr
        (by omega)]
      exact ih (by omega)

theorem l1Run_carry_succ (q : MacState) (bi : UInt256) (pa n j0 k : Nat) :
    (l1Run q bi pa n j0 (k + 1)).carry =
      macCarry (MachineState.readWord (l1Run q bi pa n j0 k).memory (pa + 32 * (n - 1 - (j0 + k))))
        bi (MachineState.readWord (l1Run q bi pa n j0 k).memory (tAddr n (j0 + k)))
        (l1Run q bi pa n j0 k).carry := rfl

theorem l1Run_memory_succ (q : MacState) (bi : UInt256) (pa n j0 k : Nat) :
    (l1Run q bi pa n j0 (k + 1)).memory =
      MachineState.writeBytes (l1Run q bi pa n j0 k).memory
        (Data.Bytes.natToBytesPadded
          (macSum (MachineState.readWord (l1Run q bi pa n j0 k).memory (pa + 32 * (n - 1 - (j0 + k))))
            bi (MachineState.readWord (l1Run q bi pa n j0 k).memory (tAddr n (j0 + k)))
            (l1Run q bi pa n j0 k).carry).toNat 32)
        (tAddr n (j0 + k)) := rfl

/-! ## Limb sums over the `t` block -/

/-- Replacing one limb of a limb sum. -/
theorem limbSum_update (f g : Nat → Nat) (j : Nat) :
    ∀ m, (∀ k, k < m → k ≠ j → g k = f k) → j < m →
      limbSum g m + f j * Limbs.radix ^ j = limbSum f m + g j * Limbs.radix ^ j := by
  intro m
  induction m with
  | zero => intro _ h; exact absurd h (Nat.not_lt_zero j)
  | succ m ih =>
      intro hg hj
      rw [limbSum_succ, limbSum_succ]
      rcases Nat.lt_or_ge j m with hlt | hge
      · have h1 := ih (fun k hk hkj => hg k (by omega) hkj) hlt
        have h2 : g m = f m := hg m (by omega) (by omega)
        rw [h2]
        omega
      · have hjm : j = m := by omega
        subst hjm
        have h1 : limbSum g j = limbSum f j :=
          limbSum_congr j (fun k hk => hg k (by omega) (by omega))
        rw [h1]
        omega

/-- The `t` limbs as a function. -/
def tLimbs (mem : ByteArray) (n : Nat) (k : Nat) : Nat :=
  (MachineState.readWord mem (tAddr n k)).toNat

/-- Storing one `t` limb changes the limb sum by exactly that limb. -/
theorem limbSum_tLimbs_write (mem : ByteArray) (n j : Nat) (w : UInt256) (hj : j < n) :
    limbSum (tLimbs (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded w.toNat 32)
          (tAddr n j)) n) n +
        (MachineState.readWord mem (tAddr n j)).toNat * Limbs.radix ^ j =
      limbSum (tLimbs mem n) n + w.toNat * Limbs.radix ^ j := by
  have hj' : tLimbs (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded w.toNat 32)
      (tAddr n j)) n j = w.toNat := by
    unfold tLimbs
    rw [Challenge.EvmProof.Memory.readWord_writeWord]
  have h := limbSum_update (tLimbs mem n)
    (tLimbs (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded w.toNat 32)
      (tAddr n j)) n) j n
    (fun k hk hkj => by
      unfold tLimbs
      rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint]
      rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
      simp only [tAddr]
      omega) hj
  rw [hj'] at h
  exact h

private theorem run_step_alg {Lg Lf t s C' c x bi A0 T0 Q Aj Rj R : Nat}
    (hupd : Lg + t * Rj = Lf + s * Rj)
    (hmac : C' * R + s = t + x * bi + c)
    (hih : Lf + c * Rj + bi * A0 = T0 + Q + bi * Aj) :
    Lg + C' * (Rj * R) + bi * A0 = T0 + Q + bi * (Aj + x * Rj) := by
  have key : Lg + C' * (Rj * R) + bi * A0 + t * Rj =
      T0 + Q + bi * (Aj + x * Rj) + t * Rj := by
    calc Lg + C' * (Rj * R) + bi * A0 + t * Rj
        = (Lg + t * Rj) + C' * R * Rj + bi * A0 := by ring
      _ = (Lf + s * Rj) + C' * R * Rj + bi * A0 := by rw [hupd]
      _ = Lf + (C' * R + s) * Rj + bi * A0 := by ring
      _ = Lf + (t + x * bi + c) * Rj + bi * A0 := by rw [hmac]
      _ = (Lf + c * Rj + bi * A0) + t * Rj + x * bi * Rj := by ring
      _ = (T0 + Q + bi * Aj) + t * Rj + x * bi * Rj := by rw [hih]
      _ = T0 + Q + bi * (Aj + x * Rj) + t * Rj := by ring
  exact Nat.add_right_cancel key

/-- The source limbs of a first-loop run as a function. -/
def srcLimbs (mem : ByteArray) (pa n : Nat) (j : Nat) : Nat :=
  (MachineState.readWord mem (pa + 32 * (n - 1 - j))).toNat

/-- **The generalised first-loop invariant.**  After `k` steps from step `j0`
with incoming carry `q.carry` (of weight `radix ^ j0`), the `t` block plus the
carry (of weight `radix ^ (j0 + k)`) has gained exactly
`bi * Σ_{j0 ≤ j < j0 + k} a[j] radix ^ j`. -/
theorem l1Run_sum (q : MacState) (bi : UInt256) (pa n j0 : Nat)
    (hpa : pa + 32 * n ≤ 8192) :
    ∀ k, j0 + k ≤ n →
      limbSum (tLimbs (l1Run q bi pa n j0 k).memory n) n +
          (l1Run q bi pa n j0 k).carry.toNat * Limbs.radix ^ (j0 + k) +
          bi.toNat * limbSum (srcLimbs q.memory pa n) j0 =
        limbSum (tLimbs q.memory n) n + q.carry.toNat * Limbs.radix ^ j0 +
          bi.toNat * limbSum (srcLimbs q.memory pa n) (j0 + k) := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
      intro hk
      have hih := ih (by omega)
      have hjn : j0 + k < n := by omega
      -- the source limb is unchanged by the earlier steps
      have hx : MachineState.readWord (l1Run q bi pa n j0 k).memory (pa + 32 * (n - 1 - (j0 + k))) =
          MachineState.readWord q.memory (pa + 32 * (n - 1 - (j0 + k))) :=
        readWord_l1Run q bi pa n j0 _ (Or.inl (by omega)) k (by omega)
      have hmac := macSpec
        (MachineState.readWord (l1Run q bi pa n j0 k).memory (pa + 32 * (n - 1 - (j0 + k)))) bi
        (MachineState.readWord (l1Run q bi pa n j0 k).memory (tAddr n (j0 + k)))
        (l1Run q bi pa n j0 k).carry
      have hupd := limbSum_tLimbs_write (l1Run q bi pa n j0 k).memory n (j0 + k)
        (macSum (MachineState.readWord (l1Run q bi pa n j0 k).memory (pa + 32 * (n - 1 - (j0 + k))))
          bi (MachineState.readWord (l1Run q bi pa n j0 k).memory (tAddr n (j0 + k)))
          (l1Run q bi pa n j0 k).carry) hjn
      rw [← l1Run_memory_succ] at hupd
      rw [← l1Run_carry_succ, hx, ← radix_eq] at hmac
      rw [hx] at hupd
      have hsrc : limbSum (srcLimbs q.memory pa n) (j0 + (k + 1)) =
          limbSum (srcLimbs q.memory pa n) (j0 + k) +
            (MachineState.readWord q.memory (pa + 32 * (n - 1 - (j0 + k)))).toNat *
              Limbs.radix ^ (j0 + k) := by
        rw [show j0 + (k + 1) = (j0 + k) + 1 by omega, limbSum_succ]
        rfl
      rw [hsrc, show j0 + (k + 1) = (j0 + k) + 1 by omega, pow_succ Limbs.radix (j0 + k)]
      exact run_step_alg hupd hmac hih

/-! ## The square-row prologue -/

/-- The address of limb `k` of the squared operand. -/
def aAddr (n k : Nat) : Nat := 2048 + 32 * (n - 1 - k)

/-- The limbs of the squared operand as a function. -/
def aLimbs (mem : ByteArray) (n : Nat) (k : Nat) : Nat :=
  (MachineState.readWord mem (aAddr n k)).toNat

/-- `x = a_i`, read by `DUP1 MLOAD` at the row pointer. -/
def sqX (mem : ByteArray) (n i : Nat) : UInt256 := MachineState.readWord mem (aAddr n i)

/-- The row multiplier `b2 = (x + tb) + x` (limb `i` of `2a`). -/
def sqB2 (x tb : UInt256) : UInt256 := (x + tb) + x

/-- The low word of the diagonal `lo = x * (x + tb)`. -/
def sqLo (x tb : UInt256) : UInt256 := x * (x + tb)

/-- The high word of the diagonal, as `sq_row` computes it. -/
def sqHi (x tb : UInt256) : UInt256 := SquareDiag.diagHi x (x + tb)

/-- The stored limb `s = lo + t_i`. -/
def sqSum (mem : ByteArray) (n i : Nat) (tb : UInt256) : UInt256 :=
  sqLo (sqX mem n i) tb + MachineState.readWord mem (tAddr n i)

/-- The carry `C = [s < lo] + hi` into the chain. -/
def sqCarry (mem : ByteArray) (n i : Nat) (tb : UInt256) : UInt256 :=
  UInt256.lt (sqSum mem n i tb) (sqLo (sqX mem n i) tb) + sqHi (sqX mem n i) tb

/-- Memory and carry after the `sq_row` prologue of row `i`: `t[i] := s`, carry `C`. -/
def sqPro (mem : ByteArray) (n i : Nat) (tb : UInt256) : MacState :=
  { memory := MachineState.writeBytes mem
      (Data.Bytes.natToBytesPadded (sqSum mem n i tb).toNat 32) (tAddr n i)
    carry := sqCarry mem n i tb }

/-- The prologue with every word operation spelled out (for trace matching). -/
theorem sqPro_eq (mem : ByteArray) (n i : Nat) (tb : UInt256) :
    sqPro mem n i tb =
      { memory := MachineState.writeBytes mem
          (Data.Bytes.natToBytesPadded
            (MachineState.readWord mem (aAddr n i) * (MachineState.readWord mem (aAddr n i) + tb) +
              MachineState.readWord mem (tAddr n i)).toNat 32) (tAddr n i)
        carry :=
          UInt256.lt
              (MachineState.readWord mem (aAddr n i) * (MachineState.readWord mem (aAddr n i) + tb) +
                MachineState.readWord mem (tAddr n i))
              (MachineState.readWord mem (aAddr n i) * (MachineState.readWord mem (aAddr n i) + tb)) +
            ((UInt256.mulMod (MachineState.readWord mem (aAddr n i))
                  (MachineState.readWord mem (aAddr n i) + tb) maxWord -
                UInt256.lt (MachineState.readWord mem (aAddr n i) + tb)
                  (MachineState.readWord mem (aAddr n i)) -
              UInt256.lt
                (UInt256.mulMod (MachineState.readWord mem (aAddr n i))
                    (MachineState.readWord mem (aAddr n i) + tb) maxWord -
                  UInt256.lt (MachineState.readWord mem (aAddr n i) + tb)
                    (MachineState.readWord mem (aAddr n i)))
                (MachineState.readWord mem (aAddr n i) * (MachineState.readWord mem (aAddr n i) + tb))) -
              MachineState.readWord mem (aAddr n i) * (MachineState.readWord mem (aAddr n i) + tb)) } :=
  rfl

/-- `ADD` with the carry flag taken against the first operand. -/
theorem add_carry_split_left (a b : UInt256) :
    (UInt256.lt (a + b) a).toNat * 2 ^ 256 + (a + b).toNat = a.toNat + b.toNat := by
  rw [Challenge.EvmProof.Word.word_add_comm a b, Nat.add_comm a.toNat b.toNat]
  exact add_carry_split b a

/-- The prologue is exact and its carry does not overflow:
`C = [s < lo] + hi` without wrap, and `s + C * 2^256 = t_i + x * (x + tb)`. -/
theorem sqCarry_toNat (mem : ByteArray) (n i : Nat) (tb : UInt256) (htb : tb.toNat ≤ 1) :
    (sqCarry mem n i tb).toNat =
        (UInt256.lt (sqSum mem n i tb) (sqLo (sqX mem n i) tb)).toNat +
          (sqHi (sqX mem n i) tb).toNat ∧
      (sqSum mem n i tb).toNat + (sqCarry mem n i tb).toNat * 2 ^ 256 =
        (MachineState.readWord mem (tAddr n i)).toNat +
          (sqX mem n i).toNat * ((sqX mem n i).toNat + tb.toNat) := by
  have hd := SquareDiag.diag_spec (sqX mem n i) tb htb
  have hs := add_carry_split_left (sqLo (sqX mem n i) tb) (MachineState.readWord mem (tAddr n i))
  have hx := word_lt_size (sqX mem n i)
  have ht := word_lt_size (MachineState.readWord mem (tAddr n i))
  have hprod : (sqX mem n i).toNat * ((sqX mem n i).toNat + tb.toNat) ≤
      (2 ^ 256 - 1) * 2 ^ 256 :=
    Nat.mul_le_mul (by omega) (by omega)
  -- the carry as a natural number, before truncation
  have hexact : (sqSum mem n i tb).toNat +
      ((UInt256.lt (sqSum mem n i tb) (sqLo (sqX mem n i) tb)).toNat +
        (sqHi (sqX mem n i) tb).toNat) * 2 ^ 256 =
      (MachineState.readWord mem (tAddr n i)).toNat +
        (sqX mem n i).toNat * ((sqX mem n i).toNat + tb.toNat) := by
    unfold sqSum sqHi
    unfold sqLo at hs ⊢
    rw [← hd]
    linarith
  have hlt : (UInt256.lt (sqSum mem n i tb) (sqLo (sqX mem n i) tb)).toNat +
      (sqHi (sqX mem n i) tb).toNat < 2 ^ 256 := by
    by_contra hcon
    have hge : 2 ^ 256 * 2 ^ 256 ≤
        ((UInt256.lt (sqSum mem n i tb) (sqLo (sqX mem n i) tb)).toNat +
          (sqHi (sqX mem n i) tb).toNat) * 2 ^ 256 :=
      Nat.mul_le_mul_right _ (Nat.le_of_not_lt hcon)
    have h2 : (2 ^ 256 - 1) * 2 ^ 256 + 2 ^ 256 = 2 ^ 256 * 2 ^ 256 := by norm_num
    omega
  have hval : (sqCarry mem n i tb).toNat =
      (UInt256.lt (sqSum mem n i tb) (sqLo (sqX mem n i) tb)).toNat +
        (sqHi (sqX mem n i) tb).toNat := by
    unfold sqCarry
    rw [Challenge.EvmProof.Word.word_toNat_add, Nat.mod_eq_of_lt hlt]
  exact ⟨hval, by rw [hval]; exact hexact⟩

theorem readWord_sqPro_disj (mem : ByteArray) (n i addr : Nat) (tb : UInt256)
    (haddr : addr + 32 ≤ tAddr n i ∨ tAddr n i + 32 ≤ addr) :
    MachineState.readWord (sqPro mem n i tb).memory addr = MachineState.readWord mem addr := by
  apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
  rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  exact haddr

/-- The prologue writes only inside `[8256, 8256 + 32 * n)`. -/
theorem readWord_sqPro (mem : ByteArray) (n i addr : Nat) (tb : UInt256) (hi : i < n)
    (haddr : addr + 32 ≤ 8256 ∨ 8256 + 32 * n ≤ addr) :
    MachineState.readWord (sqPro mem n i tb).memory addr = MachineState.readWord mem addr :=
  readWord_sqPro_disj mem n i addr tb (by simp only [tAddr]; omega)

/-- The prologue adds the diagonal `x * (x + tb)` at weight `radix ^ i`
(the carry has weight `radix ^ (i + 1)`). -/
theorem sqPro_sum (mem : ByteArray) (n i : Nat) (tb : UInt256) (hi : i < n) (htb : tb.toNat ≤ 1) :
    limbSum (tLimbs (sqPro mem n i tb).memory n) n +
        (sqPro mem n i tb).carry.toNat * Limbs.radix ^ (i + 1) =
      limbSum (tLimbs mem n) n +
        (sqX mem n i).toNat * ((sqX mem n i).toNat + tb.toNat) * Limbs.radix ^ i := by
  have hupd := limbSum_tLimbs_write mem n i (sqSum mem n i tb) hi
  have hc := (sqCarry_toNat mem n i tb htb).2
  rw [← radix_eq] at hc
  have hmem : (sqPro mem n i tb).memory = MachineState.writeBytes mem
      (Data.Bytes.natToBytesPadded (sqSum mem n i tb).toNat 32) (tAddr n i) := rfl
  have hcar : (sqPro mem n i tb).carry = sqCarry mem n i tb := rfl
  rw [hmem, hcar, pow_succ Limbs.radix i]
  have key : limbSum (tLimbs (MachineState.writeBytes mem
          (Data.Bytes.natToBytesPadded (sqSum mem n i tb).toNat 32) (tAddr n i)) n) n +
        (sqCarry mem n i tb).toNat * (Limbs.radix ^ i * Limbs.radix) +
        (MachineState.readWord mem (tAddr n i)).toNat * Limbs.radix ^ i =
      limbSum (tLimbs mem n) n +
        (sqX mem n i).toNat * ((sqX mem n i).toNat + tb.toNat) * Limbs.radix ^ i +
        (MachineState.readWord mem (tAddr n i)).toNat * Limbs.radix ^ i := by
    calc _ = (limbSum (tLimbs (MachineState.writeBytes mem
          (Data.Bytes.natToBytesPadded (sqSum mem n i tb).toNat 32) (tAddr n i)) n) n +
            (MachineState.readWord mem (tAddr n i)).toNat * Limbs.radix ^ i) +
            (sqCarry mem n i tb).toNat * Limbs.radix * Limbs.radix ^ i := by ring
      _ = (limbSum (tLimbs mem n) n + (sqSum mem n i tb).toNat * Limbs.radix ^ i) +
            (sqCarry mem n i tb).toNat * Limbs.radix * Limbs.radix ^ i := by rw [hupd]
      _ = limbSum (tLimbs mem n) n +
            ((sqSum mem n i tb).toNat + (sqCarry mem n i tb).toNat * Limbs.radix) *
              Limbs.radix ^ i := by ring
      _ = _ := by rw [hc]; ring
  exact Nat.add_right_cancel key

/-! ## The first loop of a square row -/

/-- The whole first phase of square row `i`: the prologue, then the unchanged
chain for the steps `i+1 .. n-1` with multiplier `b2` and carry `C`. -/
def sqL1 (mem : ByteArray) (n i : Nat) (tb : UInt256) : MacState :=
  l1Run (sqPro mem n i tb) (sqB2 (sqX mem n i) tb) 2048 n (i + 1) (n - 1 - i)

theorem readWord_sqL1 (mem : ByteArray) (n i addr : Nat) (tb : UInt256) (hi : i < n)
    (haddr : addr + 32 ≤ 8256 ∨ 8256 + 32 * n ≤ addr) :
    MachineState.readWord (sqL1 mem n i tb).memory addr = MachineState.readWord mem addr := by
  unfold sqL1
  rw [readWord_l1Run (sqPro mem n i tb) (sqB2 (sqX mem n i) tb) 2048 n (i + 1) addr haddr
    (n - 1 - i) (by omega), readWord_sqPro mem n i addr tb hi haddr]

theorem limbSum_aLimbs_sqPro (mem : ByteArray) (n i : Nat) (tb : UInt256) (hi : i < n)
    (hn : n ≤ 32) (j : Nat) :
    limbSum (srcLimbs (sqPro mem n i tb).memory 2048 n) j = limbSum (aLimbs mem n) j := by
  apply limbSum_congr
  intro k _
  unfold srcLimbs aLimbs aAddr
  rw [readWord_sqPro mem n i (2048 + 32 * (n - 1 - k)) tb hi (Or.inl (by omega))]

/-- **The first phase of a square row is exact**:
`Σ t'[k] rad^k + C' rad^n + b2 · A_{i+1} = Σ t[k] rad^k + x (x + tb) rad^i + b2 · A_n`,
i.e. it adds the diagonal at weight `rad^i` and `b2 · Σ_{i<j<n} a_j rad^j`. -/
theorem sqL1_sum (mem : ByteArray) (n i : Nat) (tb : UInt256) (hi : i < n) (hn : n ≤ 32)
    (htb : tb.toNat ≤ 1) :
    limbSum (tLimbs (sqL1 mem n i tb).memory n) n +
        (sqL1 mem n i tb).carry.toNat * Limbs.radix ^ n +
        (sqB2 (sqX mem n i) tb).toNat * limbSum (aLimbs mem n) (i + 1) =
      limbSum (tLimbs mem n) n +
        (sqX mem n i).toNat * ((sqX mem n i).toNat + tb.toNat) * Limbs.radix ^ i +
        (sqB2 (sqX mem n i) tb).toNat * limbSum (aLimbs mem n) n := by
  have hrun := l1Run_sum (sqPro mem n i tb) (sqB2 (sqX mem n i) tb) 2048 n (i + 1) (by omega)
    (n - 1 - i) (by omega)
  have hpro := sqPro_sum mem n i tb hi htb
  rw [limbSum_aLimbs_sqPro mem n i tb hi hn, limbSum_aLimbs_sqPro mem n i tb hi hn,
    show i + 1 + (n - 1 - i) = n by omega] at hrun
  unfold sqL1
  omega

/-! ## One whole row, Monpro style -/

/-- The row middle on the first-loop result `q`. -/
def rowFromMid (q : MacState) : ByteArray := midMem q.memory q.carry

/-- The second limb loop on the first-loop result `q`. -/
def rowFromL2 (q : MacState) (n : Nat) : MacState :=
  l2Step (rowFromMid q) (rowMu q.memory n) (rowC0 q.memory n) n (n - 1)

/-- Middle, second loop and tail of a CIOS row applied to a first-loop result. -/
def rowFrom (q : MacState) (n : Nat) : ByteArray :=
  tailMem (rowFromL2 q n).memory (rowFromL2 q n).carry

theorem rowMem_eq_rowFrom (mem : ByteArray) (pa pb n i : Nat) :
    rowMem mem pa pb n i = rowFrom (rowL1 mem pa pb n i) n := rfl

theorem readWord_rowFrom (q : MacState) (n addr : Nat) (hn : n ≤ 32)
    (haddr : addr + 32 ≤ 8192 ∨ 9280 ≤ addr) :
    MachineState.readWord (rowFrom q n) addr = MachineState.readWord q.memory addr := by
  unfold rowFrom rowFromL2 rowFromMid
  rw [readWord_tailMem _ _ _ haddr, readWord_l2Step _ _ _ _ _ _ hn haddr,
    readWord_midMem _ _ _ haddr]

/-- Limbs `0 .. n-2` of the new `t` are what the second loop stored. -/
theorem readWord_rowFrom_limb (q : MacState) (n k : Nat) (hn32 : n ≤ 32) (hk : k + 2 ≤ n) :
    MachineState.readWord (rowFrom q n) (tAddr n k) =
      l2Val (rowFromMid q) (rowMu q.memory n) (rowC0 q.memory n) n k := by
  unfold rowFrom
  rw [readWord_tailMem_high (rowFromL2 q n).memory (rowFromL2 q n).carry (tAddr n k)
    (by simp only [tAddr]; omega)]
  exact readWord_l2Step_val _ _ _ n k hn32 (by omega) (n - 1) (by omega) (by omega)

theorem lowValue_rowFrom (q : MacState) (p : Nat) (hn32 : p + 2 ≤ 32) :
    Csub.lowValue (rowFrom q (p + 2)) 8256 (p + 2) (p + 2) =
      limbSum (fun k => (l2Val (rowFromMid q) (rowMu q.memory (p + 2))
          (rowC0 q.memory (p + 2)) (p + 2) k).toNat) (p + 1) +
        (MachineState.readWord (rowFrom q (p + 2)) 8256).toNat * Limbs.radix ^ (p + 1) := by
  rw [← limbSum_eq_lowValue, limbSum_succ]
  have hlast : (MachineState.readWord (rowFrom q (p + 2))
      (8256 + 32 * (p + 2 - 1 - (p + 1)))).toNat =
      (MachineState.readWord (rowFrom q (p + 2)) 8256).toNat := by
    have h0 : 8256 + 32 * (p + 2 - 1 - (p + 1)) = 8256 := by omega
    rw [h0]
  rw [hlast]
  congr 1
  apply limbSum_congr
  intro k hk
  have h := readWord_rowFrom_limb q (p + 2) k hn32 (by omega)
  simp only [tAddr] at h
  rw [h]

private theorem row_alg' {R P tn Cn u cu Cp v cv c0 mu m0 l0 S2 St Sm L1sum mm : Nat}
    (hA : cu * R + u = tn + Cn)
    (hB : cv * R + v = u + Cp)
    (hC : c0 * R = l0 + m0 * mu)
    (hD : S2 + Cp * P = c0 + (St + mu * Sm))
    (hE : St * R + l0 = L1sum)
    (hF : Sm * R + m0 = mm) :
    ((cu + cv) * (P * R) + (S2 + v * P)) * R =
      tn * (P * R) + (L1sum + Cn * (P * R)) + mu * mm := by
  calc ((cu + cv) * (P * R) + (S2 + v * P)) * R
      = cu * R * (P * R) + (cv * R + v) * (P * R) + S2 * R := by ring
    _ = cu * R * (P * R) + (u + Cp) * (P * R) + S2 * R := by rw [hB]
    _ = (cu * R + u) * (P * R) + (S2 + Cp * P) * R := by ring
    _ = (tn + Cn) * (P * R) + (S2 + Cp * P) * R := by rw [hA]
    _ = (tn + Cn) * (P * R) + (c0 + (St + mu * Sm)) * R := by rw [hD]
    _ = (tn + Cn) * (P * R) + (c0 * R + (St * R + mu * (Sm * R))) := by ring
    _ = (tn + Cn) * (P * R) + ((l0 + m0 * mu) + (St * R + mu * (Sm * R))) := by rw [hC]
    _ = (tn + Cn) * (P * R) + ((St * R + l0) + mu * (Sm * R + m0)) := by ring
    _ = (tn + Cn) * (P * R) + (L1sum + mu * (Sm * R + m0)) := by rw [hE]
    _ = (tn + Cn) * (P * R) + (L1sum + mu * mm) := by rw [hF]
    _ = tn * (P * R) + (L1sum + Cn * (P * R)) + mu * mm := by ring

/-- **The row equation from any first-loop result `q`** (a copy of
`Monpro.row_equation` with the first-loop sum left symbolic):
`t_new · rad = t[n] · rad^n + (Σ_k q.t[k] rad^k + q.carry · rad^n) + mu · m`. -/
theorem row_equation_of_l1 (q : MacState) (p mm : Nat) (hn32 : p + 2 ≤ 32)
    (hm : Model.FastRepresents q.memory 0 (p + 2) mm)
    (hminv : ((MachineState.readWord q.memory (32 * (p + 2) - 32)).toNat *
        (MachineState.readWord q.memory 9376).toNat + 1) % 2 ^ 256 = 0) :
    ((MachineState.readWord (rowFrom q (p + 2)) 8224).toNat * Limbs.radix ^ (p + 2) +
        Csub.lowValue (rowFrom q (p + 2)) 8256 (p + 2) (p + 2)) * Limbs.radix =
      (MachineState.readWord q.memory 8224).toNat * Limbs.radix ^ (p + 2) +
        (limbSum (tLimbs q.memory (p + 2)) (p + 2) + q.carry.toNat * Limbs.radix ^ (p + 2)) +
        (rowMu q.memory (p + 2)).toNat * mm := by
  have hpow : Limbs.radix ^ (p + 2) = Limbs.radix ^ (p + 1) * Limbs.radix :=
    pow_succ Limbs.radix (p + 1)
  have hMDtn : MachineState.readWord (rowFromMid q) 8224 =
      MachineState.readWord q.memory 8224 + q.carry := readWord_midMem_tn _ _
  have hMDtnp : MachineState.readWord (rowFromMid q) 8192 =
      UInt256.lt (MachineState.readWord q.memory 8224 + q.carry) q.carry :=
    readWord_midMem_tnp _ _
  have hL2tn : MachineState.readWord (rowFromL2 q (p + 2)).memory 8224 =
      MachineState.readWord (rowFromMid q) 8224 :=
    readWord_l2Step_low _ _ _ (p + 2) 8224 (p + 2 - 1) (by omega)
  have hL2tnp : MachineState.readWord (rowFromL2 q (p + 2)).memory 8192 =
      MachineState.readWord (rowFromMid q) 8192 :=
    readWord_l2Step_low _ _ _ (p + 2) 8192 (p + 2 - 1) (by omega)
  have hcu : (UInt256.lt (MachineState.readWord q.memory 8224 + q.carry) q.carry).toNat ≤ 1 := by
    rw [word_toNat_lt']
    split <;> omega
  have hcv : (UInt256.lt (MachineState.readWord (rowFromMid q) 8224 +
      (rowFromL2 q (p + 2)).carry) (rowFromL2 q (p + 2)).carry).toNat ≤ 1 := by
    rw [word_toNat_lt']
    split <;> omega
  have hFtn : (MachineState.readWord (rowFrom q (p + 2)) 8224).toNat =
      (UInt256.lt (MachineState.readWord q.memory 8224 + q.carry) q.carry).toNat +
      (UInt256.lt (MachineState.readWord (rowFromMid q) 8224 + (rowFromL2 q (p + 2)).carry)
        (rowFromL2 q (p + 2)).carry).toNat := by
    rw [rowFrom, readWord_tailMem_tn, hL2tnp, hMDtnp, hL2tn,
      Challenge.EvmProof.Word.word_toNat_add, Nat.mod_eq_of_lt (by omega)]
  have hFts : (MachineState.readWord (rowFrom q (p + 2)) 8256).toNat =
      (MachineState.readWord (rowFromMid q) 8224 + (rowFromL2 q (p + 2)).carry).toNat := by
    rw [rowFrom, readWord_tailMem_ts, hL2tn]
  have hA : (UInt256.lt (MachineState.readWord q.memory 8224 + q.carry) q.carry).toNat *
        Limbs.radix + (MachineState.readWord (rowFromMid q) 8224).toNat =
      (MachineState.readWord q.memory 8224).toNat + q.carry.toNat := by
    rw [hMDtn, radix_eq]
    exact add_carry_split (MachineState.readWord q.memory 8224) q.carry
  have hB : (UInt256.lt (MachineState.readWord (rowFromMid q) 8224 +
        (rowFromL2 q (p + 2)).carry) (rowFromL2 q (p + 2)).carry).toNat * Limbs.radix +
      (MachineState.readWord (rowFromMid q) 8224 + (rowFromL2 q (p + 2)).carry).toNat =
      (MachineState.readWord (rowFromMid q) 8224).toNat + (rowFromL2 q (p + 2)).carry.toNat := by
    rw [radix_eq]
    exact add_carry_split (MachineState.readWord (rowFromMid q) 8224) (rowFromL2 q (p + 2)).carry
  have hC : (rowC0 q.memory (p + 2)).toNat * Limbs.radix =
      (MachineState.readWord q.memory (8224 + 32 * (p + 2))).toNat +
        (MachineState.readWord q.memory (32 * (p + 2) - 32)).toNat *
          (rowMu q.memory (p + 2)).toNat := by
    rw [radix_eq]
    exact c0_spec (MachineState.readWord q.memory (32 * (p + 2) - 32))
      (MachineState.readWord q.memory 9376)
      (MachineState.readWord q.memory (8224 + 32 * (p + 2))) hminv
  have hD0 := l2_invariant (rowFromMid q) (rowMu q.memory (p + 2)) (rowC0 q.memory (p + 2))
    (p + 2) hn32 (p + 1) (by omega)
  simp only [Nat.add_sub_cancel] at hD0
  have hD : limbSum (fun k => (l2Val (rowFromMid q) (rowMu q.memory (p + 2))
          (rowC0 q.memory (p + 2)) (p + 2) k).toNat) (p + 1) +
        (rowFromL2 q (p + 2)).carry.toNat * Limbs.radix ^ (p + 1) =
      (rowC0 q.memory (p + 2)).toNat +
        (limbSum (fun k => (MachineState.readWord (rowFromMid q) (8256 + 32 * (p - k))).toNat)
            (p + 1) +
          (rowMu q.memory (p + 2)).toNat *
            limbSum (fun k => (MachineState.readWord (rowFromMid q) (32 * (p - k))).toNat)
              (p + 1)) := hD0
  have hstF : ∀ k, k < p + 1 →
      (MachineState.readWord (rowFromMid q) (8256 + 32 * (p - k))).toNat =
        tLimbs q.memory (p + 2) (k + 1) := by
    intro k hk
    unfold rowFromMid tLimbs tAddr
    rw [readWord_midMem_high q.memory q.carry (8256 + 32 * (p - k)) (by omega)]
    have haddr : 8256 + 32 * (p + 2 - 1 - (k + 1)) = 8256 + 32 * (p - k) := by omega
    rw [haddr]
  have hE : limbSum (fun k => (MachineState.readWord (rowFromMid q)
          (8256 + 32 * (p - k))).toNat) (p + 1) * Limbs.radix +
        (MachineState.readWord q.memory (8224 + 32 * (p + 2))).toNat =
      limbSum (tLimbs q.memory (p + 2)) (p + 2) := by
    rw [limbSum_congr (p + 1) hstF]
    have h0 : (MachineState.readWord q.memory (8224 + 32 * (p + 2))).toNat =
        tLimbs q.memory (p + 2) 0 := by
      unfold tLimbs tAddr
      have : 8256 + 32 * (p + 2 - 1 - 0) = 8224 + 32 * (p + 2) := by omega
      rw [this]
    rw [h0]
    exact limbSum_shift (tLimbs q.memory (p + 2)) (p + 1)
  have hmm := limbSum_fastRepresents hm
  simp only [Nat.zero_add] at hmm
  have hsmF : ∀ k, k < p + 1 →
      (MachineState.readWord (rowFromMid q) (32 * (p - k))).toNat =
        (MachineState.readWord q.memory (32 * (p + 2 - 1 - (k + 1)))).toNat := by
    intro k hk
    unfold rowFromMid
    rw [readWord_midMem_low' q.memory q.carry (32 * (p - k)) (by omega)]
    have haddr : 32 * (p + 2 - 1 - (k + 1)) = 32 * (p - k) := by omega
    rw [haddr]
  have hF : limbSum (fun k => (MachineState.readWord (rowFromMid q)
          (32 * (p - k))).toNat) (p + 1) * Limbs.radix +
        (MachineState.readWord q.memory (32 * (p + 2) - 32)).toNat = mm := by
    rw [limbSum_congr (p + 1) hsmF]
    have h0 : 32 * (p + 2) - 32 = 32 * (p + 2 - 1 - 0) := by omega
    rw [h0]
    rw [limbSum_shift (fun k =>
      (MachineState.readWord q.memory (32 * (p + 2 - 1 - k))).toNat) (p + 1)]
    exact hmm
  rw [lowValue_rowFrom q p hn32, hFtn, hFts, hpow]
  exact row_alg' hA hB hC hD hE hF

/-! ## Square rows (Monpro style) -/

/-- The top bit carried into row `i` (`SGT 0 aprev`): zero for row `0`, the top
bit of `a_{i-1}` afterwards. -/
def sqTb (mem : ByteArray) (n : Nat) : Nat → UInt256
  | 0 => UInt256.ofNat 0
  | i + 1 => UInt256.sgt (UInt256.ofNat 0) (MachineState.readWord mem (aAddr n i))

/-- Memory after square row `i` with carried top bit `tb`. -/
def sqRowMem (mem : ByteArray) (n i : Nat) (tb : UInt256) : ByteArray :=
  rowFrom (sqL1 mem n i tb) n

/-- Memory after `i` square rows. -/
def sqRowsMem (mem : ByteArray) (n : Nat) : Nat → ByteArray
  | 0 => mem
  | i + 1 => sqRowMem (sqRowsMem mem n i) n i (sqTb (sqRowsMem mem n i) n i)

theorem sgt_zero_le_one (p : UInt256) : (UInt256.sgt (UInt256.ofNat 0) p).toNat ≤ 1 := by
  rw [SquareDiag.sgt_zero_toNat]
  have := word_lt_size p
  exact Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul (by norm_num)).2 (by omega))

theorem sgt_zero_eq_zero_of_lt (p : UInt256) (hp : p.toNat < 2 ^ 255) :
    UInt256.sgt (UInt256.ofNat 0) p = UInt256.ofNat 0 := by
  apply Challenge.EvmProof.Word.word_ext
  rw [SquareDiag.sgt_zero_toNat, Nat.div_eq_of_lt hp]
  decide

theorem sqTb_le_one (mem : ByteArray) (n i : Nat) : (sqTb mem n i).toNat ≤ 1 := by
  cases i with
  | zero => show (UInt256.ofNat 0).toNat ≤ 1; decide
  | succ i => exact sgt_zero_le_one _

/-- The carried top bit is `SquareMath.tbm` of the operand limbs. -/
theorem sqTb_toNat (mem m0 : ByteArray) (n i : Nat) (hA : ∀ k, aLimbs mem n k = aLimbs m0 n k) :
    (sqTb mem n i).toNat = SquareMath.tbm (2 ^ 255) (aLimbs m0 n) i := by
  cases i with
  | zero => show (UInt256.ofNat 0).toNat = 0; decide
  | succ i =>
      show (UInt256.sgt (UInt256.ofNat 0) (MachineState.readWord mem (aAddr n i))).toNat =
        aLimbs m0 n i / 2 ^ 255
      rw [SquareDiag.sgt_zero_toNat]
      exact congrArg (· / 2 ^ 255) (hA i)

/-- The rows write only inside `[8192, 9280)`. -/
theorem readWord_sqRowMem (mem : ByteArray) (n i addr : Nat) (tb : UInt256)
    (hi : i < n) (hn : n ≤ 32) (haddr : addr + 32 ≤ 8192 ∨ 9280 ≤ addr) :
    MachineState.readWord (sqRowMem mem n i tb) addr = MachineState.readWord mem addr := by
  unfold sqRowMem
  rw [readWord_rowFrom _ _ _ hn haddr, readWord_sqL1 mem n i addr tb hi (by omega)]

theorem readWord_sqRowsMem (mem : ByteArray) (n addr : Nat) (hn : n ≤ 32)
    (haddr : addr + 32 ≤ 8192 ∨ 9280 ≤ addr) :
    ∀ i, i ≤ n → MachineState.readWord (sqRowsMem mem n i) addr = MachineState.readWord mem addr := by
  intro i
  induction i with
  | zero => intro _; rfl
  | succ i ih =>
      intro hi
      rw [sqRowsMem, readWord_sqRowMem (sqRowsMem mem n i) n i addr
        (sqTb (sqRowsMem mem n i) n i) (by omega) hn haddr]
      exact ih (by omega)

theorem fastRepresents_sqRowsMem (mem : ByteArray) (n i ptr cnt v : Nat) (hn : n ≤ 32)
    (hi : i ≤ n) (hfit : ptr + 32 * cnt ≤ 8192) (hrep : Model.FastRepresents mem ptr cnt v) :
    Model.FastRepresents (sqRowsMem mem n i) ptr cnt v := by
  refine (Model.fastRepresents_congr (a := mem) (b := sqRowsMem mem n i) ?_ v).1 hrep
  intro j hj
  rw [readWord_sqRowsMem mem n (ptr + 32 * j) hn (Or.inl (by omega)) i hi]

theorem aLimbs_sqRowsMem (mem : ByteArray) (n i : Nat) (hn : n ≤ 32) (hi : i ≤ n) (k : Nat) :
    aLimbs (sqRowsMem mem n i) n k = aLimbs mem n k := by
  unfold aLimbs
  rw [readWord_sqRowsMem mem n (aAddr n k) hn (Or.inl (by unfold aAddr; omega)) i hi]

/-- One square row is exact:
`t_{new} · rad + b2 · A_{i+1} = t + x (x + tb) rad^i + b2 · A_n + mu · m`. -/
theorem sqRow_equation (mem : ByteArray) (p i : Nat) (tb : UInt256) (mm : Nat)
    (hn32 : p + 2 ≤ 32) (hi : i < p + 2) (htb : tb.toNat ≤ 1)
    (hm : Model.FastRepresents mem 0 (p + 2) mm)
    (hminv : ((MachineState.readWord mem (32 * (p + 2) - 32)).toNat *
        (MachineState.readWord mem 9376).toNat + 1) % 2 ^ 256 = 0) :
    tValue (sqRowMem mem (p + 2) i tb) (p + 2) * Limbs.radix +
        (sqB2 (sqX mem (p + 2) i) tb).toNat * limbSum (aLimbs mem (p + 2)) (i + 1) =
      tValue mem (p + 2) +
        (sqX mem (p + 2) i).toNat * ((sqX mem (p + 2) i).toNat + tb.toNat) * Limbs.radix ^ i +
        (sqB2 (sqX mem (p + 2) i) tb).toNat * limbSum (aLimbs mem (p + 2)) (p + 2) +
        (rowMu (sqL1 mem (p + 2) i tb).memory (p + 2)).toNat * mm := by
  have hm' : Model.FastRepresents (sqL1 mem (p + 2) i tb).memory 0 (p + 2) mm := by
    refine (Model.fastRepresents_congr (a := mem) ?_ mm).1 hm
    intro j hj
    rw [readWord_sqL1 mem (p + 2) i (0 + 32 * j) tb hi (Or.inl (by omega))]
  have hminv' : ((MachineState.readWord (sqL1 mem (p + 2) i tb).memory (32 * (p + 2) - 32)).toNat *
      (MachineState.readWord (sqL1 mem (p + 2) i tb).memory 9376).toNat + 1) % 2 ^ 256 = 0 := by
    rw [readWord_sqL1 mem (p + 2) i (32 * (p + 2) - 32) tb hi (Or.inl (by omega)),
      readWord_sqL1 mem (p + 2) i 9376 tb hi (Or.inr (by omega))]
    exact hminv
  have hq := row_equation_of_l1 (sqL1 mem (p + 2) i tb) p mm hn32 hm' hminv'
  have hL := sqL1_sum mem (p + 2) i tb hi hn32 htb
  have htn : MachineState.readWord (sqL1 mem (p + 2) i tb).memory 8224 =
      MachineState.readWord mem 8224 :=
    readWord_sqL1 mem (p + 2) i 8224 tb hi (Or.inl (by omega))
  have hlow : limbSum (tLimbs mem (p + 2)) (p + 2) = Csub.lowValue mem 8256 (p + 2) (p + 2) :=
    limbSum_eq_lowValue mem 8256 (p + 2) (p + 2)
  rw [htn] at hq
  unfold tValue
  unfold sqRowMem
  rw [← hlow]
  linarith

/-! ## The global identity -/

theorem lsum_radix (f : Nat → Nat) : ∀ j, SquareMath.lsum Limbs.radix f j = limbSum f j
  | 0 => rfl
  | j + 1 => by rw [SquareMath.lsum, limbSum_succ, lsum_radix f j]

theorem two_half_radix : 2 * 2 ^ 255 = Limbs.radix := by
  unfold Limbs.radix
  norm_num

/-- The `t` accumulator of the zeroed scratch is `0`. -/
theorem tValue_mpZeroed (s : State) (mem : ByteArray) (n : Nat) :
    tValue (mpZeroed s mem n) n = 0 := by
  have hlow0 : Csub.lowValue (mpZeroed s mem n) 8256 n n = 0 :=
    Model.fastRepresents_value_unique
      (Csub.fastRepresents_lowValue (mpZeroed s mem n) 8256 n)
      (fastRepresents_mpZeroed s mem n)
  simp only [tValue, hlow0, readWord_mpZeroed_tn, Challenge.EvmProof.Word.word_toNat_ofNat]
  simp

/-- **The square-row invariant.**  After `i` square rows from an accumulator
`t = 0`: `t_i · rad^i = Σ_{r<i} X_r rad^r + Q_i · m` with `Q_i < rad^i`, where
`X_r = SquareMath.rowX` is row `r`'s contribution. -/
theorem sqRows_invariant (m0 : ByteArray) (p mm : Nat) (hn32 : p + 2 ≤ 32)
    (hm : Model.FastRepresents m0 0 (p + 2) mm)
    (hminv : ((MachineState.readWord m0 (32 * (p + 2) - 32)).toNat *
        (MachineState.readWord m0 9376).toNat + 1) % 2 ^ 256 = 0)
    (hz : tValue m0 (p + 2) = 0) :
    ∀ i, i ≤ p + 2 → ∃ Q, Q < Limbs.radix ^ i ∧
      tValue (sqRowsMem m0 (p + 2) i) (p + 2) * Limbs.radix ^ i =
        SquareMath.lsum Limbs.radix (SquareMath.rowX (2 ^ 255) (p + 2) (aLimbs m0 (p + 2))) i +
          Q * mm := by
  intro i
  induction i with
  | zero =>
      intro _
      refine ⟨0, by simp, ?_⟩
      show tValue m0 (p + 2) * Limbs.radix ^ 0 = 0 + 0 * mm
      rw [hz]; simp
  | succ i ih =>
      intro hi
      obtain ⟨Q, hQ, hinv⟩ := ih (by omega)
      -- the memory at the start of row `i`
      have hM : sqRowsMem m0 (p + 2) (i + 1) =
          sqRowMem (sqRowsMem m0 (p + 2) i) (p + 2) i
            (sqTb (sqRowsMem m0 (p + 2) i) (p + 2) i) := rfl
      have hmR := fastRepresents_sqRowsMem m0 (p + 2) i 0 (p + 2) mm hn32 (by omega)
        (by omega) hm
      have hminvR : ((MachineState.readWord (sqRowsMem m0 (p + 2) i) (32 * (p + 2) - 32)).toNat *
          (MachineState.readWord (sqRowsMem m0 (p + 2) i) 9376).toNat + 1) % 2 ^ 256 = 0 := by
        rw [readWord_sqRowsMem m0 (p + 2) (32 * (p + 2) - 32) hn32 (Or.inl (by omega)) i
            (by omega),
          readWord_sqRowsMem m0 (p + 2) 9376 hn32 (Or.inr (by omega)) i (by omega)]
        exact hminv
      have hrow := sqRow_equation (sqRowsMem m0 (p + 2) i) p i
        (sqTb (sqRowsMem m0 (p + 2) i) (p + 2) i) mm hn32 (by omega)
        (sqTb_le_one _ _ _) hmR hminvR
      rw [← hM] at hrow
      -- identify the words with the limbs of `a`
      have hA : ∀ k, aLimbs (sqRowsMem m0 (p + 2) i) (p + 2) k = aLimbs m0 (p + 2) k :=
        aLimbs_sqRowsMem m0 (p + 2) i hn32 (by omega)
      have hAf : aLimbs (sqRowsMem m0 (p + 2) i) (p + 2) = aLimbs m0 (p + 2) := funext hA
      have hx : (sqX (sqRowsMem m0 (p + 2) i) (p + 2) i).toNat = aLimbs m0 (p + 2) i := hA i
      have htb : (sqTb (sqRowsMem m0 (p + 2) i) (p + 2) i).toNat =
          SquareMath.tbm (2 ^ 255) (aLimbs m0 (p + 2)) i :=
        sqTb_toNat (sqRowsMem m0 (p + 2) i) m0 (p + 2) i hA
      have hb2 : (sqB2 (sqX (sqRowsMem m0 (p + 2) i) (p + 2) i)
          (sqTb (sqRowsMem m0 (p + 2) i) (p + 2) i)).toNat =
          SquareMath.a2 (2 ^ 255) (aLimbs m0 (p + 2)) i := by
        unfold sqB2 SquareMath.a2
        rw [Challenge.EvmProof.Word.word_toNat_add, Challenge.EvmProof.Word.word_toNat_add,
          hx, htb, Nat.mod_add_mod, show (2 : Nat) * 2 ^ 255 = 2 ^ 256 by norm_num]
        congr 1
        ring
      rw [hAf, hx, htb, hb2] at hrow
      -- the monotone limb sums
      have hmono : limbSum (aLimbs m0 (p + 2)) (i + 1) ≤ limbSum (aLimbs m0 (p + 2)) (p + 2) := by
        rw [← lsum_radix, ← lsum_radix]
        exact SquareMath.lsum_mono _ _ (by omega)
      obtain ⟨U, hU⟩ : ∃ U, limbSum (aLimbs m0 (p + 2)) (p + 2) =
          limbSum (aLimbs m0 (p + 2)) (i + 1) + U := ⟨_, (Nat.add_sub_of_le hmono).symm⟩
      have hX : SquareMath.rowX (2 ^ 255) (p + 2) (aLimbs m0 (p + 2)) i =
          aLimbs m0 (p + 2) i * (aLimbs m0 (p + 2) i + SquareMath.tbm (2 ^ 255) (aLimbs m0 (p + 2)) i) *
              Limbs.radix ^ i +
            SquareMath.a2 (2 ^ 255) (aLimbs m0 (p + 2)) i * U := by
        unfold SquareMath.rowX
        rw [two_half_radix, lsum_radix, lsum_radix, hU, Nat.add_sub_cancel_left]
      -- clear the common `b2 · A_{i+1}`
      rw [hU] at hrow
      set T' := tValue (sqRowsMem m0 (p + 2) (i + 1)) (p + 2) with hT'
      set T := tValue (sqRowsMem m0 (p + 2) i) (p + 2) with hT
      set D := aLimbs m0 (p + 2) i * (aLimbs m0 (p + 2) i +
        SquareMath.tbm (2 ^ 255) (aLimbs m0 (p + 2)) i) with hD
      set b2 := SquareMath.a2 (2 ^ 255) (aLimbs m0 (p + 2)) i with hb2def
      set mu := (rowMu (sqL1 (sqRowsMem m0 (p + 2) i) (p + 2) i
        (sqTb (sqRowsMem m0 (p + 2) i) (p + 2) i)).memory (p + 2)).toNat with hmu
      set L := limbSum (aLimbs m0 (p + 2)) (i + 1) with hL
      have hrow' : T' * Limbs.radix = T + D * Limbs.radix ^ i + b2 * U + mu * mm := by
        have e : T' * Limbs.radix + b2 * L = (T + D * Limbs.radix ^ i + b2 * U + mu * mm) + b2 * L := by
          rw [hrow]; ring
        exact Nat.add_right_cancel e
      have hmu_lt : mu < Limbs.radix := word_lt_size _
      refine ⟨Q + mu * Limbs.radix ^ i, ?_, ?_⟩
      · have h1 : mu * Limbs.radix ^ i ≤ (Limbs.radix - 1) * Limbs.radix ^ i :=
          Nat.mul_le_mul_right _ (by omega)
        have h2 : (Limbs.radix - 1) * Limbs.radix ^ i + Limbs.radix ^ i = Limbs.radix ^ (i + 1) := by
          rw [pow_succ Limbs.radix i]
          have hr : 1 ≤ Limbs.radix := Limbs.radix_pos
          calc (Limbs.radix - 1) * Limbs.radix ^ i + Limbs.radix ^ i
              = (Limbs.radix - 1 + 1) * Limbs.radix ^ i := by ring
            _ = Limbs.radix ^ i * Limbs.radix := by rw [Nat.sub_add_cancel hr, Nat.mul_comm]
        omega
      · have hstep : SquareMath.lsum Limbs.radix
            (SquareMath.rowX (2 ^ 255) (p + 2) (aLimbs m0 (p + 2))) (i + 1) =
            SquareMath.lsum Limbs.radix (SquareMath.rowX (2 ^ 255) (p + 2) (aLimbs m0 (p + 2))) i +
              SquareMath.rowX (2 ^ 255) (p + 2) (aLimbs m0 (p + 2)) i * Limbs.radix ^ i := rfl
        rw [hstep, hX, pow_succ Limbs.radix i]
        calc T' * (Limbs.radix ^ i * Limbs.radix)
            = (T' * Limbs.radix) * Limbs.radix ^ i := by ring
          _ = (T + D * Limbs.radix ^ i + b2 * U + mu * mm) * Limbs.radix ^ i := by rw [hrow']
          _ = T * Limbs.radix ^ i + (D * Limbs.radix ^ i + b2 * U) * Limbs.radix ^ i +
                mu * Limbs.radix ^ i * mm := by ring
          _ = (SquareMath.lsum Limbs.radix (SquareMath.rowX (2 ^ 255) (p + 2) (aLimbs m0 (p + 2))) i +
                Q * mm) + (D * Limbs.radix ^ i + b2 * U) * Limbs.radix ^ i +
                mu * Limbs.radix ^ i * mm := by rw [hinv]
          _ = _ := by ring

/-- **The square rows compute `a² + Q·m`**: after all `n` rows,
`t · rad^n = a · a + Q · m` and `t < 2 m`. -/
theorem sqRows_final (m0 : ByteArray) (p a mm : Nat) (hn32 : p + 2 ≤ 32)
    (ha : Model.FastRepresents m0 2048 (p + 2) a)
    (hm : Model.FastRepresents m0 0 (p + 2) mm)
    (hminv : ((MachineState.readWord m0 (32 * (p + 2) - 32)).toNat *
        (MachineState.readWord m0 9376).toNat + 1) % 2 ^ 256 = 0)
    (hz : tValue m0 (p + 2) = 0) (ham : a < mm) :
    ∃ Q, tValue (sqRowsMem m0 (p + 2) (p + 2)) (p + 2) * Limbs.radix ^ (p + 2) = a * a + Q * mm ∧
      tValue (sqRowsMem m0 (p + 2) (p + 2)) (p + 2) < 2 * mm := by
  obtain ⟨Q, hQ, hinv⟩ := sqRows_invariant m0 p mm hn32 hm hminv hz (p + 2) le_rfl
  have hlimb : ∀ k, aLimbs m0 (p + 2) k < 2 * 2 ^ 255 := by
    intro k
    rw [two_half_radix]
    exact word_lt_size _
  have hsq := SquareMath.square_identity (h := 2 ^ 255) (by norm_num) (aLimbs m0 (p + 2)) hlimb (p + 2)
  rw [two_half_radix] at hsq
  have hA : limbSum (aLimbs m0 (p + 2)) (p + 2) = a := limbSum_fastRepresents ha
  rw [hsq, lsum_radix, hA, sq] at hinv
  refine ⟨Q, hinv, ?_⟩
  have hmlt : mm < Limbs.radix ^ (p + 2) := hm.1
  have hmpos : 0 < mm := by omega
  have h1 : a * a < mm * mm := Nat.mul_self_lt_mul_self ham
  have h2 : mm * mm ≤ mm * Limbs.radix ^ (p + 2) := Nat.mul_le_mul_left _ (le_of_lt hmlt)
  have h3 : Q * mm < Limbs.radix ^ (p + 2) * mm := Nat.mul_lt_mul_of_pos_right hQ hmpos
  by_contra hcon
  have hge : 2 * mm * Limbs.radix ^ (p + 2) ≤
      tValue (sqRowsMem m0 (p + 2) (p + 2)) (p + 2) * Limbs.radix ^ (p + 2) :=
    Nat.mul_le_mul_right _ (Nat.le_of_not_lt hcon)
  have h4 : Limbs.radix ^ (p + 2) * mm = mm * Limbs.radix ^ (p + 2) := Nat.mul_comm _ _
  have h5 : 2 * mm * Limbs.radix ^ (p + 2) = mm * Limbs.radix ^ (p + 2) + mm * Limbs.radix ^ (p + 2) := by
    ring
  omega

/-- The top limb of the final square accumulator is at most one. -/
theorem sqRows_tn_le_one (m0 : ByteArray) (p a mm : Nat) (hn32 : p + 2 ≤ 32)
    (ha : Model.FastRepresents m0 2048 (p + 2) a)
    (hm : Model.FastRepresents m0 0 (p + 2) mm)
    (hminv : ((MachineState.readWord m0 (32 * (p + 2) - 32)).toNat *
        (MachineState.readWord m0 9376).toNat + 1) % 2 ^ 256 = 0)
    (hz : tValue m0 (p + 2) = 0) (ham : a < mm) :
    (MachineState.readWord (sqRowsMem m0 (p + 2) (p + 2)) 8224).toNat ≤ 1 := by
  obtain ⟨-, -, hlt⟩ := sqRows_final m0 p a mm hn32 ha hm hminv hz ham
  simp only [tValue] at hlt
  have hmlt : mm < Limbs.radix ^ (p + 2) := hm.1
  by_contra hcon
  have hge : 2 ≤ (MachineState.readWord (sqRowsMem m0 (p + 2) (p + 2)) 8224).toNat := by omega
  have hmul : 2 * Limbs.radix ^ (p + 2) ≤
      (MachineState.readWord (sqRowsMem m0 (p + 2) (p + 2)) 8224).toNat * Limbs.radix ^ (p + 2) :=
    Nat.mul_le_mul_right _ hge
  omega

/-- The square rows followed by `CSUB` leave `montMul m R a a` at `pdst`. -/
theorem sqRows_represents (m0 : ByteArray) (p a mm pdst : Nat) (hn32 : p + 2 ≤ 32)
    (ha : Model.FastRepresents m0 2048 (p + 2) a)
    (hm : Model.FastRepresents m0 0 (p + 2) mm)
    (hodd : mm % 2 = 1) (ham : a < mm)
    (hminv : ((MachineState.readWord m0 (32 * (p + 2) - 32)).toNat *
        (MachineState.readWord m0 9376).toNat + 1) % 2 ^ 256 = 0)
    (hz : tValue m0 (p + 2) = 0) :
    Model.FastRepresents (Csub.csResultMemory (sqRowsMem m0 (p + 2) (p + 2)) (p + 2) pdst)
      pdst (p + 2) (Model.montMul mm (Limbs.radix ^ (p + 2)) a a) := by
  have hmpos : 0 < mm := by omega
  obtain ⟨Q, hinv, hlt⟩ := sqRows_final m0 p a mm hn32 ha hm hminv hz ham
  have htn1 := sqRows_tn_le_one m0 p a mm hn32 ha hm hminv hz ham
  have hcop : Nat.Coprime (Limbs.radix ^ (p + 2)) mm := Model.coprime_radix_pow_of_odd hodd (p + 2)
  have hval : Model.montMul mm (Limbs.radix ^ (p + 2)) a a =
      tValue (sqRowsMem m0 (p + 2) (p + 2)) (p + 2) % mm :=
    Model.montMul_eq_mod_of_mul_eq hmpos hcop hinv
  have hmR := fastRepresents_sqRowsMem m0 (p + 2) (p + 2) 0 (p + 2) mm hn32 le_rfl (by omega) hm
  rw [hval]
  simp only [tValue] at hlt ⊢
  exact Csub.csub_correct (sqRowsMem m0 (p + 2) (p + 2)) (p + 2)
    (Csub.lowValue (sqRowsMem m0 (p + 2) (p + 2)) 8256 (p + 2) (p + 2)) mm
    (MachineState.readWord (sqRowsMem m0 (p + 2) (p + 2)) 8224).toNat
    pdst (by omega) hn32
    (Csub.fastRepresents_lowValue (sqRowsMem m0 (p + 2) (p + 2)) 8256 (p + 2))
    hmR rfl htn1 hmpos hlt

end Challenge.Modexp.Submission.Proofs.Fast.SquareModel
