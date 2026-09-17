import Challenge.Modexp.Submission.Proofs.Fast.ShiftProducerCore
import Challenge.Modexp.Submission.Proofs.Fast.Monpro
import Challenge.Modexp.Submission.Proofs.Fast.FullBaseLogic
import Challenge.Modexp.Submission.Proofs.Fast.Exp
import Challenge.Modexp.Submission.Proofs.Fast.RetainedTNormalizer
import Challenge.Modexp.Submission.Proofs.Fast.Setup
import Challenge.Modexp.Submission.Proofs.Fast.QHatBound
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Zify

set_option warningAsError false
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-!
# Memory and arithmetic model of the shift-reduce base conversion

The appended routine turns the raw `n`-limb base `b` into its Montgomery
residue `b * radix ^ n mod m` by `n` steps `r ↦ r * radix mod m`.  Each step
forms `u = r * radix` in the CIOS `t` area, guesses a quotient word `q`, runs
one CIOS-style limb pass accumulating `q * (radix ^ n - m)` (so the result is
`u - q * m + q * radix ^ n`), removes the `q * radix ^ n` term from the top
limb, repairs the sign and the top limb with `± m` rounds, and finally calls
`CSUB`.  Only the value relations matter here: the quotient guess is kept
abstract and the repair loops make the result `u mod m` for every guess.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.Shift

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Fast

/-! ## Address constants -/

/-- `n`-limb block holding `radix ^ n - m` (the former `CC` block). -/
def NEG : Nat := 1280
/-- Per-modulus words of the quotient estimator (the former `RR` block). -/
def PRE_L : Nat := 1536
def PRE_DODD : Nat := 1568
def PRE_X : Nat := 1600
def PRE_BMOD : Nat := 1632
def PRE_DINV : Nat := 1664

/-! ## Phase 1: the raw base into `ACC` and `TS` -/

/-- `ACC := base`, `TS := base`, `TN := 0`. -/
def hitMem (mem input : ByteArray) (n : Nat) : ByteArray :=
  ShiftProducerCanonical.hitMemory mem input n

/-- Memory and carry after `j` limbs of the negation loop. -/
def negStep (mem : ByteArray) (n : Nat) : Nat → Csub.LimbState
  | 0 => ⟨mem, UInt256.ofNat 1⟩
  | j + 1 =>
      let prev := negStep mem n j
      let md := MachineState.readWord prev.memory (32 * (n - 1 - j))
      let sum := prev.flag + UInt256.lnot md
      { memory := MachineState.writeBytes prev.memory
          (Data.Bytes.natToBytesPadded sum.toNat 32) (NEG + 32 * (n - 1 - j))
        flag := UInt256.lt sum prev.flag }

/-! ## Phase 3: the per-modulus estimator words -/

/-- One Newton step `x ↦ (2 - d * x) * x`, as the bytecode computes it. -/
def newtonW (d x : UInt256) : UInt256 := (UInt256.ofNat 2 - d * x) * x

def newton4W (d : UInt256) : UInt256 :=
  newtonW d (newtonW d (newtonW d
    (UInt256.xor (UInt256.ofNat 2) (UInt256.ofNat 3 * d))))

def newton8W (d : UInt256) : UInt256 :=
  newtonW d (newtonW d (newtonW d (newton4W d)))

def preL (d : UInt256) : UInt256 := UInt256.land d (UInt256.ofNat 0 - d)
def preDodd (d : UInt256) : UInt256 := d / preL d
def preX (d : UInt256) : UInt256 := UInt256.ofNat 1 + (UInt256.ofNat 0 - preL d) / preL d
def preBmod (d : UInt256) : UInt256 := (UInt256.ofNat 0 - preDodd d) % preDodd d
def preDinv (d : UInt256) : UInt256 := newton8W (preDodd d)

/-- The five stores, in program order, from the top limb `d` of the modulus. -/
def preMemOf (mem : ByteArray) (d : UInt256) : ByteArray :=
  Exp.storeWord (Exp.storeWord (Exp.storeWord (Exp.storeWord (Exp.storeWord mem
    PRE_L (preL d)) PRE_DODD (preDodd d)) PRE_X (preX d)) PRE_BMOD (preBmod d))
    PRE_DINV (preDinv d)

def preMem (mem : ByteArray) : ByteArray := preMemOf mem (MachineState.readWord mem 0)

/-! ## Phase 4: one shift step -/

/-- `u := r * radix` in the `t` area: `MCOPY(TN, BASE, s32)` then `t[0] := 0`. -/
def uMem (mem : ByteArray) (n : Nat) : ByteArray :=
  Exp.storeWord (Exp.mcopyMem mem 2080 2112 (32 * n)) (2080 + 32 * n) (UInt256.ofNat 0)

/-- The quotient guess, exactly as the `ESTIMATE` block computes it.  Its value
is irrelevant to correctness. -/
def qhatOf (mem : ByteArray) : UInt256 :=
  let utop := MachineState.readWord mem 2080
  let L := MachineState.readWord mem PRE_L
  let hi := utop / L
  let X := MachineState.readWord mem PRE_X
  let xr := X * utop
  let unext := MachineState.readWord mem 2112
  let uL := unext / L
  let lo := uL + xr
  let dodd := MachineState.readWord mem PRE_DODD
  let bmod := MachineState.readWord mem PRE_BMOD
  let mm := UInt256.mulMod hi bmod dodd
  let rho := UInt256.addMod mm lo dodd
  let diff := lo - rho
  let dinv := MachineState.readWord mem PRE_DINV
  let q := dinv * diff
  -- Saturate a quotient that would wrap at the word radix. The generic
  -- correction proof below accepts every UInt256 quotient, including this one.
  let overflow := UInt256.isZero (UInt256.lt hi dodd)
  -- Record-style refinement: decrement only when
  -- `(q >> 128) * (N1 >> 128) > r̂`, which implies `q * N1 > r̂ * radix`.
  UInt256.lor (UInt256.ofNat 0 - overflow)
    (q - UInt256.gt
      (UInt256.shiftRight q (UInt256.ofNat 128) *
        UInt256.shiftRight (MachineState.readWord mem 32) (UInt256.ofNat 128))
      (unext - MachineState.readWord mem 0 * q))

/-- The limb pass `t += q * NEG` is exactly a CIOS first loop with `a = NEG`. -/
def macOf (mem : ByteArray) (n : Nat) (q : UInt256) : Monpro.MacState :=
  Monpro.l1Step mem q NEG n n

/-! ### The middle block -/

def wN (mem : ByteArray) (c : UInt256) : UInt256 := c + MachineState.readWord mem 2080
def cwOf (mem : ByteArray) (c : UInt256) : UInt256 := UInt256.lt (wN mem c) c
def tnOf (mem : ByteArray) (c q : UInt256) : UInt256 := wN mem c - q
def bwOf (mem : ByteArray) (c q : UInt256) : UInt256 := UInt256.lt (wN mem c) q
def negOf (mem : ByteArray) (c q : UInt256) : UInt256 := UInt256.gt (bwOf mem c q) (cwOf mem c)
def midMem (mem : ByteArray) (c q : UInt256) : ByteArray :=
  Exp.storeWord mem 2080 (tnOf mem c q)

/-! ### The repair rounds -/

/-- One limb of `t += m`, in place, least significant limb first. -/
def addStep (mem : ByteArray) (n : Nat) : Nat → Csub.LimbState
  | 0 => ⟨mem, UInt256.ofNat 0⟩
  | j + 1 =>
      let prev := addStep mem n j
      let t := MachineState.readWord prev.memory (2112 + 32 * (n - 1 - j))
      let md := MachineState.readWord prev.memory (32 * (n - 1 - j))
      let s1 := t + md
      let c1 := UInt256.gt t s1
      let s2 := prev.flag + s1
      let c2 := UInt256.gt prev.flag s2
      { memory := MachineState.writeBytes prev.memory
          (Data.Bytes.natToBytesPadded s2.toNat 32) (2112 + 32 * (n - 1 - j))
        flag := UInt256.lor c2 c1 }

/-- The carry into `TN` after a full add pass. -/
def addCarry (mem : ByteArray) (n : Nat) : UInt256 := (addStep mem n n).flag

/-- Memory after one whole add round: the pass and `TN += carry`. -/
def addRoundMem (mem : ByteArray) (n : Nat) : ByteArray :=
  Exp.storeWord (addStep mem n n).memory 2080
    (addCarry mem n + MachineState.readWord (addStep mem n n).memory 2080)

/-- The carry out of `TN` in that round: the round is the last one iff it is `1`. -/
def addOut (mem : ByteArray) (n : Nat) : UInt256 :=
  UInt256.lt (addCarry mem n + MachineState.readWord (addStep mem n n).memory 2080)
    (addCarry mem n)

def addRounds (mem : ByteArray) (n : Nat) : Nat → ByteArray
  | 0 => mem
  | k + 1 => addRoundMem (addRounds mem n k) n

/-- One limb of `t -= m`, in place, least significant limb first. -/
def subStep (mem : ByteArray) (n : Nat) : Nat → Csub.LimbState
  | 0 => ⟨mem, UInt256.ofNat 0⟩
  | j + 1 =>
      let prev := subStep mem n j
      let t := MachineState.readWord prev.memory (2112 + 32 * (n - 1 - j))
      let md := MachineState.readWord prev.memory (32 * (n - 1 - j))
      let b1 := UInt256.gt md t
      let d1 := t - md
      let b2 := UInt256.lt d1 prev.flag
      let d2 := d1 - prev.flag
      { memory := MachineState.writeBytes prev.memory
          (Data.Bytes.natToBytesPadded d2.toNat 32) (2112 + 32 * (n - 1 - j))
        flag := UInt256.lor b2 b1 }

def subBorrow (mem : ByteArray) (n : Nat) : UInt256 := (subStep mem n n).flag

/-- Memory after one whole subtract round: the pass and `TN -= borrow`. -/
def subRoundMem (mem : ByteArray) (n : Nat) : ByteArray :=
  Exp.storeWord (subStep mem n n).memory 2080
    (MachineState.readWord (subStep mem n n).memory 2080 - subBorrow mem n)

def subRounds (mem : ByteArray) (n : Nat) : Nat → ByteArray
  | 0 => mem
  | k + 1 => subRoundMem (subRounds mem n k) n

/-! ### Round counts, as functions of the `t` value -/

/-- The `(n+1)`-limb value held by `TN` and `TS`. -/
def tv (mem : ByteArray) (n : Nat) : Nat := Monpro.tValue mem n

/-- Number of add rounds: none when the sign flag is clear, otherwise the
least `k ≥ 1` with `tv + k * m ≥ radix ^ (n + 1)`. -/
def addCount (mem : ByteArray) (n mm : Nat) (neg : UInt256) : Nat :=
  if neg.toNat = 0 then 0 else (Limbs.radix ^ (n + 1) - tv mem n + mm - 1) / mm

/-- Number of subtract rounds: the least `k` with `tv - k * m < radix ^ n`. -/
def subCount (mem : ByteArray) (n mm : Nat) : Nat :=
  if tv mem n < Limbs.radix ^ n then 0 else (tv mem n - Limbs.radix ^ n) / mm + 1

/-- Memory after the repair rounds, from the middle block's output. -/
def fixMem (mem : ByteArray) (n mm : Nat) (neg : UInt256) : ByteArray :=
  subRounds (addRounds mem n (addCount mem n mm neg)) n
    (subCount (addRounds mem n (addCount mem n mm neg)) n mm)

/-- The whole step, from the memory at `SHIFT_LOOP` to the memory back at it. -/
def stepMem (mem : ByteArray) (n mm : Nat) : ByteArray :=
  let um := uMem mem n
  let q := qhatOf um
  let mac := macOf um n q
  let mid := midMem mac.memory mac.carry q
  let neg := negOf mac.memory mac.carry q
  fixMem mid n mm neg

def stepMems (mem : ByteArray) (n mm : Nat) : Nat → ByteArray
  | 0 => mem
  | k + 1 => stepMem (stepMems mem n mm k) n mm


/-! ## Word-level helpers -/

theorem lnot_toNat (a : UInt256) : (UInt256.lnot a).toNat = 2 ^ 256 - 1 - a.toNat := by
  have ha : a.toNat < 2 ^ 256 := a.val.isLt
  unfold UInt256.lnot UInt256.size
  rw [Challenge.EvmProof.Word.word_toNat_ofNat]
  exact Nat.mod_eq_of_lt (by omega)

theorem gt_toNat (a b : UInt256) :
    (UInt256.gt a b).toNat = if b.toNat < a.toNat then 1 else 0 := by
  simp only [UInt256.gt, GT.gt]
  split <;> norm_num [EvmSemantics.UInt256.ofNat, EvmSemantics.UInt256.toNat,
    EvmSemantics.UInt256.size]

theorem radix_eq : Limbs.radix = 2 ^ 256 := rfl

/-- One word addition with its carry-out, tested against the first summand. -/
theorem add_carry_spec (a b : UInt256) :
    (a + b).toNat + (UInt256.lt (a + b) a).toNat * Limbs.radix = a.toNat + b.toNat ∧
      (UInt256.lt (a + b) a).toNat ≤ 1 := by
  have ha : a.toNat < 2 ^ 256 := a.val.isLt
  have hb : b.toNat < 2 ^ 256 := b.val.isLt
  rw [radix_eq, Challenge.EvmProof.Word.word_toNat_lt, Challenge.EvmProof.Word.word_toNat_add]
  by_cases h : a.toNat + b.toNat < 2 ^ 256
  · rw [Nat.mod_eq_of_lt h]
    constructor
    · rw [if_neg (by omega)]; omega
    · split <;> omega
  · have hmod : (a.toNat + b.toNat) % 2 ^ 256 = a.toNat + b.toNat - 2 ^ 256 := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [hmod]
    constructor
    · rw [if_pos (by omega)]; omega
    · split <;> omega

/-- One word addition with its carry-out, tested against the second summand. -/
theorem add_carry_spec' (a b : UInt256) :
    (a + b).toNat + (UInt256.lt (a + b) b).toNat * Limbs.radix = a.toNat + b.toNat ∧
      (UInt256.lt (a + b) b).toNat ≤ 1 := by
  have ha : a.toNat < 2 ^ 256 := a.val.isLt
  have hb : b.toNat < 2 ^ 256 := b.val.isLt
  rw [radix_eq, Challenge.EvmProof.Word.word_toNat_lt, Challenge.EvmProof.Word.word_toNat_add]
  by_cases h : a.toNat + b.toNat < 2 ^ 256
  · rw [Nat.mod_eq_of_lt h]
    constructor
    · rw [if_neg (by omega)]; omega
    · split <;> omega
  · have hmod : (a.toNat + b.toNat) % 2 ^ 256 = a.toNat + b.toNat - 2 ^ 256 := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [hmod]
    constructor
    · rw [if_pos (by omega)]; omega
    · split <;> omega

/-- One word subtraction with its borrow. -/
theorem sub_borrow_spec (a b : UInt256) :
    (a - b).toNat + b.toNat = a.toNat + (UInt256.lt a b).toNat * Limbs.radix ∧
      (UInt256.lt a b).toNat ≤ 1 := by
  have ha : a.toNat < 2 ^ 256 := a.val.isLt
  have hb : b.toNat < 2 ^ 256 := b.val.isLt
  rw [radix_eq, Challenge.EvmProof.Word.word_toNat_lt, Challenge.EvmProof.Word.word_toNat_sub_cond]
  constructor
  · split_ifs <;> omega
  · split <;> omega

/-- `tv` in terms of `TN` and the `TS` limbs. -/
theorem tv_def (mem : ByteArray) (n : Nat) :
    tv mem n = (MachineState.readWord mem 2080).toNat * Limbs.radix ^ n +
      Csub.lowValue mem 2112 n n := rfl

theorem tn_ne_zero_iff (mem : ByteArray) (n : Nat) :
    (MachineState.readWord mem 2080).toNat ≠ 0 ↔ Limbs.radix ^ n ≤ tv mem n := by
  rw [tv_def]
  have hlow := Csub.lowValue_lt mem 2112 n n
  constructor
  · intro h
    have : 1 ≤ (MachineState.readWord mem 2080).toNat := by omega
    nlinarith
  · intro h hz
    rw [hz] at h
    omega

theorem tn_zero_of_lt (mem : ByteArray) (n : Nat) (h : tv mem n < Limbs.radix ^ n) :
    (MachineState.readWord mem 2080).toNat = 0 := by
  by_contra hne
  have := (tn_ne_zero_iff mem n).1 hne
  omega

/-! ## The negation loop -/

theorem negStep_readWord_disjoint (mem : ByteArray) (n addr : Nat)
    (hdisj : addr + 32 ≤ NEG ∨ NEG + 32 * n ≤ addr) :
    ∀ j, j ≤ n → MachineState.readWord (negStep mem n j).memory addr =
      MachineState.readWord mem addr := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
      intro hj
      have hstep : MachineState.readWord (negStep mem n (j + 1)).memory addr =
          MachineState.readWord (negStep mem n j).memory addr := by
        simp only [negStep]
        exact Csub.readWord_write_disjoint _ _ _ _ (by unfold NEG at hdisj ⊢; omega)
      rw [hstep, ih (by omega)]

theorem negStep_lowValue_stable (mem : ByteArray) (n j : Nat) (hj : j < n) :
    Csub.lowValue (negStep mem n (j + 1)).memory NEG n j =
      Csub.lowValue (negStep mem n j).memory NEG n j := by
  apply Csub.lowValue_congr
  intro k hk
  simp only [negStep]
  exact Csub.readWord_write_disjoint _ _ _ _ (by omega)

theorem negStep_readWord_new (mem : ByteArray) (n j : Nat) :
    MachineState.readWord (negStep mem n (j + 1)).memory (NEG + 32 * (n - 1 - j)) =
      (negStep mem n j).flag +
        UInt256.lnot (MachineState.readWord (negStep mem n j).memory (32 * (n - 1 - j))) := by
  simp only [negStep]
  exact Challenge.EvmProof.Memory.readWord_writeWord _ _ _

theorem negStep_flag_succ (mem : ByteArray) (n j : Nat) :
    (negStep mem n (j + 1)).flag =
      UInt256.lt ((negStep mem n j).flag +
        UInt256.lnot (MachineState.readWord (negStep mem n j).memory (32 * (n - 1 - j))))
        (negStep mem n j).flag := by
  simp only [negStep]

private theorem neg_algebra {L S F M x c P R : Nat}
    (hspec : S + F * R + x + 1 = c + R) (hinv : L + c * P + M = P) :
    L + S * P + F * (P * R) + (M + x * P) = P * R := by
  have h : (S + F * R + x + 1) * P = (c + R) * P := by rw [hspec]
  nlinarith [h, hinv]

/-- `I_NEG(j)`: the low `j` limbs of `NEG` plus the carry complement the low
`j` limbs of `m` to `radix ^ j`. -/
theorem negStep_invariant (mem : ByteArray) (n : Nat) (hn32 : n ≤ 8) :
    ∀ j, j ≤ n →
      Csub.lowValue (negStep mem n j).memory NEG n j +
          (negStep mem n j).flag.toNat * Limbs.radix ^ j +
          Csub.lowValue mem 0 n j = Limbs.radix ^ j ∧
        (negStep mem n j).flag.toNat ≤ 1 := by
  intro j
  induction j with
  | zero =>
      intro _
      simp [negStep]
  | succ j ih =>
      intro hj
      obtain ⟨ihEq, ihLe⟩ := ih (by omega)
      have hxm : MachineState.readWord (negStep mem n j).memory (32 * (n - 1 - j)) =
          MachineState.readWord mem (32 * (n - 1 - j)) :=
        negStep_readWord_disjoint mem n _ (Or.inl (by unfold NEG; omega)) j (by omega)
      have hx : (MachineState.readWord mem (32 * (n - 1 - j))).toNat < 2 ^ 256 :=
        (MachineState.readWord mem (32 * (n - 1 - j))).val.isLt
      have hspec := add_carry_spec (negStep mem n j).flag
        (UInt256.lnot (MachineState.readWord mem (32 * (n - 1 - j))))
      rw [lnot_toNat] at hspec
      rw [Csub.lowValue_succ (negStep mem n (j + 1)).memory NEG n j,
        negStep_lowValue_stable mem n j (by omega),
        negStep_readWord_new, negStep_flag_succ, hxm,
        Csub.lowValue_succ mem 0 n j, pow_succ]
      simp only [Nat.zero_add]
      refine ⟨?_, hspec.2⟩
      have hspec' : ((negStep mem n j).flag +
          UInt256.lnot (MachineState.readWord mem (32 * (n - 1 - j)))).toNat +
          (UInt256.lt ((negStep mem n j).flag +
            UInt256.lnot (MachineState.readWord mem (32 * (n - 1 - j))))
            (negStep mem n j).flag).toNat * Limbs.radix +
          (MachineState.readWord mem (32 * (n - 1 - j))).toNat + 1 =
          (negStep mem n j).flag.toNat + Limbs.radix := by
        rw [radix_eq] at hspec ⊢; omega
      exact neg_algebra hspec' ihEq

theorem neg_represents (mem : ByteArray) (n mm : Nat) (hn : 1 ≤ n) (hn32 : n ≤ 8)
    (hmpos : 0 < mm) (hmod : Model.FastRepresents mem 0 n mm) :
    Model.FastRepresents (negStep mem n n).memory NEG n (Limbs.radix ^ n - mm) := by
  obtain ⟨hinv, hle⟩ := negStep_invariant mem n hn32 n le_rfl
  have hM : Csub.lowValue mem 0 n n = mm := by
    rw [Csub.lowValue_full]; exact Model.value_of_fastRepresents hmod
  rw [hM] at hinv
  have hlt := Csub.lowValue_lt (negStep mem n n).memory NEG n n
  have hflag : (negStep mem n n).flag.toNat = 0 := by
    by_contra hne
    have h1 : (negStep mem n n).flag.toNat = 1 := by omega
    rw [h1] at hinv
    omega
  rw [hflag] at hinv
  have hval : Csub.lowValue (negStep mem n n).memory NEG n n = Limbs.radix ^ n - mm := by
    omega
  rw [← hval]
  exact Csub.fastRepresents_lowValue _ _ _

theorem fastRepresents_negStep (mem : ByteArray) (n ptr cnt v : Nat)
    (hdisj : ptr + 32 * cnt ≤ NEG ∨ NEG + 32 * n ≤ ptr)
    (hrep : Model.FastRepresents mem ptr cnt v) (j : Nat) (hj : j ≤ n) :
    Model.FastRepresents (negStep mem n j).memory ptr cnt v := by
  refine (Model.fastRepresents_congr ?_ v).2 hrep
  intro i hi
  exact negStep_readWord_disjoint mem n _ (by omega) j hj

/-! ## The estimator words -/

theorem preMemOf_readWord_disjoint (mem : ByteArray) (d : UInt256) (addr : Nat)
    (hdisj : addr + 32 ≤ PRE_L ∨ PRE_DINV + 32 ≤ addr) :
    MachineState.readWord (preMemOf mem d) addr = MachineState.readWord mem addr := by
  unfold PRE_L PRE_DINV at hdisj
  unfold preMemOf PRE_L PRE_DODD PRE_X PRE_BMOD PRE_DINV Exp.storeWord
  rw [Csub.readWord_write_disjoint _ _ _ _ (by omega),
    Csub.readWord_write_disjoint _ _ _ _ (by omega),
    Csub.readWord_write_disjoint _ _ _ _ (by omega),
    Csub.readWord_write_disjoint _ _ _ _ (by omega),
    Csub.readWord_write_disjoint _ _ _ _ (by omega)]

theorem fastRepresents_preMemOf (mem : ByteArray) (d : UInt256) (ptr cnt v : Nat)
    (hdisj : ptr + 32 * cnt ≤ PRE_L ∨ PRE_DINV + 32 ≤ ptr)
    (hrep : Model.FastRepresents mem ptr cnt v) :
    Model.FastRepresents (preMemOf mem d) ptr cnt v := by
  refine (Model.fastRepresents_congr ?_ v).2 hrep
  intro i hi
  exact preMemOf_readWord_disjoint mem d _ (by unfold PRE_L PRE_DINV at hdisj ⊢; omega)

/-! ## `u = r * radix` -/

theorem uMem_readWord_disjoint (mem : ByteArray) (n addr : Nat)
    (hdisj : addr + 32 ≤ 2080 ∨ 2112 + 32 * n ≤ addr) :
    MachineState.readWord (uMem mem n) addr = MachineState.readWord mem addr := by
  unfold uMem Exp.storeWord Exp.mcopyMem
  rw [Csub.readWord_write_disjoint _ _ _ _ (by omega)]
  rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint _ _ _ _
    (by rw [Challenge.EvmProof.Memory.readPadded_size]; omega)]

/-- The word of `u` at `TN`: the top limb of `r`. -/
theorem uMem_readWord_tn (mem : ByteArray) (n : Nat) (hn : 1 ≤ n) :
    MachineState.readWord (uMem mem n) 2080 = MachineState.readWord mem 2112 := by
  unfold uMem Exp.storeWord Exp.mcopyMem
  rw [Csub.readWord_write_disjoint _ _ _ _ (by omega)]
  have h := Csub.readWord_mcopy mem 2112 2080 (32 * n) 0 (by omega)
  simpa using h

/-- The limbs of `u` inside `TS`: limb `j` of `u` is limb `j - 1` of `r`, and
limb `0` is zero. -/
theorem uMem_readWord_limb (mem : ByteArray) (n k : Nat) (hn : 1 ≤ n) (hk : k < n) :
    MachineState.readWord (uMem mem n) (2112 + 32 * (n - 1 - k)) =
      if k = 0 then UInt256.ofNat 0
      else MachineState.readWord mem (2112 + 32 * (n - 1 - (k - 1))) := by
  unfold uMem Exp.storeWord Exp.mcopyMem
  by_cases hk0 : k = 0
  · subst hk0
    rw [if_pos rfl]
    have h : 2112 + 32 * (n - 1 - 0) = 2080 + 32 * n := by omega
    rw [h]
    exact Challenge.EvmProof.Memory.readWord_writeWord _ _ _
  · rw [if_neg hk0]
    rw [Csub.readWord_write_disjoint _ _ _ _ (by omega)]
    have h : 2112 + 32 * (n - 1 - k) = 2080 + 32 * (n - k) := by omega
    rw [h]
    have hm := Csub.readWord_mcopy mem 2112 2080 (32 * n) (n - k) (by omega)
    rw [hm]
    congr 1
    omega

/-- The `TS` limbs of `u` are the limbs of `r` shifted up by one, so their value
below limb `j + 1` is `radix * (r mod radix ^ j)`. -/
theorem uMem_lowValue (mem : ByteArray) (n r : Nat) (hn : 1 ≤ n)
    (hrep : Model.FastRepresents mem 2112 n r) :
    ∀ j, j + 1 ≤ n →
      Csub.lowValue (uMem mem n) 2112 n (j + 1) = Limbs.radix * (r % Limbs.radix ^ j) := by
  intro j
  induction j with
  | zero =>
      intro _
      rw [Csub.lowValue_succ, Csub.lowValue_zero, uMem_readWord_limb mem n 0 hn (by omega),
        if_pos rfl]
      simp [Nat.mod_one]
  | succ j ih =>
      intro hj
      rw [Csub.lowValue_succ, ih (by omega), uMem_readWord_limb mem n (j + 1) hn (by omega),
        if_neg (by omega)]
      have hlimb := Model.readLimb_of_fastRepresents hrep (k := j) (by omega)
      rw [show j + 1 - 1 = j from rfl, hlimb]
      rw [pow_succ, Nat.mod_mul]
      ring

theorem uMem_tv (mem : ByteArray) (n r : Nat) (hn : 2 ≤ n) (hn32 : n ≤ 8)
    (hrep : Model.FastRepresents mem 2112 n r) :
    tv (uMem mem n) n = r * Limbs.radix := by
  rw [tv_def, uMem_readWord_tn mem n (by omega)]
  have hlow := uMem_lowValue mem n r (by omega) hrep (n - 1) (by omega)
  rw [show n - 1 + 1 = n from by omega] at hlow
  rw [hlow]
  have htop := Model.readWord_of_fastRepresents hrep (j := 0) (by omega)
  simp only [Nat.mul_zero, Nat.add_zero, Nat.sub_zero] at htop
  rw [htop]
  have hr : r < Limbs.radix ^ n := Model.fastRepresents_lt hrep
  have hdiv : r / Limbs.radix ^ (n - 1) < Limbs.radix := by
    rw [Nat.div_lt_iff_lt_mul (Nat.pow_pos Limbs.radix_pos)]
    calc r < Limbs.radix ^ n := hr
      _ = Limbs.radix ^ (n - 1) * Limbs.radix := by rw [← pow_succ]; congr 1; omega
      _ = Limbs.radix * Limbs.radix ^ (n - 1) := by ring
  rw [Nat.mod_eq_of_lt hdiv]
  have hsplit := Nat.div_add_mod r (Limbs.radix ^ (n - 1))
  have hpow : Limbs.radix ^ n = Limbs.radix ^ (n - 1) * Limbs.radix := by
    rw [← pow_succ]; congr 1; omega
  rw [hpow]
  nlinarith [hsplit]

/-! ## The limb pass -/

theorem mac_value (mem : ByteArray) (n : Nat) (q : UInt256) (a : Nat) (hn32 : n ≤ 8)
    (hneg : Model.FastRepresents mem NEG n a) :
    Csub.lowValue (macOf mem n q).memory 2112 n n +
        (macOf mem n q).carry.toNat * Limbs.radix ^ n =
      Csub.lowValue mem 2112 n n + q.toNat * a := by
  have h := Monpro.l1_row mem q NEG n (Csub.lowValue mem 2112 n n) a (by omega)
    (by unfold NEG; omega) hneg (Csub.fastRepresents_lowValue mem 2112 n)
  have hsum : Monpro.limbSum (fun k => (Monpro.l1Val mem q NEG n k).toNat) n =
      Csub.lowValue (Monpro.l1Step mem q NEG n n).memory 2112 n n := by
    rw [← Monpro.limbSum_eq_lowValue]
    apply Monpro.limbSum_congr
    intro k hk
    rw [show 2112 + 32 * (n - 1 - k) = Monpro.tAddr n k from rfl,
      Monpro.readWord_l1Step_val mem q NEG n k (by omega) hk (by unfold NEG; omega) n hk le_rfl]
  unfold macOf
  rw [← hsum]
  exact h

theorem l1Step_readWord_disjoint (mem : ByteArray) (bi : UInt256) (pa n addr : Nat)
    (hn : 1 ≤ n) (hdisj : addr + 32 ≤ 2112 ∨ 2112 + 32 * n ≤ addr) :
    ∀ j, MachineState.readWord (Monpro.l1Step mem bi pa n j).memory addr =
      MachineState.readWord mem addr := by
  intro j
  induction j with
  | zero => rfl
  | succ j ih =>
      simp only [Monpro.l1Step]
      rw [Csub.readWord_write_disjoint _ _ _ _ (by omega)]
      exact ih

theorem mac_readWord_disjoint (mem : ByteArray) (n addr : Nat) (q : UInt256)
    (hn : 1 ≤ n) (hdisj : addr + 32 ≤ 2112 ∨ 2112 + 32 * n ≤ addr) :
    MachineState.readWord (macOf mem n q).memory addr = MachineState.readWord mem addr :=
  l1Step_readWord_disjoint mem q NEG n addr hn hdisj n

/-- The middle block: the signed relation `u + neg * radix^(n+1) = q * m + t`. -/
theorem mid_relation (mem : ByteArray) (n mm : Nat) (q : UInt256) (u : Nat)
    (hn : 2 ≤ n) (hn32 : n ≤ 8) (hmm : mm < Limbs.radix ^ n)
    (hmod : Model.FastRepresents mem 0 n mm)
    (hneg : Model.FastRepresents mem NEG n (Limbs.radix ^ n - mm))
    (hu : tv mem n = u) (hulo : u < Limbs.radix ^ (n + 1)) :
    u + (negOf (macOf mem n q).memory (macOf mem n q).carry q).toNat * Limbs.radix ^ (n + 1) =
        q.toNat * mm + tv (midMem (macOf mem n q).memory (macOf mem n q).carry q) n ∧
      tv (midMem (macOf mem n q).memory (macOf mem n q).carry q) n < Limbs.radix ^ (n + 1) ∧
      (negOf (macOf mem n q).memory (macOf mem n q).carry q).toNat ≤ 1 := by
  have hmac := mac_value mem n q (Limbs.radix ^ n - mm) hn32 hneg
  have hTN : MachineState.readWord (macOf mem n q).memory 2080 =
      MachineState.readWord mem 2080 :=
    mac_readWord_disjoint mem n 2080 q (by omega) (Or.inl (by omega))
  have hW := add_carry_spec (macOf mem n q).carry (MachineState.readWord mem 2080)
  have hT := sub_borrow_spec ((macOf mem n q).carry + MachineState.readWord mem 2080) q
  have hlowMid : Csub.lowValue (midMem (macOf mem n q).memory (macOf mem n q).carry q)
      2112 n n = Csub.lowValue (macOf mem n q).memory 2112 n n := by
    apply Csub.lowValue_congr
    intro k hk
    unfold midMem Exp.storeWord
    exact Csub.readWord_write_disjoint _ _ _ _ (by omega)
  have htnMid : MachineState.readWord (midMem (macOf mem n q).memory (macOf mem n q).carry q)
      2080 = (macOf mem n q).carry + MachineState.readWord mem 2080 - q := by
    unfold midMem Exp.storeWord tnOf wN
    rw [Challenge.EvmProof.Memory.readWord_writeWord, hTN]
  have htv : tv (midMem (macOf mem n q).memory (macOf mem n q).carry q) n =
      ((macOf mem n q).carry + MachineState.readWord mem 2080 - q).toNat * Limbs.radix ^ n +
        Csub.lowValue (macOf mem n q).memory 2112 n n := by
    rw [tv_def, htnMid, hlowMid]
  have hu' : (MachineState.readWord mem 2080).toNat * Limbs.radix ^ n +
      Csub.lowValue mem 2112 n n = u := by rw [← hu, tv_def]
  have hnegv : (negOf (macOf mem n q).memory (macOf mem n q).carry q).toNat =
      if (UInt256.lt ((macOf mem n q).carry + MachineState.readWord mem 2080)
            (macOf mem n q).carry).toNat <
          (UInt256.lt ((macOf mem n q).carry + MachineState.readWord mem 2080) q).toNat
        then 1 else 0 := by
    unfold negOf bwOf cwOf wN
    rw [gt_toNat, hTN]
  have hTnlt : ((macOf mem n q).carry + MachineState.readWord mem 2080 - q).toNat <
      Limbs.radix := ((macOf mem n q).carry + MachineState.readWord mem 2080 - q).val.isLt
  have hlow'lt : Csub.lowValue (macOf mem n q).memory 2112 n n < Limbs.radix ^ n :=
    Csub.lowValue_lt _ _ _ _
  have hR' : Limbs.radix ^ (n + 1) = Limbs.radix ^ n * Limbs.radix := pow_succ _ _
  have hqa : q.toNat * (Limbs.radix ^ n - mm) + q.toNat * mm = q.toNat * Limbs.radix ^ n := by
    rw [← Nat.mul_add, Nat.sub_add_cancel (le_of_lt hmm)]
  have hW1 := hW.1
  have hT1 := hT.1
  have hcw1 := hW.2
  have hbw1 := hT.2
  -- the key identity: u + bw R' = t + q m + cw R'
  have hkey : u + (UInt256.lt ((macOf mem n q).carry + MachineState.readWord mem 2080)
        q).toNat * (Limbs.radix ^ n * Limbs.radix) =
      ((macOf mem n q).carry + MachineState.readWord mem 2080 - q).toNat * Limbs.radix ^ n +
        Csub.lowValue (macOf mem n q).memory 2112 n n + q.toNat * mm +
        (UInt256.lt ((macOf mem n q).carry + MachineState.readWord mem 2080)
          (macOf mem n q).carry).toNat * (Limbs.radix ^ n * Limbs.radix) := by
    zify at hu' hmac hW1 hT1 hqa ⊢
    linear_combination (-1 : ℤ) * hu' + (-1 : ℤ) * hmac +
      (-((Limbs.radix : ℤ) ^ n)) * hW1 + (-((Limbs.radix : ℤ) ^ n)) * hT1 + (-1 : ℤ) * hqa
  refine ⟨?_, ?_, ?_⟩
  · rw [htv, hR', hnegv]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hcw1 with h0 | h1 <;>
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hbw1 with g0 | g1
    · rw [h0, g0] at hkey ⊢; rw [if_neg (by decide)]; omega
    · rw [h0, g1] at hkey ⊢; rw [if_pos (by decide)]; omega
    · rw [h1, g0] at hkey
      exfalso
      rw [hR'] at hulo
      omega
    · rw [h1, g1] at hkey ⊢; rw [if_neg (by decide)]; omega
  · rw [htv, hR']
    have h1 : ((macOf mem n q).carry + MachineState.readWord mem 2080 - q).toNat *
        Limbs.radix ^ n + Csub.lowValue (macOf mem n q).memory 2112 n n <
        (((macOf mem n q).carry + MachineState.readWord mem 2080 - q).toNat + 1) *
          Limbs.radix ^ n := by
      rw [Nat.succ_mul]; omega
    have h2 : (((macOf mem n q).carry + MachineState.readWord mem 2080 - q).toNat + 1) *
        Limbs.radix ^ n ≤ Limbs.radix * Limbs.radix ^ n :=
      Nat.mul_le_mul_right _ hTnlt
    rw [Nat.mul_comm (Limbs.radix ^ n) Limbs.radix]
    omega
  · rw [hnegv]; split <;> omega

/-! ## The repair rounds -/

theorem addStep_readWord_disjoint (mem : ByteArray) (n addr : Nat)
    (hdisj : addr + 32 ≤ 2112 ∨ 2112 + 32 * n ≤ addr) :
    ∀ j, j ≤ n → MachineState.readWord (addStep mem n j).memory addr =
      MachineState.readWord mem addr := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
      intro hj
      have hstep : MachineState.readWord (addStep mem n (j + 1)).memory addr =
          MachineState.readWord (addStep mem n j).memory addr := by
        simp only [addStep]
        exact Csub.readWord_write_disjoint _ _ _ _ (by omega)
      rw [hstep, ih (by omega)]

/-- Limbs at or above `j` are untouched by the first `j` steps. -/
theorem addStep_readWord_keep (mem : ByteArray) (n k : Nat) (hk : k < n) :
    ∀ j, j ≤ k → MachineState.readWord (addStep mem n j).memory (2112 + 32 * (n - 1 - k)) =
      MachineState.readWord mem (2112 + 32 * (n - 1 - k)) := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
      intro hj
      have hstep : MachineState.readWord (addStep mem n (j + 1)).memory
          (2112 + 32 * (n - 1 - k)) =
          MachineState.readWord (addStep mem n j).memory (2112 + 32 * (n - 1 - k)) := by
        simp only [addStep]
        exact Csub.readWord_write_disjoint _ _ _ _ (by omega)
      rw [hstep, ih (by omega)]

theorem addStep_lowValue_stable (mem : ByteArray) (n j : Nat) (hj : j < n) :
    Csub.lowValue (addStep mem n (j + 1)).memory 2112 n j =
      Csub.lowValue (addStep mem n j).memory 2112 n j := by
  apply Csub.lowValue_congr
  intro k hk
  simp only [addStep]
  exact Csub.readWord_write_disjoint _ _ _ _ (by omega)

theorem addStep_readWord_new (mem : ByteArray) (n j : Nat) :
    MachineState.readWord (addStep mem n (j + 1)).memory (2112 + 32 * (n - 1 - j)) =
      (addStep mem n j).flag +
        (MachineState.readWord (addStep mem n j).memory (2112 + 32 * (n - 1 - j)) +
          MachineState.readWord (addStep mem n j).memory (32 * (n - 1 - j))) := by
  simp only [addStep]
  exact Challenge.EvmProof.Memory.readWord_writeWord _ _ _

theorem addStep_flag_succ (mem : ByteArray) (n j : Nat) :
    (addStep mem n (j + 1)).flag =
      UInt256.lor
        (UInt256.gt (addStep mem n j).flag ((addStep mem n j).flag +
          (MachineState.readWord (addStep mem n j).memory (2112 + 32 * (n - 1 - j)) +
            MachineState.readWord (addStep mem n j).memory (32 * (n - 1 - j)))))
        (UInt256.gt (MachineState.readWord (addStep mem n j).memory (2112 + 32 * (n - 1 - j)))
          (MachineState.readWord (addStep mem n j).memory (2112 + 32 * (n - 1 - j)) +
            MachineState.readWord (addStep mem n j).memory (32 * (n - 1 - j)))) := by
  simp only [addStep]

/-- One in-place add limb: `t + m + c` with its carry. -/
theorem addLimb_spec' (t md c : UInt256) (hc : c.toNat ≤ 1) :
    (c + (t + md)).toNat + Limbs.radix *
        (UInt256.lor (UInt256.gt c (c + (t + md))) (UInt256.gt t (t + md))).toNat =
      t.toNat + md.toNat + c.toNat ∧
    (UInt256.lor (UInt256.gt c (c + (t + md))) (UInt256.gt t (t + md))).toNat ≤ 1 := by
  have hx : t.toNat < 2 ^ 256 := t.val.isLt
  have hy : md.toNat < 2 ^ 256 := md.val.isLt
  have h1 : (UInt256.gt c (c + (t + md))).toNat ≤ 1 := by
    rw [gt_toNat]; split <;> omega
  have h2 : (UInt256.gt t (t + md)).toNat ≤ 1 := by
    rw [gt_toNat]; split <;> omega
  rw [Challenge.EvmProof.Word.word_toNat_lor, Csub.or_of_le_one h1 h2]
  simp only [gt_toNat, Challenge.EvmProof.Word.word_toNat_add, radix_eq]
  constructor
  · split_ifs <;> omega
  · split_ifs <;> omega

theorem addStep_invariant (mem : ByteArray) (n : Nat) (hn32 : n ≤ 8) :
    ∀ j, j ≤ n →
      Csub.lowValue (addStep mem n j).memory 2112 n j +
          (addStep mem n j).flag.toNat * Limbs.radix ^ j =
        Csub.lowValue mem 2112 n j + Csub.lowValue mem 0 n j ∧
        (addStep mem n j).flag.toNat ≤ 1 := by
  intro j
  induction j with
  | zero => intro _; simp [addStep]
  | succ j ih =>
      intro hj
      obtain ⟨ihEq, ihLe⟩ := ih (by omega)
      have hxt : MachineState.readWord (addStep mem n j).memory (2112 + 32 * (n - 1 - j)) =
          MachineState.readWord mem (2112 + 32 * (n - 1 - j)) :=
        addStep_readWord_keep mem n j (by omega) j le_rfl
      have hxm : MachineState.readWord (addStep mem n j).memory (32 * (n - 1 - j)) =
          MachineState.readWord mem (32 * (n - 1 - j)) :=
        addStep_readWord_disjoint mem n _ (Or.inl (by omega)) j (by omega)
      have hlimb := addLimb_spec' (MachineState.readWord mem (2112 + 32 * (n - 1 - j)))
        (MachineState.readWord mem (32 * (n - 1 - j))) (addStep mem n j).flag ihLe
      rw [Csub.lowValue_succ (addStep mem n (j + 1)).memory 2112 n j,
        addStep_lowValue_stable mem n j (by omega),
        addStep_readWord_new, addStep_flag_succ,
        Csub.lowValue_succ mem 2112 n j, Csub.lowValue_succ mem 0 n j, pow_succ]
      simp only [Nat.zero_add, hxt, hxm]
      exact ⟨Csub.am_algebra _ _ _ _ _ _ _ _ _ _ hlimb.1 ihEq, hlimb.2⟩

theorem addRound_value (mem : ByteArray) (n mm : Nat) (hn : 1 ≤ n) (hn32 : n ≤ 8)
    (hmod : Model.FastRepresents mem 0 n mm) :
    tv (addRoundMem mem n) n + (addOut mem n).toNat * Limbs.radix ^ (n + 1) =
      tv mem n + mm ∧ (addOut mem n).toNat ≤ 1 := by
  obtain ⟨hinv, hle⟩ := addStep_invariant mem n hn32 n le_rfl
  have hM : Csub.lowValue mem 0 n n = mm := by
    rw [Csub.lowValue_full]; exact Model.value_of_fastRepresents hmod
  rw [hM] at hinv
  have htn : MachineState.readWord (addStep mem n n).memory 2080 =
      MachineState.readWord mem 2080 :=
    addStep_readWord_disjoint mem n 2080 (Or.inl (by omega)) n le_rfl
  have hcarry := add_carry_spec (addStep mem n n).flag
    (MachineState.readWord (addStep mem n n).memory 2080)
  unfold addOut addCarry
  rw [tv_def, tv_def]
  unfold addRoundMem addCarry Exp.storeWord
  rw [Challenge.EvmProof.Memory.readWord_writeWord]
  have hlow : Csub.lowValue (MachineState.writeBytes (addStep mem n n).memory
      (Data.Bytes.natToBytesPadded (((addStep mem n n).flag +
        MachineState.readWord (addStep mem n n).memory 2080).toNat) 32) 2080) 2112 n n =
      Csub.lowValue (addStep mem n n).memory 2112 n n := by
    apply Csub.lowValue_congr
    intro k hk
    exact Csub.readWord_write_disjoint _ _ _ _ (by omega)
  rw [hlow, htn]
  rw [htn] at hcarry
  refine ⟨?_, hcarry.2⟩
  rw [pow_succ]
  have hc' : (((addStep mem n n).flag + MachineState.readWord mem 2080).toNat +
      (UInt256.lt ((addStep mem n n).flag + MachineState.readWord mem 2080)
        (addStep mem n n).flag).toNat * Limbs.radix) * Limbs.radix ^ n =
      ((addStep mem n n).flag.toNat + (MachineState.readWord mem 2080).toNat) * Limbs.radix ^ n :=
    by rw [hcarry.1]
  nlinarith [hc', hinv]

theorem addRoundMem_readWord_disjoint (mem : ByteArray) (n addr : Nat)
    (hdisj : addr + 32 ≤ 2080 ∨ 2112 + 32 * n ≤ addr) :
    MachineState.readWord (addRoundMem mem n) addr = MachineState.readWord mem addr := by
  unfold addRoundMem Exp.storeWord
  rw [Csub.readWord_write_disjoint _ _ _ _ (by omega)]
  exact addStep_readWord_disjoint mem n addr (by omega) n le_rfl

theorem subStep_readWord_disjoint (mem : ByteArray) (n addr : Nat)
    (hdisj : addr + 32 ≤ 2112 ∨ 2112 + 32 * n ≤ addr) :
    ∀ j, j ≤ n → MachineState.readWord (subStep mem n j).memory addr =
      MachineState.readWord mem addr := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
      intro hj
      have hstep : MachineState.readWord (subStep mem n (j + 1)).memory addr =
          MachineState.readWord (subStep mem n j).memory addr := by
        simp only [subStep]
        exact Csub.readWord_write_disjoint _ _ _ _ (by omega)
      rw [hstep, ih (by omega)]

theorem subStep_readWord_keep (mem : ByteArray) (n k : Nat) (hk : k < n) :
    ∀ j, j ≤ k → MachineState.readWord (subStep mem n j).memory (2112 + 32 * (n - 1 - k)) =
      MachineState.readWord mem (2112 + 32 * (n - 1 - k)) := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
      intro hj
      have hstep : MachineState.readWord (subStep mem n (j + 1)).memory
          (2112 + 32 * (n - 1 - k)) =
          MachineState.readWord (subStep mem n j).memory (2112 + 32 * (n - 1 - k)) := by
        simp only [subStep]
        exact Csub.readWord_write_disjoint _ _ _ _ (by omega)
      rw [hstep, ih (by omega)]

theorem subStep_lowValue_stable (mem : ByteArray) (n j : Nat) (hj : j < n) :
    Csub.lowValue (subStep mem n (j + 1)).memory 2112 n j =
      Csub.lowValue (subStep mem n j).memory 2112 n j := by
  apply Csub.lowValue_congr
  intro k hk
  simp only [subStep]
  exact Csub.readWord_write_disjoint _ _ _ _ (by omega)

theorem subStep_readWord_new (mem : ByteArray) (n j : Nat) :
    MachineState.readWord (subStep mem n (j + 1)).memory (2112 + 32 * (n - 1 - j)) =
      MachineState.readWord (subStep mem n j).memory (2112 + 32 * (n - 1 - j)) -
        MachineState.readWord (subStep mem n j).memory (32 * (n - 1 - j)) -
        (subStep mem n j).flag := by
  simp only [subStep]
  exact Challenge.EvmProof.Memory.readWord_writeWord _ _ _

theorem subStep_flag_succ (mem : ByteArray) (n j : Nat) :
    (subStep mem n (j + 1)).flag =
      UInt256.lor
        (UInt256.lt (MachineState.readWord (subStep mem n j).memory (2112 + 32 * (n - 1 - j)) -
            MachineState.readWord (subStep mem n j).memory (32 * (n - 1 - j)))
          (subStep mem n j).flag)
        (UInt256.gt (MachineState.readWord (subStep mem n j).memory (32 * (n - 1 - j)))
          (MachineState.readWord (subStep mem n j).memory (2112 + 32 * (n - 1 - j)))) := by
  simp only [subStep]

theorem subLimb_spec' (x y b : UInt256) (hb : b.toNat ≤ 1) :
    (x - y - b).toNat + y.toNat + b.toNat =
      x.toNat + Limbs.radix *
        (UInt256.lor (UInt256.lt (x - y) b) (UInt256.gt y x)).toNat ∧
    (UInt256.lor (UInt256.lt (x - y) b) (UInt256.gt y x)).toNat ≤ 1 := by
  have hx : x.toNat < 2 ^ 256 := x.val.isLt
  have hy : y.toNat < 2 ^ 256 := y.val.isLt
  have h1 : (UInt256.lt (x - y) b).toNat ≤ 1 := by
    rw [Challenge.EvmProof.Word.word_toNat_lt]; split <;> omega
  have h2 : (UInt256.gt y x).toNat ≤ 1 := by
    rw [gt_toNat]; split <;> omega
  rw [Challenge.EvmProof.Word.word_toNat_lor, Csub.or_of_le_one h1 h2]
  simp only [Challenge.EvmProof.Word.word_toNat_lt, gt_toNat,
    Challenge.EvmProof.Word.word_toNat_sub_cond, radix_eq]
  constructor
  · split_ifs <;> omega
  · split_ifs <;> omega

theorem subStep_invariant (mem : ByteArray) (n : Nat) (hn32 : n ≤ 8) :
    ∀ j, j ≤ n →
      Csub.lowValue (subStep mem n j).memory 2112 n j + Csub.lowValue mem 0 n j =
        Csub.lowValue mem 2112 n j + (subStep mem n j).flag.toNat * Limbs.radix ^ j ∧
        (subStep mem n j).flag.toNat ≤ 1 := by
  intro j
  induction j with
  | zero => intro _; simp [subStep]
  | succ j ih =>
      intro hj
      obtain ⟨ihEq, ihLe⟩ := ih (by omega)
      have hxt : MachineState.readWord (subStep mem n j).memory (2112 + 32 * (n - 1 - j)) =
          MachineState.readWord mem (2112 + 32 * (n - 1 - j)) :=
        subStep_readWord_keep mem n j (by omega) j le_rfl
      have hxm : MachineState.readWord (subStep mem n j).memory (32 * (n - 1 - j)) =
          MachineState.readWord mem (32 * (n - 1 - j)) :=
        subStep_readWord_disjoint mem n _ (Or.inl (by omega)) j (by omega)
      have hlimb := subLimb_spec' (MachineState.readWord mem (2112 + 32 * (n - 1 - j)))
        (MachineState.readWord mem (32 * (n - 1 - j))) (subStep mem n j).flag ihLe
      rw [Csub.lowValue_succ (subStep mem n (j + 1)).memory 2112 n j,
        subStep_lowValue_stable mem n j (by omega),
        subStep_readWord_new, subStep_flag_succ,
        Csub.lowValue_succ mem 0 n j, Csub.lowValue_succ mem 2112 n j, pow_succ]
      simp only [Nat.zero_add, hxt, hxm]
      exact ⟨Csub.cs_algebra _ _ _ _ _ _ _ _ _ _ hlimb.1 ihEq, hlimb.2⟩

theorem subRound_value (mem : ByteArray) (n mm : Nat) (hn : 1 ≤ n) (hn32 : n ≤ 8)
    (hmod : Model.FastRepresents mem 0 n mm)
    (htn : (MachineState.readWord mem 2080).toNat ≠ 0) :
    tv (subRoundMem mem n) n + mm = tv mem n := by
  obtain ⟨hinv, hle⟩ := subStep_invariant mem n hn32 n le_rfl
  have hM : Csub.lowValue mem 0 n n = mm := by
    rw [Csub.lowValue_full]; exact Model.value_of_fastRepresents hmod
  rw [hM] at hinv
  have htn' : MachineState.readWord (subStep mem n n).memory 2080 =
      MachineState.readWord mem 2080 :=
    subStep_readWord_disjoint mem n 2080 (Or.inl (by omega)) n le_rfl
  have hborrow := (sub_borrow_spec (MachineState.readWord (subStep mem n n).memory 2080)
    (subStep mem n n).flag).1
  rw [tv_def, tv_def]
  unfold subRoundMem subBorrow Exp.storeWord
  rw [Challenge.EvmProof.Memory.readWord_writeWord]
  have hlow : Csub.lowValue (MachineState.writeBytes (subStep mem n n).memory
      (Data.Bytes.natToBytesPadded ((MachineState.readWord (subStep mem n n).memory 2080 -
        (subStep mem n n).flag).toNat) 32) 2080) 2112 n n =
      Csub.lowValue (subStep mem n n).memory 2112 n n := by
    apply Csub.lowValue_congr
    intro k hk
    exact Csub.readWord_write_disjoint _ _ _ _ (by omega)
  rw [hlow, htn']
  rw [htn'] at hborrow
  have hnb : (UInt256.lt (MachineState.readWord mem 2080) (subStep mem n n).flag).toNat = 0 := by
    rw [Challenge.EvmProof.Word.word_toNat_lt]
    rw [if_neg]; omega
  rw [hnb, Nat.zero_mul, Nat.add_zero] at hborrow
  have hb' : ((MachineState.readWord mem 2080 - (subStep mem n n).flag).toNat +
      (subStep mem n n).flag.toNat) * Limbs.radix ^ n =
      (MachineState.readWord mem 2080).toNat * Limbs.radix ^ n := by rw [hborrow]
  nlinarith [hb', hinv]

theorem subRoundMem_readWord_disjoint (mem : ByteArray) (n addr : Nat)
    (hdisj : addr + 32 ≤ 2080 ∨ 2112 + 32 * n ≤ addr) :
    MachineState.readWord (subRoundMem mem n) addr = MachineState.readWord mem addr := by
  unfold subRoundMem Exp.storeWord
  rw [Csub.readWord_write_disjoint _ _ _ _ (by omega)]
  exact subStep_readWord_disjoint mem n addr (by omega) n le_rfl

/-! ### Rounds -/

theorem addRounds_readWord_disjoint (mem : ByteArray) (n addr : Nat)
    (hdisj : addr + 32 ≤ 2080 ∨ 2112 + 32 * n ≤ addr) :
    ∀ k, MachineState.readWord (addRounds mem n k) addr = MachineState.readWord mem addr := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih => exact (addRoundMem_readWord_disjoint _ n addr hdisj).trans ih

theorem subRounds_readWord_disjoint (mem : ByteArray) (n addr : Nat)
    (hdisj : addr + 32 ≤ 2080 ∨ 2112 + 32 * n ≤ addr) :
    ∀ k, MachineState.readWord (subRounds mem n k) addr = MachineState.readWord mem addr := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih => exact (subRoundMem_readWord_disjoint _ n addr hdisj).trans ih

theorem fastRepresents_addRounds (mem : ByteArray) (n ptr cnt v : Nat)
    (hdisj : ptr + 32 * cnt ≤ 2080 ∨ 2112 + 32 * n ≤ ptr)
    (hrep : Model.FastRepresents mem ptr cnt v) (k : Nat) :
    Model.FastRepresents (addRounds mem n k) ptr cnt v := by
  refine (Model.fastRepresents_congr ?_ v).2 hrep
  intro i hi
  exact addRounds_readWord_disjoint mem n _ (by omega) k

theorem fastRepresents_subRounds (mem : ByteArray) (n ptr cnt v : Nat)
    (hdisj : ptr + 32 * cnt ≤ 2080 ∨ 2112 + 32 * n ≤ ptr)
    (hrep : Model.FastRepresents mem ptr cnt v) (k : Nat) :
    Model.FastRepresents (subRounds mem n k) ptr cnt v := by
  refine (Model.fastRepresents_congr ?_ v).2 hrep
  intro i hi
  exact subRounds_readWord_disjoint mem n _ (by omega) k

/-- Add rounds without a carry out: the value grows by `m` each round. -/
theorem addRounds_value (mem : ByteArray) (n mm : Nat) (hn : 1 ≤ n) (hn32 : n ≤ 8)
    (hmod : Model.FastRepresents mem 0 n mm) :
    ∀ i, tv mem n + i * mm < Limbs.radix ^ (n + 1) →
      tv (addRounds mem n i) n = tv mem n + i * mm ∧
        ∀ j, j < i → addOut (addRounds mem n j) n = UInt256.ofNat 0 := by
  intro i
  induction i with
  | zero =>
      intro _
      exact ⟨by simp [addRounds], fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  | succ i ih =>
      intro hlt
      obtain ⟨hval, hout⟩ := ih (by rw [Nat.succ_mul] at hlt; omega)
      have hmod' : Model.FastRepresents (addRounds mem n i) 0 n mm :=
        fastRepresents_addRounds mem n 0 n mm (Or.inl (by omega)) hmod i
      obtain ⟨hround, hle⟩ := addRound_value (addRounds mem n i) n mm hn hn32 hmod'
      have hout0 : (addOut (addRounds mem n i) n).toNat = 0 := by
        by_contra hne
        have h1 : (addOut (addRounds mem n i) n).toNat = 1 := by omega
        rw [h1, hval] at hround
        rw [Nat.succ_mul] at hlt
        omega
      have hout0' : addOut (addRounds mem n i) n = UInt256.ofNat 0 := by
        rw [Challenge.EvmProof.Word.word_eq_ofNat_toNat (addOut (addRounds mem n i) n), hout0]
      refine ⟨?_, ?_⟩
      · show tv (addRoundMem (addRounds mem n i) n) n = _
        rw [hout0, hval] at hround
        rw [Nat.succ_mul]
        omega
      · intro j hj
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with h | h
        · exact hout j h
        · subst h; exact hout0'

/-- The final add round overflows and leaves `tv + k m - radix^(n+1)`. -/
theorem addRounds_last (mem : ByteArray) (n mm k : Nat) (hn : 1 ≤ n) (hn32 : n ≤ 8)
    (hmod : Model.FastRepresents mem 0 n mm)
    (hlt : tv mem n + k * mm < Limbs.radix ^ (n + 1))
    (hge : Limbs.radix ^ (n + 1) ≤ tv mem n + (k + 1) * mm) :
    addOut (addRounds mem n k) n = UInt256.ofNat 1 ∧
      tv (addRounds mem n (k + 1)) n + Limbs.radix ^ (n + 1) = tv mem n + (k + 1) * mm := by
  obtain ⟨hval, _⟩ := addRounds_value mem n mm hn hn32 hmod k hlt
  have hmod' : Model.FastRepresents (addRounds mem n k) 0 n mm :=
    fastRepresents_addRounds mem n 0 n mm (Or.inl (by omega)) hmod k
  obtain ⟨hround, hle⟩ := addRound_value (addRounds mem n k) n mm hn hn32 hmod'
  have hout1 : (addOut (addRounds mem n k) n).toNat = 1 := by
    by_contra hne
    have h0 : (addOut (addRounds mem n k) n).toNat = 0 := by omega
    rw [h0, hval] at hround
    have hlow := Csub.lowValue_lt (addRoundMem (addRounds mem n k) n) 2112 n n
    have hlt' : tv (addRoundMem (addRounds mem n k) n) n < Limbs.radix ^ (n + 1) := by
      rw [tv_def, pow_succ]
      have htn : (MachineState.readWord (addRoundMem (addRounds mem n k) n) 2080).toNat <
          Limbs.radix := (MachineState.readWord _ 2080).val.isLt
      nlinarith
    rw [Nat.succ_mul] at hge
    omega
  refine ⟨?_, ?_⟩
  · rw [Challenge.EvmProof.Word.word_eq_ofNat_toNat (addOut (addRounds mem n k) n), hout1]
  · show tv (addRoundMem (addRounds mem n k) n) n + _ = _
    rw [hout1, hval] at hround
    rw [Nat.succ_mul]
    omega

/-- Subtract rounds: the value drops by `m` each round while the top limb is
nonzero. -/
theorem subRounds_value (mem : ByteArray) (n mm : Nat) (hn : 1 ≤ n) (hn32 : n ≤ 8)
    (hmod : Model.FastRepresents mem 0 n mm) :
    ∀ i, (∀ j, j < i → Limbs.radix ^ n + j * mm ≤ tv mem n) →
      tv (subRounds mem n i) n + i * mm = tv mem n := by
  intro i
  induction i with
  | zero => intro _; simp [subRounds]
  | succ i ih =>
      intro hle
      have hprev := ih (fun j hj => hle j (by omega))
      have hmod' : Model.FastRepresents (subRounds mem n i) 0 n mm :=
        fastRepresents_subRounds mem n 0 n mm (Or.inl (by omega)) hmod i
      have htn : (MachineState.readWord (subRounds mem n i) 2080).toNat ≠ 0 := by
        rw [tn_ne_zero_iff _ n]
        have := hle i (by omega)
        omega
      have hround := subRound_value (subRounds mem n i) n mm hn hn32 hmod' htn
      show tv (subRoundMem (subRounds mem n i) n) n + _ = _
      rw [Nat.succ_mul]
      omega

/-- The round counts and exit conditions the repair loops need. -/
structure RepairFacts (mid : ByteArray) (n mm : Nat) (neg : UInt256) : Prop where
  addRoundsOut : ∀ i, i < addCount mid n mm neg - 1 →
    addOut (addRounds mid n i) n = UInt256.ofNat 0
  addLastOut : 1 ≤ addCount mid n mm neg →
    addOut (addRounds mid n (addCount mid n mm neg - 1)) n = UInt256.ofNat 1
  subRoundsTn : ∀ i, i < subCount (addRounds mid n (addCount mid n mm neg)) n mm →
    (MachineState.readWord
      (subRounds (addRounds mid n (addCount mid n mm neg)) n i) 2080).toNat ≠ 0
  subDoneTn : (MachineState.readWord (fixMem mid n mm neg) 2080).toNat = 0
  negCount : neg = UInt256.ofNat 1 → 1 ≤ addCount mid n mm neg
  posCount : neg = UInt256.ofNat 0 → addCount mid n mm neg = 0

/-- The subtract phase from a non-negative value: rounds while the top limb is
nonzero, ending below `radix ^ n`. -/
theorem subPhase_spec (mem : ByteArray) (n mm : Nat) (hn : 1 ≤ n) (hn32 : n ≤ 8)
    (hmpos : 0 < mm) (hmod : Model.FastRepresents mem 0 n mm) :
    (∀ i, i < subCount mem n mm →
      (MachineState.readWord (subRounds mem n i) 2080).toNat ≠ 0) ∧
    tv (subRounds mem n (subCount mem n mm)) n + subCount mem n mm * mm = tv mem n ∧
    tv (subRounds mem n (subCount mem n mm)) n < Limbs.radix ^ n := by
  unfold subCount
  by_cases hlt : tv mem n < Limbs.radix ^ n
  · rw [if_pos hlt]
    refine ⟨fun i hi => absurd hi (Nat.not_lt_zero i), by simp [subRounds], ?_⟩
    simpa [subRounds] using hlt
  · rw [if_neg hlt]
    have hge : Limbs.radix ^ n ≤ tv mem n := Nat.le_of_not_lt hlt
    have hdivle := Nat.div_mul_le_self (tv mem n - Limbs.radix ^ n) mm
    have hdivlt := Nat.lt_div_mul_add (a := tv mem n - Limbs.radix ^ n) hmpos
    have hle : ∀ i, i < (tv mem n - Limbs.radix ^ n) / mm + 1 →
        Limbs.radix ^ n + i * mm ≤ tv mem n := by
      intro i hi
      have : i * mm ≤ (tv mem n - Limbs.radix ^ n) / mm * mm :=
        Nat.mul_le_mul_right mm (by omega)
      omega
    refine ⟨?_, ?_, ?_⟩
    · intro i hi
      rw [tn_ne_zero_iff _ n]
      have hval := subRounds_value mem n mm hn hn32 hmod i (fun j hj => hle j (by omega))
      have : i * mm + mm ≤ ((tv mem n - Limbs.radix ^ n) / mm + 1) * mm := by
        rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right mm hi
      have h2 : ((tv mem n - Limbs.radix ^ n) / mm + 1) * mm =
          (tv mem n - Limbs.radix ^ n) / mm * mm + mm := by rw [Nat.succ_mul]
      omega
    · exact subRounds_value mem n mm hn hn32 hmod _ hle
    · have hval := subRounds_value mem n mm hn hn32 hmod _ hle
      have h2 : ((tv mem n - Limbs.radix ^ n) / mm + 1) * mm =
          (tv mem n - Limbs.radix ^ n) / mm * mm + mm := by rw [Nat.succ_mul]
      omega

theorem subRounds_zero (mem : ByteArray) (n : Nat) : subRounds mem n 0 = mem := by
  simp [subRounds]

theorem addRounds_zero (mem : ByteArray) (n : Nat) : addRounds mem n 0 = mem := by
  simp [addRounds]

/-- After the repair rounds the value is `u`-congruent, below `radix ^ n`,
and `TN` is zero; and the loop facts hold. -/
theorem repair_spec (mem : ByteArray) (n mm : Nat) (neg : UInt256) (u q : Nat)
    (hn : 1 ≤ n) (hn32 : n ≤ 8) (hmpos : 0 < mm) (hmm : mm < Limbs.radix ^ n)
    (hmod : Model.FastRepresents mem 0 n mm)
    (hrel : u + neg.toNat * Limbs.radix ^ (n + 1) = q * mm + tv mem n)
    (hlt : tv mem n < Limbs.radix ^ (n + 1)) (hneg : neg.toNat ≤ 1) :
    RepairFacts mem n mm neg ∧
      tv (fixMem mem n mm neg) n % mm = u % mm ∧
      tv (fixMem mem n mm neg) n < Limbs.radix ^ n ∧
      (MachineState.readWord (fixMem mem n mm neg) 2080).toNat = 0 := by
  have hnegCases : neg = UInt256.ofNat 0 ∨ neg = UInt256.ofNat 1 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hneg with h | h
    · left; rw [Challenge.EvmProof.Word.word_eq_ofNat_toNat neg, h]
    · right; rw [Challenge.EvmProof.Word.word_eq_ofNat_toNat neg, h]
  have h01 : ¬ (UInt256.ofNat 0 = UInt256.ofNat 1) := by
    intro h
    have := congrArg UInt256.toNat h
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat] at this
    norm_num at this
  rcases hnegCases with h0 | h1
  · have hn0 : neg.toNat = 0 := by
      rw [h0, Challenge.EvmProof.Word.word_toNat_ofNat]; exact Nat.zero_mod _
    have hcount : addCount mem n mm neg = 0 := by unfold addCount; rw [if_pos hn0]
    have hsub := subPhase_spec mem n mm hn hn32 hmpos hmod
    have hfix : fixMem mem n mm neg = subRounds mem n (subCount mem n mm) := by
      unfold fixMem
      rw [hcount, addRounds_zero]
    rw [hn0, Nat.zero_mul, Nat.add_zero] at hrel
    have htn0 := tn_zero_of_lt _ n hsub.2.2
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
    · intro i hi; rw [hcount] at hi; exact absurd hi (Nat.not_lt_zero i)
    · intro h; rw [hcount] at h; omega
    · intro i hi; rw [hcount] at hi ⊢; exact hsub.1 i hi
    · rw [hfix]; exact htn0
    · intro h; exact absurd (h0.symm.trans h) h01
    · intro _; exact hcount
    · rw [hfix]
      have hv := hsub.2.1
      have : tv (subRounds mem n (subCount mem n mm)) n =
          tv mem n - mm * subCount mem n mm := by rw [Nat.mul_comm]; omega
      rw [this, Nat.sub_mul_mod (by rw [Nat.mul_comm]; omega), hrel, Nat.add_comm,
        Nat.add_mul_mod_self_right]
    · rw [hfix]; exact hsub.2.2
    · rw [hfix]; exact htn0
  · have hn1 : neg.toNat = 1 := by
      rw [h1, Challenge.EvmProof.Word.word_toNat_ofNat]; exact Nat.mod_eq_of_lt (by norm_num)
    have hR' : Limbs.radix ^ (n + 1) = Limbs.radix ^ n * Limbs.radix := pow_succ _ _
    -- the count
    have hcount : addCount mem n mm neg =
        (Limbs.radix ^ (n + 1) - tv mem n + mm - 1) / mm := by
      unfold addCount; rw [if_neg (by omega)]
    generalize hk : (Limbs.radix ^ (n + 1) - tv mem n + mm - 1) / mm = k at hcount
    generalize hD : Limbs.radix ^ (n + 1) - tv mem n = D at *
    have hD1 : 1 ≤ D := by omega
    have hk1 : 1 ≤ k := by
      rw [← hk]
      exact Nat.div_pos (by omega) hmpos
    have hkm : D ≤ k * mm := by
      have h := Nat.div_add_mod (D + mm - 1) mm
      have hmodlt := Nat.mod_lt (D + mm - 1) hmpos
      rw [hk] at h
      rw [Nat.mul_comm]
      omega
    have hkm' : k * mm < D + mm := by
      have h := Nat.div_mul_le_self (D + mm - 1) mm
      rw [hk] at h
      omega
    have hlt1 : tv mem n + (k - 1) * mm < Limbs.radix ^ (n + 1) := by
      rw [Nat.sub_one_mul]; omega
    have hadd := addRounds_value mem n mm hn hn32 hmod (k - 1) hlt1
    have hlast := addRounds_last mem n mm (k - 1) hn hn32 hmod hlt1
      (by rw [Nat.sub_add_cancel hk1]; omega)
    rw [Nat.sub_add_cancel hk1] at hlast
    have hlt' : tv (addRounds mem n k) n < mm := by
      have := hlast.2
      rw [Nat.sub_one_mul] at hlt1
      omega
    have hltP : tv (addRounds mem n k) n < Limbs.radix ^ n := lt_trans hlt' hmm
    have hsc : subCount (addRounds mem n k) n mm = 0 := by
      unfold subCount; rw [if_pos hltP]
    have hfix : fixMem mem n mm neg = addRounds mem n k := by
      unfold fixMem
      rw [hcount, hsc, subRounds_zero]
    rw [hn1, Nat.one_mul] at hrel
    have htn0 := tn_zero_of_lt _ n hltP
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
    · intro i hi; rw [hcount] at hi; exact hadd.2 i hi
    · intro _; rw [hcount]; exact hlast.1
    · intro i hi; rw [hcount, hsc] at hi; exact absurd hi (Nat.not_lt_zero i)
    · rw [hfix]; exact htn0
    · intro _; rw [hcount]; exact hk1
    · intro h; exact absurd (h.symm.trans h1) h01
    · rw [hfix]
      have hsum : tv (addRounds mem n k) n + q * mm = u + k * mm := by
        have := hlast.2
        omega
      have h2 : (tv (addRounds mem n k) n + q * mm) % mm = (u + k * mm) % mm := by rw [hsum]
      rw [Nat.add_mul_mod_self_right, Nat.add_mul_mod_self_right] at h2
      exact h2
    · rw [hfix]; exact hltP
    · rw [hfix]; exact htn0

/-- **The repair lands strictly below the modulus** once the quotient is known not to
under-shoot.  For `neg = 1` this is already what `repair_spec` derives internally before
weakening it to `< radix ^ n`; for `neg = 0` it is exactly where `u / mm ≤ q` is load-bearing,
because the subtract phase stops at `radix ^ n`, not at `mm`. -/
theorem repair_lt_mm (mem : ByteArray) (n mm : Nat) (neg : UInt256) (u q : Nat)
    (hn : 1 ≤ n) (hn32 : n ≤ 8) (hmpos : 0 < mm) (hmm : mm < Limbs.radix ^ n)
    (hmod : Model.FastRepresents mem 0 n mm)
    (hrel : u + neg.toNat * Limbs.radix ^ (n + 1) = q * mm + tv mem n)
    (hlt : tv mem n < Limbs.radix ^ (n + 1)) (hneg : neg.toNat ≤ 1)
    (hq : u / mm ≤ q) :
    tv (fixMem mem n mm neg) n < mm := by
  have hnegCases : neg.toNat = 0 ∨ neg.toNat = 1 := by omega
  rcases hnegCases with hn0 | hn1
  · have hcount : addCount mem n mm neg = 0 := by unfold addCount; rw [if_pos hn0]
    have hfix : fixMem mem n mm neg = subRounds mem n (subCount mem n mm) := by
      unfold fixMem; rw [hcount, addRounds_zero]
    rw [hn0, Nat.zero_mul, Nat.add_zero] at hrel
    have hqle : q ≤ u / mm := (Nat.le_div_iff_mul_le hmpos).mpr (by omega)
    have hqeq : q = u / mm := by omega
    have hdm := Nat.div_add_mod' u mm
    have hmod2 : u % mm < mm := Nat.mod_lt _ hmpos
    have htvlt : tv mem n < mm := by rw [hqeq] at hrel; omega
    have hsc : subCount mem n mm = 0 := by
      unfold subCount; rw [if_pos (lt_trans htvlt hmm)]
    rw [hfix, hsc, subRounds_zero]
    exact htvlt
  · have hR' : Limbs.radix ^ (n + 1) = Limbs.radix ^ n * Limbs.radix := pow_succ _ _
    have hcount : addCount mem n mm neg =
        (Limbs.radix ^ (n + 1) - tv mem n + mm - 1) / mm := by
      unfold addCount; rw [if_neg (by omega)]
    generalize hk : (Limbs.radix ^ (n + 1) - tv mem n + mm - 1) / mm = k at hcount
    generalize hD : Limbs.radix ^ (n + 1) - tv mem n = D at *
    have hD1 : 1 ≤ D := by omega
    have hk1 : 1 ≤ k := by rw [← hk]; exact Nat.div_pos (by omega) hmpos
    have hkm : D ≤ k * mm := by
      have h := Nat.div_add_mod (D + mm - 1) mm
      have hmodlt := Nat.mod_lt (D + mm - 1) hmpos
      rw [hk] at h
      rw [Nat.mul_comm]
      omega
    have hkm' : k * mm < D + mm := by
      have h := Nat.div_mul_le_self (D + mm - 1) mm
      rw [hk] at h
      omega
    have hlt1 : tv mem n + (k - 1) * mm < Limbs.radix ^ (n + 1) := by
      rw [Nat.sub_one_mul]; omega
    have hlast := addRounds_last mem n mm (k - 1) hn hn32 hmod hlt1
      (by rw [Nat.sub_add_cancel hk1]; omega)
    rw [Nat.sub_add_cancel hk1] at hlast
    have hlt' : tv (addRounds mem n k) n < mm := by
      have := hlast.2
      rw [Nat.sub_one_mul] at hlt1
      omega
    have hltP : tv (addRounds mem n k) n < Limbs.radix ^ n := lt_trans hlt' hmm
    have hsc : subCount (addRounds mem n k) n mm = 0 := by
      unfold subCount; rw [if_pos hltP]
    have hfix : fixMem mem n mm neg = addRounds mem n k := by
      unfold fixMem; rw [hcount, hsc, subRounds_zero]
    rw [hfix]
    exact hlt'

theorem fixMem_value (mem : ByteArray) (n mm : Nat) (neg : UInt256) (u q : Nat)
    (hn : 1 ≤ n) (hn32 : n ≤ 8) (hmpos : 0 < mm) (hmm : mm < Limbs.radix ^ n)
    (hmod : Model.FastRepresents mem 0 n mm)
    (hrel : u + neg.toNat * Limbs.radix ^ (n + 1) = q * mm + tv mem n)
    (hlt : tv mem n < Limbs.radix ^ (n + 1)) (hneg : neg.toNat ≤ 1) :
    tv (fixMem mem n mm neg) n % mm = u % mm ∧
      tv (fixMem mem n mm neg) n < Limbs.radix ^ n ∧
      (MachineState.readWord (fixMem mem n mm neg) 2080).toNat = 0 :=
  (repair_spec mem n mm neg u q hn hn32 hmpos hmm hmod hrel hlt hneg).2

theorem fixMem_readWord_disjoint (mem : ByteArray) (n mm : Nat) (neg : UInt256) (addr : Nat)
    (hdisj : addr + 32 ≤ 2080 ∨ 2112 + 32 * n ≤ addr) :
    MachineState.readWord (fixMem mem n mm neg) addr = MachineState.readWord mem addr := by
  unfold fixMem
  rw [subRounds_readWord_disjoint _ n addr hdisj, addRounds_readWord_disjoint _ n addr hdisj]

/-! ### The whole step -/

/-- Words the step leaves alone. -/
theorem stepMem_readWord_disjoint (mem : ByteArray) (n mm addr : Nat) (hn : 1 ≤ n)
    (hdisj : (addr + 32 ≤ 512 ∨ 512 + 32 * n ≤ addr) ∧
      (addr + 32 ≤ 1792 ∨ 1792 + 32 * n ≤ addr) ∧
      (addr + 32 ≤ 2080 ∨ 2112 + 32 * n ≤ addr)) :
    MachineState.readWord (stepMem mem n mm) addr = MachineState.readWord mem addr := by
  unfold stepMem
  simp only
  rw [fixMem_readWord_disjoint _ n mm _ addr hdisj.2.2]
  show MachineState.readWord (Exp.storeWord _ 2080 _) addr = _
  unfold Exp.storeWord
  rw [Csub.readWord_write_disjoint _ _ _ _ (by omega)]
  rw [mac_readWord_disjoint _ n addr _ hn (by omega)]
  exact uMem_readWord_disjoint mem n addr hdisj.2.2

theorem fastRepresents_stepMem (mem : ByteArray) (n mm ptr cnt v : Nat) (hn : 1 ≤ n)
    (hdisj : (ptr + 32 * cnt ≤ 512 ∨ 512 + 32 * n ≤ ptr) ∧
      (ptr + 32 * cnt ≤ 1792 ∨ 1792 + 32 * n ≤ ptr) ∧
      (ptr + 32 * cnt ≤ 2080 ∨ 2112 + 32 * n ≤ ptr))
    (hrep : Model.FastRepresents mem ptr cnt v) :
    Model.FastRepresents (stepMem mem n mm) ptr cnt v := by
  refine (Model.fastRepresents_congr ?_ v).2 hrep
  intro i hi
  exact stepMem_readWord_disjoint mem n mm _ hn (by omega)

section QHatGe
open Challenge.EvmProof.Word
open Challenge.Modexp.Submission.Proofs.Fast.QHat


/-- One word-level Newton step is one `Nat`-level Newton step. -/
theorem newtonW_ofNat (D x : Nat) :
    newtonW (UInt256.ofNat D) (UInt256.ofNat x) = UInt256.ofNat (Model.newtonStep D x) :=
  Setup.newton_word_step D x

theorem newton4W_eq (D : Nat) :
    newton4W (UInt256.ofNat D) = UInt256.ofNat (Setup.newton4 D) := by
  have hseed : UInt256.xor (UInt256.ofNat 2) (UInt256.ofNat 3 * UInt256.ofNat D)
      = UInt256.ofNat (NewtonSeed.seed D) := NewtonSeed.word_seed D
  show newtonW (UInt256.ofNat D) (newtonW (UInt256.ofNat D)
      (newtonW (UInt256.ofNat D) (UInt256.xor (UInt256.ofNat 2)
        (UInt256.ofNat 3 * UInt256.ofNat D)))) = _
  rw [hseed, newtonW_ofNat, newtonW_ofNat, newtonW_ofNat]
  rfl

theorem newton8W_eq (D : Nat) :
    newton8W (UInt256.ofNat D) = UInt256.ofNat (Setup.newton8 D) := by
  show newtonW (UInt256.ofNat D) (newtonW (UInt256.ofNat D)
      (newtonW (UInt256.ofNat D) (newton4W (UInt256.ofNat D)))) = _
  rw [newton4W_eq, newtonW_ofNat, newtonW_ofNat, newtonW_ofNat]
  rfl

/-- The stored inverse really inverts the odd part, modulo the radix. -/
theorem preDinv_inv (d : UInt256) (hodd : (preDodd d).toNat % 2 = 1) :
    (preDodd d).toNat * (preDinv d).toNat ≡ 1 [MOD Limbs.radix] := by
  have hD : preDodd d = UInt256.ofNat (preDodd d).toNat := word_eq_ofNat_toNat _
  have hback : (UInt256.ofNat (preDodd d).toNat).toNat = (preDodd d).toNat := by
    rw [word_toNat_ofNat]; exact Nat.mod_eq_of_lt (preDodd d).val.isLt
  have h1 : (preDinv d).toNat = Setup.newton8 (preDodd d).toNat % 2 ^ 256 := by
    unfold preDinv
    rw [hD, newton8W_eq, word_toNat_ofNat, hback]
  have h2 : Setup.newton8 (preDodd d).toNat = Model.newtonIter (preDodd d).toNat 8 :=
    Setup.newton8_eq _ hodd
  have h3 := Model.newtonIter_eight (m := (preDodd d).toNat) hodd
  unfold Nat.ModEq
  rw [h1, h2]
  have hr : Limbs.radix = 2 ^ 256 := rfl
  rw [hr] at h3 ⊢
  rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, h3]
  exact (Nat.mod_eq_of_lt (by norm_num)).symm


/-! ## The five estimator words, in `Nat` terms -/



theorem toNat_mod (a b : UInt256) (hb0 : b.toNat ≠ 0) : (a % b).toNat = a.toNat % b.toNat := by
  show (UInt256.mod a b).toNat = _
  unfold UInt256.mod
  by_cases hb : b.val.val = 0
  · exact absurd hb hb0
  · rw [if_neg hb]
    show (a.val % b.val).val = _
    exact Fin.mod_val a.val b.val

theorem neg_toNat (a : UInt256) (ha : a.toNat ≠ 0) :
    (UInt256.ofNat 0 - a).toNat = 2 ^ 256 - a.toNat := by
  have hlt : a.toNat < 2 ^ 256 := a.val.isLt
  rw [word_toNat_sub, word_toNat_ofNat]
  have h0 : (0 : Nat) % 2 ^ 256 = 0 := by norm_num
  rw [h0, Nat.add_zero]
  exact Nat.mod_eq_of_lt (by omega)

/-- Everything the estimator's five stored words mean, for a nonzero top limb. -/
theorem pre_facts (d : UInt256) (hd : d.toNat ≠ 0) :
    ∃ v, v < 256 ∧ (preL d).toNat = 2 ^ v ∧
      2 ^ v * (preDodd d).toNat = d.toNat ∧
      (preDodd d).toNat % 2 = 1 ∧ 0 < (preDodd d).toNat ∧
      (preBmod d).toNat = 2 ^ 256 % (preDodd d).toNat ∧
      (2 ^ v * (preX d).toNat = 2 ^ 256 ∨ (2 ^ v = 1 ∧ (preX d).toNat = 0)) := by
  obtain ⟨v, hv, hL0, hdvd, hodd⟩ := lsb_word d hd
  have hL : (preL d).toNat = 2 ^ v := hL0
  have hLpos : (0 : Nat) < 2 ^ v := Nat.two_pow_pos v
  have hdodd : (preDodd d).toNat = d.toNat / 2 ^ v := by
    show (d / preL d).toNat = _
    rw [toNat_div, hL]
  have hmul : 2 ^ v * (preDodd d).toNat = d.toNat := by
    rw [hdodd]; exact Nat.mul_div_cancel' hdvd
  have hdoddodd : (preDodd d).toNat % 2 = 1 := by rw [hdodd]; exact hodd
  have hdoddpos : 0 < (preDodd d).toNat := by omega
  refine ⟨v, hv, hL, hmul, hdoddodd, hdoddpos, ?_, ?_⟩
  · show ((UInt256.ofNat 0 - preDodd d) % preDodd d).toNat = _
    rw [toNat_mod _ _ (by omega), neg_toNat _ (by omega)]
    have hle : (preDodd d).toNat ≤ 2 ^ 256 := le_of_lt (preDodd d).val.isLt
    exact sub_mod_self (2 ^ 256) (preDodd d).toNat hdoddpos hle
  · have hXnat : (preX d).toNat = (1 + (2 ^ 256 - 2 ^ v) / 2 ^ v) % 2 ^ 256 := by
      show (UInt256.ofNat 1 + (UInt256.ofNat 0 - preL d) / preL d).toNat = _
      rw [word_toNat_add, toNat_div, neg_toNat _ (by rw [hL]; exact (Nat.two_pow_pos v).ne'), hL, word_toNat_ofNat]
      norm_num
    have hdv : (2 : Nat) ^ v ∣ 2 ^ 256 := pow_dvd_pow 2 (by omega)
    have hq : (2 ^ 256 - 2 ^ v) / 2 ^ v = 2 ^ 256 / 2 ^ v - 1 := by
      obtain ⟨c, hc⟩ := hdv
      have hcpos : 0 < c := by
        rcases Nat.eq_zero_or_pos c with h | h
        · subst h; simp at hc
        · exact h
      rw [hc, show 2 ^ v * c - 2 ^ v = 2 ^ v * (c - 1) by
            rw [Nat.mul_sub, Nat.mul_one], Nat.mul_div_cancel_left _ hLpos,
          Nat.mul_div_cancel_left _ hLpos]
    have hdiv : 2 ^ 256 / 2 ^ v = 2 ^ (256 - v) := by
      rw [← Nat.pow_div (by omega) (by norm_num)]
    have hge : 1 ≤ 2 ^ 256 / 2 ^ v := by rw [hdiv]; exact Nat.one_le_two_pow
    rw [hXnat, hq, show 1 + (2 ^ 256 / 2 ^ v - 1) = 2 ^ 256 / 2 ^ v by omega, hdiv]
    by_cases hv0 : v = 0
    · subst hv0
      exact Or.inr ⟨by norm_num, by simp⟩
    · left
      have hlt : 2 ^ (256 - v) < 2 ^ 256 := by
        apply Nat.pow_lt_pow_right (by norm_num); omega
      rw [Nat.mod_eq_of_lt hlt, ← pow_add]
      congr 1
      omega


/-! ## The limb decomposition of the dividend and the divisor -/

theorem mod_two_limbs (mem : ByteArray) (n mm : Nat) (hn : 2 ≤ n)
    (hmod : Model.FastRepresents mem 0 n mm) :
    (MachineState.readWord mem 0).toNat * (Limbs.radix * Limbs.radix ^ (n - 2)) +
      (MachineState.readWord mem 32).toNat * Limbs.radix ^ (n - 2) ≤ mm := by
  have h0 := Model.readWord_of_fastRepresents hmod (j := 0) (by omega)
  have h1 := Model.readWord_of_fastRepresents hmod (j := 1) (by omega)
  simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one, Nat.zero_add] at h0 h1
  rw [show n - 1 - 0 = n - 1 by omega] at h0
  rw [show n - 1 - 1 = n - 2 by omega] at h1
  have hP1 : Limbs.radix ^ (n - 2) * Limbs.radix = Limbs.radix ^ (n - 1) := by
    rw [← pow_succ]; congr 1; omega
  have hRn : Limbs.radix ^ (n - 1) * Limbs.radix = Limbs.radix ^ n := by
    rw [← pow_succ]; congr 1; omega
  have hmmlt : mm < Limbs.radix ^ (n - 1) * Limbs.radix := by rw [hRn]; exact hmod.1
  have hfit : mm / Limbs.radix ^ (n - 1) < Limbs.radix := Nat.div_lt_of_lt_mul hmmlt
  have hdd : mm / Limbs.radix ^ (n - 2) / Limbs.radix = mm / Limbs.radix ^ (n - 1) := by
    rw [Nat.div_div_eq_div_mul, hP1]
  have hkey : mm / Limbs.radix ^ (n - 1) * Limbs.radix +
      mm / Limbs.radix ^ (n - 2) % Limbs.radix = mm / Limbs.radix ^ (n - 2) := by
    rw [← hdd]
    exact Nat.div_add_mod' (mm / Limbs.radix ^ (n - 2)) Limbs.radix
  rw [h0, h1, Nat.mod_eq_of_lt hfit]
  have hfin : mm / Limbs.radix ^ (n - 1) * (Limbs.radix * Limbs.radix ^ (n - 2)) +
      mm / Limbs.radix ^ (n - 2) % Limbs.radix * Limbs.radix ^ (n - 2)
      = (mm / Limbs.radix ^ (n - 2)) * Limbs.radix ^ (n - 2) := by
    conv_rhs => rw [← hkey]
    ring
  rw [hfin]
  exact Nat.div_mul_le_self _ _

theorem tv_three_limbs (mem : ByteArray) (n : Nat) (hn : 2 ≤ n) :
    tv mem n < ((MachineState.readWord mem 2080).toNat * Limbs.radix +
        (MachineState.readWord mem 2112).toNat) * (Limbs.radix * Limbs.radix ^ (n - 2)) +
      ((MachineState.readWord mem 2144).toNat + 1) * Limbs.radix ^ (n - 2) := by
  have hlow := Csub.lowValue_succ mem 2112 n (n - 1)
  have hlow2 := Csub.lowValue_succ mem 2112 n (n - 2)
  have hlt := Csub.lowValue_lt mem 2112 n (n - 2)
  rw [show n - 1 + 1 = n by omega] at hlow
  rw [show n - 2 + 1 = n - 1 by omega] at hlow2
  rw [show n - 1 - (n - 1) = 0 by omega, Nat.mul_zero, Nat.add_zero] at hlow
  rw [show n - 1 - (n - 2) = 1 by omega, show 2112 + 32 * 1 = 2144 from rfl] at hlow2
  have hP1 : Limbs.radix ^ (n - 1) = Limbs.radix ^ (n - 2) * Limbs.radix := by
    rw [← pow_succ]; congr 1; omega
  have hPn : Limbs.radix ^ n = Limbs.radix ^ (n - 2) * Limbs.radix * Limbs.radix := by
    rw [← hP1, ← pow_succ]; congr 1; omega
  rw [tv_def, hlow, hlow2, hP1, hPn]
  nlinarith [hlt, Limbs.radix_pos]


/-! ## The estimator, unfolded -/

/-- The five words the estimator reads, as a predicate on memory. -/
def PreOK (mem : ByteArray) : Prop :=
  MachineState.readWord mem PRE_L = preL (MachineState.readWord mem 0) ∧
  MachineState.readWord mem PRE_DODD = preDodd (MachineState.readWord mem 0) ∧
  MachineState.readWord mem PRE_X = preX (MachineState.readWord mem 0) ∧
  MachineState.readWord mem PRE_BMOD = preBmod (MachineState.readWord mem 0) ∧
  MachineState.readWord mem PRE_DINV = preDinv (MachineState.readWord mem 0)

/-- `preMem` establishes the estimator words by construction. -/
theorem PreOK_preMem (mem : ByteArray) : PreOK (preMem mem) := by
  have hz : MachineState.readWord (preMem mem) 0 = MachineState.readWord mem 0 :=
    preMemOf_readWord_disjoint mem _ 0 (Or.inl (by simp only [PRE_L]; omega))
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> rw [hz] <;>
    show MachineState.readWord (preMemOf mem (MachineState.readWord mem 0)) _ = _ <;>
    (unfold preMemOf Exp.storeWord PRE_L PRE_DODD PRE_X PRE_BMOD PRE_DINV
     repeat rw [Csub.readWord_write_disjoint _ _ _ _ (by omega)]) <;>
    exact Challenge.EvmProof.Memory.readWord_writeWord _ _ _

theorem PreOK_uMem (mem : ByteArray) (n : Nat) (hn32 : n ≤ 8) (h : PreOK mem) :
    PreOK (uMem mem n) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have hz : MachineState.readWord (uMem mem n) 0 = MachineState.readWord mem 0 :=
    uMem_readWord_disjoint mem n 0 (Or.inl (by omega))
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [uMem_readWord_disjoint mem n PRE_L (Or.inl (by simp only [PRE_L]; omega)), hz]; exact h1
  · rw [uMem_readWord_disjoint mem n PRE_DODD (Or.inl (by simp only [PRE_DODD]; omega)), hz]
    exact h2
  · rw [uMem_readWord_disjoint mem n PRE_X (Or.inl (by simp only [PRE_X]; omega)), hz]; exact h3
  · rw [uMem_readWord_disjoint mem n PRE_BMOD (Or.inl (by simp only [PRE_BMOD]; omega)), hz]
    exact h4
  · rw [uMem_readWord_disjoint mem n PRE_DINV (Or.inl (by simp only [PRE_DINV]; omega)), hz]
    exact h5


/-- The estimator's own intermediate values, named so the proof can talk about them. -/
def eHi (mem : ByteArray) : UInt256 :=
  MachineState.readWord mem 2080 / MachineState.readWord mem PRE_L
def eLo (mem : ByteArray) : UInt256 :=
  MachineState.readWord mem 2112 / MachineState.readWord mem PRE_L +
    MachineState.readWord mem PRE_X * MachineState.readWord mem 2080
def eRho (mem : ByteArray) : UInt256 :=
  UInt256.addMod (UInt256.mulMod (eHi mem) (MachineState.readWord mem PRE_BMOD)
    (MachineState.readWord mem PRE_DODD)) (eLo mem) (MachineState.readWord mem PRE_DODD)
def eDiff (mem : ByteArray) : UInt256 := eLo mem - eRho mem
def eQ (mem : ByteArray) : UInt256 := MachineState.readWord mem PRE_DINV * eDiff mem
def eDec (mem : ByteArray) : UInt256 :=
  UInt256.gt (UInt256.shiftRight (eQ mem) (UInt256.ofNat 128) *
    UInt256.shiftRight (MachineState.readWord mem 32) (UInt256.ofNat 128))
    (MachineState.readWord mem 2112 - MachineState.readWord mem 0 * eQ mem)

theorem qhatOf_eq (mem : ByteArray) :
    qhatOf mem = UInt256.lor
      (UInt256.ofNat 0 -
        UInt256.isZero (UInt256.lt (eHi mem) (MachineState.readWord mem PRE_DODD)))
      (eQ mem - eDec mem) := rfl


/-! ## The estimator's pieces, in `Nat` -/

section Pieces
variable (mem : ByteArray)

theorem eHi_toNat (hPL : MachineState.readWord mem PRE_L = preL (MachineState.readWord mem 0)) :
    (eHi mem).toNat =
      (MachineState.readWord mem 2080).toNat / (preL (MachineState.readWord mem 0)).toNat := by
  show (MachineState.readWord mem 2080 / MachineState.readWord mem PRE_L).toNat = _
  rw [toNat_div, hPL]

theorem eLo_toNat (hPL : MachineState.readWord mem PRE_L = preL (MachineState.readWord mem 0))
    (hPX : MachineState.readWord mem PRE_X = preX (MachineState.readWord mem 0)) :
    (eLo mem).toNat =
      ((MachineState.readWord mem 2112).toNat / (preL (MachineState.readWord mem 0)).toNat +
        (preX (MachineState.readWord mem 0)).toNat * (MachineState.readWord mem 2080).toNat
          % 2 ^ 256) % 2 ^ 256 := by
  show (MachineState.readWord mem 2112 / MachineState.readWord mem PRE_L +
    MachineState.readWord mem PRE_X * MachineState.readWord mem 2080).toNat = _
  rw [word_toNat_add, toNat_div, Setup.word_toNat_mul, hPL, hPX]

theorem eRho_toNat
    (hPL : MachineState.readWord mem PRE_L = preL (MachineState.readWord mem 0))
    (hPD : MachineState.readWord mem PRE_DODD = preDodd (MachineState.readWord mem 0))
    (hPB : MachineState.readWord mem PRE_BMOD = preBmod (MachineState.readWord mem 0))
    (hdne : (preDodd (MachineState.readWord mem 0)).toNat ≠ 0) :
    (eRho mem).toNat =
      ((eHi mem).toNat * (preBmod (MachineState.readWord mem 0)).toNat
          % (preDodd (MachineState.readWord mem 0)).toNat + (eLo mem).toNat)
        % (preDodd (MachineState.readWord mem 0)).toNat := by
  show (UInt256.addMod (UInt256.mulMod (eHi mem) (MachineState.readWord mem PRE_BMOD)
    (MachineState.readWord mem PRE_DODD)) (eLo mem) (MachineState.readWord mem PRE_DODD)).toNat = _
  rw [toNat_addMod _ _ _ (by rw [hPD]; exact hdne),
      toNat_mulMod _ _ _ (by rw [hPD]; exact hdne), hPD, hPB]

theorem eDiff_toNat :
    (eDiff mem).toNat = (2 ^ 256 + (eLo mem).toNat - (eRho mem).toNat) % 2 ^ 256 := by
  show (eLo mem - eRho mem).toNat = _
  rw [word_toNat_sub]

theorem eQ_toNat (hPI : MachineState.readWord mem PRE_DINV = preDinv (MachineState.readWord mem 0)) :
    (eQ mem).toNat =
      (preDinv (MachineState.readWord mem 0)).toNat * (eDiff mem).toNat % 2 ^ 256 := by
  show (MachineState.readWord mem PRE_DINV * eDiff mem).toNat = _
  rw [Setup.word_toNat_mul, hPI]

end Pieces


/-! ## The estimator never under-shoots -/

theorem top_limb_ne_zero (mem : ByteArray) (n mm : Nat) (hn : 2 ≤ n)
    (htop : Limbs.radix ^ n < 2 * mm) (hmod : Model.FastRepresents mem 0 n mm) :
    (MachineState.readWord mem 0).toNat ≠ 0 := by
  have hmmlt : mm < Limbs.radix ^ n := hmod.1
  have hDval := Model.readWord_of_fastRepresents hmod (j := 0) (by omega)
  simp only [Nat.mul_zero, Nat.add_zero] at hDval
  rw [show n - 1 - 0 = n - 1 by omega] at hDval
  have hRn : Limbs.radix ^ (n - 1) * Limbs.radix = Limbs.radix ^ n := by
    rw [← pow_succ]; congr 1; omega
  have hfit : mm / Limbs.radix ^ (n - 1) < Limbs.radix :=
    Nat.div_lt_of_lt_mul (by rw [hRn]; exact hmmlt)
  rw [hDval, Nat.mod_eq_of_lt hfit]
  intro h
  have hpospow : 0 < Limbs.radix ^ (n - 1) := pow_pos Limbs.radix_pos _
  have hlt : mm < Limbs.radix ^ (n - 1) := by
    by_contra hc
    push_neg at hc
    have hd := Nat.div_pos hc hpospow
    omega
  have h2 : 2 * Limbs.radix ^ (n - 1) ≤ Limbs.radix ^ (n - 1) * Limbs.radix := by
    have : (2 : Nat) ≤ Limbs.radix := by
      have := Limbs.radix_gt_one; omega
    calc 2 * Limbs.radix ^ (n - 1) = Limbs.radix ^ (n - 1) * 2 := by ring
      _ ≤ Limbs.radix ^ (n - 1) * Limbs.radix := Nat.mul_le_mul_left _ this
  omega


theorem eDec_le_one (mem : ByteArray) : (eDec mem).toNat ≤ 1 := by
  show (UInt256.gt _ _).toNat ≤ 1
  rw [QHat.toNat_gt]
  split <;> omega

/-- The artifact's final quotient, as a branch on the saturation test. -/
theorem qhatOf_branch (mem : ByteArray)
    (hPD : MachineState.readWord mem PRE_DODD = preDodd (MachineState.readWord mem 0))
    (hdec : (eDec mem).toNat ≤ (eQ mem).toNat) :
    (qhatOf mem).toNat =
      if (eHi mem).toNat < (preDodd (MachineState.readWord mem 0)).toNat
      then (eQ mem).toNat - (eDec mem).toNat
      else 2 ^ 256 - 1 := by
  rw [qhatOf_eq, hPD]
  by_cases hs : (eHi mem).toNat < (preDodd (MachineState.readWord mem 0)).toNat
  · rw [if_pos hs]
    have hlt : UInt256.lt (eHi mem) (preDodd (MachineState.readWord mem 0)) = UInt256.ofNat 1 := by
      unfold UInt256.lt; rw [if_pos hs]
    rw [hlt]
    have hz : UInt256.isZero (UInt256.ofNat 1) = UInt256.ofNat 0 := by
      unfold UInt256.isZero; rw [if_neg (by simp)]
    rw [hz]
    have hsub : UInt256.ofNat 0 - UInt256.ofNat 0 = UInt256.ofNat 0 := by
      apply Challenge.EvmProof.Word.word_ext
      simp [word_toNat_sub, word_toNat_ofNat]
    rw [hsub, word_toNat_lor, word_toNat_ofNat]
    simp only [Nat.zero_mod, Nat.zero_or]
    rw [word_toNat_sub]
    have h1 : (eQ mem).toNat < 2 ^ 256 := (eQ mem).val.isLt
    have h2 : (eDec mem).toNat < 2 ^ 256 := (eDec mem).val.isLt
    omega
  · rw [if_neg hs]
    have hlt : UInt256.lt (eHi mem) (preDodd (MachineState.readWord mem 0)) = UInt256.ofNat 0 := by
      unfold UInt256.lt; rw [if_neg hs]
    rw [hlt]
    have hz : UInt256.isZero (UInt256.ofNat 0) = UInt256.ofNat 1 := by
      unfold UInt256.isZero; rw [if_pos (by simp)]
    rw [hz]
    have hsub : (UInt256.ofNat 0 - UInt256.ofNat 1).toNat = 2 ^ 256 - 1 := by
      rw [word_toNat_sub, word_toNat_ofNat, word_toNat_ofNat]
      norm_num
    rw [word_toNat_lor, hsub]
    exact QHat.or_two_pow_sub_one 256 _ (eQ mem - eDec mem).val.isLt


/-- **The estimator never under-shoots the true quotient.**  This is the fact the
conditional subtract after the limb pass was paying for at runtime. -/
theorem qhatOf_ge (mem : ByteArray) (n mm u : Nat)
    (hn : 2 ≤ n) (hn32 : n ≤ 8) (htop : Limbs.radix ^ n < 2 * mm)
    (hmod : Model.FastRepresents mem 0 n mm)
    (hpre : PreOK mem) (htv : tv mem n = u) (hu : u < mm * Limbs.radix) :
    u / mm ≤ (qhatOf mem).toNat := by
  obtain ⟨hPL, hPD, hPX, hPB, hPI⟩ := hpre
  have hR : Limbs.radix = 2 ^ 256 := rfl
  have hDne := top_limb_ne_zero mem n mm hn htop hmod
  obtain ⟨v, hv, hL, hmul, hodd, hdpos, hbmod, hXd⟩ :=
    pre_facts (MachineState.readWord mem 0) hDne
  have hmpos : 0 < mm := by omega
  -- abbreviations
  have hspos : (0:Nat) < 2 ^ v := Nat.two_pow_pos v
  have hsdvd : (2:Nat) ^ v ∣ 2 ^ 256 := pow_dvd_pow 2 (by omega)
  have hst : (2:Nat) ^ v * (2 ^ 256 / 2 ^ v) = 2 ^ 256 := Nat.mul_div_cancel' hsdvd
  have htpos : 0 < (2:Nat) ^ 256 / 2 ^ v := by
    rcases Nat.eq_zero_or_pos (2 ^ 256 / 2 ^ v) with h | h
    · rw [h, Nat.mul_zero] at hst; norm_num at hst
    · exact h
  -- the estimator's low word
  have hHi : (eHi mem).toNat = (MachineState.readWord mem 2080).toNat / 2 ^ v := by
    rw [eHi_toNat mem hPL, hL]
  have hLwlt : (MachineState.readWord mem 2112).toNat < 2 ^ 256 :=
    (MachineState.readWord mem 2112).val.isLt
  have hHlt : (MachineState.readWord mem 2080).toNat < 2 ^ 256 :=
    (MachineState.readWord mem 2080).val.isLt
  have hlorw : (MachineState.readWord mem 2112).toNat / 2 ^ v +
      (2 ^ 256 / 2 ^ v) * ((MachineState.readWord mem 2080).toNat % 2 ^ v) < 2 ^ 256 := by
    have h1 : (MachineState.readWord mem 2112).toNat / 2 ^ v < 2 ^ 256 / 2 ^ v := by
      apply Nat.div_lt_div_of_lt_of_dvd hsdvd hLwlt
    have h2 : (MachineState.readWord mem 2080).toNat % 2 ^ v < 2 ^ v := Nat.mod_lt _ hspos
    have h3 : (2 ^ 256 / 2 ^ v) * ((MachineState.readWord mem 2080).toNat % 2 ^ v)
        ≤ (2 ^ 256 / 2 ^ v) * (2 ^ v - 1) := Nat.mul_le_mul_left _ (by omega)
    have h4 : (2 ^ 256 / 2 ^ v) * (2 ^ v - 1) = 2 ^ 256 - 2 ^ 256 / 2 ^ v := by
      rw [Nat.mul_sub, Nat.mul_one, Nat.mul_comm, hst]
    have h5 : 2 ^ 256 / 2 ^ v ≤ 2 ^ 256 := Nat.div_le_self _ _
    omega
  have hLo : (eLo mem).toNat =
      (2 ^ 256 / 2 ^ v) * ((MachineState.readWord mem 2080).toNat % 2 ^ v) +
        (MachineState.readWord mem 2112).toNat / 2 ^ v := by
    rw [eLo_toNat mem hPL hPX, hL]
    rcases hXd with hX1 | ⟨hv1, hX0⟩
    · have hXt : (preX (MachineState.readWord mem 0)).toNat = 2 ^ 256 / 2 ^ v :=
        Nat.eq_of_mul_eq_mul_left hspos (by rw [hX1, hst])
      rw [hXt, QHat.mul_shift_mod (2 ^ 256) (2 ^ v) (2 ^ 256 / 2 ^ v)
        (MachineState.readWord mem 2080).toNat hspos htpos hst]
      rw [Nat.mod_eq_of_lt (by
        have := hlorw
        omega)]
      omega
    · rw [hX0, Nat.zero_mul, Nat.zero_mod]
      have hv0 : v = 0 := by
        by_contra hc
        have : (2:Nat) ^ 1 ≤ 2 ^ v := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      subst hv0
      simp only [pow_zero, Nat.div_one, Nat.mod_one, Nat.mul_zero, Nat.add_zero, Nat.zero_add]
      exact Nat.mod_eq_of_lt hLwlt
  -- the shifted two-word value
  have hsplit := QHat.shift_split (2 ^ 256) (2 ^ v) (2 ^ 256 / 2 ^ v)
      (MachineState.readWord mem 2080).toNat (MachineState.readWord mem 2112).toNat hspos hst
  have hRho : (eRho mem).toNat =
      (((MachineState.readWord mem 2080).toNat * 2 ^ 256 +
        (MachineState.readWord mem 2112).toNat) / 2 ^ v)
        % (preDodd (MachineState.readWord mem 0)).toNat := by
    rw [eRho_toNat mem hPL hPD hPB (by omega), hHi, hbmod, hLo, ← hsplit]
    have hcong : (MachineState.readWord mem 2080).toNat / 2 ^ v *
        (2 ^ 256 % (preDodd (MachineState.readWord mem 0)).toNat)
        ≡ (MachineState.readWord mem 2080).toNat / 2 ^ v * 2 ^ 256
          [MOD (preDodd (MachineState.readWord mem 0)).toNat] :=
      Nat.ModEq.mul_left _ (Nat.mod_modEq _ _)
    clear hcong
    rw [Nat.add_mod, Nat.add_mod ((MachineState.readWord mem 2080).toNat / 2 ^ v * 2 ^ 256)]
    congr 2
    simp [Nat.mul_mod]
  -- bounds on rho
  have hDlt : (MachineState.readWord mem 0).toNat < 2 ^ 256 :=
    (MachineState.readWord mem 0).val.isLt
  have hdoddle : (preDodd (MachineState.readWord mem 0)).toNat ≤
      (MachineState.readWord mem 0).toNat := by
    rw [← hmul]; exact Nat.le_mul_of_pos_left _ hspos
  have hrholt : (eRho mem).toNat < (preDodd (MachineState.readWord mem 0)).toNat := by
    rw [hRho]; exact Nat.mod_lt _ hdpos
  -- the word difference
  have hDiff : (eDiff mem).toNat ≡
      (eLo mem).toNat + (2 ^ 256 - (eRho mem).toNat) [MOD 2 ^ 256] := by
    rw [eDiff_toNat]
    have heq : 2 ^ 256 + (eLo mem).toNat - (eRho mem).toNat
        = (eLo mem).toNat + (2 ^ 256 - (eRho mem).toNat) := by omega
    rw [heq]
    exact Nat.mod_modEq _ _
  have hQval : (eQ mem).toNat =
      (preDinv (MachineState.readWord mem 0)).toNat * (eDiff mem).toNat % 2 ^ 256 :=
    eQ_toNat mem hPI
  -- the truncated-product test, in Nat
  have hshift : ∀ a : UInt256, (UInt256.shiftRight a (UInt256.ofNat 128)).toNat
      = a.toNat / 2 ^ 128 := by
    intro a
    rw [Challenge.EvmProof.Word.shiftRight_toNat a (by norm_num), Nat.shiftRight_eq_div_pow]
  have hprod : ((UInt256.shiftRight (eQ mem) (UInt256.ofNat 128) *
      UInt256.shiftRight (MachineState.readWord mem 32) (UInt256.ofNat 128)).toNat)
      = ((eQ mem).toNat / 2 ^ 128) * ((MachineState.readWord mem 32).toNat / 2 ^ 128) := by
    rw [Setup.word_toNat_mul, hshift, hshift]
    apply Nat.mod_eq_of_lt
    have h1 : (eQ mem).toNat / 2 ^ 128 < 2 ^ 128 :=
      Nat.div_lt_of_lt_mul (by rw [← pow_add]; exact (eQ mem).val.isLt)
    have h2 : (MachineState.readWord mem 32).toNat / 2 ^ 128 < 2 ^ 128 :=
      Nat.div_lt_of_lt_mul (by rw [← pow_add]; exact (MachineState.readWord mem 32).val.isLt)
    calc (eQ mem).toNat / 2 ^ 128 * ((MachineState.readWord mem 32).toNat / 2 ^ 128)
        < 2 ^ 128 * 2 ^ 128 := Nat.mul_lt_mul'' h1 h2
      _ = 2 ^ 256 := by rw [← pow_add]
  have hdecval : (eDec mem).toNat =
      if (MachineState.readWord mem 2112 - MachineState.readWord mem 0 * eQ mem).toNat <
        ((eQ mem).toNat / 2 ^ 128) * ((MachineState.readWord mem 32).toNat / 2 ^ 128)
      then 1 else 0 := by
    show (UInt256.gt _ _).toNat = _
    rw [QHat.toNat_gt, hprod]
  have hdec1 : (eDec mem).toNat = 1 → 2 ^ 128 ≤ (eQ mem).toNat := by
    intro h1
    rw [hdecval] at h1
    split at h1
    · rename_i hlt
      rcases Nat.eq_zero_or_pos ((eQ mem).toNat / 2 ^ 128) with h0 | hp
      · rw [h0, Nat.zero_mul] at hlt; omega
      · have hle := (Nat.le_div_iff_mul_le (Nat.two_pow_pos 128)).mp hp
        omega
    · omega
  -- the word remainder is the true remainder, in the non-saturated case
  have hrhatw : (eHi mem).toNat < (preDodd (MachineState.readWord mem 0)).toNat →
      (MachineState.readWord mem 2112 - MachineState.readWord mem 0 * eQ mem).toNat =
        ((MachineState.readWord mem 2080).toNat * 2 ^ 256 +
          (MachineState.readWord mem 2112).toNat) % (MachineState.readWord mem 0).toNat := by
    intro hsat
    rw [hHi] at hsat
    have hraw : (eQ mem).toNat =
        ((MachineState.readWord mem 2080).toNat * 2 ^ 256 +
          (MachineState.readWord mem 2112).toNat) / (MachineState.readWord mem 0).toNat := by
      rw [hQval]
      exact QHat.est_raw (2 ^ 256) (2 ^ v) (2 ^ 256 / 2 ^ v)
        (preDodd (MachineState.readWord mem 0)).toNat (MachineState.readWord mem 0).toNat
        (MachineState.readWord mem 2080).toNat (MachineState.readWord mem 2112).toNat
        (eRho mem).toNat (eDiff mem).toNat (preDinv (MachineState.readWord mem 0)).toNat
        hspos htpos hst hmul hdpos hHlt hLwlt hDlt hsat hRho (by rw [← hLo]; exact hDiff)
        (preDinv_inv (MachineState.readWord mem 0) hodd)
    set U := (MachineState.readWord mem 2080).toNat * 2 ^ 256 +
      (MachineState.readWord mem 2112).toNat with hU
    set D := (MachineState.readWord mem 0).toNat with hD
    have hdm : D * (U / D) + U % D = U := Nat.div_add_mod U D
    have hrlt : U % D < D := Nat.mod_lt _ (by omega)
    rw [word_toNat_sub, Setup.word_toNat_mul, hraw]
    have hXle : D * (U / D) % 2 ^ 256 < 2 ^ 256 := Nat.mod_lt _ (by norm_num)
    have hcong1 : D * (U / D) % 2 ^ 256 ≡ D * (U / D) [MOD 2 ^ 256] := Nat.mod_modEq _ _
    have hcanc : 2 ^ 256 + (MachineState.readWord mem 2112).toNat - D * (U / D) % 2 ^ 256
        + D * (U / D) % 2 ^ 256 = 2 ^ 256 + (MachineState.readWord mem 2112).toNat := by omega
    have hgoal : 2 ^ 256 + (MachineState.readWord mem 2112).toNat - D * (U / D) % 2 ^ 256
        ≡ U % D [MOD 2 ^ 256] := by
      apply Nat.ModEq.add_right_cancel' (D * (U / D) % 2 ^ 256)
      rw [hcanc]
      calc 2 ^ 256 + (MachineState.readWord mem 2112).toNat
          ≡ (MachineState.readWord mem 2112).toNat [MOD 2 ^ 256] := by
            unfold Nat.ModEq; simp
        _ ≡ (MachineState.readWord mem 2080).toNat * 2 ^ 256 +
              (MachineState.readWord mem 2112).toNat [MOD 2 ^ 256] := by
            unfold Nat.ModEq; simp [Nat.add_mul_mod_self_right, Nat.mul_mod_left]
        _ = U := by rw [hU]
        _ = D * (U / D) + U % D := hdm.symm
        _ ≡ U % D + D * (U / D) % 2 ^ 256 [MOD 2 ^ 256] := by
            unfold Nat.ModEq
            rw [Nat.add_mod (U % D) (D * (U / D) % 2 ^ 256), Nat.mod_mod,
              ← Nat.add_mod, Nat.add_comm]
    unfold Nat.ModEq at hgoal
    rw [hgoal, Nat.mod_eq_of_lt (by omega)]
  -- limb bounds
  have hmbound := mod_two_limbs mem n mm hn hmod
  have htvb := tv_three_limbs mem n hn
  rw [htv] at htvb
  simp only [Limbs.radix] at hmbound htvb hu
  have ha2lt : (MachineState.readWord mem 2144).toNat < 2 ^ 256 :=
    (MachineState.readWord mem 2144).val.isLt
  have hQ2pos : (0:Nat) < (2 ^ 256) ^ (n - 2) := pow_pos (by norm_num) _
  have hdecle : (eDec mem).toNat ≤ (eQ mem).toNat := by
    have h1 := eDec_le_one mem
    rcases Nat.lt_or_ge (eDec mem).toNat 1 with h | h
    · omega
    · have := hdec1 (by omega)
      have h128 : (1:Nat) ≤ 2 ^ 128 := Nat.one_le_two_pow
      omega
  have hbr := qhatOf_branch mem hPD hdecle
  rw [hHi, hQval] at hbr
  refine QHat.est_ge (2 ^ 256) (2 ^ v) (2 ^ 256 / 2 ^ v)
    (preDodd (MachineState.readWord mem 0)).toNat (MachineState.readWord mem 0).toNat
    (MachineState.readWord mem 32).toNat (MachineState.readWord mem 2144).toNat
    (MachineState.readWord mem 2080).toNat (MachineState.readWord mem 2112).toNat
    u mm (eRho mem).toNat (eDiff mem).toNat (preDinv (MachineState.readWord mem 0)).toNat
    ((2 ^ 256) ^ (n - 2)) ((qhatOf mem).toNat)
    (decide ((eDec mem).toNat = 1))
    hspos htpos hst hmul hdpos hHlt hLwlt hDlt hQ2pos (by omega)
    hRho (by rw [← hLo]; exact hDiff) (preDinv_inv (MachineState.readWord mem 0) hodd)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact htvb
  · have h1 : ((MachineState.readWord mem 2144).toNat + 1) * (2 ^ 256) ^ (n - 2)
        ≤ 2 ^ 256 * (2 ^ 256) ^ (n - 2) := Nat.mul_le_mul_right _ (by omega)
    nlinarith [htvb, h1]
  · exact hmbound
  · nlinarith [hmbound]
  · exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm] at hu ⊢; exact hu)
  · intro hsat hc
    have hr := hrhatw (by rw [hHi]; exact hsat)
    have hd1 : (eDec mem).toNat = 1 := of_decide_eq_true hc
    rw [hdecval] at hd1
    split at hd1
    · rename_i hlt
      rw [hr] at hlt
      have := QHat.trunc_gt (2 ^ 256) (2 ^ 128) (eQ mem).toNat
        (MachineState.readWord mem 32).toNat
        (((MachineState.readWord mem 2080).toNat * 2 ^ 256 +
          (MachineState.readWord mem 2112).toNat) % (MachineState.readWord mem 0).toNat)
        (MachineState.readWord mem 2144).toNat (by rw [← pow_add]) ha2lt hlt
      rw [hQval] at this
      exact this
    · omega
  · rw [hbr]
    congr 1
    have h1 := eDec_le_one mem
    by_cases hd : (eDec mem).toNat = 1
    · rw [hd]; simp [hd]
    · have : (eDec mem).toNat = 0 := by omega
      rw [this]; simp [hd]

end QHatGe

/-- The value-side facts of one step: the repair facts and the result. -/
theorem step_spec (mem : ByteArray) (n mm r : Nat)
    (hn : 2 ≤ n) (hn32 : n ≤ 8) (hmpos : 0 < mm) (hmm : mm < Limbs.radix ^ n)
    (htop : Limbs.radix ^ n < 2 * mm)
    (hmod : Model.FastRepresents mem 0 n mm)
    (hneg : Model.FastRepresents mem NEG n (Limbs.radix ^ n - mm))
    (hbase : Model.FastRepresents mem 2112 n r) (hr : r < mm) (hpre : PreOK mem) :
    RepairFacts
      (midMem (macOf (uMem mem n) n (qhatOf (uMem mem n))).memory
        (macOf (uMem mem n) n (qhatOf (uMem mem n))).carry (qhatOf (uMem mem n)))
      n mm
      (negOf (macOf (uMem mem n) n (qhatOf (uMem mem n))).memory
        (macOf (uMem mem n) n (qhatOf (uMem mem n))).carry (qhatOf (uMem mem n))) ∧
    Model.FastRepresents (stepMem mem n mm) 2112 n (r * Limbs.radix % mm) := by
  have hmodU : Model.FastRepresents (uMem mem n) 0 n mm := by
    refine (Model.fastRepresents_congr ?_ mm).2 hmod
    intro i hi
    exact uMem_readWord_disjoint mem n _ (Or.inl (by omega))
  have hnegU : Model.FastRepresents (uMem mem n) NEG n (Limbs.radix ^ n - mm) := by
    refine (Model.fastRepresents_congr ?_ _).2 hneg
    intro i hi
    exact uMem_readWord_disjoint mem n _ (Or.inl (by unfold NEG; omega))
  have hu : tv (uMem mem n) n = r * Limbs.radix := uMem_tv mem n r hn hn32 hbase
  have hulo : r * Limbs.radix < Limbs.radix ^ (n + 1) := by
    rw [pow_succ]
    exact Nat.mul_lt_mul_of_pos_right (lt_trans hr hmm) Limbs.radix_pos
  obtain ⟨hrel, hltmid, hneg1⟩ :=
    mid_relation (uMem mem n) n mm (qhatOf (uMem mem n)) (r * Limbs.radix) hn hn32 hmm hmodU
      hnegU hu hulo
  have hmodMid : Model.FastRepresents
      (midMem (macOf (uMem mem n) n (qhatOf (uMem mem n))).memory
        (macOf (uMem mem n) n (qhatOf (uMem mem n))).carry (qhatOf (uMem mem n))) 0 n mm := by
    refine (Model.fastRepresents_congr ?_ mm).2 hmodU
    intro i hi
    show MachineState.readWord (Exp.storeWord _ 2080 _) _ = _
    unfold Exp.storeWord
    rw [Csub.readWord_write_disjoint _ _ _ _ (by omega)]
    exact mac_readWord_disjoint (uMem mem n) n _ _ (by omega) (Or.inl (by omega))
  obtain ⟨rf, hcong, hltP, htn⟩ :=
    repair_spec _ n mm _ (r * Limbs.radix) (qhatOf (uMem mem n)).toNat (by omega) hn32 hmpos hmm
      hmodMid hrel hltmid hneg1
  refine ⟨rf, ?_⟩
  show Model.FastRepresents (fixMem
    (midMem (macOf (uMem mem n) n (qhatOf (uMem mem n))).memory
      (macOf (uMem mem n) n (qhatOf (uMem mem n))).carry (qhatOf (uMem mem n))) n mm
    (negOf (macOf (uMem mem n) n (qhatOf (uMem mem n))).memory
      (macOf (uMem mem n) n (qhatOf (uMem mem n))).carry (qhatOf (uMem mem n))))
    2112 n (r * Limbs.radix % mm)
  set fix := fixMem
    (midMem (macOf (uMem mem n) n (qhatOf (uMem mem n))).memory
      (macOf (uMem mem n) n (qhatOf (uMem mem n))).carry (qhatOf (uMem mem n))) n mm
    (negOf (macOf (uMem mem n) n (qhatOf (uMem mem n))).memory
      (macOf (uMem mem n) n (qhatOf (uMem mem n))).carry (qhatOf (uMem mem n))) with hfixv
  have hlowFix : Model.FastRepresents fix 2112 n (Csub.lowValue fix 2112 n n) :=
    Csub.fastRepresents_lowValue _ _ _
  have htvFix : tv fix n = Csub.lowValue fix 2112 n n := by
    rw [tv_def, htn]; simp
  -- the estimate never under-shoots, so the repair lands strictly below the modulus
  have hqge : (r * Limbs.radix) / mm ≤ (qhatOf (uMem mem n)).toNat :=
    qhatOf_ge (uMem mem n) n mm (r * Limbs.radix) hn hn32 htop hmodU
      (PreOK_uMem mem n hn32 hpre) hu
      (Nat.mul_lt_mul_of_pos_right hr Limbs.radix_pos)
  have hltmm : tv fix n < mm := by
    rw [hfixv]
    exact repair_lt_mm _ n mm _ (r * Limbs.radix) (qhatOf (uMem mem n)).toNat
      (by omega) hn32 hmpos hmm hmodMid hrel hltmid hneg1 hqge
  have heq : Csub.lowValue fix 2112 n n = r * Limbs.radix % mm := by
    rw [← htvFix, ← hcong, Nat.mod_eq_of_lt hltmm]
  rw [heq] at hlowFix
  exact hlowFix

theorem stepMem_represents (mem : ByteArray) (n mm r : Nat)
    (hn : 2 ≤ n) (hn32 : n ≤ 8) (hmpos : 0 < mm) (hmm : mm < Limbs.radix ^ n)
    (htop : Limbs.radix ^ n < 2 * mm)
    (hmod : Model.FastRepresents mem 0 n mm)
    (hneg : Model.FastRepresents mem NEG n (Limbs.radix ^ n - mm))
    (hbase : Model.FastRepresents mem 2112 n r) (hr : r < mm) (hpre : PreOK mem) :
    Model.FastRepresents (stepMem mem n mm) 2112 n (r * Limbs.radix % mm) :=
  (step_spec mem n mm r hn hn32 hmpos hmm htop hmod hneg hbase hr hpre).2

theorem stepMems_modulus (mem : ByteArray) (n mm : Nat) (hn : 1 ≤ n) (hn32 : n ≤ 8)
    (hmod : Model.FastRepresents mem 0 n mm) :
    ∀ k, Model.FastRepresents (stepMems mem n mm k) 0 n mm := by
  intro k
  induction k with
  | zero => exact hmod
  | succ k ih =>
      exact fastRepresents_stepMem _ n mm 0 n mm hn
        ⟨Or.inl (by omega), Or.inl (by omega), Or.inl (by omega)⟩ ih

theorem stepMems_neg (mem : ByteArray) (n mm : Nat) (hn : 1 ≤ n) (hn32 : n ≤ 8)
    (hneg : Model.FastRepresents mem NEG n (Limbs.radix ^ n - mm)) :
    ∀ k, Model.FastRepresents (stepMems mem n mm k) NEG n (Limbs.radix ^ n - mm) := by
  intro k
  induction k with
  | zero => exact hneg
  | succ k ih =>
      exact fastRepresents_stepMem _ n mm NEG n _ hn
        ⟨Or.inr (by unfold NEG; omega), Or.inl (by unfold NEG; omega),
          Or.inl (by unfold NEG; omega)⟩ ih

/-- The five estimator words survive a step: they lie outside everything it writes. -/
theorem PreOK_stepMem (mem : ByteArray) (n mm : Nat) (hn : 1 ≤ n) (hn32 : n ≤ 8)
    (h : PreOK mem) : PreOK (stepMem mem n mm) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have hz : MachineState.readWord (stepMem mem n mm) 0 = MachineState.readWord mem 0 :=
    stepMem_readWord_disjoint mem n mm 0 hn
      ⟨Or.inl (by omega), Or.inl (by omega), Or.inl (by omega)⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [stepMem_readWord_disjoint mem n mm PRE_L hn
      ⟨Or.inr (by simp only [PRE_L]; omega), Or.inl (by simp only [PRE_L]; omega),
        Or.inl (by simp only [PRE_L]; omega)⟩, hz]
    exact h1
  · rw [stepMem_readWord_disjoint mem n mm PRE_DODD hn
      ⟨Or.inr (by simp only [PRE_DODD]; omega), Or.inl (by simp only [PRE_DODD]; omega),
        Or.inl (by simp only [PRE_DODD]; omega)⟩, hz]
    exact h2
  · rw [stepMem_readWord_disjoint mem n mm PRE_X hn
      ⟨Or.inr (by simp only [PRE_X]; omega), Or.inl (by simp only [PRE_X]; omega),
        Or.inl (by simp only [PRE_X]; omega)⟩, hz]
    exact h3
  · rw [stepMem_readWord_disjoint mem n mm PRE_BMOD hn
      ⟨Or.inr (by simp only [PRE_BMOD]; omega), Or.inl (by simp only [PRE_BMOD]; omega),
        Or.inl (by simp only [PRE_BMOD]; omega)⟩, hz]
    exact h4
  · rw [stepMem_readWord_disjoint mem n mm PRE_DINV hn
      ⟨Or.inr (by simp only [PRE_DINV]; omega), Or.inl (by simp only [PRE_DINV]; omega),
        Or.inl (by simp only [PRE_DINV]; omega)⟩, hz]
    exact h5

theorem PreOK_stepMems (mem : ByteArray) (n mm : Nat) (hn : 1 ≤ n) (hn32 : n ≤ 8)
    (h : PreOK mem) : ∀ k, PreOK (stepMems mem n mm k) := by
  intro k
  induction k with
  | zero => exact h
  | succ k ih => exact PreOK_stepMem _ n mm hn hn32 ih

/-- **`k` steps multiply `BASE` by `radix ^ k` modulo `m`.** -/
theorem stepMems_represents (mem : ByteArray) (n mm r : Nat)
    (hn : 2 ≤ n) (hn32 : n ≤ 8) (hmpos : 0 < mm) (hmm : mm < Limbs.radix ^ n)
    (htop : Limbs.radix ^ n < 2 * mm)
    (hmod : Model.FastRepresents mem 0 n mm)
    (hneg : Model.FastRepresents mem NEG n (Limbs.radix ^ n - mm))
    (hbase : Model.FastRepresents mem 2112 n r) (hr : r < mm) (hpre : PreOK mem) :
    ∀ k, Model.FastRepresents (stepMems mem n mm k) 2112 n (r * Limbs.radix ^ k % mm) := by
  intro k
  induction k with
  | zero =>
      simp only [stepMems, pow_zero, Nat.mul_one]
      rw [Nat.mod_eq_of_lt hr]; exact hbase
  | succ k ih =>
      show Model.FastRepresents (stepMem (stepMems mem n mm k) n mm) 2112 n _
      have h := stepMem_represents (stepMems mem n mm k) n mm _ hn (by omega) hmpos hmm htop
        (stepMems_modulus mem n mm (by omega) hn32 hmod k) (stepMems_neg mem n mm (by omega) hn32 hneg k)
        ih (Nat.mod_lt _ hmpos) (PreOK_stepMems mem n mm (by omega) hn32 hpre k)
      have heq : r * Limbs.radix ^ k % mm * Limbs.radix % mm =
          r * Limbs.radix ^ (k + 1) % mm := by
        rw [pow_succ, ← Nat.mul_assoc, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]
      rw [← heq]
      exact h

theorem stepMems_readWord_disjoint (mem : ByteArray) (n mm addr : Nat) (hn : 1 ≤ n)
    (hdisj : (addr + 32 ≤ 512 ∨ 512 + 32 * n ≤ addr) ∧
      (addr + 32 ≤ 1792 ∨ 1792 + 32 * n ≤ addr) ∧
      (addr + 32 ≤ 2080 ∨ 2112 + 32 * n ≤ addr)) :
    ∀ k, MachineState.readWord (stepMems mem n mm k) addr = MachineState.readWord mem addr := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih => exact (stepMem_readWord_disjoint _ n mm addr hn hdisj).trans ih

end Challenge.Modexp.Submission.Proofs.Fast.Shift
