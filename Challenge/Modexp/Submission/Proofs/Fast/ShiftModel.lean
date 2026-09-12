import Challenge.Modexp.Submission.Proofs.Fast.Monpro
import Challenge.Modexp.Submission.Proofs.Fast.FullBaseLogic
import Challenge.Modexp.Submission.Proofs.Fast.Exp
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
def NEG : Nat := 5120
/-- Per-modulus words of the quotient estimator (the former `RR` block). -/
def PRE_L : Nat := 6144
def PRE_DODD : Nat := 6176
def PRE_X : Nat := 6208
def PRE_BMOD : Nat := 6240
def PRE_DINV : Nat := 6272

/-! ## Phase 1: the raw base into `ACC` and `TS` -/

/-- `ACC := base`, `TS := base`, `TN := 0`. -/
def hitMem (mem input : ByteArray) (n : Nat) : ByteArray :=
  Exp.storeWord
    (MachineState.writeBytes (FullBase.copyBaseMem mem input n)
      (MachineState.readPadded input 96 (32 * n)) 8256)
    8224 (UInt256.ofNat 0)

/-! ## Phase 2: `NEG := radix ^ n - m`, least significant limb first -/

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
  newtonW d (newtonW d (newtonW d (newtonW d (UInt256.ofNat 1))))

def newton8W (d : UInt256) : UInt256 :=
  newtonW d (newtonW d (newtonW d (newtonW d (newton4W d))))

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
  Exp.storeWord (Exp.mcopyMem mem 8224 2048 (32 * n)) (8224 + 32 * n) (UInt256.ofNat 0)

/-- The quotient guess, exactly as the `ESTIMATE` block computes it.  Its value
is irrelevant to correctness. -/
def qhatOf (mem : ByteArray) : UInt256 :=
  let utop := MachineState.readWord mem 2048
  let L := MachineState.readWord mem PRE_L
  let hi := utop / L
  let r := utop % L
  let X := MachineState.readWord mem PRE_X
  let xr := X * r
  let unext := MachineState.readWord mem 2080
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
  UInt256.lor (UInt256.ofNat 0 - overflow)
    (q - UInt256.land
      (UInt256.isZero (UInt256.isZero q))
      (UInt256.gt (MachineState.readWord mem 32)
        (unext - MachineState.readWord mem 0 * q)))

/-- The limb pass `t += q * NEG` is exactly a CIOS first loop with `a = NEG`. -/
def macOf (mem : ByteArray) (n : Nat) (q : UInt256) : Monpro.MacState :=
  Monpro.l1Step mem q NEG n n

/-! ### The middle block -/

def wN (mem : ByteArray) (c : UInt256) : UInt256 := c + MachineState.readWord mem 8224
def cwOf (mem : ByteArray) (c : UInt256) : UInt256 := UInt256.lt (wN mem c) c
def tnOf (mem : ByteArray) (c q : UInt256) : UInt256 := wN mem c - q
def bwOf (mem : ByteArray) (c q : UInt256) : UInt256 := UInt256.lt (wN mem c) q
def negOf (mem : ByteArray) (c q : UInt256) : UInt256 := UInt256.gt (bwOf mem c q) (cwOf mem c)
def midMem (mem : ByteArray) (c q : UInt256) : ByteArray :=
  Exp.storeWord mem 8224 (tnOf mem c q)

/-! ### The repair rounds -/

/-- One limb of `t += m`, in place, least significant limb first. -/
def addStep (mem : ByteArray) (n : Nat) : Nat → Csub.LimbState
  | 0 => ⟨mem, UInt256.ofNat 0⟩
  | j + 1 =>
      let prev := addStep mem n j
      let t := MachineState.readWord prev.memory (8256 + 32 * (n - 1 - j))
      let md := MachineState.readWord prev.memory (32 * (n - 1 - j))
      let s1 := t + md
      let c1 := UInt256.gt t s1
      let s2 := prev.flag + s1
      let c2 := UInt256.gt prev.flag s2
      { memory := MachineState.writeBytes prev.memory
          (Data.Bytes.natToBytesPadded s2.toNat 32) (8256 + 32 * (n - 1 - j))
        flag := UInt256.lor c2 c1 }

/-- The carry into `TN` after a full add pass. -/
def addCarry (mem : ByteArray) (n : Nat) : UInt256 := (addStep mem n n).flag

/-- Memory after one whole add round: the pass and `TN += carry`. -/
def addRoundMem (mem : ByteArray) (n : Nat) : ByteArray :=
  Exp.storeWord (addStep mem n n).memory 8224
    (addCarry mem n + MachineState.readWord (addStep mem n n).memory 8224)

/-- The carry out of `TN` in that round: the round is the last one iff it is `1`. -/
def addOut (mem : ByteArray) (n : Nat) : UInt256 :=
  UInt256.lt (addCarry mem n + MachineState.readWord (addStep mem n n).memory 8224)
    (addCarry mem n)

def addRounds (mem : ByteArray) (n : Nat) : Nat → ByteArray
  | 0 => mem
  | k + 1 => addRoundMem (addRounds mem n k) n

/-- One limb of `t -= m`, in place, least significant limb first. -/
def subStep (mem : ByteArray) (n : Nat) : Nat → Csub.LimbState
  | 0 => ⟨mem, UInt256.ofNat 0⟩
  | j + 1 =>
      let prev := subStep mem n j
      let t := MachineState.readWord prev.memory (8256 + 32 * (n - 1 - j))
      let md := MachineState.readWord prev.memory (32 * (n - 1 - j))
      let b1 := UInt256.gt md t
      let d1 := t - md
      let b2 := UInt256.lt d1 prev.flag
      let d2 := d1 - prev.flag
      { memory := MachineState.writeBytes prev.memory
          (Data.Bytes.natToBytesPadded d2.toNat 32) (8256 + 32 * (n - 1 - j))
        flag := UInt256.lor b2 b1 }

def subBorrow (mem : ByteArray) (n : Nat) : UInt256 := (subStep mem n n).flag

/-- Memory after one whole subtract round: the pass and `TN -= borrow`. -/
def subRoundMem (mem : ByteArray) (n : Nat) : ByteArray :=
  Exp.storeWord (subStep mem n n).memory 8224
    (MachineState.readWord (subStep mem n n).memory 8224 - subBorrow mem n)

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
  Csub.csResultMemory (fixMem mid n mm neg) n 2048

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
    tv mem n = (MachineState.readWord mem 8224).toNat * Limbs.radix ^ n +
      Csub.lowValue mem 8256 n n := rfl

theorem tn_ne_zero_iff (mem : ByteArray) (n : Nat) :
    (MachineState.readWord mem 8224).toNat ≠ 0 ↔ Limbs.radix ^ n ≤ tv mem n := by
  rw [tv_def]
  have hlow := Csub.lowValue_lt mem 8256 n n
  constructor
  · intro h
    have : 1 ≤ (MachineState.readWord mem 8224).toNat := by omega
    nlinarith
  · intro h hz
    rw [hz] at h
    omega

theorem tn_zero_of_lt (mem : ByteArray) (n : Nat) (h : tv mem n < Limbs.radix ^ n) :
    (MachineState.readWord mem 8224).toNat = 0 := by
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
theorem negStep_invariant (mem : ByteArray) (n : Nat) (hn32 : n ≤ 32) :
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

theorem neg_represents (mem : ByteArray) (n mm : Nat) (hn : 1 ≤ n) (hn32 : n ≤ 32)
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
    (hdisj : addr + 32 ≤ 8224 ∨ 8256 + 32 * n ≤ addr) :
    MachineState.readWord (uMem mem n) addr = MachineState.readWord mem addr := by
  unfold uMem Exp.storeWord Exp.mcopyMem
  rw [Csub.readWord_write_disjoint _ _ _ _ (by omega)]
  rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint _ _ _ _
    (by rw [Challenge.EvmProof.Memory.readPadded_size]; omega)]

/-- The word of `u` at `TN`: the top limb of `r`. -/
theorem uMem_readWord_tn (mem : ByteArray) (n : Nat) (hn : 1 ≤ n) :
    MachineState.readWord (uMem mem n) 8224 = MachineState.readWord mem 2048 := by
  unfold uMem Exp.storeWord Exp.mcopyMem
  rw [Csub.readWord_write_disjoint _ _ _ _ (by omega)]
  have h := Csub.readWord_mcopy mem 2048 8224 (32 * n) 0 (by omega)
  simpa using h

/-- The limbs of `u` inside `TS`: limb `j` of `u` is limb `j - 1` of `r`, and
limb `0` is zero. -/
theorem uMem_readWord_limb (mem : ByteArray) (n k : Nat) (hn : 1 ≤ n) (hk : k < n) :
    MachineState.readWord (uMem mem n) (8256 + 32 * (n - 1 - k)) =
      if k = 0 then UInt256.ofNat 0
      else MachineState.readWord mem (2048 + 32 * (n - 1 - (k - 1))) := by
  unfold uMem Exp.storeWord Exp.mcopyMem
  by_cases hk0 : k = 0
  · subst hk0
    rw [if_pos rfl]
    have h : 8256 + 32 * (n - 1 - 0) = 8224 + 32 * n := by omega
    rw [h]
    exact Challenge.EvmProof.Memory.readWord_writeWord _ _ _
  · rw [if_neg hk0]
    rw [Csub.readWord_write_disjoint _ _ _ _ (by omega)]
    have h : 8256 + 32 * (n - 1 - k) = 8224 + 32 * (n - k) := by omega
    rw [h]
    have hm := Csub.readWord_mcopy mem 2048 8224 (32 * n) (n - k) (by omega)
    rw [hm]
    congr 1
    omega

/-- The `TS` limbs of `u` are the limbs of `r` shifted up by one, so their value
below limb `j + 1` is `radix * (r mod radix ^ j)`. -/
theorem uMem_lowValue (mem : ByteArray) (n r : Nat) (hn : 1 ≤ n)
    (hrep : Model.FastRepresents mem 2048 n r) :
    ∀ j, j + 1 ≤ n →
      Csub.lowValue (uMem mem n) 8256 n (j + 1) = Limbs.radix * (r % Limbs.radix ^ j) := by
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

theorem uMem_tv (mem : ByteArray) (n r : Nat) (hn : 2 ≤ n) (hn32 : n ≤ 32)
    (hrep : Model.FastRepresents mem 2048 n r) :
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

theorem mac_value (mem : ByteArray) (n : Nat) (q : UInt256) (a : Nat) (hn32 : n ≤ 32)
    (hneg : Model.FastRepresents mem NEG n a) :
    Csub.lowValue (macOf mem n q).memory 8256 n n +
        (macOf mem n q).carry.toNat * Limbs.radix ^ n =
      Csub.lowValue mem 8256 n n + q.toNat * a := by
  have h := Monpro.l1_row mem q NEG n (Csub.lowValue mem 8256 n n) a hn32
    (by unfold NEG; omega) hneg (Csub.fastRepresents_lowValue mem 8256 n)
  have hsum : Monpro.limbSum (fun k => (Monpro.l1Val mem q NEG n k).toNat) n =
      Csub.lowValue (Monpro.l1Step mem q NEG n n).memory 8256 n n := by
    rw [← Monpro.limbSum_eq_lowValue]
    apply Monpro.limbSum_congr
    intro k hk
    rw [show 8256 + 32 * (n - 1 - k) = Monpro.tAddr n k from rfl,
      Monpro.readWord_l1Step_val mem q NEG n k hn32 hk (by unfold NEG; omega) n hk le_rfl]
  unfold macOf
  rw [← hsum]
  exact h

theorem l1Step_readWord_disjoint (mem : ByteArray) (bi : UInt256) (pa n addr : Nat)
    (hn : 1 ≤ n) (hdisj : addr + 32 ≤ 8256 ∨ 8256 + 32 * n ≤ addr) :
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
    (hn : 1 ≤ n) (hdisj : addr + 32 ≤ 8256 ∨ 8256 + 32 * n ≤ addr) :
    MachineState.readWord (macOf mem n q).memory addr = MachineState.readWord mem addr :=
  l1Step_readWord_disjoint mem q NEG n addr hn hdisj n

/-- The middle block: the signed relation `u + neg * radix^(n+1) = q * m + t`. -/
theorem mid_relation (mem : ByteArray) (n mm : Nat) (q : UInt256) (u : Nat)
    (hn : 2 ≤ n) (hn32 : n ≤ 32) (hmm : mm < Limbs.radix ^ n)
    (hmod : Model.FastRepresents mem 0 n mm)
    (hneg : Model.FastRepresents mem NEG n (Limbs.radix ^ n - mm))
    (hu : tv mem n = u) (hulo : u < Limbs.radix ^ (n + 1)) :
    u + (negOf (macOf mem n q).memory (macOf mem n q).carry q).toNat * Limbs.radix ^ (n + 1) =
        q.toNat * mm + tv (midMem (macOf mem n q).memory (macOf mem n q).carry q) n ∧
      tv (midMem (macOf mem n q).memory (macOf mem n q).carry q) n < Limbs.radix ^ (n + 1) ∧
      (negOf (macOf mem n q).memory (macOf mem n q).carry q).toNat ≤ 1 := by
  have hmac := mac_value mem n q (Limbs.radix ^ n - mm) hn32 hneg
  have hTN : MachineState.readWord (macOf mem n q).memory 8224 =
      MachineState.readWord mem 8224 :=
    mac_readWord_disjoint mem n 8224 q (by omega) (Or.inl (by omega))
  have hW := add_carry_spec (macOf mem n q).carry (MachineState.readWord mem 8224)
  have hT := sub_borrow_spec ((macOf mem n q).carry + MachineState.readWord mem 8224) q
  have hlowMid : Csub.lowValue (midMem (macOf mem n q).memory (macOf mem n q).carry q)
      8256 n n = Csub.lowValue (macOf mem n q).memory 8256 n n := by
    apply Csub.lowValue_congr
    intro k hk
    unfold midMem Exp.storeWord
    exact Csub.readWord_write_disjoint _ _ _ _ (by omega)
  have htnMid : MachineState.readWord (midMem (macOf mem n q).memory (macOf mem n q).carry q)
      8224 = (macOf mem n q).carry + MachineState.readWord mem 8224 - q := by
    unfold midMem Exp.storeWord tnOf wN
    rw [Challenge.EvmProof.Memory.readWord_writeWord, hTN]
  have htv : tv (midMem (macOf mem n q).memory (macOf mem n q).carry q) n =
      ((macOf mem n q).carry + MachineState.readWord mem 8224 - q).toNat * Limbs.radix ^ n +
        Csub.lowValue (macOf mem n q).memory 8256 n n := by
    rw [tv_def, htnMid, hlowMid]
  have hu' : (MachineState.readWord mem 8224).toNat * Limbs.radix ^ n +
      Csub.lowValue mem 8256 n n = u := by rw [← hu, tv_def]
  have hnegv : (negOf (macOf mem n q).memory (macOf mem n q).carry q).toNat =
      if (UInt256.lt ((macOf mem n q).carry + MachineState.readWord mem 8224)
            (macOf mem n q).carry).toNat <
          (UInt256.lt ((macOf mem n q).carry + MachineState.readWord mem 8224) q).toNat
        then 1 else 0 := by
    unfold negOf bwOf cwOf wN
    rw [gt_toNat, hTN]
  have hTnlt : ((macOf mem n q).carry + MachineState.readWord mem 8224 - q).toNat <
      Limbs.radix := ((macOf mem n q).carry + MachineState.readWord mem 8224 - q).val.isLt
  have hlow'lt : Csub.lowValue (macOf mem n q).memory 8256 n n < Limbs.radix ^ n :=
    Csub.lowValue_lt _ _ _ _
  have hR' : Limbs.radix ^ (n + 1) = Limbs.radix ^ n * Limbs.radix := pow_succ _ _
  have hqa : q.toNat * (Limbs.radix ^ n - mm) + q.toNat * mm = q.toNat * Limbs.radix ^ n := by
    rw [← Nat.mul_add, Nat.sub_add_cancel (le_of_lt hmm)]
  have hW1 := hW.1
  have hT1 := hT.1
  have hcw1 := hW.2
  have hbw1 := hT.2
  -- the key identity: u + bw R' = t + q m + cw R'
  have hkey : u + (UInt256.lt ((macOf mem n q).carry + MachineState.readWord mem 8224)
        q).toNat * (Limbs.radix ^ n * Limbs.radix) =
      ((macOf mem n q).carry + MachineState.readWord mem 8224 - q).toNat * Limbs.radix ^ n +
        Csub.lowValue (macOf mem n q).memory 8256 n n + q.toNat * mm +
        (UInt256.lt ((macOf mem n q).carry + MachineState.readWord mem 8224)
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
    have h1 : ((macOf mem n q).carry + MachineState.readWord mem 8224 - q).toNat *
        Limbs.radix ^ n + Csub.lowValue (macOf mem n q).memory 8256 n n <
        (((macOf mem n q).carry + MachineState.readWord mem 8224 - q).toNat + 1) *
          Limbs.radix ^ n := by
      rw [Nat.succ_mul]; omega
    have h2 : (((macOf mem n q).carry + MachineState.readWord mem 8224 - q).toNat + 1) *
        Limbs.radix ^ n ≤ Limbs.radix * Limbs.radix ^ n :=
      Nat.mul_le_mul_right _ hTnlt
    rw [Nat.mul_comm (Limbs.radix ^ n) Limbs.radix]
    omega
  · rw [hnegv]; split <;> omega

/-! ## The repair rounds -/

theorem addStep_readWord_disjoint (mem : ByteArray) (n addr : Nat)
    (hdisj : addr + 32 ≤ 8256 ∨ 8256 + 32 * n ≤ addr) :
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
    ∀ j, j ≤ k → MachineState.readWord (addStep mem n j).memory (8256 + 32 * (n - 1 - k)) =
      MachineState.readWord mem (8256 + 32 * (n - 1 - k)) := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
      intro hj
      have hstep : MachineState.readWord (addStep mem n (j + 1)).memory
          (8256 + 32 * (n - 1 - k)) =
          MachineState.readWord (addStep mem n j).memory (8256 + 32 * (n - 1 - k)) := by
        simp only [addStep]
        exact Csub.readWord_write_disjoint _ _ _ _ (by omega)
      rw [hstep, ih (by omega)]

theorem addStep_lowValue_stable (mem : ByteArray) (n j : Nat) (hj : j < n) :
    Csub.lowValue (addStep mem n (j + 1)).memory 8256 n j =
      Csub.lowValue (addStep mem n j).memory 8256 n j := by
  apply Csub.lowValue_congr
  intro k hk
  simp only [addStep]
  exact Csub.readWord_write_disjoint _ _ _ _ (by omega)

theorem addStep_readWord_new (mem : ByteArray) (n j : Nat) :
    MachineState.readWord (addStep mem n (j + 1)).memory (8256 + 32 * (n - 1 - j)) =
      (addStep mem n j).flag +
        (MachineState.readWord (addStep mem n j).memory (8256 + 32 * (n - 1 - j)) +
          MachineState.readWord (addStep mem n j).memory (32 * (n - 1 - j))) := by
  simp only [addStep]
  exact Challenge.EvmProof.Memory.readWord_writeWord _ _ _

theorem addStep_flag_succ (mem : ByteArray) (n j : Nat) :
    (addStep mem n (j + 1)).flag =
      UInt256.lor
        (UInt256.gt (addStep mem n j).flag ((addStep mem n j).flag +
          (MachineState.readWord (addStep mem n j).memory (8256 + 32 * (n - 1 - j)) +
            MachineState.readWord (addStep mem n j).memory (32 * (n - 1 - j)))))
        (UInt256.gt (MachineState.readWord (addStep mem n j).memory (8256 + 32 * (n - 1 - j)))
          (MachineState.readWord (addStep mem n j).memory (8256 + 32 * (n - 1 - j)) +
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

theorem addStep_invariant (mem : ByteArray) (n : Nat) (hn32 : n ≤ 32) :
    ∀ j, j ≤ n →
      Csub.lowValue (addStep mem n j).memory 8256 n j +
          (addStep mem n j).flag.toNat * Limbs.radix ^ j =
        Csub.lowValue mem 8256 n j + Csub.lowValue mem 0 n j ∧
        (addStep mem n j).flag.toNat ≤ 1 := by
  intro j
  induction j with
  | zero => intro _; simp [addStep]
  | succ j ih =>
      intro hj
      obtain ⟨ihEq, ihLe⟩ := ih (by omega)
      have hxt : MachineState.readWord (addStep mem n j).memory (8256 + 32 * (n - 1 - j)) =
          MachineState.readWord mem (8256 + 32 * (n - 1 - j)) :=
        addStep_readWord_keep mem n j (by omega) j le_rfl
      have hxm : MachineState.readWord (addStep mem n j).memory (32 * (n - 1 - j)) =
          MachineState.readWord mem (32 * (n - 1 - j)) :=
        addStep_readWord_disjoint mem n _ (Or.inl (by omega)) j (by omega)
      have hlimb := addLimb_spec' (MachineState.readWord mem (8256 + 32 * (n - 1 - j)))
        (MachineState.readWord mem (32 * (n - 1 - j))) (addStep mem n j).flag ihLe
      rw [Csub.lowValue_succ (addStep mem n (j + 1)).memory 8256 n j,
        addStep_lowValue_stable mem n j (by omega),
        addStep_readWord_new, addStep_flag_succ,
        Csub.lowValue_succ mem 8256 n j, Csub.lowValue_succ mem 0 n j, pow_succ]
      simp only [Nat.zero_add, hxt, hxm]
      exact ⟨Csub.am_algebra _ _ _ _ _ _ _ _ _ _ hlimb.1 ihEq, hlimb.2⟩

theorem addRound_value (mem : ByteArray) (n mm : Nat) (hn : 1 ≤ n) (hn32 : n ≤ 32)
    (hmod : Model.FastRepresents mem 0 n mm) :
    tv (addRoundMem mem n) n + (addOut mem n).toNat * Limbs.radix ^ (n + 1) =
      tv mem n + mm ∧ (addOut mem n).toNat ≤ 1 := by
  obtain ⟨hinv, hle⟩ := addStep_invariant mem n hn32 n le_rfl
  have hM : Csub.lowValue mem 0 n n = mm := by
    rw [Csub.lowValue_full]; exact Model.value_of_fastRepresents hmod
  rw [hM] at hinv
  have htn : MachineState.readWord (addStep mem n n).memory 8224 =
      MachineState.readWord mem 8224 :=
    addStep_readWord_disjoint mem n 8224 (Or.inl (by omega)) n le_rfl
  have hcarry := add_carry_spec (addStep mem n n).flag
    (MachineState.readWord (addStep mem n n).memory 8224)
  unfold addOut addCarry
  rw [tv_def, tv_def]
  unfold addRoundMem addCarry Exp.storeWord
  rw [Challenge.EvmProof.Memory.readWord_writeWord]
  have hlow : Csub.lowValue (MachineState.writeBytes (addStep mem n n).memory
      (Data.Bytes.natToBytesPadded (((addStep mem n n).flag +
        MachineState.readWord (addStep mem n n).memory 8224).toNat) 32) 8224) 8256 n n =
      Csub.lowValue (addStep mem n n).memory 8256 n n := by
    apply Csub.lowValue_congr
    intro k hk
    exact Csub.readWord_write_disjoint _ _ _ _ (by omega)
  rw [hlow, htn]
  rw [htn] at hcarry
  refine ⟨?_, hcarry.2⟩
  rw [pow_succ]
  have hc' : (((addStep mem n n).flag + MachineState.readWord mem 8224).toNat +
      (UInt256.lt ((addStep mem n n).flag + MachineState.readWord mem 8224)
        (addStep mem n n).flag).toNat * Limbs.radix) * Limbs.radix ^ n =
      ((addStep mem n n).flag.toNat + (MachineState.readWord mem 8224).toNat) * Limbs.radix ^ n :=
    by rw [hcarry.1]
  nlinarith [hc', hinv]

theorem addRoundMem_readWord_disjoint (mem : ByteArray) (n addr : Nat)
    (hdisj : addr + 32 ≤ 8224 ∨ 8256 + 32 * n ≤ addr) :
    MachineState.readWord (addRoundMem mem n) addr = MachineState.readWord mem addr := by
  unfold addRoundMem Exp.storeWord
  rw [Csub.readWord_write_disjoint _ _ _ _ (by omega)]
  exact addStep_readWord_disjoint mem n addr (by omega) n le_rfl

theorem subStep_readWord_disjoint (mem : ByteArray) (n addr : Nat)
    (hdisj : addr + 32 ≤ 8256 ∨ 8256 + 32 * n ≤ addr) :
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
    ∀ j, j ≤ k → MachineState.readWord (subStep mem n j).memory (8256 + 32 * (n - 1 - k)) =
      MachineState.readWord mem (8256 + 32 * (n - 1 - k)) := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
      intro hj
      have hstep : MachineState.readWord (subStep mem n (j + 1)).memory
          (8256 + 32 * (n - 1 - k)) =
          MachineState.readWord (subStep mem n j).memory (8256 + 32 * (n - 1 - k)) := by
        simp only [subStep]
        exact Csub.readWord_write_disjoint _ _ _ _ (by omega)
      rw [hstep, ih (by omega)]

theorem subStep_lowValue_stable (mem : ByteArray) (n j : Nat) (hj : j < n) :
    Csub.lowValue (subStep mem n (j + 1)).memory 8256 n j =
      Csub.lowValue (subStep mem n j).memory 8256 n j := by
  apply Csub.lowValue_congr
  intro k hk
  simp only [subStep]
  exact Csub.readWord_write_disjoint _ _ _ _ (by omega)

theorem subStep_readWord_new (mem : ByteArray) (n j : Nat) :
    MachineState.readWord (subStep mem n (j + 1)).memory (8256 + 32 * (n - 1 - j)) =
      MachineState.readWord (subStep mem n j).memory (8256 + 32 * (n - 1 - j)) -
        MachineState.readWord (subStep mem n j).memory (32 * (n - 1 - j)) -
        (subStep mem n j).flag := by
  simp only [subStep]
  exact Challenge.EvmProof.Memory.readWord_writeWord _ _ _

theorem subStep_flag_succ (mem : ByteArray) (n j : Nat) :
    (subStep mem n (j + 1)).flag =
      UInt256.lor
        (UInt256.lt (MachineState.readWord (subStep mem n j).memory (8256 + 32 * (n - 1 - j)) -
            MachineState.readWord (subStep mem n j).memory (32 * (n - 1 - j)))
          (subStep mem n j).flag)
        (UInt256.gt (MachineState.readWord (subStep mem n j).memory (32 * (n - 1 - j)))
          (MachineState.readWord (subStep mem n j).memory (8256 + 32 * (n - 1 - j)))) := by
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

theorem subStep_invariant (mem : ByteArray) (n : Nat) (hn32 : n ≤ 32) :
    ∀ j, j ≤ n →
      Csub.lowValue (subStep mem n j).memory 8256 n j + Csub.lowValue mem 0 n j =
        Csub.lowValue mem 8256 n j + (subStep mem n j).flag.toNat * Limbs.radix ^ j ∧
        (subStep mem n j).flag.toNat ≤ 1 := by
  intro j
  induction j with
  | zero => intro _; simp [subStep]
  | succ j ih =>
      intro hj
      obtain ⟨ihEq, ihLe⟩ := ih (by omega)
      have hxt : MachineState.readWord (subStep mem n j).memory (8256 + 32 * (n - 1 - j)) =
          MachineState.readWord mem (8256 + 32 * (n - 1 - j)) :=
        subStep_readWord_keep mem n j (by omega) j le_rfl
      have hxm : MachineState.readWord (subStep mem n j).memory (32 * (n - 1 - j)) =
          MachineState.readWord mem (32 * (n - 1 - j)) :=
        subStep_readWord_disjoint mem n _ (Or.inl (by omega)) j (by omega)
      have hlimb := subLimb_spec' (MachineState.readWord mem (8256 + 32 * (n - 1 - j)))
        (MachineState.readWord mem (32 * (n - 1 - j))) (subStep mem n j).flag ihLe
      rw [Csub.lowValue_succ (subStep mem n (j + 1)).memory 8256 n j,
        subStep_lowValue_stable mem n j (by omega),
        subStep_readWord_new, subStep_flag_succ,
        Csub.lowValue_succ mem 0 n j, Csub.lowValue_succ mem 8256 n j, pow_succ]
      simp only [Nat.zero_add, hxt, hxm]
      exact ⟨Csub.cs_algebra _ _ _ _ _ _ _ _ _ _ hlimb.1 ihEq, hlimb.2⟩

theorem subRound_value (mem : ByteArray) (n mm : Nat) (hn : 1 ≤ n) (hn32 : n ≤ 32)
    (hmod : Model.FastRepresents mem 0 n mm)
    (htn : (MachineState.readWord mem 8224).toNat ≠ 0) :
    tv (subRoundMem mem n) n + mm = tv mem n := by
  obtain ⟨hinv, hle⟩ := subStep_invariant mem n hn32 n le_rfl
  have hM : Csub.lowValue mem 0 n n = mm := by
    rw [Csub.lowValue_full]; exact Model.value_of_fastRepresents hmod
  rw [hM] at hinv
  have htn' : MachineState.readWord (subStep mem n n).memory 8224 =
      MachineState.readWord mem 8224 :=
    subStep_readWord_disjoint mem n 8224 (Or.inl (by omega)) n le_rfl
  have hborrow := (sub_borrow_spec (MachineState.readWord (subStep mem n n).memory 8224)
    (subStep mem n n).flag).1
  rw [tv_def, tv_def]
  unfold subRoundMem subBorrow Exp.storeWord
  rw [Challenge.EvmProof.Memory.readWord_writeWord]
  have hlow : Csub.lowValue (MachineState.writeBytes (subStep mem n n).memory
      (Data.Bytes.natToBytesPadded ((MachineState.readWord (subStep mem n n).memory 8224 -
        (subStep mem n n).flag).toNat) 32) 8224) 8256 n n =
      Csub.lowValue (subStep mem n n).memory 8256 n n := by
    apply Csub.lowValue_congr
    intro k hk
    exact Csub.readWord_write_disjoint _ _ _ _ (by omega)
  rw [hlow, htn']
  rw [htn'] at hborrow
  have hnb : (UInt256.lt (MachineState.readWord mem 8224) (subStep mem n n).flag).toNat = 0 := by
    rw [Challenge.EvmProof.Word.word_toNat_lt]
    rw [if_neg]; omega
  rw [hnb, Nat.zero_mul, Nat.add_zero] at hborrow
  have hb' : ((MachineState.readWord mem 8224 - (subStep mem n n).flag).toNat +
      (subStep mem n n).flag.toNat) * Limbs.radix ^ n =
      (MachineState.readWord mem 8224).toNat * Limbs.radix ^ n := by rw [hborrow]
  nlinarith [hb', hinv]

theorem subRoundMem_readWord_disjoint (mem : ByteArray) (n addr : Nat)
    (hdisj : addr + 32 ≤ 8224 ∨ 8256 + 32 * n ≤ addr) :
    MachineState.readWord (subRoundMem mem n) addr = MachineState.readWord mem addr := by
  unfold subRoundMem Exp.storeWord
  rw [Csub.readWord_write_disjoint _ _ _ _ (by omega)]
  exact subStep_readWord_disjoint mem n addr (by omega) n le_rfl

/-! ### Rounds -/

theorem addRounds_readWord_disjoint (mem : ByteArray) (n addr : Nat)
    (hdisj : addr + 32 ≤ 8224 ∨ 8256 + 32 * n ≤ addr) :
    ∀ k, MachineState.readWord (addRounds mem n k) addr = MachineState.readWord mem addr := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih => exact (addRoundMem_readWord_disjoint _ n addr hdisj).trans ih

theorem subRounds_readWord_disjoint (mem : ByteArray) (n addr : Nat)
    (hdisj : addr + 32 ≤ 8224 ∨ 8256 + 32 * n ≤ addr) :
    ∀ k, MachineState.readWord (subRounds mem n k) addr = MachineState.readWord mem addr := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih => exact (subRoundMem_readWord_disjoint _ n addr hdisj).trans ih

theorem fastRepresents_addRounds (mem : ByteArray) (n ptr cnt v : Nat)
    (hdisj : ptr + 32 * cnt ≤ 8224 ∨ 8256 + 32 * n ≤ ptr)
    (hrep : Model.FastRepresents mem ptr cnt v) (k : Nat) :
    Model.FastRepresents (addRounds mem n k) ptr cnt v := by
  refine (Model.fastRepresents_congr ?_ v).2 hrep
  intro i hi
  exact addRounds_readWord_disjoint mem n _ (by omega) k

theorem fastRepresents_subRounds (mem : ByteArray) (n ptr cnt v : Nat)
    (hdisj : ptr + 32 * cnt ≤ 8224 ∨ 8256 + 32 * n ≤ ptr)
    (hrep : Model.FastRepresents mem ptr cnt v) (k : Nat) :
    Model.FastRepresents (subRounds mem n k) ptr cnt v := by
  refine (Model.fastRepresents_congr ?_ v).2 hrep
  intro i hi
  exact subRounds_readWord_disjoint mem n _ (by omega) k

/-- Add rounds without a carry out: the value grows by `m` each round. -/
theorem addRounds_value (mem : ByteArray) (n mm : Nat) (hn : 1 ≤ n) (hn32 : n ≤ 32)
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
theorem addRounds_last (mem : ByteArray) (n mm k : Nat) (hn : 1 ≤ n) (hn32 : n ≤ 32)
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
    have hlow := Csub.lowValue_lt (addRoundMem (addRounds mem n k) n) 8256 n n
    have hlt' : tv (addRoundMem (addRounds mem n k) n) n < Limbs.radix ^ (n + 1) := by
      rw [tv_def, pow_succ]
      have htn : (MachineState.readWord (addRoundMem (addRounds mem n k) n) 8224).toNat <
          Limbs.radix := (MachineState.readWord _ 8224).val.isLt
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
theorem subRounds_value (mem : ByteArray) (n mm : Nat) (hn : 1 ≤ n) (hn32 : n ≤ 32)
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
      have htn : (MachineState.readWord (subRounds mem n i) 8224).toNat ≠ 0 := by
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
      (subRounds (addRounds mid n (addCount mid n mm neg)) n i) 8224).toNat ≠ 0
  subDoneTn : (MachineState.readWord (fixMem mid n mm neg) 8224).toNat = 0
  negCount : neg = UInt256.ofNat 1 → 1 ≤ addCount mid n mm neg
  posCount : neg = UInt256.ofNat 0 → addCount mid n mm neg = 0

/-- The subtract phase from a non-negative value: rounds while the top limb is
nonzero, ending below `radix ^ n`. -/
theorem subPhase_spec (mem : ByteArray) (n mm : Nat) (hn : 1 ≤ n) (hn32 : n ≤ 32)
    (hmpos : 0 < mm) (hmod : Model.FastRepresents mem 0 n mm) :
    (∀ i, i < subCount mem n mm →
      (MachineState.readWord (subRounds mem n i) 8224).toNat ≠ 0) ∧
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
    (hn : 1 ≤ n) (hn32 : n ≤ 32) (hmpos : 0 < mm) (hmm : mm < Limbs.radix ^ n)
    (hmod : Model.FastRepresents mem 0 n mm)
    (hrel : u + neg.toNat * Limbs.radix ^ (n + 1) = q * mm + tv mem n)
    (hlt : tv mem n < Limbs.radix ^ (n + 1)) (hneg : neg.toNat ≤ 1) :
    RepairFacts mem n mm neg ∧
      tv (fixMem mem n mm neg) n % mm = u % mm ∧
      tv (fixMem mem n mm neg) n < Limbs.radix ^ n ∧
      (MachineState.readWord (fixMem mem n mm neg) 8224).toNat = 0 := by
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

theorem fixMem_value (mem : ByteArray) (n mm : Nat) (neg : UInt256) (u q : Nat)
    (hn : 1 ≤ n) (hn32 : n ≤ 32) (hmpos : 0 < mm) (hmm : mm < Limbs.radix ^ n)
    (hmod : Model.FastRepresents mem 0 n mm)
    (hrel : u + neg.toNat * Limbs.radix ^ (n + 1) = q * mm + tv mem n)
    (hlt : tv mem n < Limbs.radix ^ (n + 1)) (hneg : neg.toNat ≤ 1) :
    tv (fixMem mem n mm neg) n % mm = u % mm ∧
      tv (fixMem mem n mm neg) n < Limbs.radix ^ n ∧
      (MachineState.readWord (fixMem mem n mm neg) 8224).toNat = 0 :=
  (repair_spec mem n mm neg u q hn hn32 hmpos hmm hmod hrel hlt hneg).2

theorem fixMem_readWord_disjoint (mem : ByteArray) (n mm : Nat) (neg : UInt256) (addr : Nat)
    (hdisj : addr + 32 ≤ 8224 ∨ 8256 + 32 * n ≤ addr) :
    MachineState.readWord (fixMem mem n mm neg) addr = MachineState.readWord mem addr := by
  unfold fixMem
  rw [subRounds_readWord_disjoint _ n addr hdisj, addRounds_readWord_disjoint _ n addr hdisj]

/-! ### The whole step -/

/-- Words the step leaves alone. -/
theorem stepMem_readWord_disjoint (mem : ByteArray) (n mm addr : Nat) (hn : 1 ≤ n)
    (hdisj : (addr + 32 ≤ 2048 ∨ 2048 + 32 * n ≤ addr) ∧
      (addr + 32 ≤ 7168 ∨ 7168 + 32 * n ≤ addr) ∧
      (addr + 32 ≤ 8224 ∨ 8256 + 32 * n ≤ addr)) :
    MachineState.readWord (stepMem mem n mm) addr = MachineState.readWord mem addr := by
  unfold stepMem
  simp only
  rw [Monpro.csResultMemory_readWord_outside _ n 2048 addr hn hdisj.2.1 hdisj.1,
    fixMem_readWord_disjoint _ n mm _ addr hdisj.2.2]
  show MachineState.readWord (Exp.storeWord _ 8224 _) addr = _
  unfold Exp.storeWord
  rw [Csub.readWord_write_disjoint _ _ _ _ (by omega)]
  rw [mac_readWord_disjoint _ n addr _ hn (by omega)]
  exact uMem_readWord_disjoint mem n addr hdisj.2.2

theorem fastRepresents_stepMem (mem : ByteArray) (n mm ptr cnt v : Nat) (hn : 1 ≤ n)
    (hdisj : (ptr + 32 * cnt ≤ 2048 ∨ 2048 + 32 * n ≤ ptr) ∧
      (ptr + 32 * cnt ≤ 7168 ∨ 7168 + 32 * n ≤ ptr) ∧
      (ptr + 32 * cnt ≤ 8224 ∨ 8256 + 32 * n ≤ ptr))
    (hrep : Model.FastRepresents mem ptr cnt v) :
    Model.FastRepresents (stepMem mem n mm) ptr cnt v := by
  refine (Model.fastRepresents_congr ?_ v).2 hrep
  intro i hi
  exact stepMem_readWord_disjoint mem n mm _ hn (by omega)

/-- The value-side facts of one step: the repair facts and the result. -/
theorem step_spec (mem : ByteArray) (n mm r : Nat)
    (hn : 2 ≤ n) (hn32 : n ≤ 32) (hmpos : 0 < mm) (hmm : mm < Limbs.radix ^ n)
    (htop : Limbs.radix ^ n < 2 * mm)
    (hmod : Model.FastRepresents mem 0 n mm)
    (hneg : Model.FastRepresents mem NEG n (Limbs.radix ^ n - mm))
    (hbase : Model.FastRepresents mem 2048 n r) (hr : r < mm) :
    RepairFacts
      (midMem (macOf (uMem mem n) n (qhatOf (uMem mem n))).memory
        (macOf (uMem mem n) n (qhatOf (uMem mem n))).carry (qhatOf (uMem mem n)))
      n mm
      (negOf (macOf (uMem mem n) n (qhatOf (uMem mem n))).memory
        (macOf (uMem mem n) n (qhatOf (uMem mem n))).carry (qhatOf (uMem mem n))) ∧
    Model.FastRepresents (stepMem mem n mm) 2048 n (r * Limbs.radix % mm) := by
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
    show MachineState.readWord (Exp.storeWord _ 8224 _) _ = _
    unfold Exp.storeWord
    rw [Csub.readWord_write_disjoint _ _ _ _ (by omega)]
    exact mac_readWord_disjoint (uMem mem n) n _ _ (by omega) (Or.inl (by omega))
  obtain ⟨rf, hcong, hltP, htn⟩ :=
    repair_spec _ n mm _ (r * Limbs.radix) (qhatOf (uMem mem n)).toNat (by omega) hn32 hmpos hmm
      hmodMid hrel hltmid hneg1
  refine ⟨rf, ?_⟩
  show Model.FastRepresents (Csub.csResultMemory (fixMem
    (midMem (macOf (uMem mem n) n (qhatOf (uMem mem n))).memory
      (macOf (uMem mem n) n (qhatOf (uMem mem n))).carry (qhatOf (uMem mem n))) n mm
    (negOf (macOf (uMem mem n) n (qhatOf (uMem mem n))).memory
      (macOf (uMem mem n) n (qhatOf (uMem mem n))).carry (qhatOf (uMem mem n)))) n 2048)
    2048 n (r * Limbs.radix % mm)
  set fix := fixMem
    (midMem (macOf (uMem mem n) n (qhatOf (uMem mem n))).memory
      (macOf (uMem mem n) n (qhatOf (uMem mem n))).carry (qhatOf (uMem mem n))) n mm
    (negOf (macOf (uMem mem n) n (qhatOf (uMem mem n))).memory
      (macOf (uMem mem n) n (qhatOf (uMem mem n))).carry (qhatOf (uMem mem n))) with hfixv
  have hmodFix : Model.FastRepresents fix 0 n mm := by
    rw [hfixv]
    refine (Model.fastRepresents_congr ?_ mm).2 hmodMid
    intro i hi
    exact fixMem_readWord_disjoint _ n mm _ _ (Or.inl (by omega))
  have hlowFix : Model.FastRepresents fix 8256 n (Csub.lowValue fix 8256 n n) :=
    Csub.fastRepresents_lowValue _ _ _
  have htvFix : tv fix n = Csub.lowValue fix 8256 n n := by
    rw [tv_def, htn]; simp
  have hbound : 0 * Limbs.radix ^ n + Csub.lowValue fix 8256 n n < 2 * mm := by
    rw [Nat.zero_mul, Nat.zero_add, ← htvFix]
    exact lt_trans hltP htop
  have hres := Csub.csub_correct fix n _ mm 0 2048 hn hn32 hlowFix hmodFix htn
    (Nat.zero_le 1) hmpos hbound
  rw [Nat.zero_mul, Nat.zero_add, ← htvFix, hcong] at hres
  exact hres

theorem stepMem_represents (mem : ByteArray) (n mm r : Nat)
    (hn : 2 ≤ n) (hn32 : n ≤ 32) (hmpos : 0 < mm) (hmm : mm < Limbs.radix ^ n)
    (htop : Limbs.radix ^ n < 2 * mm)
    (hmod : Model.FastRepresents mem 0 n mm)
    (hneg : Model.FastRepresents mem NEG n (Limbs.radix ^ n - mm))
    (hbase : Model.FastRepresents mem 2048 n r) (hr : r < mm) :
    Model.FastRepresents (stepMem mem n mm) 2048 n (r * Limbs.radix % mm) :=
  (step_spec mem n mm r hn hn32 hmpos hmm htop hmod hneg hbase hr).2

theorem stepMems_modulus (mem : ByteArray) (n mm : Nat) (hn : 1 ≤ n) (hn32 : n ≤ 32)
    (hmod : Model.FastRepresents mem 0 n mm) :
    ∀ k, Model.FastRepresents (stepMems mem n mm k) 0 n mm := by
  intro k
  induction k with
  | zero => exact hmod
  | succ k ih =>
      exact fastRepresents_stepMem _ n mm 0 n mm hn
        ⟨Or.inl (by omega), Or.inl (by omega), Or.inl (by omega)⟩ ih

theorem stepMems_neg (mem : ByteArray) (n mm : Nat) (hn : 1 ≤ n) (hn32 : n ≤ 32)
    (hneg : Model.FastRepresents mem NEG n (Limbs.radix ^ n - mm)) :
    ∀ k, Model.FastRepresents (stepMems mem n mm k) NEG n (Limbs.radix ^ n - mm) := by
  intro k
  induction k with
  | zero => exact hneg
  | succ k ih =>
      exact fastRepresents_stepMem _ n mm NEG n _ hn
        ⟨Or.inr (by unfold NEG; omega), Or.inl (by unfold NEG; omega),
          Or.inl (by unfold NEG; omega)⟩ ih

/-- **`k` steps multiply `BASE` by `radix ^ k` modulo `m`.** -/
theorem stepMems_represents (mem : ByteArray) (n mm r : Nat)
    (hn : 2 ≤ n) (hn32 : n ≤ 32) (hmpos : 0 < mm) (hmm : mm < Limbs.radix ^ n)
    (htop : Limbs.radix ^ n < 2 * mm)
    (hmod : Model.FastRepresents mem 0 n mm)
    (hneg : Model.FastRepresents mem NEG n (Limbs.radix ^ n - mm))
    (hbase : Model.FastRepresents mem 2048 n r) (hr : r < mm) :
    ∀ k, Model.FastRepresents (stepMems mem n mm k) 2048 n (r * Limbs.radix ^ k % mm) := by
  intro k
  induction k with
  | zero =>
      simp only [stepMems, pow_zero, Nat.mul_one]
      rw [Nat.mod_eq_of_lt hr]; exact hbase
  | succ k ih =>
      show Model.FastRepresents (stepMem (stepMems mem n mm k) n mm) 2048 n _
      have h := stepMem_represents (stepMems mem n mm k) n mm _ hn hn32 hmpos hmm htop
        (stepMems_modulus mem n mm (by omega) hn32 hmod k) (stepMems_neg mem n mm (by omega) hn32 hneg k)
        ih (Nat.mod_lt _ hmpos)
      have heq : r * Limbs.radix ^ k % mm * Limbs.radix % mm =
          r * Limbs.radix ^ (k + 1) % mm := by
        rw [pow_succ, ← Nat.mul_assoc, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]
      rw [← heq]
      exact h

theorem stepMems_readWord_disjoint (mem : ByteArray) (n mm addr : Nat) (hn : 1 ≤ n)
    (hdisj : (addr + 32 ≤ 2048 ∨ 2048 + 32 * n ≤ addr) ∧
      (addr + 32 ≤ 7168 ∨ 7168 + 32 * n ≤ addr) ∧
      (addr + 32 ≤ 8224 ∨ 8256 + 32 * n ≤ addr)) :
    ∀ k, MachineState.readWord (stepMems mem n mm k) addr = MachineState.readWord mem addr := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih => exact (stepMem_readWord_disjoint _ n mm addr hn hdisj).trans ih

end Challenge.Modexp.Submission.Proofs.Fast.Shift
