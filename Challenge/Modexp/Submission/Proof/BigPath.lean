import Challenge.Modexp.Submission.Proof.BigBase
import Challenge.Modexp.Submission.Proof.BigSer
import Challenge.Modexp.Submission.Proof.MulModProof
import Mathlib.Tactic

set_option warningAsError true
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false

/-!
# The MODEXP big path: the value-dependent exponent loop and the main theorem

`secBigPath`'s tail, from the exponent scan (`bbExpRest`, the continuation the
base reduction hands over) through the serialize jump: the leading-zero scan
of the exponent bytes, the top-bit find in the first nonzero byte, the
accumulator seed, and the MSB-first square-and-multiply over the remaining
exponent bits — the only part of the program whose control flow depends on
the operand *values* rather than their sizes.

The square-and-multiply body is four inlined `mulModFrag`s. Three of them
(the two multiplies, `ACC := ACC · BASE`) are covered by
`MulModProof.mulModFrag_correct`. The fourth kind — the square
`mulModFrag ACC …`, whose multiplier region *is* the accumulator region —
falls outside that theorem's region-disjointness hypotheses (`hbAcc`), so
this module first re-proves the bits phase for that shape
(`mulBitsSq_steps`) and packages it as `mulModSq_correct`, reusing every
phase lemma of `MulModBase` (none of which needs the disjointness; only the
composed `mulModFrag_correct`/`mulBits_steps` do).

Value invariant (MSB-first): with `B = b % m` in the BASE region and the
exponent `e` the big-endian value of its `esize` bytes, at each loop head the
ACC region holds `B ^ (e / 2 ^ q) % m` where `q` is the number of
not-yet-processed low exponent bits. Each bit round squares (and
conditionally multiplies by `B`), halving the pending quotient; the exit at
`q = 0` leaves `B ^ e % m`, which `BigSer.big_ser_ret` serializes and returns.

`bigPath_correct` composes `Header.header_big`, `BigLoad`'s load/scan chain,
`BigBase.big_base`, the exponent phase below, and the two serialize outcomes
(zero and nonzero modulus) into the `msize > 32` case of the full run.
-/

namespace Challenge.Modexp.Submission.Proof.BigPath

open YulEvmCompiler
open YulSemantics.EVM (U256 EvmState wordFrom byteFrom byteAt loadWord storeWord
  storeByte readBytes touchMemory activeWordsAfter b2w)
open Challenge.Modexp.Submission (Expr store storeAt storeAt8 jumpIfNz jumpIfZ
  jumpUnlessLt cdbCell bitTest compileExpr loadAt evalExpr exprOK
  BS ES MS BO EO MO Ncell Icell I2 Jcell Wcell T0 T1 T2 RET TOP ONE ACC BASE MOD OUT
  SUBC HIcell C1 C2 AOFF AX AY AS AZ
  programAsm programLabels secWordPath secBigPath secHalt secHeader
  localModel addModFrag mulModFrag ProgLabels AddModLabels MulModLabels)
open Challenge.Modexp.Submission.Proof.Header
open Challenge.Modexp.Submission.Proof.BigLoad
open Challenge.Modexp.Submission.Proof.BigBase
open Challenge.Modexp.Submission.Proof.BigSer
open Challenge.Modexp.Submission.Proof.YulMem
open Challenge.Modexp.Submission.Proof.YulLimbs
open Challenge.Modexp.Submission.Proof.MulModProof
open Challenge.Modexp.Submission.Proof.MulModBase
open Challenge.Modexp.Submission.Proof.AddModProof
open Challenge.Modexp.Submission.Proofs.Limbs (radix limbCount limbDigits
  length_limbDigits limbDigits_lt value_limbDigits radix_gt_one radix_pos
  pow_radix limbCount_le_32 width_le_limbs limbCount_pos)
open Challenge.Modexp (baseSize exponentSize modulusSize spec ValidInput)
open EvmSemantics.EVM.Precompile (bytesToNatPadded natToBytes modPow)
open Challenge.Modexp.Submission.Proofs.Algorithm (modPow_eq)

/-- Shorthand for the 256-bit word carrying the natural `n`. -/
local notation:max "W " n:max => BitVec.ofNat 256 n

/-! ## The squaring fragment: bits phase for `bptr = ACC`

`mulBits_steps`'s invariant maintains the multiplier limbs (`bptr` region)
by re-deriving them from the reference memory `M₀` through
`MulModKeeps`, which needs `bptr` disjoint from `ACC`. For the square the
multiplier region *is* `ACC`, so the invariant is maintained directly: both
`addModFrag`s of the bits phase write `dst = OUT`, and the `ACC` region lies
below `OUT`, so each round's `AddModKeeps`-with-respect-to-`OUT` preserves it
— exactly how the original proof already maintains the multiplicand limbs
(`hacc₂`/`hacc₃`). Everything else is `mulBits_steps` verbatim with
`bptr := ACC`, `b := a`. -/

set_option maxHeartbeats 400000000 in
theorem mulBitsSq_steps [model : ExternalModel] {prog : List Asm}
    (l : MulModLabels) (lsq ladd : AddModLabels)
    (bs : List Nat) (n m a h₀ t₀ : Nat)
    {cont : List Asm} {σ : List AVal} {S : EvmState} {M₀ : Nat → UInt8}
    (hBits : findLabel l.lBits prog =
      some (mulModFromBits ACC l lsq ladd ++ cont))
    (hNextLimb : findLabel l.lNextLimb prog =
      some (mulModFromNextLimb ACC l ++ cont))
    (hDone : findLabel l.lDone prog = some (mulModFromRet l ++ cont))
    (hSqAdd : findLabel lsq.lAdd prog =
      some (addModAddBody OUT OUT lsq ++ addModFromSubStart OUT OUT lsq ++
        (mulModSqCont ACC l ladd ++ cont)))
    (hSqSubStart : findLabel lsq.lSubStart prog =
      some (store C2 (.imm 0) ++ store I2 (.imm 0) ++
        (addModFromSub OUT OUT lsq ++ (mulModSqCont ACC l ladd ++ cont))))
    (hSqSub : findLabel lsq.lSub prog =
      some (addModSubBody OUT OUT lsq ++ addModFromSel OUT OUT lsq ++
        (mulModSqCont ACC l ladd ++ cont)))
    (hSqSel : findLabel lsq.lSel prog =
      some (addModSelBody OUT OUT lsq ++ addModFromDoCopy OUT OUT lsq ++
        (mulModSqCont ACC l ladd ++ cont)))
    (hSqDoCopy : findLabel lsq.lDoCopy prog =
      some (store I2 (.imm 0) ++ (addModFromCopy OUT OUT lsq ++
        (mulModSqCont ACC l ladd ++ cont))))
    (hSqCopy : findLabel lsq.lCopy prog =
      some (addModCopyBody OUT OUT lsq ++ addModFromDone OUT OUT lsq ++
        (mulModSqCont ACC l ladd ++ cont)))
    (hSqDone : findLabel lsq.lDone prog =
      some (mulModSqCont ACC l ladd ++ cont))
    (hAdAdd : findLabel ladd.lAdd prog =
      some (addModAddBody OUT ACC ladd ++ addModFromSubStart OUT ACC ladd ++
        (mulModAdCont ACC l ++ cont)))
    (hAdSubStart : findLabel ladd.lSubStart prog =
      some (store C2 (.imm 0) ++ store I2 (.imm 0) ++
        (addModFromSub OUT ACC ladd ++ (mulModAdCont ACC l ++ cont))))
    (hAdSub : findLabel ladd.lSub prog =
      some (addModSubBody OUT ACC ladd ++ addModFromSel OUT ACC ladd ++
        (mulModAdCont ACC l ++ cont)))
    (hAdSel : findLabel ladd.lSel prog =
      some (addModSelBody OUT ACC ladd ++ addModFromDoCopy OUT ACC ladd ++
        (mulModAdCont ACC l ++ cont)))
    (hAdDoCopy : findLabel ladd.lDoCopy prog =
      some (store I2 (.imm 0) ++ (addModFromCopy OUT ACC ladd ++
        (mulModAdCont ACC l ++ cont))))
    (hAdCopy : findLabel ladd.lCopy prog =
      some (addModCopyBody OUT ACC ladd ++ addModFromDone OUT ACC ladd ++
        (mulModAdCont ACC l ++ cont)))
    (hAdDone : findLabel ladd.lDone prog = some (mulModAdCont ACC l ++ cont))
    (haw : 0x1f40 ≤ 32 * S.activeWords.toNat)
    (hn : 0 < n) (hn32 : n ≤ 32)
    (hmodRep : RepresentsY S.memory MOD n m) (hm0 : 0 < m)
    (haccRep : RepresentsY S.memory ACC n a) (ham : a < m)
    (hbs : yLimbs S.memory ACC n = bs) (hbv : a = Nat.ofDigits radix bs)
    (hT0 : (loadWord S.memory T0).toNat = lget bs h₀)
    (hHI : (loadWord S.memory HIcell).toNat = h₀) (hh₀ : h₀ < n)
    (hT1 : (loadWord S.memory T1).toNat = t₀) (ht₀ : t₀ ≤ 256)
    (hval : RepresentsY S.memory OUT n ((a * (a / 2 ^ (256 * h₀ + t₀))) % m))
    (hN : (loadWord S.memory Ncell).toNat = n)
    (hkeeps : MulModKeeps S.memory M₀ n) :
    ∃ S', ASteps prog
        ⟨mulModFromBits ACC l lsq ladd ++ cont, σ, S⟩
        ⟨mulModFromRet l ++ cont, σ, S'⟩ ∧
      RepresentsY S'.memory OUT n ((a * a) % m) ∧
      (loadWord S'.memory Ncell).toNat = n ∧
      MulModKeeps S'.memory M₀ n ∧ S'.activeWords = S.activeWords := by
  have hOUTlit : (OUT : Nat) = 0xc00 := rfl
  have hMODlit : (MOD : Nat) = 0 := rfl
  have hACClit : (ACC : Nat) = 0x800 := rfl
  have hSUBClit : (SUBC : Nat) = 0x1400 := rfl
  have hNcellLit : (Ncell : Nat) = 0x1cc0 := rfl
  have hHIlit : (HIcell : Nat) = 0x1d80 := rfl
  have hT0lit : (T0 : Nat) = 0x1dc0 := rfl
  have hT1lit : (T1 : Nat) = 0x1de0 := rfl
  have hI2lit : (I2 : Nat) = 0x1e60 := rfl
  have houtN : OUT + 32 * n ≤ Ncell := by omega
  have haccN : ACC + 32 * n ≤ Ncell := by omega
  have haccOut : ACC + 32 * n ≤ OUT := by omega
  have houtSubc : OUT + 32 * n ≤ SUBC := by omega
  have haccSubc : ACC + 32 * n ≤ SUBC := by omega
  have hmodOut : MOD + 32 * n ≤ OUT := by omega
  have hmodAcc : MOD + 32 * n ≤ ACC := by omega
  have hmodN : MOD + 32 * n ≤ Ncell := by omega
  have hbsd : ∀ d ∈ bs, d < radix := fun d hd => yLimb_lt hd
  have hbslen : bs.length = n := length_yLimbs S.memory ACC n
  have hbsdef : bs = limbDigits n a := hbs.symm.trans haccRep.2
  have hbsdef : bs = limbDigits n a := hbs.symm.trans haccRep.2
  have hmodRepOf : ∀ {St : EvmState}, yLimbs St.memory MOD n = limbDigits n m →
      RepresentsY St.memory MOD n m := fun h => ⟨hmodRep.1, h⟩
  have haccRepOf : ∀ {St : EvmState}, yLimbs St.memory ACC n = limbDigits n a →
      RepresentsY St.memory ACC n a := fun h => ⟨haccRep.1, h⟩
  have hSqCont :
      mulModSqCont ACC l ladd ++ cont =
        jumpIfZ (bitTestOf T0 T1) l.lBits ++
          (addModFrag OUT ACC ladd ++
            ([.jump l.lBits] ++ (mulModBitsTail ACC l ++ cont))) := by
    simp only [mulModSqCont, mulModBitsTail, mulModFromNextLimb,
      List.append_assoc]
  have hAdCont :
      mulModAdCont ACC l ++ cont =
        [.jump l.lBits] ++ (mulModBitsTail ACC l ++ cont) := by
    simp only [mulModAdCont, mulModBitsTail, mulModFromNextLimb,
      List.append_assoc]
  have hSqAddE := hSqAdd
  have hSqSubStartE := hSqSubStart
  have hSqSubE := hSqSub
  have hSqSelE := hSqSel
  have hSqDoCopyE := hSqDoCopy
  have hSqCopyE := hSqCopy
  have hSqDoneE := hSqDone
  rw [hSqCont] at hSqAddE hSqSubStartE hSqSubE hSqSelE hSqDoCopyE hSqCopyE hSqDoneE
  have hAdAddE := hAdAdd
  have hAdSubStartE := hAdSubStart
  have hAdSubE := hAdSub
  have hAdSelE := hAdSel
  have hAdDoCopyE := hAdDoCopy
  have hAdCopyE := hAdCopy
  have hAdDoneE := hAdDone
  rw [hAdCont] at hAdAddE hAdSubStartE hAdSubE hAdSelE hAdDoCopyE hAdCopyE hAdDoneE
  have hTop : mulModFromBits ACC l lsq ladd ++ cont =
      jumpIfZ (.load T1) l.lNextLimb ++ (store T1 (.bin .sub (.load T1) (.imm 1)) ++
          (addModFrag OUT OUT lsq ++
          (jumpIfZ (bitTestOf T0 T1) l.lBits ++
          (addModFrag OUT ACC ladd ++ ([.jump l.lBits] ++
            (mulModBitsTail ACC l ++ cont)))))) := by
    rw [mulModFromBits_eq2, mulModBitsBody_eq]
  have hround : ∀ {μ : Nat} {St : EvmState}, 0 < μ →
      (∃ h t, (loadWord St.memory HIcell).toNat = h ∧
        (loadWord St.memory T1).toNat = t ∧ 257 * h + t = μ ∧ t ≤ 256 ∧
        h < n ∧ (loadWord St.memory T0).toNat = lget bs h ∧
        RepresentsY St.memory OUT n ((a * (a / 2 ^ (256 * h + t))) % m) ∧
        yLimbs St.memory ACC n = bs ∧
        yLimbs St.memory MOD n = limbDigits n m ∧
        (loadWord St.memory Ncell).toNat = n ∧
        MulModKeeps St.memory M₀ n ∧ St.activeWords = S.activeWords) →
      ((∃ St', (∃ h t, (loadWord St'.memory HIcell).toNat = h ∧
          (loadWord St'.memory T1).toNat = t ∧
          257 * h + t = μ - 1 ∧ t ≤ 256 ∧ h < n ∧
          (loadWord St'.memory T0).toNat = lget bs h ∧
          RepresentsY St'.memory OUT n
            ((a * (a / 2 ^ (256 * h + t))) % m) ∧
          yLimbs St'.memory ACC n = bs ∧
          yLimbs St'.memory MOD n = limbDigits n m ∧
          (loadWord St'.memory Ncell).toNat = n ∧
          MulModKeeps St'.memory M₀ n ∧
          St'.activeWords = S.activeWords) ∧
        ASteps prog ⟨mulModFromBits ACC l lsq ladd ++ cont, σ, St⟩
          ⟨mulModFromBits ACC l lsq ladd ++ cont, σ, St'⟩) ∨
      ((RepresentsY St.memory OUT n ((a * a) % m) ∧
          (loadWord St.memory Ncell).toNat = n ∧
          MulModKeeps St.memory M₀ n ∧
          St.activeWords = S.activeWords) ∧
        ASteps prog ⟨mulModFromBits ACC l lsq ladd ++ cont, σ, St⟩
          ⟨mulModFromRet l ++ cont, σ, St⟩)) := by
    intro μ St hμ hm
    rcases hm with ⟨h, t, hHIst, hT1st, hμeq, ht256, hhn, hT0st, hvalst,
      haccst, hmodst, hNst, hkeepsst, hawEq⟩
    have hawSt : 0x1f40 ≤ 32 * St.activeWords.toNat := by
      rw [hawEq]; exact haw
    have hrv : (a * (a / 2 ^ (256 * h + t))) % m < m :=
      Nat.mod_lt _ hm0
    rcases Nat.eq_zero_or_pos t with ht0 | htp
    · ------------------------------------------------------------------ t = 0
      subst ht0
      have hh : 0 < h := by omega
      obtain ⟨St', hsteps, hHI', hT1', hT0', hval', hacc', hbs', hmod',
          hN', hkeeps', haw'⟩ :=
        mulBitsT0Round_steps ACC l lsq ladd bs n m a a h
          hBits hNextLimb hawSt hn32 (by omega) hh hhn hHIst hT1st hvalst
          haccst haccst hmodst hNst hkeepsst hbsd hbslen
      left
      exact ⟨St', ⟨h - 1, 256, hHI', hT1', by omega, by omega, by omega,
        hT0', hval', hacc', hmod', hN', hkeeps',
        by rw [haw', hawEq]⟩, hsteps⟩
    · ------------------------------------------------------------------ t ≥ 1
      -- shared facts
      have hdecomp := div_decomp bs hbsd a hbv h
      have hbitbridge := bit_bridge a (t - 1) h (lget bs h)
        (a / 2 ^ (256 * (h + 1))) (show t - 1 < 256 by omega) hdecomp
      have hdsstep := div_step a (256 * h + t) (by omega)
      -- step 1: the T1 exit test falls
      have hj1 : evalExpr (.load T1) St ≠ 0 := by
        show loadWord St.memory T1 ≠ 0
        rw [word_of_toNat hT1st (by omega)]
        exact ofNat_ne_zero (by omega) (by omega)
      have s1 := jumpIfZ_fall (prog := prog) (σ := σ)
        (e := .load T1) (l := l.lNextLimb)
        (k := store T1 (.bin .sub (.load T1) (.imm 1)) ++
          (addModFrag OUT OUT lsq ++
          (jumpIfZ (bitTestOf T0 T1) l.lBits ++
          (addModFrag OUT ACC ladd ++ ([.jump l.lBits] ++
            (mulModBitsTail ACC l ++ cont))))))
        (exprOK_load_cell' hawSt (by simp [fragCells])) hj1
      -- step 2: T1 := t - 1
      have hevT1 : evalExpr (.bin .sub (.load T1) (.imm 1)) St
          = BitVec.ofNat 256 (t - 1) := by
        show loadWord St.memory T1 - BitVec.ofNat 256 1 =
          BitVec.ofNat 256 (t - 1)
        rw [word_of_toNat hT1st (by omega),
          ofNat_sub_one (by omega) (by omega)]
        try rfl
      have s2 := store_cell_val (prog := prog) (c := T1)
        (e := .bin .sub (.load T1) (.imm 1)) (w := BitVec.ofNat 256 (t - 1))
        (k := addModFrag OUT OUT lsq ++
          (jumpIfZ (bitTestOf T0 T1) l.lBits ++
          (addModFrag OUT ACC ladd ++ ([.jump l.lBits] ++
            (mulModBitsTail ACC l ++ cont)))))
        (σ := σ) hevT1
        ⟨rfl, exprOK_load_cell' hawSt (by simp [fragCells]), True.intro⟩
        (haw_pin hawSt (by simp [fragCells]))
      set S₁ : EvmState := {St with memory :=
          (storeWord St.memory T1 (BitVec.ofNat 256 (t - 1)))} with hS₁def
      have hawS₁ : 0x1f40 ≤ 32 * S₁.activeWords.toNat := hawSt
      have hS₁mem : S₁.memory =
          storeWord St.memory T1 (BitVec.ofNat 256 (t - 1)) := rfl
      have hN₁ : (loadWord S₁.memory Ncell).toNat = n := by
        rw [hS₁mem, loadWord_storeWord_disj (p := T1) (q := Ncell)
          (cells_disj (by simp [fragCells]) (by simp [fragCells])
            (by decide))]
        exact hNst
      have hval₁ : RepresentsY S₁.memory OUT n
          ((a * (a / 2 ^ (256 * h + t))) % m) := by
        refine ⟨hvalst.1, ?_⟩
        rw [hS₁mem, yLimbs_storeWord_disjoint (q := T1)
          (Or.inr (by omega))]
        exact hvalst.2
      have hmod₁ : RepresentsY S₁.memory MOD n m := by
        refine hmodRepOf ?_
        rw [hS₁mem, yLimbs_storeWord_disjoint (q := T1)
          (Or.inr (by omega))]
        exact hmodst
      -- step 3: the doubling addMod
      obtain ⟨S₂, hsq, hOUT₂, hN₂, hkeeps₂a, haw₂⟩ :=
        addModFrag_steps (dst := OUT) (src := OUT) (l := lsq) (n := n)
          (m := m) (x := (a * (a / 2 ^ (256 * h + t))) % m)
          (y := (a * (a / 2 ^ (256 * h + t))) % m)
          (cont := mulModSqCont ACC l ladd ++ cont)
          (σ := σ) (yst := S₁)
          hSqAdd hSqSubStart hSqSub hSqSel hSqDoCopy hSqCopy hSqDone
          hn hn32 hN₁ hawS₁ houtN houtN hmodOut hmodOut
          (Or.inr (Or.inr rfl)) houtSubc houtSubc hmod₁ hm0 hval₁ hrv
          hval₁ (Nat.le_of_lt hrv)
      rw [hSqCont] at hsq
      -- transfers across the doubling
      have hkeepsS₁ : MulModKeeps S₁.memory M₀ n :=
        mulKeeps_storeWord hkeepsst
          (Or.inr (Or.inr (Or.inr (by simp [mulModScratch]))))
      have hkeeps₂ : MulModKeeps S₂.memory M₀ n :=
        mulKeeps_trans (mulKeeps_of_add hkeeps₂a) hkeepsS₁
      have hawS₂ : 0x1f40 ≤ 32 * S₂.activeWords.toNat := by
        rw [haw₂]; exact hawSt
      have hT0w₂ : loadWord S₂.memory T0 = BitVec.ofNat 256 (lget bs h) := by
        rw [loadWord_of_addKeeps hkeeps₂a (Or.inr (by omega)) (Or.inr (by omega))
          (hregdisj T0 (by simp)), hS₁mem,
          loadWord_storeWord_disj (p := T1) (q := T0)
            (cells_disj (by simp [fragCells]) (by simp [fragCells]) (by decide)),
          word_of_toNat hT0st (by omega)]
      have hT1₂ : (loadWord S₂.memory T1).toNat = t - 1 := by
        rw [loadWord_of_addKeeps hkeeps₂a (Or.inr (by omega)) (Or.inr (by omega))
          (hregdisj T1 (by simp)), hS₁mem, loadWord_storeWord,
          BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      have hT1w₂ : loadWord S₂.memory T1 = BitVec.ofNat 256 (t - 1) :=
        word_of_toNat hT1₂ (by omega)
      have hHI₂ : (loadWord S₂.memory HIcell).toNat = h := by
        rw [loadWord_of_addKeeps hkeeps₂a (Or.inr (by omega)) (Or.inr (by omega))
          (hregdisj HIcell (by simp)), hS₁mem,
          loadWord_storeWord_disj (p := T1) (q := HIcell)
            (cells_disj (by simp [fragCells]) (by simp [fragCells]) (by decide)),
          hHIst]
      have haccS₁ : yLimbs S₁.memory ACC n = bs := by
        rw [hS₁mem, yLimbs_storeWord_disjoint (q := T1) (Or.inr (by omega))]
        exact haccst
      have hacc₂ : yLimbs S₂.memory ACC n = bs :=
        (yLimbs_of_keeps hkeeps₂a (Or.inl haccOut) haccSubc
          (fun c hc => by have := fragCells_ge c (scratch_cells hc); omega)).trans haccS₁
      have hmodM₀ : yLimbs M₀ MOD n = limbDigits n m :=
        (yLimbs_of_mulKeeps hkeepsst (Or.inl hmodOut) (Or.inl hmodAcc)
          (Or.inl (by omega : MOD + 32 * n ≤ SUBC)) hmodN).symm.trans hmodst
      have hmod₂ : yLimbs S₂.memory MOD n = limbDigits n m :=
        (yLimbs_of_mulKeeps hkeeps₂ (Or.inl hmodOut) (Or.inl hmodAcc)
          (Or.inl (by omega : MOD + 32 * n ≤ SUBC)) hmodN).trans hmodM₀
      -- the bit value
      have hlimb256 : lget bs h < 2 ^ 256 := by
        have h1 : lget bs h < radix :=
          hbsd _ (by
            rw [lget_eq (show h < bs.length by omega)]
            exact mem_getElem (show h < bs.length by omega))
        rw [hradius] at h1
        omega
      have hbit : (evalExpr (bitTestOf T0 T1) S₂).toNat
          = (lget bs h / 2 ^ (t - 1)) % 2 := by
        rw [toNat_bitTestOf hT0w₂ hT1w₂ (by omega), BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt hlimb256]
      have hbitok : exprOK (bitTestOf T0 T1) S₂ :=
        ⟨rfl, ⟨rfl, exprOK_load_cell' hawS₂ (by simp [fragCells]),
          exprOK_load_cell' hawS₂ (by simp [fragCells])⟩, True.intro⟩
      have hbitword (v : Nat) (hlt : v < 2 ^ 256) (hv : v = (lget bs h / 2 ^ (t - 1)) % 2) :
          evalExpr (bitTestOf T0 T1) S₂ = BitVec.ofNat 256 v :=
        word_of_toNat (hbit.trans hv.symm) hlt
      -- the value bridge
      have hOUT₂v : Nat.ofDigits radix (yLimbs S₂.memory OUT n)
          = ((a * (a / 2 ^ (256 * h + t))) % m +
              (a * (a / 2 ^ (256 * h + t))) % m) % m :=
        value_of_RepresentsY hOUT₂
      have hrv2 : ((a * (a / 2 ^ (256 * h + t))) % m +
          (a * (a / 2 ^ (256 * h + t))) % m) % m < m :=
        Nat.mod_lt _ hm0
      have hBitsIn : findLabel l.lBits prog = some
          (jumpIfZ (.load T1) l.lNextLimb ++ (store T1 (.bin .sub (.load T1) (.imm 1)) ++
          (addModFrag OUT OUT lsq ++
          (jumpIfZ (bitTestOf T0 T1) l.lBits ++
          (addModFrag OUT ACC ladd ++ ([.jump l.lBits] ++
            (mulModBitsTail ACC l ++ cont))))))) := by
        rw [hBits, hTop]
      rcases Nat.eq_zero_or_pos ((lget bs h / 2 ^ (t - 1)) % 2) with hb0 | hbp
      · -- bit zero: jump back
        have h0eq : evalExpr (bitTestOf T0 T1) S₂
            = BitVec.ofNat 256 0 := hbitword 0 (by omega) hb0.symm
        have hj := jumpIfZ_taken (σ := σ) (e := bitTestOf T0 T1) (l := l.lBits)
          (k := addModFrag OUT ACC ladd ++
            ([.jump l.lBits] ++ (mulModBitsTail ACC l ++ cont)))
          hbitok h0eq hBitsIn
        -- value: r2 = a * (a / 2^(256h + (t-1)))
        have hvalnew : RepresentsY S₂.memory OUT n
            ((a * (a / 2 ^ (256 * h + (t - 1)))) % m) := by
          refine ⟨Nat.lt_of_lt_of_le (Nat.mod_lt _ hm0) (Nat.le_of_lt hmodRep.1), ?_⟩
          have hr := round_bit m a (a / 2 ^ (256 * h + t))
            ((a * (a / 2 ^ (256 * h + t))) % m)
            (((a * (a / 2 ^ (256 * h + t))) % m +
              (a * (a / 2 ^ (256 * h + t))) % m) % m)
            (((a * (a / 2 ^ (256 * h + t))) % m +
              (a * (a / 2 ^ (256 * h + t))) % m) % m) 0
            rfl rfl
            (by
              rw [Nat.zero_mul, Nat.add_zero, Nat.mod_eq_of_lt hrv2])
          have heq : a / 2 ^ (256 * h + t - 1)
              = 2 * (a / 2 ^ (256 * h + t)) + 0 := by
            have h1 : (a / 2 ^ (256 * h + t - 1)) % 2 = 0 := by
              rw [show 256 * h + t - 1 = 256 * h + (t - 1) from by omega,
                hbitbridge]
              exact hb0
            omega
          rw [hOUT₂.2, hr,
            show 2 * (a / 2 ^ (256 * h + t)) + 0
                = a / 2 ^ (256 * h + (t - 1)) from by
              rw [show 256 * h + (t - 1) = 256 * h + t - 1 from by omega]
              omega]
        left
        have hchain : ASteps prog
            ⟨mulModFromBits ACC l lsq ladd ++ cont, σ, St⟩
            ⟨mulModFromBits ACC l lsq ladd ++ cont, σ, S₂⟩ := by
          rw [hTop]
          exact ((s1.trans s2).trans hsq).trans hj
        exact ⟨S₂, ⟨h, t - 1, hHI₂, hT1₂, by omega, by omega, by omega,
          by rw [hT0w₂, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlimb256],
          hvalnew, hacc₂, hmod₂, hN₂, hkeeps₂, by rw [haw₂, hawEq]⟩,
          hchain⟩
      · -- bit one: add ACC, then jump back
        have hb1 : (lget bs h / 2 ^ (t - 1)) % 2 = 1 := by
          have hmod := Nat.mod_lt (lget bs h / 2 ^ (t - 1))
            (show (0 : Nat) < 2 by omega)
          omega
        have h1ne : evalExpr (bitTestOf T0 T1) S₂ ≠ 0 := by
          rw [hbitword 1 (by omega) hb1.symm]
          exact ofNat_ne_zero (by omega) (by omega)
        have hj := jumpIfZ_fall (prog := prog) (σ := σ) (e := bitTestOf T0 T1) (l := l.lBits)
          (k := addModFrag OUT ACC ladd ++
            ([.jump l.lBits] ++ (mulModBitsTail ACC l ++ cont)))
          hbitok h1ne
        obtain ⟨S₃, had, hOUT₃, hN₃, hkeeps₃a, haw₃⟩ :=
          addModFrag_steps (dst := OUT) (src := ACC) (l := ladd) (n := n)
            (m := m) (x := ((a * (a / 2 ^ (256 * h + t))) % m +
                (a * (a / 2 ^ (256 * h + t))) % m) % m) (y := a)
            (cont := mulModAdCont ACC l ++ cont)
            (σ := σ) (yst := S₂)
            hAdAdd hAdSubStart hAdSub hAdSel hAdDoCopy hAdCopy hAdDone
            hn hn32 hN₂ hawS₂ houtN haccN hmodOut hmodAcc
            (Or.inl haccOut) houtSubc haccSubc
            (hmodRepOf hmod₂) hm0 hOUT₂ hrv2
            (haccRepOf (hacc₂.trans hbsdef)) (Nat.le_of_lt ham)
        rw [hAdCont] at had
        have hjump := astep_jump (prog := prog) (l := l.lBits)
          (k := mulModBitsTail ACC l ++ cont) (σ := σ) (yst := S₃) hBitsIn
        have hkeeps₃ : MulModKeeps S₃.memory M₀ n :=
          mulKeeps_trans (mulKeeps_of_add hkeeps₃a) hkeeps₂
        have hawS₃ : 0x1f40 ≤ 32 * S₃.activeWords.toNat := by
          rw [haw₃]; exact hawS₂
        have hT0₃ : (loadWord S₃.memory T0).toNat = lget bs h := by
          rw [loadWord_of_addKeeps hkeeps₃a (Or.inr (by omega)) (Or.inr (by omega))
            (hregdisj T0 (by simp)), hT0w₂, BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt hlimb256]
        have hT1₃ : (loadWord S₃.memory T1).toNat = t - 1 := by
          rw [loadWord_of_addKeeps hkeeps₃a (Or.inr (by omega)) (Or.inr (by omega))
            (hregdisj T1 (by simp)), hT1w₂, BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt (by omega)]
        have hHI₃ : (loadWord S₃.memory HIcell).toNat = h := by
          rw [loadWord_of_addKeeps hkeeps₃a (Or.inr (by omega)) (Or.inr (by omega))
            (hregdisj HIcell (by simp)), hHI₂]
        have hmod₃ : yLimbs S₃.memory MOD n = limbDigits n m :=
          (yLimbs_of_mulKeeps hkeeps₃ (Or.inl hmodOut) (Or.inl hmodAcc)
            (Or.inl (by omega : MOD + 32 * n ≤ SUBC)) hmodN).trans
            ((yLimbs_of_mulKeeps hkeeps₂ (Or.inl hmodOut) (Or.inl hmodAcc)
              (Or.inl (by omega : MOD + 32 * n ≤ SUBC)) hmodN).symm.trans hmod₂)
        have hacc₃ : yLimbs S₃.memory ACC n = bs :=
          (yLimbs_of_keeps hkeeps₃a (Or.inl haccOut) haccSubc
            (fun c hc => by have := fragCells_ge c (scratch_cells hc); omega)).trans hacc₂
        have hvalnew : RepresentsY S₃.memory OUT n
            ((a * (a / 2 ^ (256 * h + (t - 1)))) % m) := by
          refine ⟨Nat.lt_of_lt_of_le (Nat.mod_lt _ hm0)
            (Nat.le_of_lt hmodRep.1), ?_⟩
          have hOUT₂v' : Nat.ofDigits radix (yLimbs S₂.memory OUT n)
              = ((a * (a / 2 ^ (256 * h + t))) % m +
                (a * (a / 2 ^ (256 * h + t))) % m) % m :=
            value_of_RepresentsY hOUT₂
          have hOUT₃v : Nat.ofDigits radix (yLimbs S₃.memory OUT n)
              = ((((a * (a / 2 ^ (256 * h + t))) % m +
                  (a * (a / 2 ^ (256 * h + t))) % m) % m) + a) % m :=
            value_of_RepresentsY hOUT₃
          have hr := round_bit m a (a / 2 ^ (256 * h + t))
            ((a * (a / 2 ^ (256 * h + t))) % m)
            (((a * (a / 2 ^ (256 * h + t))) % m +
              (a * (a / 2 ^ (256 * h + t))) % m) % m)
            (((((a * (a / 2 ^ (256 * h + t))) % m +
              (a * (a / 2 ^ (256 * h + t))) % m) % m) + a) % m) 1
            rfl rfl (by rw [Nat.one_mul])
          have heq : a / 2 ^ (256 * h + t - 1)
              = 2 * (a / 2 ^ (256 * h + t)) + 1 := by
            have h1 : (a / 2 ^ (256 * h + t - 1)) % 2 = 1 := by
              rw [show 256 * h + t - 1 = 256 * h + (t - 1) from by omega,
                hbitbridge]
              exact hb1
            omega
          rw [hOUT₃.2, hr,
            show 2 * (a / 2 ^ (256 * h + t)) + 1
                = a / 2 ^ (256 * h + (t - 1)) from by
              rw [show 256 * h + (t - 1) = 256 * h + t - 1 from by omega]
              omega]
        left
        have hchain : ASteps prog
            ⟨mulModFromBits ACC l lsq ladd ++ cont, σ, St⟩
            ⟨mulModFromBits ACC l lsq ladd ++ cont, σ, S₃⟩ := by
          rw [hTop]
          exact (((s1.trans s2).trans hsq).trans hj).trans
            (had.trans (ASteps.single hjump))
        exact ⟨S₃, ⟨h, t - 1, hHI₃, hT1₃, by omega, by omega, by omega,
          hT0₃, hvalnew, hacc₃, hmod₃, hN₃, hkeeps₃, by rw [haw₃, haw₂, hawEq]⟩,
          hchain⟩
  -- the exit at μ = 0: h = 0 ∧ t = 0, two taken jumps, state preserved
  have hexit : ∀ St : EvmState,
      (∃ h t, (loadWord St.memory HIcell).toNat = h ∧
        (loadWord St.memory T1).toNat = t ∧ 257 * h + t = 0 ∧ t ≤ 256 ∧
        h < n ∧ (loadWord St.memory T0).toNat = lget bs h ∧
        RepresentsY St.memory OUT n ((a * (a / 2 ^ (256 * h + t))) % m) ∧
        yLimbs St.memory ACC n = bs ∧
        yLimbs St.memory MOD n = limbDigits n m ∧
        (loadWord St.memory Ncell).toNat = n ∧
        MulModKeeps St.memory M₀ n ∧ St.activeWords = S.activeWords) →
      (RepresentsY St.memory OUT n ((a * a) % m) ∧
          (loadWord St.memory Ncell).toNat = n ∧
          MulModKeeps St.memory M₀ n ∧
          St.activeWords = S.activeWords) ∧
        ASteps prog ⟨mulModFromBits ACC l lsq ladd ++ cont, σ, St⟩
          ⟨mulModFromRet l ++ cont, σ, St⟩ := by
    intro St hm
    rcases hm with ⟨h, t, hHIst, hT1st, hμeq, -, -, hT0st, hvalst, -, -, -,
      hNst, hkeepsst, hawEq⟩
    have hawSt : 0x1f40 ≤ 32 * St.activeWords.toNat := by
      rw [hawEq]; exact haw
    have h0 : h = 0 ∧ t = 0 := by omega
    have hvalb : RepresentsY St.memory OUT n ((a * a) % m) := by
      refine ⟨Nat.lt_of_lt_of_le (Nat.mod_lt _ hm0)
        (Nat.le_of_lt hmodRep.1), ?_⟩
      rw [hvalst.2, h0.1, h0.2, show a / 2 ^ (256 * 0 + 0) = a from by
        rw [Nat.mul_zero, Nat.add_zero, Nat.pow_zero, Nat.div_one]]
    have hj1 : evalExpr (.load T1) St = 0 := by
      show loadWord St.memory T1 = 0
      rw [word_of_toNat hT1st (by omega), h0.2]
      rfl
    have hj2 : evalExpr (.load HIcell) St = 0 := by
      show loadWord St.memory HIcell = 0
      rw [word_of_toNat hHIst (by omega), h0.1]
      rfl
    refine ⟨⟨hvalb, hNst, hkeepsst, hawEq⟩, ?_⟩
    have hNextLimbI := hNextLimb
    rw [mulModFromNextLimb_eq2, mulModNextLimbBody_eq] at hNextLimbI
    have hs1 := jumpIfZ_taken (σ := σ) (e := .load T1)
      (l := l.lNextLimb)
      (c' := jumpIfZ (.load HIcell) l.lDone ++
        (store HIcell (.bin .sub (.load HIcell) (.imm 1)) ++
        (store T1 (.imm 256) ++
        (store T0 (loadAt (.bin .add (.imm ACC)
          (.bin .mul (.imm 32) (.load HIcell)))) ++
        ([.jump l.lBits] ++ [.label l.lZero] ++
        (mulModFromZero l ++ cont))))))
      (k := store T1 (.bin .sub (.load T1) (.imm 1)) ++
          (addModFrag OUT OUT lsq ++
          (jumpIfZ (bitTestOf T0 T1) l.lBits ++
          (addModFrag OUT ACC ladd ++ ([.jump l.lBits] ++
            (mulModBitsTail ACC l ++ cont))))))
      (exprOK_load_cell' hawSt (by simp [fragCells])) hj1 hNextLimbI
    have hs2 := jumpIfZ_taken (σ := σ) (e := .load HIcell)
      (l := l.lDone) (c' := mulModFromRet l ++ cont)
      (k := store HIcell (.bin .sub (.load HIcell) (.imm 1)) ++
        (store T1 (.imm 256) ++
        (store T0 (loadAt (.bin .add (.imm ACC)
          (.bin .mul (.imm 32) (.load HIcell)))) ++
        ([.jump l.lBits] ++ [.label l.lZero] ++
        (mulModFromZero l ++ cont)))))
      (exprOK_load_cell' hawSt (by simp [fragCells])) hj2 hDone
    rw [hTop]
    exact hs1.trans hs2
  obtain ⟨S', hP', hsteps⟩ :=
    loop_counted (model := model) (prog := prog)
      (top := mulModFromBits ACC l lsq ladd ++ cont) (σ := σ)
      (c' := mulModFromRet l ++ cont)
      (Inv := fun St μ => ∃ h t, (loadWord St.memory HIcell).toNat = h ∧
        (loadWord St.memory T1).toNat = t ∧ 257 * h + t = μ ∧ t ≤ 256 ∧
        h < n ∧ (loadWord St.memory T0).toNat = lget bs h ∧
        RepresentsY St.memory OUT n ((a * (a / 2 ^ (256 * h + t))) % m) ∧
        yLimbs St.memory ACC n = bs ∧
        yLimbs St.memory MOD n = limbDigits n m ∧
        (loadWord St.memory Ncell).toNat = n ∧
        MulModKeeps St.memory M₀ n ∧ St.activeWords = S.activeWords)
      (P := fun St => RepresentsY St.memory OUT n ((a * a) % m) ∧
        (loadWord St.memory Ncell).toNat = n ∧
        MulModKeeps St.memory M₀ n ∧ St.activeWords = S.activeWords)
      hround hexit (n := 257 * h₀ + t₀) (yst := S)
      ⟨h₀, t₀, hHI, hT1, rfl, ht₀, hh₀, hT0, hval, hbs, hmodRep.2,
        hN, hkeeps, rfl⟩
  exact ⟨S', hsteps, hP'.1, hP'.2.1, hP'.2.2.1, hP'.2.2.2⟩
