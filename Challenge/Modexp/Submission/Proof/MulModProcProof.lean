import Challenge.Modexp.Submission.Proof.MulModProcBase

set_option warningAsError true
set_option maxHeartbeats 80000000
set_option maxRecDepth 1000000
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false

/-!
# Asm-level correctness of the `mulModBig` PROCEDURE

`mulModProc` is the procedure-based program's multiplier: entered via
`[store BPTR (.load BPTR), .pushLabel lret, .jump lmmEntry, .label lret]`,
it computes `ACC := ACC · (bptr region) mod MOD` in place, calling the
`addMod` PROCEDURE twice per multiplier bit (doubling `OUT += OUT`, and
the conditional `OUT += ACC`), and returns through its trailing `.dynJump`.

The `addMod` procedure is consumed through the `AddModProcSpec` contract
(pinned to `Proof/AddModProcProof.lean`'s `addModCall_correct`): from the
call site `[store ADST (.imm dst), store ASRC (.imm src), .pushLabel lret,
.jump lamEntry, .label lret]` against a continuation `cont` whose label
resolves, the call reaches `cont` with the stack unchanged, the `dst`
region representing `(x + y) % m`, `Ncell` preserved, every byte outside
the `dst`/`SUBC` regions and the eight `addMod` scratch cells unchanged,
and `activeWords`/environment unchanged.

* `mulModProcEntry_correct` — from the procedure's entry code (with the
  return address on the stack) to the trailing `.dynJump`: the `ACC`
  region represents `(a * b) % m`, `Ncell` holds `n`, the `mulMod` frame
  is preserved, `activeWords` unchanged.
* `mulModCall_correct` — the call-site-composable export: from
  `store BPTR (.load BPTR) ++ [.pushLabel lret, .jump lmmEntry,
  .label lret] ++ cont` to `cont`, stack unchanged, same conclusions.

The program's concrete labels (`procLabels`) and the `findLabel` facts
are discharged by `decide` over `programAsm`.
-/

namespace Challenge.Modexp.Submission.Proof.MulModProc

open Challenge.Modexp.Submission
open Challenge.Modexp.Submission.Proofs.Limbs
open Challenge.Modexp.Submission.Proof.YulLimbs
open YulEvmCompiler
open YulSemantics.EVM (U256 EvmState loadWord storeWord b2w)

/-! ## The `addMod` call contract -/

/-- The `mulModBig` procedure's concrete labels, as allocated by
`genProgram`: `lmmEntry = 50`, scan `51`, top-bit `52`, copy `53`, bits
`54`, next-limb `55`, zero `56`, zero-loop `57`, done `58`, ret-copy `59`,
exit `60`; call returns `lmSqRet = 68`, `lmAddRet = 69`; the `addMod`
entry `lamEntry = 42`. -/
def procLabels : MulModProcLabels :=
  ⟨50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 68, 69, 42⟩

/-- The `addMod` procedure's call-site correctness, as consumed by the
`mulMod` bit loop.  This is exactly the statement of
`Proof.AddModProcProof.addModCall_correct` specialized to `programAsm`,
the concrete labels, and the caller's return label; the composition
wrapper instantiates it. -/
structure AddModProcSpec where
  correct : ∀ (dst src lret : Nat) (cont : List Asm)
      (σ : List AVal) (yst : EvmState) (n m x y : Nat),
    0 < n → n ≤ 32 → (loadWord yst.memory Ncell).toNat = n →
    0x1f40 ≤ 32 * yst.activeWords.toNat →
    dst + 32 * n ≤ Ncell → src + 32 * n ≤ Ncell →
    MOD + 32 * n ≤ dst → MOD + 32 * n ≤ src →
    (src + 32 * n ≤ dst ∨ dst + 32 * n ≤ src ∨ src = dst) →
    dst + 32 * n ≤ SUBC → src + 32 * n ≤ SUBC →
    RepresentsY yst.memory MOD n m → 0 < m →
    RepresentsY yst.memory dst n x → x < m →
    RepresentsY yst.memory src n y → y ≤ m →
    findLabel lret programAsm = some cont →
    ∃ yst', ASteps programAsm
        ⟨store ADST (.imm dst) ++ store ASRC (.imm src) ++
          [.pushLabel lret, .jump procLabels.lamEntry, .label lret] ++ cont,
          σ, yst⟩
        ⟨cont, σ, yst'⟩ ∧
      RepresentsY yst'.memory dst n ((x + y) % m) ∧
      (loadWord yst'.memory Ncell).toNat = n ∧
      (∀ a, (a < dst ∨ dst + 32 * n ≤ a) → (a < SUBC ∨ SUBC + 32 * n ≤ a) →
        (∀ c ∈ addModScratch, a < c ∨ c + 32 ≤ a) →
        yst'.memory a = yst.memory a) ∧
      yst'.activeWords = yst.activeWords ∧ yst'.env = yst.env

/-! ## The l-abstract call contract -/

/-- The `addMod` call contract at an (abstract) mulMod label record: the
same statement as `AddModProcSpec` but with the call sites spelled through
`l`'s own labels.  The bits phase consumes this; the wrapper instantiates
it from the pinned `AddModProcSpec` at `l := procLabels` (where the two
call-site spellings agree by `rfl`). -/
structure CallSpec (l : MulModProcLabels) where
  correct : ∀ (dst src lret : Nat) (cont : List Asm)
      (σ : List AVal) (yst : EvmState) (n m x y : Nat),
    0 < n → n ≤ 32 → (loadWord yst.memory Ncell).toNat = n →
    0x1f40 ≤ 32 * yst.activeWords.toNat →
    dst + 32 * n ≤ Ncell → src + 32 * n ≤ Ncell →
    MOD + 32 * n ≤ dst → MOD + 32 * n ≤ src →
    (src + 32 * n ≤ dst ∨ dst + 32 * n ≤ src ∨ src = dst) →
    dst + 32 * n ≤ SUBC → src + 32 * n ≤ SUBC →
    RepresentsY yst.memory MOD n m → 0 < m →
    RepresentsY yst.memory dst n x → x < m →
    RepresentsY yst.memory src n y → y ≤ m →
    findLabel lret programAsm = some cont →
    ∃ yst', ASteps programAsm
        ⟨mmCallSite dst src lret l.lamEntry ++ cont, σ, yst⟩
        ⟨cont, σ, yst'⟩ ∧
      RepresentsY yst'.memory dst n ((x + y) % m) ∧
      (loadWord yst'.memory Ncell).toNat = n ∧
      (∀ a, (a < dst ∨ dst + 32 * n ≤ a) → (a < SUBC ∨ SUBC + 32 * n ≤ a) →
        (∀ c ∈ addModScratch, a < c ∨ c + 32 ≤ a) →
        yst'.memory a = yst.memory a) ∧
      yst'.activeWords = yst.activeWords ∧ yst'.env = yst.env

/-- The pinned contract implies the `procLabels`-abstracted one: the call
sites agree definitionally. -/
def callSpecOf (sp : AddModProcSpec) : CallSpec procLabels where
  correct := sp.correct

/-! ## The bits phase -/

/-- The continuation of the doubling call inside the bits body. -/
def mmSqCont (l : MulModProcLabels) : List Asm :=
  jumpIfZ (bitTestOf T0 T1) l.lBits ++ mmCallSite OUT ACC l.lAddRet l.lamEntry ++
  [.jump l.lBits] ++ mulModBitsTail l

/-- The continuation of the conditional-add call inside the bits body. -/
def mmAdCont (l : MulModProcLabels) : List Asm :=
  [.jump l.lBits] ++ mulModBitsTail l

set_option maxHeartbeats 80000000 in
/-- The combined bits/limb phase: from the `lBits` top with `HI = h₀`,
`T1 = t₀`, `T0 = limb h₀`, and `OUT` representing
`a · (b / 2^(256h₀+t₀)) mod m`, the loop consumes every bit (one round per
bit, one `lNextLimb` transition per limb, each round making two `addMod`
procedure calls) and exits to the `lDone` code with `OUT` representing
`(a * b) % m`.  The measure is `257 * HI + T1`. -/
theorem mulBits_steps (l : MulModProcLabels) (cs : CallSpec l) (bptr : Nat)
    (bs : List Nat) (n m a b h₀ t₀ : Nat)
    {cont : List Asm} {σ : List AVal} {S : EvmState} {M₀ : Nat → UInt8}
    (hBits : findLabel l.lBits programAsm =
      some (mulModFromBits l ++ cont))
    (hNextLimb : findLabel l.lNextLimb programAsm =
      some (mulModFromNextLimb l ++ cont))
    (hDone : findLabel l.lDone programAsm = some (mulModFromRet l ++ cont))
    (hSqRet : findLabel l.lSqRet programAsm = some (mmSqCont l ++ cont))
    (hAddRet : findLabel l.lAddRet programAsm = some (mmAdCont l ++ cont))
    (haw : 0x1f40 ≤ 32 * S.activeWords.toNat)
    (hn : 0 < n) (hn32 : n ≤ 32)
    (hbptrN : bptr + 32 * n ≤ Ncell)
    (hbOut : bptr + 32 * n ≤ OUT ∨ OUT + 32 * n ≤ bptr)
    (hbAcc : bptr + 32 * n ≤ ACC ∨ ACC + 32 * n ≤ bptr ∨ bptr = ACC)
    (hbSubc : bptr + 32 * n ≤ SUBC ∨ SUBC + 32 * n ≤ bptr)
    (hmodRep : RepresentsY S.memory MOD n m) (hm0 : 0 < m)
    (haccRep : RepresentsY S.memory ACC n a) (ham : a < m)
    (hbs : yLimbs S.memory bptr n = bs) (hbv : b = Nat.ofDigits radix bs)
    (hT0 : (loadWord S.memory T0).toNat = lget bs h₀)
    (hHI : (loadWord S.memory HIcell).toNat = h₀) (hh₀ : h₀ < n)
    (hT1 : (loadWord S.memory T1).toNat = t₀) (ht₀ : t₀ ≤ 256)
    (hval : RepresentsY S.memory OUT n ((a * (b / 2 ^ (256 * h₀ + t₀))) % m))
    (hN : (loadWord S.memory Ncell).toNat = n)
    (hkeeps : MulModKeeps S.memory M₀ n)
    (hBPTR : (loadWord S.memory BPTR).toNat = bptr) :
    ∃ S', ASteps programAsm
        ⟨mulModFromBits l ++ cont, σ, S⟩
        ⟨mulModFromRet l ++ cont, σ, S'⟩ ∧
      RepresentsY S'.memory OUT n ((a * b) % m) ∧
      (loadWord S'.memory Ncell).toNat = n ∧
      MulModKeeps S'.memory M₀ n ∧ S'.activeWords = S.activeWords ∧
      S'.env = S.env := by
  have hbsd : ∀ d ∈ bs, d < radix := by
    intro d hd
    rw [← hbs] at hd
    exact yLimb_lt hd
  have hbslen : bs.length = n := by
    rw [← hbs]; exact length_yLimbs S.memory bptr n
  have hOUTeq : (OUT : Nat) = 0xc00 := rfl
  have hMODlit : (MOD : Nat) = 0 := rfl
  have hACClit : (ACC : Nat) = 0x800 := rfl
  have hSUBClit : (SUBC : Nat) = 0x1400 := rfl
  have hNcellLit : (Ncell : Nat) = 0x1cc0 := rfl
  have hHIlit : (HIcell : Nat) = 0x1d80 := rfl
  have hT0lit : (T0 : Nat) = 0x1dc0 := rfl
  have hT1lit : (T1 : Nat) = 0x1de0 := rfl
  have hBPTRlit : (BPTR : Nat) = 0x1da0 := rfl
  have houtN : OUT + 32 * n ≤ Ncell := by omega
  have haccN : ACC + 32 * n ≤ Ncell := by omega
  have haccOut : ACC + 32 * n ≤ OUT := by omega
  have houtSubc : OUT + 32 * n ≤ SUBC := by omega
  have haccSubc : ACC + 32 * n ≤ SUBC := by omega
  have hmodOut : MOD + 32 * n ≤ OUT := by omega
  have hmodAcc : MOD + 32 * n ≤ ACC := by omega
  have hmodN : MOD + 32 * n ≤ Ncell := by omega
  have hregdisj (q : Nat) (hq : q ∈ [(Ncell : Nat), HIcell, BPTR, T0, T1]) :
      ∀ c ∈ addModScratch, q + 32 ≤ c ∨ c + 32 ≤ q :=
    fun c hc => addScratch_vs_regs c hc q hq
  have hBPTRdisj : ∀ c ∈ mulModScratch, BPTR + 32 ≤ c ∨ c + 32 ≤ BPTR := by
    intro c hc
    unfold mulModScratch at hc
    rcases List.mem_append.mp hc with h | h
    · have hlit : ∀ c ∈ [HIcell, T0, T1],
          BPTR + 32 ≤ c ∨ c + 32 ≤ BPTR := by decide
      exact hlit c h
    · exact hregdisj BPTR (by simp) c h
  have hmodRepOf : ∀ {St : EvmState}, yLimbs St.memory MOD n = limbDigits n m →
      RepresentsY St.memory MOD n m := fun h => ⟨hmodRep.1, h⟩
  have haccRepOf : ∀ {St : EvmState}, yLimbs St.memory ACC n = limbDigits n a →
      RepresentsY St.memory ACC n a := fun h => ⟨haccRep.1, h⟩
  have hSqCont :
      mmSqCont l ++ cont =
        jumpIfZ (bitTestOf T0 T1) l.lBits ++
          (mmCallSite OUT ACC l.lAddRet l.lamEntry ++
            ([.jump l.lBits] ++ (mulModBitsTail l ++ cont))) := by
    simp only [mmSqCont, mulModBitsTail, List.append_assoc]
  have hAdCont :
      mmAdCont l ++ cont =
        [.jump l.lBits] ++ (mulModBitsTail l ++ cont) := by
    simp only [mmAdCont, mulModBitsTail, List.append_assoc]
  have hSqRetE := hSqRet
  have hAddRetE := hAddRet
  rw [hSqCont] at hSqRetE
  rw [hAdCont] at hAddRetE
  have hTop : mulModFromBits l ++ cont =
      jumpIfZ (.load T1) l.lNextLimb ++ (store T1 (.bin .sub (.load T1) (.imm 1)) ++
          (mmCallSite OUT OUT l.lSqRet l.lamEntry ++
          (jumpIfZ (bitTestOf T0 T1) l.lBits ++
          (mmCallSite OUT ACC l.lAddRet l.lamEntry ++ ([.jump l.lBits] ++
            (mulModBitsTail l ++ cont)))))) := by
    rw [mulModFromBits_eq2, mulModBitsBody_eq]
  have hround : ∀ {μ : Nat} {St : EvmState}, 0 < μ →
      (∃ h t, (loadWord St.memory HIcell).toNat = h ∧
        (loadWord St.memory T1).toNat = t ∧ 257 * h + t = μ ∧ t ≤ 256 ∧
        h < n ∧ (loadWord St.memory T0).toNat = lget bs h ∧
        RepresentsY St.memory OUT n ((a * (b / 2 ^ (256 * h + t))) % m) ∧
        yLimbs St.memory ACC n = limbDigits n a ∧
        yLimbs St.memory bptr n = bs ∧
        yLimbs St.memory MOD n = limbDigits n m ∧
        (loadWord St.memory Ncell).toNat = n ∧
        MulModKeeps St.memory M₀ n ∧ St.activeWords = S.activeWords ∧
        (loadWord St.memory BPTR).toNat = bptr ∧
        St.env = S.env) →
      ((∃ St', (∃ h t, (loadWord St'.memory HIcell).toNat = h ∧
          (loadWord St'.memory T1).toNat = t ∧
          257 * h + t = μ - 1 ∧ t ≤ 256 ∧ h < n ∧
          (loadWord St'.memory T0).toNat = lget bs h ∧
          RepresentsY St'.memory OUT n
            ((a * (b / 2 ^ (256 * h + t))) % m) ∧
          yLimbs St'.memory ACC n = limbDigits n a ∧
          yLimbs St'.memory bptr n = bs ∧
          yLimbs St'.memory MOD n = limbDigits n m ∧
          (loadWord St'.memory Ncell).toNat = n ∧
          MulModKeeps St'.memory M₀ n ∧
          St'.activeWords = S.activeWords ∧
          (loadWord St'.memory BPTR).toNat = bptr ∧
          St'.env = S.env) ∧
        ASteps programAsm ⟨mulModFromBits l ++ cont, σ, St⟩
          ⟨mulModFromBits l ++ cont, σ, St'⟩) ∨
      ((RepresentsY St.memory OUT n ((a * b) % m) ∧
          (loadWord St.memory Ncell).toNat = n ∧
          MulModKeeps St.memory M₀ n ∧
          St.activeWords = S.activeWords ∧
          St.env = S.env) ∧
        ASteps programAsm ⟨mulModFromBits l ++ cont, σ, St⟩
          ⟨mulModFromRet l ++ cont, σ, St⟩)) := by
    intro μ St hμ hm
    rcases hm with ⟨h, t, hHIst, hT1st, hμeq, ht256, hhn, hT0st, hvalst,
      haccst, hbsst, hmodst, hNst, hkeepsst, hawEq, hBPTRst, henvSt⟩
    have hawSt : 0x1f40 ≤ 32 * St.activeWords.toNat := by
      rw [hawEq]; exact haw
    have hrv : (a * (b / 2 ^ (256 * h + t))) % m < m :=
      Nat.mod_lt _ hm0
    rcases Nat.eq_zero_or_pos t with ht0 | htp
    · ------------------------------------------------------------------ t = 0
      subst ht0
      have hh : 0 < h := by omega
      have hBPTRwSt : loadWord St.memory BPTR = BitVec.ofNat 256 bptr :=
        BPTR_word hBPTRst (by omega)
      have hBPTRM₀ : loadWord M₀ BPTR = BitVec.ofNat 256 bptr := by
        rw [← loadWord_of_mulKeeps hkeepsst
          (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega))
          hBPTRdisj]
        exact hBPTRwSt
      obtain ⟨St', hsteps, hHI', hT1', hT0', hval', hacc', hbs', hmod',
          hN', hkeeps', haw', henv'⟩ :=
        mulBitsT0Round_steps bptr l bs n m a b h
          hBits hNextLimb hBPTRst hawSt hn32 hbptrN hh hhn hHIst hT1st hvalst
          haccst hbsst hmodst hNst hkeepsst hbsd hbslen
      have hBPTR' : (loadWord St'.memory BPTR).toNat = bptr := by
        rw [loadWord_of_mulKeeps hkeeps'
          (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega))
          hBPTRdisj, hBPTRM₀, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      left
      exact ⟨St', ⟨h - 1, 256, hHI', hT1', by omega, by omega, by omega,
        hT0', hval', hacc', hbs', hmod', hN', hkeeps',
        by rw [haw', hawEq], hBPTR', henv'.trans henvSt⟩, hsteps⟩
    · ------------------------------------------------------------------ t ≥ 1
      -- shared facts
      have hdecomp := div_decomp bs hbsd b hbv h
      have hbitbridge := bit_bridge b (t - 1) h (lget bs h)
        (b / 2 ^ (256 * (h + 1))) (show t - 1 < 256 by omega) hdecomp
      have hdsstep := div_step b (256 * h + t) (by omega)
      -- step 1: the T1 exit test falls
      have hj1 : evalExpr (.load T1) St ≠ 0 := by
        show loadWord St.memory T1 ≠ 0
        rw [word_of_toNat hT1st (by omega)]
        exact ofNat_ne_zero (by omega) (by omega)
      have s1 := jumpIfZ_fall (prog := programAsm) (σ := σ)
        (e := .load T1) (l := l.lNextLimb)
        (k := store T1 (.bin .sub (.load T1) (.imm 1)) ++
          (mmCallSite OUT OUT l.lSqRet l.lamEntry ++
          (jumpIfZ (bitTestOf T0 T1) l.lBits ++
          (mmCallSite OUT ACC l.lAddRet l.lamEntry ++ ([.jump l.lBits] ++
            (mulModBitsTail l ++ cont))))))
        (exprOK_load_cell' hawSt (by simp [fragCells])) hj1
      -- step 2: T1 := t - 1
      have hevT1 : evalExpr (.bin .sub (.load T1) (.imm 1)) St
          = BitVec.ofNat 256 (t - 1) := by
        show loadWord St.memory T1 - BitVec.ofNat 256 1 =
          BitVec.ofNat 256 (t - 1)
        rw [word_of_toNat hT1st (by omega),
          ofNat_sub_one (by omega) (by omega)]
        try rfl
      have s2 := store_cell_val (prog := programAsm) (c := T1)
        (e := .bin .sub (.load T1) (.imm 1)) (w := BitVec.ofNat 256 (t - 1))
        (k := mmCallSite OUT OUT l.lSqRet l.lamEntry ++
          (jumpIfZ (bitTestOf T0 T1) l.lBits ++
          (mmCallSite OUT ACC l.lAddRet l.lamEntry ++ ([.jump l.lBits] ++
            (mulModBitsTail l ++ cont)))))
        (σ := σ) hevT1
        ⟨rfl, exprOK_load_cell' hawSt (by simp [fragCells]), True.intro⟩
        (haw_pin hawSt (by simp [fragCells]))
      set S₁ : EvmState := {St with memory :=
          (storeWord St.memory T1 (BitVec.ofNat 256 (t - 1)))} with hS₁def
      have hawS₁ : 0x1f40 ≤ 32 * S₁.activeWords.toNat := hawSt
      have henvS₁ : S₁.env = St.env := rfl
      have hS₁mem : S₁.memory =
          storeWord St.memory T1 (BitVec.ofNat 256 (t - 1)) := rfl
      have hN₁ : (loadWord S₁.memory Ncell).toNat = n := by
        rw [hS₁mem, loadWord_storeWord_disj (p := T1) (q := Ncell)
          (cells_disj (by simp [fragCells]) (by simp [fragCells])
            (by decide))]
        exact hNst
      have hval₁ : RepresentsY S₁.memory OUT n
          ((a * (b / 2 ^ (256 * h + t))) % m) := by
        refine ⟨hvalst.1, ?_⟩
        rw [hS₁mem, yLimbs_storeWord_disjoint (q := T1)
          (Or.inr (by omega))]
        exact hvalst.2
      have hmod₁ : RepresentsY S₁.memory MOD n m := by
        refine hmodRepOf ?_
        rw [hS₁mem, yLimbs_storeWord_disjoint (q := T1)
          (Or.inr (by omega))]
        exact hmodst
      have hBPTRwSt : loadWord St.memory BPTR = BitVec.ofNat 256 bptr :=
        BPTR_word hBPTRst (by omega)
      have hBPTRwS₁ : loadWord S₁.memory BPTR = BitVec.ofNat 256 bptr := by
        rw [hS₁mem, loadWord_storeWord_disj (p := T1) (q := BPTR)
          (cells_disj (by simp [fragCells]) (by simp [fragCells]) (by decide))]
        exact hBPTRwSt
      -- step 3: the doubling addMod
      obtain ⟨S₂, hsq, hOUT₂, hN₂, hkeeps₂a, haw₂, henv₂⟩ :=
        cs.correct OUT OUT l.lSqRet (mmSqCont l ++ cont) σ S₁ n m
          ((a * (b / 2 ^ (256 * h + t))) % m)
          ((a * (b / 2 ^ (256 * h + t))) % m)
          hn hn32 hN₁ hawS₁ houtN houtN hmodOut hmodOut
          (Or.inr (Or.inr rfl)) houtSubc houtSubc hmod₁ hm0 hval₁ hrv
          hval₁ (Nat.le_of_lt hrv) hSqRet
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
      have haccS₁ : yLimbs S₁.memory ACC n = limbDigits n a := by
        rw [hS₁mem, yLimbs_storeWord_disjoint (q := T1) (Or.inr (by omega))]
        exact haccst
      have hacc₂ : yLimbs S₂.memory ACC n = limbDigits n a :=
        (yLimbs_of_keeps hkeeps₂a (Or.inl haccOut) haccSubc
          (fun c hc => by have := fragCells_ge c (scratch_cells hc); omega)).trans haccS₁
      have hbs₁ : yLimbs S₁.memory bptr n = bs := by
        rw [hS₁mem, yLimbs_storeWord_disjoint (q := T1) (Or.inr (by omega))]
        exact hbsst
      have hbs₂ : yLimbs S₂.memory bptr n = bs :=
        (yLimbs_congr (fun a ha1 ha2 =>
          hkeeps₂a a (by rcases hbOut with h | h <;> omega)
            (by rcases hbSubc with h | h <;> omega)
            (fun c hc => by
              have hc' := scratch_cells hc
              have hge := fragCells_ge c hc'
              have hbp := hbptrN
              omega))).trans hbs₁
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
          = ((a * (b / 2 ^ (256 * h + t))) % m +
              (a * (b / 2 ^ (256 * h + t))) % m) % m :=
        value_of_RepresentsY hOUT₂
      have hrv2 : ((a * (b / 2 ^ (256 * h + t))) % m +
          (a * (b / 2 ^ (256 * h + t))) % m) % m < m :=
        Nat.mod_lt _ hm0
      have hBitsIn : findLabel l.lBits programAsm = some
          (jumpIfZ (.load T1) l.lNextLimb ++ (store T1 (.bin .sub (.load T1) (.imm 1)) ++
          (mmCallSite OUT OUT l.lSqRet l.lamEntry ++
          (jumpIfZ (bitTestOf T0 T1) l.lBits ++
          (mmCallSite OUT ACC l.lAddRet l.lamEntry ++ ([.jump l.lBits] ++
            (mulModBitsTail l ++ cont))))))) := by
        rw [hBits, hTop]
      rcases Nat.eq_zero_or_pos ((lget bs h / 2 ^ (t - 1)) % 2) with hb0 | hbp
      · -- bit zero: jump back
        have h0eq : evalExpr (bitTestOf T0 T1) S₂
            = BitVec.ofNat 256 0 := hbitword 0 (by omega) hb0.symm
        have hj := jumpIfZ_taken (σ := σ) (e := bitTestOf T0 T1) (l := l.lBits)
          (k := mmCallSite OUT ACC l.lAddRet l.lamEntry ++
            ([.jump l.lBits] ++ (mulModBitsTail l ++ cont)))
          hbitok h0eq hBitsIn
        -- value: r2 = a * (b / 2^(256h + (t-1)))
        have hvalnew : RepresentsY S₂.memory OUT n
            ((a * (b / 2 ^ (256 * h + (t - 1)))) % m) := by
          refine ⟨Nat.lt_of_lt_of_le (Nat.mod_lt _ hm0) (Nat.le_of_lt hmodRep.1), ?_⟩
          have hr := round_bit m a (b / 2 ^ (256 * h + t))
            ((a * (b / 2 ^ (256 * h + t))) % m)
            (((a * (b / 2 ^ (256 * h + t))) % m +
              (a * (b / 2 ^ (256 * h + t))) % m) % m)
            (((a * (b / 2 ^ (256 * h + t))) % m +
              (a * (b / 2 ^ (256 * h + t))) % m) % m) 0
            rfl rfl
            (by
              rw [Nat.zero_mul, Nat.add_zero, Nat.mod_eq_of_lt hrv2])
          have heq : b / 2 ^ (256 * h + t - 1)
              = 2 * (b / 2 ^ (256 * h + t)) + 0 := by
            have h1 : (b / 2 ^ (256 * h + t - 1)) % 2 = 0 := by
              rw [show 256 * h + t - 1 = 256 * h + (t - 1) from by omega,
                hbitbridge]
              exact hb0
            omega
          rw [hOUT₂.2, hr,
            show 2 * (b / 2 ^ (256 * h + t)) + 0
                = b / 2 ^ (256 * h + (t - 1)) from by
              rw [show 256 * h + (t - 1) = 256 * h + t - 1 from by omega]
              omega]
        left
        have hchain : ASteps programAsm
            ⟨mulModFromBits l ++ cont, σ, St⟩
            ⟨mulModFromBits l ++ cont, σ, S₂⟩ := by
          rw [hTop]
          exact ((s1.trans s2).trans hsq).trans hj
        have hBPTR₂ : (loadWord S₂.memory BPTR).toNat = bptr := by
          rw [loadWord_of_addKeeps hkeeps₂a
            (Or.inr (by omega)) (Or.inr (by omega))
            (hregdisj BPTR (by simp)), hBPTRwS₁, BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt (by omega)]
        exact ⟨S₂, ⟨h, t - 1, hHI₂, hT1₂, by omega, by omega, by omega,
          by rw [hT0w₂, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlimb256],
          hvalnew, hacc₂, hbs₂, hmod₂, hN₂, hkeeps₂, by rw [haw₂, hawEq],
          hBPTR₂, (henv₂.trans henvS₁).trans henvSt⟩, hchain⟩
      · -- bit one: add ACC, then jump back
        have hb1 : (lget bs h / 2 ^ (t - 1)) % 2 = 1 := by
          have hmod := Nat.mod_lt (lget bs h / 2 ^ (t - 1))
            (show (0 : Nat) < 2 by omega)
          omega
        have h1ne : evalExpr (bitTestOf T0 T1) S₂ ≠ 0 := by
          rw [hbitword 1 (by omega) hb1.symm]
          exact ofNat_ne_zero (by omega) (by omega)
        have hj := jumpIfZ_fall (prog := programAsm) (σ := σ) (e := bitTestOf T0 T1) (l := l.lBits)
          (k := mmCallSite OUT ACC l.lAddRet l.lamEntry ++
            ([.jump l.lBits] ++ (mulModBitsTail l ++ cont)))
          hbitok h1ne
        obtain ⟨S₃, had, hOUT₃, hN₃, hkeeps₃a, haw₃, henv₃⟩ :=
          cs.correct OUT ACC l.lAddRet (mmAdCont l ++ cont) σ S₂ n m
            (((a * (b / 2 ^ (256 * h + t))) % m +
                (a * (b / 2 ^ (256 * h + t))) % m) % m) a
            hn hn32 hN₂ hawS₂ houtN haccN hmodOut hmodAcc
            (Or.inl haccOut) houtSubc haccSubc
            (hmodRepOf hmod₂) hm0 hOUT₂ hrv2
            (haccRepOf hacc₂) (Nat.le_of_lt ham) hAddRet
        rw [hAdCont] at had
        have hjump := astep_jump (prog := programAsm) (l := l.lBits)
          (k := mulModBitsTail l ++ cont) (σ := σ) (yst := S₃) hBitsIn
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
        have hbs₃ : yLimbs S₃.memory bptr n = bs :=
          (yLimbs_congr (fun a ha1 ha2 =>
            hkeeps₃a a (by rcases hbOut with h | h <;> omega)
              (by rcases hbSubc with h | h <;> omega)
              (fun c hc => by
                have hc' := scratch_cells hc
                have hge := fragCells_ge c hc'
                omega))).trans hbs₂
        have hmod₃ : yLimbs S₃.memory MOD n = limbDigits n m :=
          (yLimbs_of_mulKeeps hkeeps₃ (Or.inl hmodOut) (Or.inl hmodAcc)
            (Or.inl (by omega : MOD + 32 * n ≤ SUBC)) hmodN).trans
            ((yLimbs_of_mulKeeps hkeeps₂ (Or.inl hmodOut) (Or.inl hmodAcc)
              (Or.inl (by omega : MOD + 32 * n ≤ SUBC)) hmodN).symm.trans hmod₂)
        have hvalnew : RepresentsY S₃.memory OUT n
            ((a * (b / 2 ^ (256 * h + (t - 1)))) % m) := by
          refine ⟨Nat.lt_of_lt_of_le (Nat.mod_lt _ hm0)
            (Nat.le_of_lt hmodRep.1), ?_⟩
          have hOUT₂v' : Nat.ofDigits radix (yLimbs S₂.memory OUT n)
              = ((a * (b / 2 ^ (256 * h + t))) % m +
                (a * (b / 2 ^ (256 * h + t))) % m) % m :=
            value_of_RepresentsY hOUT₂
          have hOUT₃v : Nat.ofDigits radix (yLimbs S₃.memory OUT n)
              = ((((a * (b / 2 ^ (256 * h + t))) % m +
                  (a * (b / 2 ^ (256 * h + t))) % m) % m) + a) % m :=
            value_of_RepresentsY hOUT₃
          have hr := round_bit m a (b / 2 ^ (256 * h + t))
            ((a * (b / 2 ^ (256 * h + t))) % m)
            (((a * (b / 2 ^ (256 * h + t))) % m +
              (a * (b / 2 ^ (256 * h + t))) % m) % m)
            (((((a * (b / 2 ^ (256 * h + t))) % m +
                (a * (b / 2 ^ (256 * h + t))) % m) % m) + a) % m) 1
            rfl rfl (by rw [Nat.one_mul])
          have heq : b / 2 ^ (256 * h + t - 1)
              = 2 * (b / 2 ^ (256 * h + t)) + 1 := by
            have h1 : (b / 2 ^ (256 * h + t - 1)) % 2 = 1 := by
              rw [show 256 * h + t - 1 = 256 * h + (t - 1) from by omega,
                hbitbridge]
              exact hb1
            omega
          rw [hOUT₃.2, hr,
            show 2 * (b / 2 ^ (256 * h + t)) + 1
                = b / 2 ^ (256 * h + (t - 1)) from by
              rw [show 256 * h + (t - 1) = 256 * h + t - 1 from by omega]
              omega]
        left
        have hchain : ASteps programAsm
            ⟨mulModFromBits l ++ cont, σ, St⟩
            ⟨mulModFromBits l ++ cont, σ, S₃⟩ := by
          rw [hTop]
          exact (((s1.trans s2).trans hsq).trans hj).trans
            (had.trans (ASteps.single hjump))
        have hBPTRw₂ : loadWord S₂.memory BPTR = BitVec.ofNat 256 bptr := by
          rw [loadWord_of_addKeeps hkeeps₂a
            (Or.inr (by omega)) (Or.inr (by omega))
            (hregdisj BPTR (by simp))]
          exact hBPTRwS₁
        have hBPTR₃ : (loadWord S₃.memory BPTR).toNat = bptr := by
          rw [loadWord_of_addKeeps hkeeps₃a
            (Or.inr (by omega)) (Or.inr (by omega))
            (hregdisj BPTR (by simp)), hBPTRw₂, BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt (by omega)]
        exact ⟨S₃, ⟨h, t - 1, hHI₃, hT1₃, by omega, by omega, by omega,
          hT0₃, hvalnew,
          (yLimbs_of_keeps hkeeps₃a (Or.inl haccOut) haccSubc
            (fun c hc => by have := fragCells_ge c (scratch_cells hc); omega)).trans hacc₂,
          hbs₃, hmod₃, hN₃, hkeeps₃, by rw [haw₃, haw₂, hawEq], hBPTR₃,
          henv₃.trans ((henv₂.trans henvS₁).trans henvSt)⟩, hchain⟩
  -- the exit at μ = 0: h = 0 ∧ t = 0, two taken jumps, state preserved
  have hexit : ∀ St : EvmState,
      (∃ h t, (loadWord St.memory HIcell).toNat = h ∧
        (loadWord St.memory T1).toNat = t ∧ 257 * h + t = 0 ∧ t ≤ 256 ∧
        h < n ∧ (loadWord St.memory T0).toNat = lget bs h ∧
        RepresentsY St.memory OUT n ((a * (b / 2 ^ (256 * h + t))) % m) ∧
        yLimbs St.memory ACC n = limbDigits n a ∧
        yLimbs St.memory bptr n = bs ∧
        yLimbs St.memory MOD n = limbDigits n m ∧
        (loadWord St.memory Ncell).toNat = n ∧
        MulModKeeps St.memory M₀ n ∧ St.activeWords = S.activeWords ∧
        (loadWord St.memory BPTR).toNat = bptr ∧
        St.env = S.env) →
      (RepresentsY St.memory OUT n ((a * b) % m) ∧
          (loadWord St.memory Ncell).toNat = n ∧
          MulModKeeps St.memory M₀ n ∧
          St.activeWords = S.activeWords ∧
          St.env = S.env) ∧
        ASteps programAsm ⟨mulModFromBits l ++ cont, σ, St⟩
          ⟨mulModFromRet l ++ cont, σ, St⟩ := by
    intro St hm
    rcases hm with ⟨h, t, hHIst, hT1st, hμeq, -, -, hT0st, hvalst, -, -, -,
      hNst, hkeepsst, hawEq, -, henvSt⟩
    have hawSt : 0x1f40 ≤ 32 * St.activeWords.toNat := by
      rw [hawEq]; exact haw
    have h0 : h = 0 ∧ t = 0 := by omega
    have hvalb : RepresentsY St.memory OUT n ((a * b) % m) := by
      refine ⟨Nat.lt_of_lt_of_le (Nat.mod_lt _ hm0)
        (Nat.le_of_lt hmodRep.1), ?_⟩
      rw [hvalst.2, h0.1, h0.2, show b / 2 ^ (256 * 0 + 0) = b from by
        rw [Nat.mul_zero, Nat.add_zero, Nat.pow_zero, Nat.div_one]]
    have hj1 : evalExpr (.load T1) St = 0 := by
      show loadWord St.memory T1 = 0
      rw [word_of_toNat hT1st (by omega), h0.2]
      rfl
    have hj2 : evalExpr (.load HIcell) St = 0 := by
      show loadWord St.memory HIcell = 0
      rw [word_of_toNat hHIst (by omega), h0.1]
      rfl
    refine ⟨⟨hvalb, hNst, hkeepsst, hawEq, henvSt⟩, ?_⟩
    have hNextLimbI := hNextLimb
    rw [mulModFromNextLimb_eq2, mulModNextLimbBody_eq] at hNextLimbI
    have hs1 := jumpIfZ_taken (σ := σ) (e := .load T1)
      (l := l.lNextLimb)
      (c' := jumpIfZ (.load HIcell) l.lDone ++
        (store HIcell (.bin .sub (.load HIcell) (.imm 1)) ++
        (store T1 (.imm 256) ++
        (store T0 (loadAt (.bin .add (.load BPTR)
          (.bin .mul (.imm 32) (.load HIcell)))) ++
        ([.jump l.lBits] ++ [.label l.lZero] ++
        (mulModFromZero l ++ cont))))))
      (k := store T1 (.bin .sub (.load T1) (.imm 1)) ++
          (mmCallSite OUT OUT l.lSqRet l.lamEntry ++
          (jumpIfZ (bitTestOf T0 T1) l.lBits ++
          (mmCallSite OUT ACC l.lAddRet l.lamEntry ++ ([.jump l.lBits] ++
            (mulModBitsTail l ++ cont))))))
      (exprOK_load_cell' hawSt (by simp [fragCells])) hj1 hNextLimbI
    have hs2 := jumpIfZ_taken (σ := σ) (e := .load HIcell)
      (l := l.lDone) (c' := mulModFromRet l ++ cont)
      (k := store HIcell (.bin .sub (.load HIcell) (.imm 1)) ++
        (store T1 (.imm 256) ++
        (store T0 (loadAt (.bin .add (.load BPTR)
          (.bin .mul (.imm 32) (.load HIcell)))) ++
        ([.jump l.lBits] ++ [.label l.lZero] ++
        (mulModFromZero l ++ cont)))))
      (exprOK_load_cell' hawSt (by simp [fragCells])) hj2 hDone
    rw [hTop]
    exact hs1.trans hs2
  obtain ⟨S', hP', hsteps⟩ :=
    loop_counted (prog := programAsm)
      (top := mulModFromBits l ++ cont) (σ := σ)
      (c' := mulModFromRet l ++ cont)
      (Inv := fun St μ => ∃ h t, (loadWord St.memory HIcell).toNat = h ∧
        (loadWord St.memory T1).toNat = t ∧ 257 * h + t = μ ∧ t ≤ 256 ∧
        h < n ∧ (loadWord St.memory T0).toNat = lget bs h ∧
        RepresentsY St.memory OUT n ((a * (b / 2 ^ (256 * h + t))) % m) ∧
        yLimbs St.memory ACC n = limbDigits n a ∧
        yLimbs St.memory bptr n = bs ∧
        yLimbs St.memory MOD n = limbDigits n m ∧
        (loadWord St.memory Ncell).toNat = n ∧
        MulModKeeps St.memory M₀ n ∧ St.activeWords = S.activeWords ∧
        (loadWord St.memory BPTR).toNat = bptr ∧
        St.env = S.env)
      (P := fun St => RepresentsY St.memory OUT n ((a * b) % m) ∧
        (loadWord St.memory Ncell).toNat = n ∧
        MulModKeeps St.memory M₀ n ∧ St.activeWords = S.activeWords ∧
        St.env = S.env)
      hround hexit (n := 257 * h₀ + t₀) (yst := S)
      ⟨h₀, t₀, hHI, hT1, rfl, ht₀, hh₀, hT0, hval, haccRep.2, hbs, hmodRep.2,
        hN, hkeeps, rfl, hBPTR, rfl⟩
  exact ⟨S', hsteps, hP'.1, hP'.2.1, hP'.2.2.1, hP'.2.2.2.1, hP'.2.2.2.2⟩
/-! ## The procedure's entry-level theorem -/

set_option maxHeartbeats 80000000 in
/-- The `mulModBig` procedure from its entry code (the return address
already on the stack) to the trailing `.dynJump`: the `ACC` region comes to
represent `(a * b) % m`, `Ncell` still holds `n`, the `mulMod` frame is
preserved, and `activeWords` and the environment are unchanged.  The
`findLabel` hypotheses are discharged by `decide` over the concrete
`programAsm` in the call-site wrapper below. -/
theorem mulModProcEntry_correct (l : MulModProcLabels) (cs : CallSpec l)
    (bptr : Nat) (n m a b : Nat)
    {σ : List AVal} {yst : EvmState}
    (hScan : findLabel l.lScanTop programAsm =
      some (mulModScanTopBody l ++ (mulModFromTopBit l ++ ([] : List Asm))))
    (hTopBit : findLabel l.lTopBit programAsm =
      some (mulModTopBitBody l ++ ([Asm.label l.lCopy] ++
        (mulModCopyBody OUT ACC l.lBits l ++
          ([Asm.label l.lBits] ++ (mulModFromBits l ++ ([] : List Asm)))))))
    (hCopy : findLabel l.lCopy programAsm =
      some (mulModCopyBody OUT ACC l.lBits l ++
        ([Asm.label l.lBits] ++ (mulModFromBits l ++ ([] : List Asm)))))
    (hBits : findLabel l.lBits programAsm =
      some (mulModFromBits l ++ ([] : List Asm)))
    (hNextLimb : findLabel l.lNextLimb programAsm =
      some (mulModFromNextLimb l ++ ([] : List Asm)))
    (hZero : findLabel l.lZero programAsm = some (mulModFromZero l ++ ([] : List Asm)))
    (hZeroLoop : findLabel l.lZeroLoop programAsm =
      some (mulModZeroLoopBody l ++
        ([Asm.label l.lDone] ++ (mulModFromRet l ++ ([] : List Asm)))))
    (hDone : findLabel l.lDone programAsm = some (mulModFromRet l ++ ([] : List Asm)))
    (hRetCopy : findLabel l.lRetCopy programAsm =
      some (mulModRetCopyBody l ++ ([Asm.label l.lExit] ++ [.dynJump])))
    (hExit : findLabel l.lExit programAsm = some [.dynJump])
    (hSqRet : findLabel l.lSqRet programAsm = some (mmSqCont l ++ ([] : List Asm)))
    (hAddRet : findLabel l.lAddRet programAsm = some (mmAdCont l ++ ([] : List Asm)))
    (hn : 0 < n) (hn32 : n ≤ 32)
    (hbptrN : bptr + 32 * n ≤ Ncell)
    (hbOut : bptr + 32 * n ≤ OUT ∨ OUT + 32 * n ≤ bptr)
    (hbAcc : bptr + 32 * n ≤ ACC ∨ ACC + 32 * n ≤ bptr ∨ bptr = ACC)
    (hbSubc : bptr + 32 * n ≤ SUBC ∨ SUBC + 32 * n ≤ bptr)
    (haw : 0x1f40 ≤ 32 * yst.activeWords.toNat)
    (hN : (loadWord yst.memory Ncell).toNat = n)
    (hBPTR : (loadWord yst.memory BPTR).toNat = bptr)
    (hmodRep : RepresentsY yst.memory MOD n m) (hm0 : 0 < m)
    (haccRep : RepresentsY yst.memory ACC n a) (ham : a < m)
    (hbRep : RepresentsY yst.memory bptr n b) :
    ∃ yst', ASteps programAsm ⟨mulModProcBody l ++ ([] : List Asm), σ, yst⟩
        ⟨[.dynJump], σ, yst'⟩ ∧
      RepresentsY yst'.memory ACC n ((a * b) % m) ∧
      (loadWord yst'.memory Ncell).toNat = n ∧
      (∀ q, (q < OUT ∨ OUT + 32 * n ≤ q) → (q < ACC ∨ ACC + 32 * n ≤ q) →
        (q < SUBC ∨ SUBC + 32 * n ≤ q) →
        (∀ c ∈ mulModScratch, q < c ∨ c + 32 ≤ q) →
        yst'.memory q = yst.memory q) ∧
      yst'.activeWords = yst.activeWords ∧ yst'.env = yst.env := by

  have hOUTlit : (OUT : Nat) = 0xc00 := rfl
  have hMODlit : (MOD : Nat) = 0 := rfl
  have hACClit : (ACC : Nat) = 0x800 := rfl
  have hSUBClit : (SUBC : Nat) = 0x1400 := rfl
  have hNcellLit : (Ncell : Nat) = 0x1cc0 := rfl
  have hHIlit : (HIcell : Nat) = 0x1d80 := rfl
  have hT0lit : (T0 : Nat) = 0x1dc0 := rfl
  have hT1lit : (T1 : Nat) = 0x1de0 := rfl
  have hI2lit : (I2 : Nat) = 0x1e60 := rfl
  have hBPTRlit : (BPTR : Nat) = 0x1da0 := rfl
  have houtN : OUT + 32 * n ≤ Ncell := by omega
  have haccN : ACC + 32 * n ≤ Ncell := by omega
  have haccOut : ACC + 32 * n ≤ OUT := by omega
  have houtSubc : OUT + 32 * n ≤ SUBC := by omega
  have haccSubc : ACC + 32 * n ≤ SUBC := by omega
  have hmodOut : MOD + 32 * n ≤ OUT := by omega
  have hmodAcc : MOD + 32 * n ≤ ACC := by omega
  have hmodN : MOD + 32 * n ≤ Ncell := by omega
  have hBPTRdisjM₀ : ∀ c ∈ mulModScratch, BPTR + 32 ≤ c ∨ c + 32 ≤ BPTR := by
    intro c hc
    unfold mulModScratch at hc
    rcases List.mem_append.mp hc with h | h
    · have hlit : ∀ c ∈ [HIcell, T0, T1],
          BPTR + 32 ≤ c ∨ c + 32 ≤ BPTR := by decide
      exact hlit c h
    · exact addScratch_vs_regs c h BPTR (by simp)
  have hBPTRM₀word : loadWord yst.memory BPTR = BitVec.ofNat 256 bptr :=
    BPTR_word hBPTR (by omega)
  set bs : List Nat := yLimbs yst.memory bptr n with hbsdef
  have hbv : b = Nat.ofDigits radix bs :=
    (value_of_RepresentsY hbRep).symm
  have hbsd : ∀ d ∈ bs, d < radix := fun d hd => yLimb_lt hd
  have hbslen : bs.length = n := length_yLimbs yst.memory bptr n
  -- entry: HI := n, then the label
  have hevN : evalExpr (.load Ncell) yst = BitVec.ofNat 256 n := by
    show loadWord yst.memory Ncell = _
    rw [word_of_toNat hN (by omega)]
  have s0 := store_cell_val (prog := programAsm) (c := HIcell) (e := .load Ncell)
    (w := BitVec.ofNat 256 n)
    (k := [Asm.label l.lScanTop] ++ (mulModScanTopBody l ++
      (mulModFromTopBit l ++ ([] : List Asm))))
    (σ := σ) hevN (exprOK_load_cell' haw (by simp [fragCells]))
    (haw_pin haw (by simp [fragCells]))
  set S₀ : EvmState := {yst with memory :=
      (storeWord yst.memory HIcell (BitVec.ofNat 256 n))} with hS₀def
  have hS₀mem : S₀.memory =
      storeWord yst.memory HIcell (BitVec.ofNat 256 n) := rfl
  have hBPTR₀ : (loadWord S₀.memory BPTR).toNat = bptr := by
    rw [hS₀mem, loadWord_storeWord_disj (p := HIcell) (q := BPTR)
      (cells_disj (by simp [fragCells]) (by simp [fragCells]) (by decide)),
      hBPTRM₀word, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hawS₀ : 0x1f40 ≤ 32 * S₀.activeWords.toNat := haw
  have hHI₀ : (loadWord S₀.memory HIcell).toNat = n := by
    rw [hS₀mem, loadWord_storeWord, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega)]
  have hN₀ : (loadWord S₀.memory Ncell).toNat = n := by
    rw [hS₀mem, loadWord_storeWord_disj (p := HIcell) (q := Ncell)
      (cells_disj (by simp [fragCells]) (by simp [fragCells]) (by decide))]
    exact hN
  have hkeeps₀ : MulModKeeps S₀.memory yst.memory n :=
    mulKeeps_storeWord (mulKeeps_refl yst.memory n)
      (Or.inr (by simp [mulModScratch]))
  have hmod₀ : RepresentsY S₀.memory MOD n m := by
    refine ⟨hmodRep.1, ?_⟩
    rw [hS₀mem, yLimbs_storeWord_disjoint (q := HIcell)
      (Or.inr (by omega))]
    exact hmodRep.2
  have hacc₀ : RepresentsY S₀.memory ACC n a := by
    refine ⟨haccRep.1, ?_⟩
    rw [hS₀mem, yLimbs_storeWord_disjoint (q := HIcell)
      (Or.inr (by omega))]
    exact haccRep.2
  have hbs₀ : yLimbs S₀.memory bptr n = bs := by
    rw [hS₀mem, yLimbs_storeWord_disjoint (q := HIcell)
      (Or.inr (by omega))]
  have sentry : ASteps programAsm ⟨mulModProcBody l ++ ([] : List Asm), σ, yst⟩
      ⟨mulModScanTopBody l ++
        (mulModFromTopBit l ++ ([] : List Asm)), σ, S₀⟩ := by
    rw [show mulModProcBody l ++ ([] : List Asm) =
      store HIcell (.load Ncell) ++ ([.label l.lScanTop] ++
        (mulModScanTopBody l ++ (mulModFromTopBit l ++ ([] : List Asm)))) from by
        rw [mulModProcBody_split]; simp only [List.append_assoc]]
    exact (s0.trans (ASteps.single (astep_label (prog := programAsm)
      (l := l.lScanTop)
      (k := mulModScanTopBody l ++
        (mulModFromTopBit l ++ ([] : List Asm))) (σ := σ)
      (yst := S₀))))
  rcases mulScan_steps (σ := σ) bptr l bs n hScan hZero hn hn32 hbptrN n S₀
      hawS₀ hN₀ hkeeps₀ hbs₀ hBPTR₀ hHI₀ (Nat.le_refl n)
      (fun j _ hj => absurd hj (by omega)) with
    ⟨Sz, hsz, hallzero, hkeepsZ, hNZ, hawZ, hbsZ, henvZ⟩
  | ⟨St, hst, htop, htoplt, htopnz, hHISt, hT0St, hT1St, hupperSt,
      hkeepsSt, hNSt, hawStEq, hbsSt, haccSt, henvSt⟩
  · ---------------------------------------------------------------- zero path
    have hbz : b = 0 := by
      rw [hbv, ofDigits_zero_all bs (fun j hj => hallzero j (by omega))]
    have hval0 : (a * b) % m = 0 := by
      rw [hbz]
      simp
    have hawZ' : 0x1f40 ≤ 32 * Sz.activeWords.toNat := by
      rw [hawZ]; exact hawS₀
    rw [mulModFromZero_eq] at hsz
    have s1 := store_cell_val (prog := programAsm) (c := I2) (e := .imm 0)
      (w := BitVec.ofNat 256 0)
      (k := [Asm.label l.lZeroLoop] ++
        (mulModZeroLoopBody l ++
          ([Asm.label l.lDone] ++ (mulModFromRet l ++ ([] : List Asm)))))
      (σ := σ) (yst := Sz) rfl True.intro
      (haw_pin hawZ' (by simp [fragCells]))
    set Sz₁ : EvmState := {Sz with memory :=
        (storeWord Sz.memory I2 (BitVec.ofNat 256 0))} with hSz₁def
    have hSz₁mem : Sz₁.memory =
        storeWord Sz.memory I2 (BitVec.ofNat 256 0) := rfl
    have hawZ₁ : 0x1f40 ≤ 32 * Sz₁.activeWords.toNat := hawZ'
    have hI2Z₁ : (loadWord Sz₁.memory I2).toNat = 0 := by
      rw [hSz₁mem, loadWord_storeWord, BitVec.toNat_ofNat]
    have hNZ₁ : (loadWord Sz₁.memory Ncell).toNat = n := by
      rw [hSz₁mem, loadWord_storeWord_disj (p := I2) (q := Ncell)
        (cells_disj (by simp [fragCells]) (by simp [fragCells])
          (by decide))]
      exact hNZ
    obtain ⟨Sz', hzloop, houtZ, hNZ', hbytesZ, hawZ₂, henvZ₂⟩ :=
      mulZeroLoop_steps (l := l) (out₀ := yLimbs Sz₁.memory OUT n)
        (n := n) (c' := mulModFromRet l ++ ([] : List Asm))
        (k := [Asm.label l.lDone] ++ (mulModFromRet l ++ ([] : List Asm)))
        (σ := σ) (S := Sz₁) hZeroLoop hDone hawZ₁ hn hn32 houtN hNZ₁
        hI2Z₁ rfl (length_yLimbs Sz₁.memory OUT n)
    have hkeepsZ' : MulModKeeps Sz'.memory yst.memory n := by
      refine mulKeeps_trans ?_ hkeepsZ
      intro q hq1 hq2 hq3 hq4
      calc
        Sz'.memory q = Sz₁.memory q :=
          hbytesZ q hq1
            (hq4 I2 (mulScratch_add (show I2 ∈ addModScratch by decide)))
        _ = Sz.memory q := by
          rw [hSz₁mem]
          exact storeWord_other
            (hq4 I2 (mulScratch_add (show I2 ∈ addModScratch by decide)))
    rw [List.append_nil] at hzloop
    obtain ⟨Sf, htail, haccF, hNf, hkeepsF, hawF, henvF⟩ :=
      mulTail_steps (σ := σ) (l := l) (n := n) hRetCopy hExit
        (by rw [hawZ₂]; exact hawZ') hn hn32 hNZ' hkeepsZ'
    have hzeroStart : ASteps programAsm
        ⟨mulModZeroEntry ++ ([Asm.label l.lZeroLoop] ++ (mulModZeroLoopBody l ++
          ([Asm.label l.lDone] ++ (mulModFromRet l ++ ([] : List Asm))))), σ, Sz⟩
        ⟨mulModZeroLoopBody l ++ ([Asm.label l.lDone] ++ (mulModFromRet l ++ ([] : List Asm))),
          σ, Sz₁⟩ :=
      s1.trans (ASteps.single (astep_label (prog := programAsm) (l := l.lZeroLoop)
        (k := mulModZeroLoopBody l ++
          ([Asm.label l.lDone] ++ (mulModFromRet l ++ ([] : List Asm))))
        (σ := σ) (yst := Sz₁)))
    have hzeroSteps :=
      (((sentry.trans hsz).trans hzeroStart).trans hzloop).trans htail
    refine ⟨Sf, hzeroSteps, ?_, hNf, hkeepsF,
      by rw [hawF, hawZ₂, hawZ], by rw [henvF, henvZ₂, henvZ]⟩
    rw [hval0]
    refine (RepresentsY_iff_value ?_).mpr ?_
    · have h1 : 0 < radix ^ n := by
        have := Nat.one_le_pow n radix radix_pos
        omega
      exact h1
    · rw [haccF, houtZ, ofDigits_replicate_zero n]
  · ---------------------------------------------------------------- main path
    have hlab : AStep programAsm
        ⟨mulModFromTopBit l ++ ([] : List Asm), σ, St⟩
        ⟨mulModTopBitBody l ++ ([Asm.label l.lCopy] ++
          (mulModCopyBody OUT ACC l.lBits l ++
            ([Asm.label l.lBits] ++ (mulModFromBits l ++ ([] : List Asm))))), σ, St⟩ := by
      rw [mulModFromTopBit_eq2]
      exact astep_label
    have hawSt : 0x1f40 ≤ 32 * St.activeWords.toNat := by
      rw [hawStEq]; exact hawS₀
    have henvStEq : St.env = S₀.env := henvSt
    have hL256 : lget bs htop < 2 ^ 256 := by
      have h1 : lget bs htop < radix :=
        hbsd _ (by
          rw [lget_eq (show htop < bs.length by omega)]
          exact mem_getElem (show htop < bs.length by omega))
      rw [hradius] at h1
      exact h1
    obtain ⟨S₂, τ, htop', hT1₂, hτle, hτlt, hHI₂, hT0₂, hI2₂, hN₂, hacc₂,
        hkeeps₂, haw₂, henv₂⟩ :=
      mulTopBit_steps (σ := σ) (l := l) (n := n) (h := htop) (L := lget bs htop)
        (hTopBit := hTopBit) (haw := hawSt) (hn32 := hn32) (hN := hNSt)
        (hHI := hHISt) (hT1 := hT1St) (hT0 := hT0St)
        (hL0 := Nat.pos_of_ne_zero htopnz) (hL256 := hL256) (hkeeps := hkeepsSt)
    have hawS₂ : 0x1f40 ≤ 32 * S₂.activeWords.toNat := by
      rw [haw₂]; exact hawSt
    have hacc₂a : yLimbs S₂.memory ACC n = limbDigits n a := by
      rw [hacc₂, haccSt]
      exact hacc₀.2
    have hbs₂ : yLimbs S₂.memory bptr n = bs := by
      rcases hbAcc with h | h | rfl
      · exact (yLimbs_of_mulKeeps hkeeps₂ hbOut (Or.inl h) hbSubc hbptrN).trans
          hbsdef.symm
      · exact (yLimbs_of_mulKeeps hkeeps₂ hbOut (Or.inr h) hbSubc hbptrN).trans
          hbsdef.symm
      · have hS0acc : yLimbs S₀.memory ACC n = yLimbs yst.memory ACC n := by
          rw [hS₀mem, yLimbs_storeWord_disjoint (q := HIcell) (Or.inr (by omega))]
        exact hacc₂.trans (haccSt.trans (hS0acc.trans hbsdef.symm))
    -- copy-in: OUT := ACC
    obtain ⟨S₃, hcopyin, hout₃, hN₃, hacc₃, hbytes₃, haw₃, henv₃⟩ :=
      mulCopyLoop_steps (dstBase := OUT) (srcBase := ACC) (l := l)
        (xs := limbDigits n a) (out₀ := yLimbs S₂.memory OUT n) (n := n)
        (lExit := l.lBits)
        (σ := σ) (S := S₂) hCopy hBits hawS₂ hn hn32 houtN haccN
        (Or.inr haccOut) hN₂ hI2₂ rfl hacc₂a
        (length_limbDigits haccRep.1)
        (length_yLimbs S₂.memory OUT n)
        (fun d hd => limbDigits_lt hd)
    have hawS₃ : 0x1f40 ≤ 32 * S₃.activeWords.toNat := by
      rw [haw₃]; exact hawS₂
    -- regions preserved into S₃
    have hkeeps₃ : MulModKeeps S₃.memory yst.memory n := by
      refine mulKeeps_trans ?_ hkeeps₂
      intro q hq1 hq2 hq3 hq4
      exact hbytes₃ q hq1
        (hq4 I2 (mulScratch_add (show I2 ∈ addModScratch by decide)))
    have hmodSubc : MOD + 32 * n ≤ SUBC := by omega
    have hmod₃ : RepresentsY S₃.memory MOD n m :=
      ⟨hmodRep.1, (yLimbs_of_mulKeeps hkeeps₃ (Or.inl hmodOut)
        (Or.inl hmodAcc) (Or.inl hmodSubc) hmodN).trans hmodRep.2⟩
    have hacc₃rep : RepresentsY S₃.memory ACC n a := ⟨haccRep.1, hacc₃⟩
    have hbs₃ : yLimbs S₃.memory bptr n = bs := by
      rw [← hbs₂]
      refine yLimbs_congr ?_
      intro q hq1 hq2
      exact hbytes₃ q (by rcases hbOut with h | h <;> omega)
        (show q < I2 ∨ I2 + 32 ≤ q by
          have := fragCells_ge I2 (by simp [fragCells])
          omega)
    -- cell values into S₃ (the copy-in writes only the OUT region and I2)
    have hloadq (q : Nat) (hq1 : q + 32 ≤ OUT ∨ OUT + 32 * n ≤ q)
        (hq2 : q + 32 ≤ I2 ∨ I2 + 32 ≤ q) :
        loadWord S₃.memory q = loadWord S₂.memory q := by
      rw [loadWord_congr]
      intro d hd1 hd2
      exact hbytes₃ d (by rcases hq1 with h | h <;> omega)
        (show d < I2 ∨ I2 + 32 ≤ d by rcases hq2 with h | h <;> omega)
    have hHI₃ : (loadWord S₃.memory HIcell).toNat = htop := by
      rw [hloadq HIcell (Or.inr (by omega)) (Or.inl (by omega)), hHI₂]
    have hT0₃ : (loadWord S₃.memory T0).toNat = lget bs htop := by
      rw [hloadq T0 (Or.inr (by omega)) (Or.inl (by omega))]
      exact hT0₂
    have hT1₃ : (loadWord S₃.memory T1).toNat = τ := by
      rw [hloadq T1 (Or.inr (by omega)) (Or.inl (by omega))]
      exact hT1₂
    -- seed: b / 2^(256*htop+τ) = 1
    have hseed : b / 2 ^ (256 * htop + τ) = 1 := by
      rw [hbv]
      have htopL := div_top_limb bs hbsd htop
        (fun j hj1 hj2 => hupperSt j (by omega) (by omega))
        (show htop < bs.length by omega)
      rw [show 2 ^ (256 * htop + τ) = 2 ^ (256 * htop) * 2 ^ τ from by
          rw [← Nat.pow_add],
        ← Nat.div_div_eq_div_mul, htopL]
      exact seed_top (lget bs htop) τ hτle hτlt
    have hvalbound : (a * (b / 2 ^ (256 * htop + τ))) % m < radix ^ n :=
      Nat.lt_trans (Nat.mod_lt _ hm0) hmodRep.1
    have hval₃ : RepresentsY S₃.memory OUT n
        ((a * (b / 2 ^ (256 * htop + τ))) % m) := by
      refine (RepresentsY_iff_value hvalbound).mpr ?_
      rw [hout₃, value_limbDigits, hseed, Nat.mul_one,
        Nat.mod_eq_of_lt ham]
    -- the bits phase
    obtain ⟨S₄, hbits', hval₄, hN₄, hkeeps₄, haw₄, henv₄⟩ :=
      mulBits_steps (σ := σ) l cs bptr bs n m a b htop τ
        hBits hNextLimb hDone hSqRet hAddRet hawS₃ hn hn32 hbptrN hbOut hbAcc hbSubc
        hmod₃ hm0 hacc₃rep ham hbs₃ hbv hT0₃ hHI₃ htoplt hT1₃
        (show τ ≤ 256 by
          by_contra hcon
          have hpow : 2 ^ 256 ≤ 2 ^ τ :=
            Nat.pow_le_pow_right (by decide) (by omega)
          have hlt : 2 ^ τ < 2 ^ 256 := Nat.lt_of_le_of_lt hτle hL256
          omega) hval₃ hN₃ hkeeps₃
        (by
          rw [loadWord_of_mulKeeps hkeeps₃
            (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega))
            hBPTRdisjM₀, hBPTRM₀word, BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt (by omega)])
    -- the tail
    rw [List.append_nil] at hbits'
    obtain ⟨Sf, htail, haccF, hNf, hkeepsF, hawF, henvF⟩ :=
      mulTail_steps (σ := σ) (l := l) (n := n) hRetCopy hExit
        (by rw [haw₄]; exact hawS₃) hn hn32 hN₄ hkeeps₄
    refine ⟨Sf, (((((sentry.trans hst).trans
        (ASteps.single hlab)).trans htop').trans hcopyin).trans
        hbits').trans htail, ⟨hval₄.1, ?_⟩, hNf,
      hkeepsF, by
        rw [hawF, haw₄, haw₃, haw₂, hawStEq], by
        rw [henvF, henv₄, henv₃, henv₂, henvStEq]⟩
    rw [haccF, hval₄.2]

/-! ## The call-site-composable export -/

set_option maxHeartbeats 400000000 in
/-- The `mulModBig` call site: from `store BPTR (.imm bptr)` +
`[.pushLabel lret, .jump lmmEntry, .label lret]` against a continuation
`cont` whose label resolves, the program reaches `cont` with the stack
unchanged, the `ACC` region representing `(a * b) % m`, `Ncell` holding
`n`, every byte outside the `OUT`/`ACC`/`SUBC` regions and the scratch
cells unchanged, and `activeWords`/environment unchanged. -/
theorem mulModCall_correct (spec : AddModProcSpec) (bptr lret : Nat)
    (n m a b : Nat) (cont : List Asm) (σ : List AVal) (yst : EvmState)
    (hfindRet : findLabel lret programAsm = some cont)
    (hmem : lret ∈ labelDefs programAsm)
    (hfindEntry : findLabel procLabels.lmmEntry programAsm =
      some (mulModProcBody procLabels))
    (hn : 0 < n) (hn32 : n ≤ 32)
    (hbptrN : bptr + 32 * n ≤ Ncell)
    (hbOut : bptr + 32 * n ≤ OUT ∨ OUT + 32 * n ≤ bptr)
    (hbAcc : bptr + 32 * n ≤ ACC ∨ ACC + 32 * n ≤ bptr ∨ bptr = ACC)
    (hbSubc : bptr + 32 * n ≤ SUBC ∨ SUBC + 32 * n ≤ bptr)
    (haw : 0x1f40 ≤ 32 * yst.activeWords.toNat)
    (hN : (loadWord yst.memory Ncell).toNat = n)
    (hmodRep : RepresentsY yst.memory MOD n m) (hm0 : 0 < m)
    (haccRep : RepresentsY yst.memory ACC n a) (ham : a < m)
    (hbRep : RepresentsY yst.memory bptr n b) :
    ∃ yst', ASteps programAsm
        ⟨store BPTR (.imm bptr) ++
          [.pushLabel lret, .jump procLabels.lmmEntry, .label lret] ++ cont,
          σ, yst⟩
        ⟨cont, σ, yst'⟩ ∧
      RepresentsY yst'.memory ACC n ((a * b) % m) ∧
      (loadWord yst'.memory Ncell).toNat = n ∧
      (∀ q, (q < OUT ∨ OUT + 32 * n ≤ q) → (q < ACC ∨ ACC + 32 * n ≤ q) →
        (q < SUBC ∨ SUBC + 32 * n ≤ q) →
        (∀ c ∈ mulModScratch, q < c ∨ c + 32 ≤ q) →
        (q < BPTR ∨ BPTR + 32 ≤ q) →
        yst'.memory q = yst.memory q) ∧
      yst'.activeWords = yst.activeWords ∧ yst'.env = yst.env := by
  -- the BPTR cell setup
  have sB := store_cell_val (prog := programAsm) (c := BPTR) (e := .imm bptr)
    (w := BitVec.ofNat 256 bptr)
    (k := [.pushLabel lret, .jump procLabels.lmmEntry, .label lret] ++ cont)
    (σ := σ) (yst := yst)
    (show evalExpr (.imm bptr) yst = BitVec.ofNat 256 bptr from rfl) True.intro
    (haw_pin haw (by simp [fragCells]))
  have hOUTlit : (OUT : Nat) = 0xc00 := rfl
  have hMODlit : (MOD : Nat) = 0 := rfl
  have hACClit : (ACC : Nat) = 0x800 := rfl
  have hSUBClit : (SUBC : Nat) = 0x1400 := rfl
  have hNcellLit : (Ncell : Nat) = 0x1cc0 := rfl
  have hBPTRlit : (BPTR : Nat) = 0x1da0 := rfl
  set S₀ : EvmState := {yst with memory :=
      (storeWord yst.memory BPTR (BitVec.ofNat 256 bptr))} with hS₀def
  have hS₀mem : S₀.memory =
      storeWord yst.memory BPTR (BitVec.ofNat 256 bptr) := rfl
  have hBPTR₀ : (loadWord S₀.memory BPTR).toNat = bptr := by
    rw [hS₀mem, loadWord_storeWord, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega)]
  have hawS₀ : 0x1f40 ≤ 32 * S₀.activeWords.toNat := haw
  have hNS₀ : (loadWord S₀.memory Ncell).toNat = n := by
    rw [hS₀mem, loadWord_storeWord_disj (p := BPTR) (q := Ncell)
      (cells_disj (by simp [fragCells]) (by simp [fragCells]) (by decide))]
    exact hN
  have hmodS₀ : RepresentsY S₀.memory MOD n m := by
    refine ⟨hmodRep.1, ?_⟩
    rw [hS₀mem, yLimbs_storeWord_disjoint (q := BPTR) (Or.inr (by omega))]
    exact hmodRep.2
  have haccS₀ : RepresentsY S₀.memory ACC n a := by
    refine ⟨haccRep.1, ?_⟩
    rw [hS₀mem, yLimbs_storeWord_disjoint (q := BPTR) (Or.inr (by omega))]
    exact haccRep.2
  have hbsS₀ : yLimbs S₀.memory bptr n = yLimbs yst.memory bptr n := by
    rw [hS₀mem, yLimbs_storeWord_disjoint (q := BPTR)
      (Or.inr (by omega))]
  have hRepS₀ : RepresentsY S₀.memory bptr n b := ⟨hbRep.1, hbsS₀.trans hbRep.2⟩
  -- enter the procedure: pushLabel + jump (the return label stays in cont's place)
  have sentry : ASteps programAsm
      ⟨[.pushLabel lret, .jump procLabels.lmmEntry, .label lret] ++ cont,
        σ, S₀⟩
      ⟨mulModProcBody procLabels ++ ([] : List Asm), .code lret :: σ, S₀⟩ :=
    call_entry_steps (prog := programAsm) (lret := lret)
      (lproc := procLabels.lmmEntry)
      (procBody := mulModProcBody procLabels ++ ([] : List Asm)) hmem
      (by rw [hfindEntry]; rfl)
  -- the findLabel facts, discharged over the concrete program
  have hScan : findLabel procLabels.lScanTop programAsm =
      some (mulModScanTopBody procLabels ++
        (mulModFromTopBit procLabels ++ ([] : List Asm))) := by decide
  have hTopBit : findLabel procLabels.lTopBit programAsm =
      some (mulModTopBitBody procLabels ++ ([Asm.label procLabels.lCopy] ++
        (mulModCopyBody OUT ACC procLabels.lBits procLabels ++
          ([Asm.label procLabels.lBits] ++
            (mulModFromBits procLabels ++ ([] : List Asm)))))) := by decide
  have hCopy : findLabel procLabels.lCopy programAsm =
      some (mulModCopyBody OUT ACC procLabels.lBits procLabels ++
        ([Asm.label procLabels.lBits] ++
          (mulModFromBits procLabels ++ ([] : List Asm)))) := by decide
  have hBits : findLabel procLabels.lBits programAsm =
      some (mulModFromBits procLabels ++ ([] : List Asm)) := by decide
  have hNextLimb : findLabel procLabels.lNextLimb programAsm =
      some (mulModFromNextLimb procLabels ++ ([] : List Asm)) := by decide
  have hZero : findLabel procLabels.lZero programAsm =
      some (mulModFromZero procLabels ++ ([] : List Asm)) := by decide
  have hZeroLoop : findLabel procLabels.lZeroLoop programAsm =
      some (mulModZeroLoopBody procLabels ++
        ([Asm.label procLabels.lDone] ++
          (mulModFromRet procLabels ++ ([] : List Asm)))) := by decide
  have hDone : findLabel procLabels.lDone programAsm =
      some (mulModFromRet procLabels ++ ([] : List Asm)) := by decide
  have hRetCopy : findLabel procLabels.lRetCopy programAsm =
      some (mulModRetCopyBody procLabels ++
        ([Asm.label procLabels.lExit] ++ [.dynJump])) := by decide
  have hExit : findLabel procLabels.lExit programAsm = some [.dynJump] := by decide
  have hSqRet : findLabel procLabels.lSqRet programAsm =
      some (mmSqCont procLabels ++ ([] : List Asm)) := by decide
  have hAddRet : findLabel procLabels.lAddRet programAsm =
      some (mmAdCont procLabels ++ ([] : List Asm)) := by decide
  -- the procedure body
  obtain ⟨yst', hbody, haccF, hNF, hkeepsF, hawF, henvF⟩ :=
    mulModProcEntry_correct (σ := .code lret :: σ) procLabels (callSpecOf spec)
      bptr n m a b
      hScan hTopBit hCopy hBits hNextLimb hZero hZeroLoop hDone hRetCopy hExit
      hSqRet hAddRet hn hn32 hbptrN hbOut hbAcc hbSubc hawS₀ hNS₀ hBPTR₀
      hmodS₀ hm0 haccS₀ ham hRepS₀
  -- the trailing dynJump returns to the caller's continuation
  have sret : ASteps programAsm ⟨[.dynJump], .code lret :: σ, yst'⟩
      ⟨cont, σ, yst'⟩ :=
    ASteps.single (astep_dynJump (prog := programAsm) (l := lret)
      (c' := cont) (k := []) (σ := σ) (yst := yst') hfindRet)
  -- the byte-frame through the BPTR store
  refine ⟨yst', (sB.trans sentry).trans (hbody.trans sret), haccF, hNF, ?_, hawF,
    by rw [henvF]⟩
  intro q hq1 hq2 hq3 hq4 hq5
  have hstep : yst'.memory q = S₀.memory q := hkeepsF q hq1 hq2 hq3 hq4
  rw [hstep, hS₀mem]
  exact storeWord_other (p := BPTR) (a := q) hq5

end Challenge.Modexp.Submission.Proof.MulModProc
