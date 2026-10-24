import Challenge.Modexp.Submission.Proofs.CRT.RoundedWordBridge
import Challenge.Modexp.Submission.Proofs.CRT.ProductAccumulate
set_option warningAsError true
set_option maxHeartbeats 2000000

namespace HistoricalSearch.ColumnExpressions
open EvmSemantics
open Challenge.EvmProof.Word
open HistoricalSearch.CRTColumn HistoricalSearch.ProductAccumulate

/-- A paired low-word/residue sum. Actual products and carries remain UInt256
inputs, so interpreting the tree preserves their exact instruction arithmetic. -/
inductive Expr where
  | product (a b : UInt256)
  | literal (a : UInt256)
  | add (a b : Expr)

def Expr.value : Expr → Nat
  | .product a b => a.toNat*b.toNat
  | .literal a => a.toNat
  | .add a b => a.value+b.value

def Expr.low : Expr → UInt256
  | .product a b => a*b
  | .literal a => a
  | .add a b => a.low+b.low

def Expr.high (P : UInt256) : Expr → UInt256
  | .product a b => UInt256.mulMod a b P
  | .literal a => a
  | .add a b => a.high P+b.high P

def Expr.count : Expr → Nat
  | .product _ _ => 1
  | .literal _ => 1
  | .add a b => a.count+b.count

def Expr.products : Expr → Nat
  | .product _ _ => 1
  | .literal _ => 0
  | .add a b => a.products+b.products

def Expr.literals : Expr → Nat
  | .product _ _ => 0
  | .literal _ => 1
  | .add a b => a.literals+b.literals

def Expr.literalsBounded (C : Nat) : Expr → Prop
  | .product _ _ => True
  | .literal a => a.toNat ≤ C
  | .add a b => a.literalsBounded C ∧ b.literalsBounded C

def Expr.productsBounded (M : Nat) : Expr → Prop
  | .product a b => a.toNat*b.toNat ≤ M
  | .literal _ => True
  | .add a b => a.productsBounded M ∧ b.productsBounded M

theorem lowValue (e : Expr) : e.low.toNat = e.value % wordRadix := by
  induction e with
  | product a b => exact mul_toNat a b
  | literal a => exact (Nat.mod_eq_of_lt a.val.isLt).symm
  | add a b ha hb =>
    change (a.low+b.low).toNat = (a.value+b.value) % wordRadix
    rw [word_toNat_add, ha, hb]
    exact (Nat.add_mod _ _ _).symm

/-- A single structural proof covers all seeded, reassociated and doubled
residue schedules, without choosing a particular addition order. -/
theorem highInvariant (P : UInt256) (hP : P.toNat = residueModulus) (e : Expr)
    (hcount : e.count ≤ 19) (hlit : e.literalsBounded (residueModulus-1)) :
    (e.high P).toNat ≤ e.count*(residueModulus-1) ∧
    (e.high P).toNat % residueModulus = e.value % residueModulus := by
  have hp : 0 < residueModulus := by norm_num [residueModulus]
  have hpw : 0 < P.toNat := by rw [hP]; exact hp
  induction e with
  | product a b =>
    simp only [Expr.high, Expr.count, Expr.value, Nat.one_mul]
    rw [mulMod_toNat a b P hpw, hP, Nat.mod_mod]
    have hr := Nat.mod_lt (a.toNat*b.toNat) hp
    exact ⟨by omega, rfl⟩
  | literal a =>
    exact ⟨by simpa only [Expr.count, Expr.high, Expr.literalsBounded, Nat.one_mul] using hlit, rfl⟩
  | add a b ha hb =>
    have hca : a.count ≤ 19 := by change a.count+b.count ≤ 19 at hcount; omega
    have hcb : b.count ≤ 19 := by change a.count+b.count ≤ 19 at hcount; omega
    have hla := ha hca hlit.1
    have hlb := hb hcb hlit.2
    have hsum : (a.high P).toNat+(b.high P).toNat ≤ (a.count+b.count)*(residueModulus-1) := by
      nlinarith [hla.1, hlb.1]
    have hroom : (a.high P).toNat+(b.high P).toNat < wordRadix := by
      have hsmall : (a.count+b.count)*(residueModulus-1) ≤ 19*(residueModulus-1) :=
        Nat.mul_le_mul_right _ hcount
      have hr : 19*(residueModulus-1) < wordRadix := by norm_num [residueModulus, wordRadix]
      exact hsum.trans_lt (hsmall.trans_lt hr)
    change ((a.high P)+(b.high P)).toNat ≤ (a.count+b.count)*(residueModulus-1) ∧
      ((a.high P)+(b.high P)).toNat % residueModulus = (a.value+b.value) % residueModulus
    simp only [word_toNat_add, Nat.mod_eq_of_lt (show (a.high P).toNat+(b.high P).toNat < 2^256 from hroom)]
    refine ⟨hsum, ?_⟩
    rw [Nat.add_mod, hla.2, hlb.2, ← Nat.add_mod]

theorem valueBound (e : Expr) (M C : Nat)
    (hp : e.productsBounded M) (hc : e.literalsBounded C) :
    e.value ≤ e.products*M+e.literals*C := by
  induction e with
  | product a b => simpa only [Expr.value, Expr.products, Expr.literals, Expr.productsBounded, Nat.one_mul, Nat.zero_mul, Nat.add_zero] using hp
  | literal a => simpa only [Expr.value, Expr.products, Expr.literals, Expr.literalsBounded, Nat.one_mul, Nat.zero_mul, Nat.zero_add] using hc
  | add a b ha hb =>
    have hA := ha hp.1 hc.1
    have hB := hb hp.2 hc.2
    simp only [Expr.value, Expr.products, Expr.literals]
    nlinarith

theorem productBound (a b : UInt256) (B : Nat) (ha : a.toNat < B) (hb : b.toNat < B) :
    a.toNat*b.toNat ≤ (B-1)^2 := by
  have ha' : a.toNat ≤ B-1 := by omega
  have hb' : b.toNat ≤ B-1 := by omega
  have hh := Nat.mul_le_mul ha' hb'
  simpa only [Nat.pow_two] using hh

theorem reconstructExpressions (hi lo : Expr) (C : Nat)
    (hcount : hi.count ≤ 19) (hlit : hi.literalsBounded (residueModulus-1))
    (hvalue : hi.value = lo.value)
    (hC : C ≤ 18*((2^244 : Nat)-1))
    (hS : hi.value ≤ 18*((2^244 : Nat)-1)^2+C) :
    (HistoricalSearch.RoundedWordBridge.carryWord (hi.high (UInt256.ofNat residueModulus))
      lo.low (UInt256.ofNat residueModulus) (UInt256.ofNat 244) (UInt256.ofNat 12)).toNat =
      hi.value / 2^244 := by
  have hpv : (UInt256.ofNat residueModulus).toNat = residueModulus := by
    rw [word_toNat_ofNat]
    apply Nat.mod_eq_of_lt
    norm_num [residueModulus]
  have hh := highInvariant (UInt256.ofNat residueModulus) hpv hi hcount hlit
  have hb : (hi.high (UInt256.ofNat residueModulus)).toNat ≤ 19*(residueModulus-1) :=
    hh.1.trans (Nat.mul_le_mul_right _ hcount)
  have hlow : UInt256.ofNat (hi.value % wordRadix) = lo.low := by
    apply word_ext
    rw [lowValue, word_toNat_ofNat, hvalue]
    exact Nat.mod_mod _ _
  have hhigh : UInt256.ofNat (hi.high (UInt256.ofNat residueModulus)).toNat =
      hi.high (UInt256.ofNat residueModulus) := (word_eq_ofNat_toNat _).symm
  have hHR : (hi.high (UInt256.ofNat residueModulus)).toNat < wordRadix := by
    have hroom : 19*(residueModulus-1) < wordRadix := by norm_num [wordRadix,residueModulus]
    exact hb.trans_lt hroom
  have hc := HistoricalSearch.RoundedWordBridge.carryWord_toNat 244 hi.value C
    (hi.high (UInt256.ofNat residueModulus)).toNat (by decide) (by decide) hC hS hHR hh.2
  simpa only [hhigh, hlow] using hc

theorem column15CarryBound (B F C S : Nat) (hB : 0 < B)
    (hC : C ≤ 18*(B-1)) (hS : S ≤ 4*(B-1)*(F-1)+C) :
    S/B ≤ 4*(F-1)+18 := by
  have hprod : S ≤ (4*(F-1)+18)*B := by nlinarith [Nat.sub_le B 1]
  exact (Nat.div_le_div_right hprod).trans (by rw [Nat.mul_div_cancel _ hB])

theorem column16Bound (A Q N C : Nat) (hA : A < 2^96) (hQ : Q < 2^96) (hN : N < 2^96)
    (hC : C ≤ 4*((2^96 : Nat)-1)+18) : A*A+Q*N+C < 2^244 := by
  have ha : A ≤ (2^96 : Nat)-1 := by omega
  have hq : Q ≤ (2^96 : Nat)-1 := by omega
  have hn : N ≤ (2^96 : Nat)-1 := by omega
  have haa := Nat.mul_le_mul ha ha
  have hqn := Nat.mul_le_mul hq hn
  have hsum : A*A+Q*N+C ≤ 2*((2^96 : Nat)-1)^2+4*((2^96 : Nat)-1)+18 := by nlinarith
  exact hsum.trans_lt HistoricalSearch.GenericColumn.width244TopCellBound


end HistoricalSearch.ColumnExpressions
