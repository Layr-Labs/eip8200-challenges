import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedLaneBoolean
import Init.Data.BitVec.Bitblast

set_option warningAsError true

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedLaneGroupTwoHoist

open PairedLaneCore PairedLaneBoolean

/-- A support predicate, not an assumption on arbitrary raw machine words. -/
def Supported (mask value : BitVec w) : Prop := value &&& mask = value

def oldBoolean (mask b c d : BitVec w) : BitVec w :=
  ((c ^^^ mask) ||| b) ^^^ d

def newBoolean (b c d : BitVec w) : BitVec w :=
  ((~~~c) ||| b) ^^^ d

def adjustedConstant (mask k : BitVec w) : BitVec w := (k + mask) + 1#w

theorem newBoolean_eq_or_gap (mask b c d : BitVec w)
    (hb : Supported mask b) (hc : Supported mask c) (hd : Supported mask d) :
    newBoolean b c d = oldBoolean mask b c d ||| ~~~mask := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hb' := congrArg (fun x : BitVec w => x.getLsbD i) hb
  have hc' := congrArg (fun x : BitVec w => x.getLsbD i) hc
  have hd' := congrArg (fun x : BitVec w => x.getLsbD i) hd
  simp only [BitVec.getLsbD_and] at hb' hc' hd'
  simp only [newBoolean, oldBoolean, BitVec.getLsbD_xor, BitVec.getLsbD_or,
    BitVec.getLsbD_not, hi, decide_true, Bool.true_and]
  cases hm : mask.getLsbD i <;> cases hb0 : b.getLsbD i <;> cases hc0 : c.getLsbD i <;>
    cases hd0 : d.getLsbD i <;> simp_all

theorem oldBoolean_disjoint_gap (mask b c d : BitVec w)
    (hb : Supported mask b) (hc : Supported mask c) (hd : Supported mask d) :
    oldBoolean mask b c d &&& ~~~mask = 0#w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hb' := congrArg (fun x : BitVec w => x.getLsbD i) hb
  have hc' := congrArg (fun x : BitVec w => x.getLsbD i) hc
  have hd' := congrArg (fun x : BitVec w => x.getLsbD i) hd
  simp only [BitVec.getLsbD_and] at hb' hc' hd'
  simp only [oldBoolean, BitVec.getLsbD_and, BitVec.getLsbD_xor, BitVec.getLsbD_or,
    BitVec.getLsbD_not, BitVec.getLsbD_zero, hi, decide_true, Bool.true_and]
  cases hm : mask.getLsbD i <;> cases hb0 : b.getLsbD i <;> cases hc0 : c.getLsbD i <;>
    cases hd0 : d.getLsbD i <;> simp_all

theorem newBoolean_eq_add_gap (mask b c d : BitVec w)
    (hb : Supported mask b) (hc : Supported mask c) (hd : Supported mask d) :
    newBoolean b c d = oldBoolean mask b c d + ~~~mask := by
  rw [BitVec.add_eq_or_of_and_eq_zero _ _ (oldBoolean_disjoint_gap mask b c d hb hc hd)]
  exact newBoolean_eq_or_gap mask b c d hb hc hd

theorem gap_constant_cancel (mask x k : BitVec w) :
    (x + ~~~mask) + adjustedConstant mask k = x + k := by
  have hcancel : ~~~mask + (mask + 1#w) = 0#w := by
    calc
      ~~~mask + (mask + 1#w) = (~~~mask + 1#w) + mask := by ac_rfl
      _ = -mask + mask := by rw [← BitVec.neg_eq_not_add]
      _ = 0#w := BitVec.add_left_neg mask
  calc
    (x + ~~~mask) + adjustedConstant mask k =
        (x + k) + (~~~mask + (mask + 1#w)) := by
          unfold adjustedConstant
          ac_rfl
    _ = x + k := by rw [hcancel, BitVec.add_zero]

theorem newBoolean_add_adjusted (mask b c d k : BitVec w)
    (hb : Supported mask b) (hc : Supported mask c) (hd : Supported mask d) :
    newBoolean b c d + adjustedConstant mask k = oldBoolean mask b c d + k := by
  rw [newBoolean_eq_add_gap mask b c d hb hc hd]
  exact gap_constant_cancel mask (oldBoolean mask b c d) k

theorem pack_supported (l r : BitVec 32) : Supported pairMask (pack l r) := by
  unfold Supported
  rw [← normalize_eq_and, normalize_pack]

theorem pairedF2_add_adjusted (b0 b1 c0 c1 d0 d1 : BitVec 32) (k : BitVec 256) :
    newBoolean (pack b0 b1) (pack c0 c1) (pack d0 d1) +
        adjustedConstant pairMask k =
      pairedF 2 (pack b0 b1) (pack c0 c1) (pack d0 d1) + k := by
  exact newBoolean_add_adjusted pairMask _ _ _ k
    (pack_supported b0 b1) (pack_supported c0 c1) (pack_supported d0 d1)

#print axioms newBoolean_eq_or_gap
#print axioms oldBoolean_disjoint_gap
#print axioms newBoolean_eq_add_gap
#print axioms gap_constant_cancel
#print axioms newBoolean_add_adjusted
#print axioms pack_supported
#print axioms pairedF2_add_adjusted

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedLaneGroupTwoHoist
