import Mathlib.Tactic.IntervalCases
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired144Boolean
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedLaneGroupTwoHoist
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired144WordRound
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerBoolean
open Paired144Core Paired144Boolean PairedLaneGroupTwoHoist
theorem pack_supported (a b : BitVec 32) : Supported pairMask (pack a b) := by
  simp only [Supported, pairMask, pack_and, BitVec.and_allOnes]

def raw (mode : Nat) (mask selector b c d : BitVec w) : BitVec w :=
  match mode with
  | 0 => (((b ^^^ c) ^^^ selector) ^^^ (d ||| (c &&& selector)))
  | 1 => ((b &&& c) ||| (d ^^^ ((b ^^^ selector) &&& (c ||| d))))
  | 2 => ((b ||| (~~~c)) ^^^ d)
  | 3 => (c ^^^ ((d ^^^ (c &&& selector)) &&& (b ^^^ (c ||| selector))))
  | 4 => (((b ^^^ c) ^^^ selector) ^^^ (d ||| (c &&& selector)))
  | 5 => (b ^^^ (d ^^^ ((d &&& selector) ||| (c ^^^ (b &&& selector)))))
  | 6 => (d ^^^ (selector ^^^ ((b ^^^ selector) &&& (c ^^^ (b &&& d)))))
  | 7 => (~~~(b ^^^ (d ^^^ ((b ^^^ selector) ||| (c ^^^ (b &&& d))))))
  | _ => (c ^^^ ((b &&& selector) ^^^ (d &&& (selector ||| (b ^^^ c)))))
def canonical (mode : Nat) (mask selector b c d : BitVec w) : BitVec w :=
  match mode with
  | 0 => (((b ^^^ c) ^^^ selector) ^^^ (d ||| (c &&& selector)))
  | 1 => ((b &&& c) ||| (d ^^^ ((b ^^^ selector) &&& (c ||| d))))
  | 2 => ((b ||| (c ^^^ mask)) ^^^ d)
  | 3 => (c ^^^ ((d ^^^ (c &&& selector)) &&& (b ^^^ (c ||| selector))))
  | 4 => (((b ^^^ c) ^^^ selector) ^^^ (d ||| (c &&& selector)))
  | 5 => (b ^^^ (d ^^^ ((d &&& selector) ||| (c ^^^ (b &&& selector)))))
  | 6 => (d ^^^ (selector ^^^ ((b ^^^ selector) &&& (c ^^^ (b &&& d)))))
  | 7 => ((b ^^^ (d ^^^ ((b ^^^ selector) ||| (c ^^^ (b &&& d))))) ^^^ mask)
  | _ => (c ^^^ ((b &&& selector) ^^^ (d &&& (selector ||| (b ^^^ c)))))

def leftGroup (mode : Nat) : Nat :=
  match mode with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 0
  | 6 => 1
  | 7 => 2
  | _ => 3

def rightGroup (mode : Nat) : Nat :=
  match mode with
  | 0 => 4
  | 1 => 3
  | 2 => 2
  | 3 => 1
  | 4 => 0
  | 5 => 3
  | 6 => 2
  | 7 => 1
  | _ => 0

def selector (mode : Nat) : BitVec 256 :=
  match mode with
  | 4 => lowerMask
  | _ => upperMask

theorem selector_supported (mode : Nat) : Supported pairMask (selector mode) := by
  unfold selector
  split <;> exact pack_supported _ _

theorem canonical_pack (mode : Nat) (hm : mode < 9)
    (bl br cl cr dl dr : BitVec 32) :
    canonical mode pairMask (selector mode) (pack bl br) (pack cl cr) (pack dl dr) =
      pack (f (leftGroup mode) (BitVec.allOnes 32) bl cl dl)
        (f (rightGroup mode) (BitVec.allOnes 32) br cr dr) := by
  interval_cases mode <;>
    simp only [canonical, selector, leftGroup, rightGroup, upperMask, lowerMask,
      pairMask, ite_true, ite_false, pack_xor, pack_and, pack_or]
  all_goals apply congrArg₂ pack
  all_goals
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [f, BitVec.getLsbD_xor, BitVec.getLsbD_or, BitVec.getLsbD_and,
      BitVec.getLsbD_zero, BitVec.getLsbD_allOnes, hi, decide_true]
    cases bl.getLsbD i <;> cases br.getLsbD i <;> cases cl.getLsbD i <;>
      cases cr.getLsbD i <;> cases dl.getLsbD i <;> cases dr.getLsbD i <;> rfl
#print axioms canonical_pack

theorem raw_gap (mode : Nat) (hm : mode = 2 ∨ mode = 7)
    (mask selector b c d : BitVec w)
    (hs : Supported mask selector) (hb : Supported mask b)
    (hc : Supported mask c) (hd : Supported mask d) :
    raw mode mask selector b c d = canonical mode mask selector b c d ||| ~~~mask := by
  rcases hm with rfl | rfl
  all_goals
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have hs' := congrArg (fun x : BitVec w => x.getLsbD i) hs
    have hb' := congrArg (fun x : BitVec w => x.getLsbD i) hb
    have hc' := congrArg (fun x : BitVec w => x.getLsbD i) hc
    have hd' := congrArg (fun x : BitVec w => x.getLsbD i) hd
    simp only [Supported, BitVec.getLsbD_and] at hs' hb' hc' hd'
    simp only [raw, canonical, BitVec.getLsbD_xor, BitVec.getLsbD_or,
      BitVec.getLsbD_and, BitVec.getLsbD_not, hi, decide_true, Bool.true_and]
    cases hm0 : mask.getLsbD i <;> cases hs0 : selector.getLsbD i <;>
      cases hb0 : b.getLsbD i <;> cases hc0 : c.getLsbD i <;>
      cases hd0 : d.getLsbD i <;> simp_all
#print axioms raw_gap

theorem canonical_disjoint (mode : Nat) (hm : mode < 9)
    (mask selector b c d : BitVec w)
    (hs : Supported mask selector) (hb : Supported mask b)
    (hc : Supported mask c) (hd : Supported mask d) :
    canonical mode mask selector b c d &&& ~~~mask = 0#w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hs' := congrArg (fun x : BitVec w => x.getLsbD i) hs
  have hb' := congrArg (fun x : BitVec w => x.getLsbD i) hb
  have hc' := congrArg (fun x : BitVec w => x.getLsbD i) hc
  have hd' := congrArg (fun x : BitVec w => x.getLsbD i) hd
  simp only [Supported, BitVec.getLsbD_and] at hs' hb' hc' hd'
  interval_cases mode <;>
    simp only [canonical, BitVec.getLsbD_xor, BitVec.getLsbD_or,
      BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_zero,
      hi, decide_true, Bool.true_and]
  all_goals
    cases hm0 : mask.getLsbD i <;> cases hs0 : selector.getLsbD i <;>
      cases hb0 : b.getLsbD i <;> cases hc0 : c.getLsbD i <;>
      cases hd0 : d.getLsbD i <;> simp_all
#print axioms canonical_disjoint

def key (mode : Nat) (mask k : BitVec w) : BitVec w :=
  if mode = 2 ∨ mode = 7 then adjustedConstant mask k else k

theorem raw_add_key (mode : Nat) (hm : mode < 9)
    (mask selector b c d k : BitVec w)
    (hs : Supported mask selector) (hb : Supported mask b)
    (hc : Supported mask c) (hd : Supported mask d) :
    raw mode mask selector b c d + key mode mask k =
      canonical mode mask selector b c d + k := by
  by_cases hmode : mode = 2 ∨ mode = 7
  · rw [key, if_pos hmode, raw_gap mode hmode mask selector b c d hs hb hc hd]
    rw [← BitVec.add_eq_or_of_and_eq_zero _ _
      (canonical_disjoint mode hm mask selector b c d hs hb hc hd)]
    exact gap_constant_cancel mask _ k
  · simp only [key, if_neg hmode]
    have hraw : raw mode mask selector b c d = canonical mode mask selector b c d := by
      interval_cases mode <;> simp_all [raw, canonical]
    rw [hraw]
#print axioms raw_add_key
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerBoolean
