import Challenge.Ripemd160.Submission.H39Memo.A1000Single
import Challenge.Ripemd160.Submission.H39Memo.PatternFactsData

set_option warningAsError true
set_option maxRecDepth 40000

namespace Challenge.Ripemd160.Submission.H39Memo.PatternTrace
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof DispatchState A1000

def Trace (s t : State) : Prop :=
  ∃ path : List Located, Stepper.runLocatedBlock path s = some t

theorem Trace.trans {s t u : State} (hst : Trace s t)
    (hrun : t.halt = .Running) (htu : Trace t u) : Trace s u := by
  obtain ⟨left, hleft⟩ := hst
  obtain ⟨right, hright⟩ := htu
  exact ⟨left ++ right,
    Stepper.runLocatedBlock_append left right s t u hleft hrun hright⟩

theorem join_branch {s t u : State} (pre : List Located) (loc : Located)
    (hp : Stepper.runLocatedBlock pre s = some t) (hrun : t.halt = .Running)
    (hb : Stepper.runLocated loc t = some u) : Trace s u := by
  refine ⟨pre ++ [loc], Stepper.runLocatedBlock_append _ _ _ _ _ hp hrun ?_⟩
  rw [run_singleton]
  exact hb

theorem eq_true_iff (a b : Nat) (ha : a < 2 ^ 256) (hb : b < 2 ^ 256) :
    UInt256.isTrue (UInt256.eq (UInt256.ofNat a) (UInt256.ofNat b)) ↔ a = b := by
  unfold UInt256.eq
  rw [Logic.toNat_ofNat_self ha, Logic.toNat_ofNat_self hb]
  by_cases h : a = b
  · rw [if_pos h]
    exact iff_of_true (by decide) h
  · rw [if_neg h]
    exact iff_of_false (by decide) h

def stateAt (s : State) (bytes : ByteArray) (pc : Nat) : State :=
  atPC s pc [UInt256.ofNat bytes.size]

def fallback (s : State) : State := atPC s 1006 []

def Prefix (bytes : ByteArray) (n : Nat) : Prop :=
  ∀ k : Fin 31, k.val < n →
    MachineState.readWord bytes (32 * k.val) = PatternFacts.prefixWord k

theorem prefix_next (bytes : ByteArray) (n : Fin 31) (hp : Prefix bytes n.val)
    (hw : MachineState.readWord bytes (32 * n.val) = PatternFacts.prefixWord n) :
    Prefix bytes (n.val + 1) := by
  intro k hk
  by_cases hkn : k.val = n.val
  · have he : k = n := Fin.ext hkn
    simpa only [he] using hw
  · exact hp k (by omega)

end Challenge.Ripemd160.Submission.H39Memo.PatternTrace
