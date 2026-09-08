import Challenge.EvmProof.Gas
import Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNResidue

set_option warningAsError true

/-!
Artifact-independent composition for an eight-copy suffix dispatcher.
Each callback performs exactly one MAC, with the final-copy callback also
covering its ordinary backedge or exit. L1 supplies total=n and L2 total=n-1.
No bytecode decoder facts or whole-subroutine correctness are assumed here.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNEight

open EvmSemantics EvmSemantics.EVM
open Challenge.EvmProof MonproKNResidue

/-- Slot is the physical copy number; completed counts semantic MAC updates. -/
structure Copies (atState : Nat → Nat → State) (finish : State) (total : Nat) where
  next : ∀ completed slot, completed + 1 ≤ total → slot < 7 →
    GasSteps (atState completed slot) (atState (completed + 1) (slot + 1))
  back : ∀ completed, completed + 1 < total →
    GasSteps (atState completed 7) (atState (completed + 1) 0)
  exit : ∀ completed, completed + 1 = total →
    GasSteps (atState completed 7) finish

/-- Execute more+1 remaining copies. Alignment ensures the last is slot seven. -/
def runAligned {atState : Nat → Nat → State} {finish : State} {total : Nat}
    (copies : Copies atState finish total) (more : Nat) :
    ∀ completed slot, completed + (more + 1) = total → slot < 8 →
      (slot + (more + 1)) % 8 = 0 → GasSteps (atState completed slot) finish := by
  induction more with
  | zero =>
      intro completed slot htotal hslot halign
      have hs : slot = 7 := by omega
      subst slot
      exact copies.exit completed (by omega)
  | succ more ih =>
      intro completed slot htotal hslot halign
      by_cases hs : slot < 7
      · exact (copies.next completed slot (by omega) hs).trans
          (ih (completed + 1) (slot + 1) (by omega) (by omega) (by omega))
      · have hseven : slot = 7 := by omega
        subst slot
        exact (copies.back completed (by omega)).trans
          (ih (completed + 1) 0 (by omega) (by decide) (by omega))

/-- The previously proved residue chooses a nonempty suffix, then full blocks. -/
def run {atState : Nat → Nat → State} {finish : State} {total : Nat}
    (copies : Copies atState finish total) (hpositive : 0 < total) :
    GasSteps (atState 0 (residue total)) finish := by
  have hsuffix := suffix_bounds total hpositive
  have hslot := residue_lt total
  exact runAligned copies (total - 1) 0 (residue total)
    (by omega) hslot (by omega)

/-- The first limb loop performs exactly n semantic MAC updates. -/
def l1Trace {atState : Nat → Nat → State} {finish : State} (n : Nat)
    (hn : 2 ≤ n) (copies : Copies atState finish n) :
    GasSteps (atState 0 (residue n)) finish :=
  run copies (by omega)

/-- The second limb loop performs exactly n-1 updates, not n or eight. -/
def l2Trace {atState : Nat → Nat → State} {finish : State} (n : Nat)
    (hn : 2 ≤ n) (copies : Copies atState finish (n-1)) :
    GasSteps (atState 0 (residue (n-1))) finish :=
  run copies (by omega)

theorem residue_one : residue 1 = 7 := by decide

/-- For n=2 the suffix consists solely of its exiting seventh-indexed copy. -/
def l2Single {atState : Nat → Nat → State} {finish : State}
    (copies : Copies atState finish 1) : GasSteps (atState 0 7) finish :=
  copies.exit 0 (by decide)

theorem l2Single_cost {atState : Nat → Nat → State} {finish : State}
    (copies : Copies atState finish 1) :
    (l2Single copies).cost = (copies.exit 0 (by decide)).cost := rfl

end Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNEight
