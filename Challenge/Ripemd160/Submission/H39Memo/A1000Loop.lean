import Challenge.Ripemd160.Submission.H39Memo.A1000Checks
import Challenge.Ripemd160.Submission.H39Memo.A1000LoopStep
import Challenge.Ripemd160.Submission.H39Memo.A1000Cleanup

set_option warningAsError true
set_option maxRecDepth 40000

namespace Challenge.Ripemd160.Submission.H39Memo.A1000
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof

def Trace (s t : State) : Prop :=
  ∃ path : List Located, Stepper.runLocatedBlock path s = some t

theorem Trace.trans {s t u : State} (hst : Trace s t)
    (hrun : t.halt = .Running) (htu : Trace t u) : Trace s u := by
  obtain ⟨left, hleft⟩ := hst
  obtain ⟨right, hright⟩ := htu
  exact ⟨left ++ right,
    Stepper.runLocatedBlock_append left right s t u hleft hrun hright⟩

private theorem loop_cases_aux (s : State) (input : ByteArray)
    (hinput : s.executionEnv.calldata = input) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = h39Bytecode)
    (remaining n : Nat) (hremaining : n + remaining = 30) (hn : n < 30) :
    Trace (loop s n) (fallback s) ∨
      (Trace (loop s n) (tailEntry s) ∧
        ∀ k, n ≤ k → k < 30 →
          MachineState.readWord input (32 * (k + 1)) = cacheWord) := by
  induction remaining generalizing n with
  | zero => omega
  | succ remaining ih =>
    by_cases hword : MachineState.readWord input (32 * (n + 1)) = cacheWord
    · have hcheck : Trace (loop s n) (checked s n) :=
        ⟨checkPath, run_check_match s input n hn hinput hrun hword⟩
      by_cases hlast : n = 29
      · subst n
        refine Or.inr ⟨hcheck.trans hrun ⟨advancePath, run_advance_last s hrun⟩, ?_⟩
        intro k hk hk30
        have : k = 29 := by omega
        simpa only [this] using hword
      · have hmore : n < 29 := by omega
        have hadvance : Trace (checked s n) (loop s (n + 1)) :=
          ⟨advancePath, run_advance_more s n hmore hrun hcode⟩
        have hnext := hcheck.trans hrun hadvance
        rcases ih (n + 1) (by omega) (by omega) with hfail | ⟨htail, hwords⟩
        · exact Or.inl (hnext.trans hrun hfail)
        · refine Or.inr ⟨hnext.trans hrun htail, ?_⟩
          intro k hk hk30
          by_cases hkn : k = n
          · simpa only [hkn] using hword
          · exact hwords k (by omega) hk30
    · exact Or.inl ((show Trace (loop s n)
          (failEntry s (UInt256.ofNat (32 * (n + 1)))) from
          ⟨checkPath, run_check_mismatch s input n hn hinput hrun hword hcode⟩).trans
        hrun ⟨failPath, run_fail s _ hrun hcode⟩)

theorem loop_cases (s : State) (input : ByteArray)
    (hinput : s.executionEnv.calldata = input) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = h39Bytecode) :
    Trace (loop s 0) (fallback s) ∨
      (Trace (loop s 0) (tailEntry s) ∧
        ∀ k, k < 30 → MachineState.readWord input (32 * (k + 1)) = cacheWord) := by
  rcases loop_cases_aux s input hinput hrun hcode 30 0 rfl (by decide) with
    hfail | ⟨htail, hwords⟩
  · exact Or.inl hfail
  · exact Or.inr ⟨htail, fun k hk => hwords k (Nat.zero_le k) hk⟩

end Challenge.Ripemd160.Submission.H39Memo.A1000
