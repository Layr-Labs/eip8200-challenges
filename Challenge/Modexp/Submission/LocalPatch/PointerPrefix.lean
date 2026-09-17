import Challenge.Modexp.Submission.LocalPatch.PointerInvertBasic

set_option warningAsError true
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.LocalPatch.PointerSub32
open EvmSemantics EvmSemantics.EVM
open Transport

/-- The actual first DUP supplies the frame, capacity, first debit and first
paused-source endpoint. No assumption that the complete macro is affordable. -/
theorem start_inverse {code : ByteArray} (old : OldCode code) {a t : State}
    (hc : a.executionEnv.code = code) (hf : a.fork = .Osaka)
    (hp : a.pc = UInt256.ofNat 2539)
    (hn : NoException t) (hs : StepRunning a t) :
    ∃ p tail, a.stack = p :: tail ∧ 3 ≤ a.gasAvailable ∧
      Capacity 1 tail ∧ t = pre a p tail 1 := by
  have hpn : a.pc.toNat = 2539 := by rw [hp]; rfl
  have hd := decodedOp_at hc hf hpn old.d0 (by decide)
  obtain ⟨p, tail, hstk, hgas, hcap, ht⟩ := invert_dup1 hd hn hs
  have hps : a.pc.succ = UInt256.ofNat 2540 := by rw [hp]; rfl
  exact ⟨p, tail, hstk, hgas, by simpa [Capacity] using hcap,
    by simpa only [pre, hps] using ht⟩

/-- One actual source prefix step yields its *necessary* additional debit.
The target has not yet moved. Only the fifth source step proves budget 15. -/
theorem next_inverse {code : ByteArray} (old : OldCode code)
    (a : State) (p : UInt256) (tail : List UInt256) (j : Nat)
    (hj : 1 ≤ j) (hj5 : j < 5)
    (hc : a.executionEnv.code = code) (hf : a.fork = .Osaka)
    (hbudget : 3 * j ≤ a.gasAvailable) (hcap : Capacity j tail)
    {t : State} (hn : NoException t) (hs : StepRunning (pre a p tail j) t) :
    3 * (j + 1) ≤ a.gasAvailable ∧ Capacity (j + 1) tail ∧
      t = pre a p tail (j + 1) := by
  have hj_cases : j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by omega
  rcases hj_cases with rfl | rfl | rfl | rfl
  · have hd := decoded_at (s := pre a p tail 1) hc hf
      (show (pre a p tail 1).pc.toNat = 2540 from rfl) old.d1 (by decide)
    obtain ⟨hg, hpk, ht⟩ := invert_push31 hd hn hs
    have hgas : a.gasAvailable - 3 - 3 = a.gasAvailable - 6 := by omega
    have hmore : 6 ≤ a.gasAvailable := by
      change 3 ≤ a.gasAvailable - 3 at hg
      omega
    have hpc :
        UInt256.ofNat 2540 + UInt256.ofNat 2 = UInt256.ofNat 2542 := by
      decide
    refine ⟨hmore, ?_, ?_⟩
    · simpa [Capacity, pre, List.length_cons, Nat.add_assoc] using hpk
    · simpa only [pre, hgas, hpc] using ht
  · have hd := decodedOp_at (s := pre a p tail 2) hc hf
      (show (pre a p tail 2).pc.toNat = 2542 from rfl) old.d2 (by decide)
    obtain ⟨hg, ht⟩ := invert_not (UInt256.ofNat 31) (p :: p :: tail) rfl hd hn hs
    have hgas : a.gasAvailable - 6 - 3 = a.gasAvailable - 9 := by omega
    have hmore : 9 ≤ a.gasAvailable := by
      change 3 ≤ a.gasAvailable - 6 at hg
      omega
    have hpc : (UInt256.ofNat 2542).succ = UInt256.ofNat 2543 := by
      decide
    exact ⟨hmore, by simpa [Capacity] using hcap,
      by simpa only [pre, negative32, hgas, hpc] using ht⟩
  · have hd := decodedOp_at (s := pre a p tail 3) hc hf
      (show (pre a p tail 3).pc.toNat = 2543 from rfl) old.d3 (by decide)
    obtain ⟨hg, ht⟩ := invert_add negative32 p (p :: tail) rfl hd hn hs
    have hgas : a.gasAvailable - 9 - 3 = a.gasAvailable - 12 := by omega
    have hmore : 12 ≤ a.gasAvailable := by
      change 3 ≤ a.gasAvailable - 9 at hg
      omega
    have hpc : (UInt256.ofNat 2543).succ = UInt256.ofNat 2544 := by
      decide
    exact ⟨hmore, by simpa [Capacity] using hcap,
      by simpa only [pre, hgas, hpc] using ht⟩
  · have hd := decodedOp_at (s := pre a p tail 4) hc hf
      (show (pre a p tail 4).pc.toNat = 2544 from rfl) old.d4 (by decide)
    obtain ⟨hg, ht⟩ := invert_swap1 (negative32 + p) p tail rfl hd hn hs
    have hgas : a.gasAvailable - 12 - 3 = a.gasAvailable - 15 := by omega
    have hmore : 15 ≤ a.gasAvailable := by
      change 3 ≤ a.gasAvailable - 12 at hg
      omega
    have hpc : (UInt256.ofNat 2544).succ = UInt256.ofNat 2545 := by
      decide
    exact ⟨hmore, by simpa [Capacity] using hcap,
      by simpa only [pre, hgas, hpc] using ht⟩

end Challenge.Modexp.Submission.LocalPatch.PointerSub32
