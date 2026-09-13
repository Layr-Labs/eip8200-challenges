import Challenge.Modexp.Submission.Proofs.Bytecode.BigCAdd
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
/-!
# Compact multi-limb fallback: modular multiplication

`MULM` clears the accumulator and runs a most-significant-bit-first
double-and-add over the multiplier window, each step being one or two `ADDM`
calls.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.BigC

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Memory outside the accumulator and the scratch window. -/
abbrev Out (ml a : Nat) : Prop := ml ≤ a ∧ (a < 4096 ∨ 5120 ≤ a)

theorem num_out {m m0 : ByteArray} {ml a n : Nat}
    (hf : ∀ k, ml ≤ k → (k < 4096 ∨ 5120 ≤ k) → bget m k = bget m0 k)
    (h1 : ml ≤ a) (h2 : a + n ≤ 4096 ∨ 5120 ≤ a) : num m a n = num m0 a n :=
  num_congr n (fun i _ => hf _ (by omega) (by omega))

theorem msv_out {m m0 : ByteArray} {ml : Nat} (hml : ml ≤ 1024)
    (hf : ∀ k, ml ≤ k → (k < 4096 ∨ 5120 ≤ k) → bget m k = bget m0 k) :
    MachineState.readWord m 9216 = MachineState.readWord m0 9216 :=
  readWord_congr (fun i _ => hf _ (by omega) (by omega))

theorem div_two_pow (Y d : Nat) :
    Y / 2 ^ d = 2 * (Y / 2 ^ (d + 1)) + Y / 2 ^ d % 2 := by
  rw [pow_succ, ← Nat.div_div_eq_div_mul]
  exact (Nat.div_add_mod (Y / 2 ^ d) 2).symm

theorem mulLoop {s : State} (henv : Env s) (ml x y k retPc : Nat) (rest : List UInt256)
    (mem0 : ByteArray) (hcap : rest.length < 990) (hml1 : 1 ≤ ml) (hml : ml ≤ 1024)
    (hk : k ≤ 1024) (hx : 1024 ≤ x) (hx' : x + ml ≤ 4096 ∨ (5120 ≤ x ∧ x ≤ 8192))
    (hy : 1024 ≤ y) (hy' : y + k ≤ 4096 ∨ (5120 ≤ y ∧ y ≤ 7168))
    (hM : 1 ≤ num mem0 1024 ml) (hX : num mem0 x ml ≤ num mem0 1024 ml) :
    ∀ d, d ≤ 8 * k → ∀ mem : ByteArray,
      MachineState.readWord mem 9216 = UInt256.ofNat ml →
      (∀ a, ml ≤ a → (a < 4096 ∨ 5120 ≤ a) → bget mem a = bget mem0 a) →
      num mem 0 ml = num mem0 y k / 2 ^ d * num mem0 x ml % num mem0 1024 ml →
      ∃ mem', Reach (st s 492 (UInt256.ofNat (8 * k - d) :: UInt256.ofNat retPc ::
            UInt256.ofNat x :: UInt256.ofNat y :: UInt256.ofNat k :: rest) mem AW)
          (st s 548 (UInt256.ofNat (8 * k) :: UInt256.ofNat retPc ::
            UInt256.ofNat x :: UInt256.ofNat y :: UInt256.ofNat k :: rest) mem' AW) ∧
        MachineState.readWord mem' 9216 = UInt256.ofNat ml ∧
        (∀ a, ml ≤ a → (a < 4096 ∨ 5120 ≤ a) → bget mem' a = bget mem0 a) ∧
        num mem' 0 ml = num mem0 y k * num mem0 x ml % num mem0 1024 ml := by
  intro d
  induction d with
  | zero =>
    intro _ mem hmsv hf hv
    refine ⟨mem, ?_, hmsv, hf, ?_⟩
    · rw [Nat.sub_zero]
      exact reach_run henv (run_mGuard_done s (8 * k) k _ _ _ rest mem (by omega) hk
        (by omega) henv.code henv.run)
    · rw [hv, pow_zero, Nat.div_one]
  | succ d ih =>
    intro hd mem hmsv hf hv
    have hj : 8 * k - (d + 1) < 8 * k := by omega
    have hrest : (UInt256.ofNat (8 * k - (d + 1)) :: UInt256.ofNat retPc :: UInt256.ofNat x ::
        UInt256.ofNat y :: UInt256.ofNat k :: rest).length < 1000 := by simp; omega
    have hMm : num mem 1024 ml = num mem0 1024 ml := num_out hf (by omega) (by omega)
    -- guard and doubling call
    have r1 := reach_run henv (run_mGuard_go s (8 * k - (d + 1)) k (UInt256.ofNat retPc)
      (UInt256.ofNat x) (UInt256.ofNat y) rest mem (by omega) hk (by omega)
      (lt_word (by omega)) henv.code henv.run)
    have r2 := reach_run henv (run_mDouble s (8 * k - (d + 1))
      (UInt256.ofNat retPc :: UInt256.ofNat x :: UInt256.ofNat y :: UInt256.ofNat k :: rest)
      mem (by simp; omega) henv.code henv.run)
    have hacc : num mem 0 ml < num mem0 1024 ml := by
      rw [hv]
      exact Nat.mod_lt _ (by omega)
    obtain ⟨mem1, r3, hv1, hf1⟩ := addm henv ml 0 511
      (UInt256.ofNat (8 * k - (d + 1)) :: UInt256.ofNat retPc :: UInt256.ofNat x ::
        UInt256.ofNat y :: UInt256.ofNat k :: rest)
      mem hrest hml1 hml (Or.inl rfl) (by norm_num) (by norm_num) jump511 hmsv
      (by rw [hMm]; omega)
    have hf1' : ∀ a, ml ≤ a → (a < 4096 ∨ 5120 ≤ a) → bget mem1 a = bget mem0 a :=
      fun a h1 h2 => (hf1 a h1 h2).trans (hf a h1 h2)
    have hmsv1 : MachineState.readWord mem1 9216 = UInt256.ofNat ml := by
      rw [msv_out hml hf1', ← msv_out hml hf, hmsv]
    have hY1 : num mem1 y k = num mem0 y k := num_out hf1' (by omega) (by omega)
    have hX1 : num mem1 x ml = num mem0 x ml := num_out hf1' (by omega) (by omega)
    have hbit : (bitWord mem1 (y + (8 * k - (d + 1)) / 8) ((8 * k - (d + 1)) % 8)).toNat =
        num mem0 y k / 2 ^ d % 2 := by
      rw [← num_bit mem1 y k _ hj, hY1, show 8 * k - (8 * k - (d + 1)) - 1 = d by omega]
    have hsplit := div_two_pow (num mem0 y k) d
    rw [hMm, hv] at hv1
    have hstep : 8 * k - (d + 1) + 1 = 8 * k - d := by omega
    by_cases hb : num mem0 y k / 2 ^ d % 2 = 0
    · -- multiplier bit clear: only the doubling
      have r4 := reach_run henv (run_m2_skip s (8 * k - (d + 1)) y (UInt256.ofNat retPc)
        (UInt256.ofNat x) (UInt256.ofNat k) rest mem1 (by omega) (by omega) (by omega)
        (by rw [hbit, hb]) henv.code henv.run)
      have r5 := reach_run henv (run_m3 s (8 * k - (d + 1))
        (UInt256.ofNat retPc :: UInt256.ofNat x :: UInt256.ofNat y :: UInt256.ofNat k :: rest)
        mem1 (by simp; omega) (by omega) henv.code henv.run)
      rw [hstep] at r5
      obtain ⟨mem', r6, hmsv', hf', hv'⟩ := ih (by omega) mem1 hmsv1 hf1' (by
        rw [hv1, Nat.mod_add_mod, Nat.add_mod_mod, hsplit, hb, Nat.add_zero]
        congr 1
        ring)
      exact ⟨mem', r1.tr (r2.tr (r3.tr (r4.tr (r5.tr r6)))), hmsv', hf', hv'⟩
    · -- multiplier bit set: doubling then adding the multiplicand
      have hb1 : num mem0 y k / 2 ^ d % 2 = 1 := by omega
      have r4 := reach_run henv (run_m2_add s (8 * k - (d + 1)) y (UInt256.ofNat retPc)
        (UInt256.ofNat x) (UInt256.ofNat k) rest mem1 (by omega) (by omega) (by omega)
        (by rw [hbit, hb1]; norm_num) henv.code henv.run)
      have r5 := reach_run henv (run_mAdd s (8 * k - (d + 1)) (UInt256.ofNat retPc)
        (UInt256.ofNat x) (UInt256.ofNat y) (UInt256.ofNat k) rest mem1 (by omega)
        henv.code henv.run)
      have hMm1 : num mem1 1024 ml = num mem0 1024 ml := num_out hf1' (by omega) (by omega)
      have hacc1 : num mem1 0 ml < num mem0 1024 ml := by
        rw [hv1]
        exact Nat.mod_lt _ (by omega)
      obtain ⟨mem2, r6, hv2, hf2⟩ := addm henv ml x 540
        (UInt256.ofNat (8 * k - (d + 1)) :: UInt256.ofNat retPc :: UInt256.ofNat x ::
          UInt256.ofNat y :: UInt256.ofNat k :: rest)
        mem1 hrest hml1 hml (Or.inr (by omega)) (by omega) (by norm_num) jump540 hmsv1
        (by rw [hMm1, hX1]; omega)
      have hf2' : ∀ a, ml ≤ a → (a < 4096 ∨ 5120 ≤ a) → bget mem2 a = bget mem0 a :=
        fun a h1 h2 => (hf2 a h1 h2).trans (hf1' a h1 h2)
      have hmsv2 : MachineState.readWord mem2 9216 = UInt256.ofNat ml := by
        rw [msv_out hml hf2', ← msv_out hml hf, hmsv]
      have r7 := reach_run henv (run_m3 s (8 * k - (d + 1))
        (UInt256.ofNat retPc :: UInt256.ofNat x :: UInt256.ofNat y :: UInt256.ofNat k :: rest)
        mem2 (by simp; omega) (by omega) henv.code henv.run)
      rw [hstep] at r7
      obtain ⟨mem', r8, hmsv', hf', hv'⟩ := ih (by omega) mem2 hmsv2 hf2' (by
        rw [hv2, hMm1, hX1, hv1, Nat.mod_add_mod, Nat.add_assoc, Nat.mod_add_mod,
          Nat.add_left_comm, Nat.mod_add_mod, hsplit, hb1]
        congr 1
        ring)
      exact ⟨mem', r1.tr (r2.tr (r3.tr (r4.tr (r5.tr (r6.tr (r7.tr r8)))))), hmsv', hf', hv'⟩

/-- `MULM`: accumulator := multiplier window * multiplicand mod modulus, for a
multiplicand at most the modulus. -/
theorem mulm {s : State} (henv : Env s) (hcds : s.executionEnv.calldata.size < 2 ^ 64)
    (ml x y k retPc : Nat) (rest : List UInt256) (mem : ByteArray)
    (hcap : rest.length < 990) (hml1 : 1 ≤ ml) (hml : ml ≤ 1024) (hk : k ≤ 1024)
    (hx : 1024 ≤ x) (hx' : x + ml ≤ 4096 ∨ (5120 ≤ x ∧ x ≤ 8192))
    (hy : 1024 ≤ y) (hy' : y + k ≤ 4096 ∨ (5120 ≤ y ∧ y ≤ 7168))
    (hret : retPc < 2 ^ 16) (hjump : Decode.isValidJumpDest submissionBytecode retPc = true)
    (hmsv : MachineState.readWord mem 9216 = UInt256.ofNat ml)
    (hM : 1 ≤ num mem 1024 ml) (hX : num mem x ml ≤ num mem 1024 ml) :
    ∃ mem', Reach (st s 483 (UInt256.ofNat retPc :: UInt256.ofNat x :: UInt256.ofNat y ::
          UInt256.ofNat k :: rest) mem AW) (st s retPc rest mem' AW) ∧
      num mem' 0 ml = num mem y k * num mem x ml % num mem 1024 ml ∧
      (∀ a, ml ≤ a → (a < 4096 ∨ 5120 ≤ a) → bget mem' a = bget mem a) := by
  have r0 := reach_run henv (run_mEntry s ml (UInt256.ofNat retPc) (UInt256.ofNat x)
    (UInt256.ofNat y) (UInt256.ofNat k) rest mem (by omega) hml hmsv hcds henv.code henv.run)
  have hf0 : ∀ a, ml ≤ a → (a < 4096 ∨ 5120 ≤ a) →
      bget (MachineState.writeBytes mem (MachineState.readPadded s.executionEnv.calldata
        s.executionEnv.calldata.size ml) 0) a = bget mem a := by
    intro a h1 _
    rw [bget_zeroCopy, if_neg (by omega)]
  have hmsv0 : MachineState.readWord (MachineState.writeBytes mem
      (MachineState.readPadded s.executionEnv.calldata s.executionEnv.calldata.size ml) 0)
      9216 = UInt256.ofNat ml := by
    rw [msv_out hml hf0, hmsv]
  have hY : num mem y k < 2 ^ (8 * k) := by
    have := num_lt mem y k
    rwa [show (256 : Nat) = 2 ^ 8 by norm_num, ← pow_mul] at this
  have h0 : num (MachineState.writeBytes mem (MachineState.readPadded s.executionEnv.calldata
      s.executionEnv.calldata.size ml) 0) 0 ml = 0 :=
    num_eq_zero ml (fun i hi => by rw [bget_zeroCopy, if_pos (by omega)])
  obtain ⟨mem', r1, hmsv', hf', hv'⟩ := mulLoop henv ml x y k retPc rest mem hcap hml1 hml hk
    hx hx' hy hy' hM hX (8 * k) (le_refl _) _ hmsv0 hf0 (by
      rw [h0, Nat.div_eq_of_lt hY, Nat.zero_mul, Nat.zero_mod])
  rw [Nat.sub_self] at r1
  have r2 := reach_run henv (run_m9 s (8 * k) retPc (UInt256.ofNat x) (UInt256.ofNat y)
    (UInt256.ofNat k) rest mem' (by omega) hret hjump henv.code henv.run)
  exact ⟨mem', r0.tr (r1.tr r2), hv', hf'⟩

end Challenge.Modexp.Submission.Proofs.Bytecode.BigC
