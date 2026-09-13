import Challenge.Modexp.Submission.Proofs.Bytecode.BigCMul
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
/-!
# Compact multi-limb fallback: exponent loop

Left-to-right square-and-multiply over the exponent bits.  The running power
lives in the result window; its residue tracks the reduced base raised to the
exponent prefix read so far.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.BigC

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

theorem sq_step {R M v p : Nat} (h : R % M = v ^ p % M) :
    R * R % M = v ^ (2 * p) % M := by
  rw [Nat.mul_mod, h, ← Nat.mul_mod, ← pow_add, two_mul]

theorem mul_step {R M v q : Nat} (h : R % M = v ^ q % M) :
    v * R % M = v ^ (q + 1) % M := by
  rw [Nat.mul_mod, h, ← Nat.mul_mod, pow_succ']

theorem msvE {m m0 : ByteArray} {ml : Nat} (hml : ml ≤ 1024)
    (hf : ∀ k, ml ≤ k → (k < 3072 ∨ 5120 ≤ k) → bget m k = bget m0 k) :
    MachineState.readWord m 9216 = MachineState.readWord m0 9216 :=
  readWord_congr (fun i _ => hf _ (by omega) (by omega))

theorem expLoop {s : State} (henv : Env s) (hcds : s.executionEnv.calldata.size < 2 ^ 64)
    (ml el : Nat) (rest : List UInt256) (mem0 : ByteArray)
    (hcap : rest.length < 980) (hml1 : 1 ≤ ml) (hml : ml ≤ 1024) (hel : el ≤ 1024)
    (hM : 1 ≤ num mem0 1024 ml) :
    ∀ d, d ≤ 8 * el → ∀ mem : ByteArray,
      MachineState.readWord mem 9216 = UInt256.ofNat ml →
      (∀ a, ml ≤ a → (a < 3072 ∨ 5120 ≤ a) → bget mem a = bget mem0 a) →
      num mem 3072 ml ≤ num mem0 1024 ml →
      num mem 3072 ml % num mem0 1024 ml =
        num mem0 2048 ml ^ (num mem0 6144 el / 2 ^ d) % num mem0 1024 ml →
      ∃ mem', Reach (st s 373 (UInt256.ofNat (8 * el - d) :: UInt256.ofNat el ::
            UInt256.ofNat ml :: rest) mem AW)
          (st s 454 (UInt256.ofNat (8 * el) :: UInt256.ofNat el :: UInt256.ofNat ml :: rest)
            mem' AW) ∧
        MachineState.readWord mem' 9216 = UInt256.ofNat ml ∧
        (∀ a, ml ≤ a → (a < 3072 ∨ 5120 ≤ a) → bget mem' a = bget mem0 a) ∧
        num mem' 3072 ml ≤ num mem0 1024 ml ∧
        num mem' 3072 ml % num mem0 1024 ml =
          num mem0 2048 ml ^ num mem0 6144 el % num mem0 1024 ml := by
  intro d
  induction d with
  | zero =>
    intro _ mem hmsv hf hR hv
    refine ⟨mem, ?_, hmsv, hf, hR, ?_⟩
    · rw [Nat.sub_zero]
      exact reach_run henv (run_eGuard_done s (8 * el) el ml rest mem (by omega) hel
        (by omega) henv.code henv.run)
    · rw [hv, pow_zero, Nat.div_one]
  | succ d ih =>
    intro hd mem hmsv hf hR hv
    have hi : 8 * el - (d + 1) < 8 * el := by omega
    have hstep : 8 * el - (d + 1) + 1 = 8 * el - d := by omega
    have hMm : num mem 1024 ml = num mem0 1024 ml :=
      num_congr ml (fun i _ => hf _ (by omega) (by omega))
    have r1 := reach_run henv (run_eGuard_go s (8 * el - (d + 1)) el ml rest mem (by omega)
      hel (by omega) (lt_word (by omega)) henv.code henv.run)
    have r2 := reach_run henv (run_eSquare s (8 * el - (d + 1)) el ml rest mem (by omega)
      henv.code henv.run)
    obtain ⟨mem1, r3, hv1, hf1⟩ := mulm henv hcds ml 3072 3072 ml 396
      (UInt256.ofNat (8 * el - (d + 1)) :: UInt256.ofNat el :: UInt256.ofNat ml :: rest) mem
      (by simp; omega) hml1 hml hml (by norm_num) (Or.inl (by omega)) (by norm_num)
      (Or.inl (by omega)) (by norm_num) jump404 hmsv (by rw [hMm]; exact hM)
      (by rw [hMm]; exact hR)
    rw [hMm] at hv1
    -- the squared power is copied into the result window
    have hf1c : ∀ a, ml ≤ a → (a < 3072 ∨ 5120 ≤ a) →
        bget (MachineState.writeBytes mem1 (MachineState.readPadded mem1 0 ml) 3072) a =
          bget mem0 a := by
      intro a h1 h2
      rw [bget_copy, if_neg (by omega), hf1 a h1 (by omega), hf a h1 h2]
    have hmsv1c : MachineState.readWord
        (MachineState.writeBytes mem1 (MachineState.readPadded mem1 0 ml) 3072) 9216 =
          UInt256.ofNat ml := by
      rw [msvE hml hf1c, ← msvE hml hf, hmsv]
    have hR1c : num (MachineState.writeBytes mem1 (MachineState.readPadded mem1 0 ml) 3072)
        3072 ml = num mem 3072 ml * num mem 3072 ml % num mem0 1024 ml := by
      rw [num_copy, hv1]
    have hE1c : num (MachineState.writeBytes mem1 (MachineState.readPadded mem1 0 ml) 3072)
        6144 el = num mem0 6144 el := num_congr el (fun i _ => hf1c _ (by omega) (by omega))
    have hbit : (bitWord (MachineState.writeBytes mem1 (MachineState.readPadded mem1 0 ml)
        3072) (6144 + (8 * el - (d + 1)) / 8) ((8 * el - (d + 1)) % 8)).toNat =
          num mem0 6144 el / 2 ^ d % 2 := by
      rw [← num_bit _ 6144 el _ hi, hE1c, show 8 * el - (8 * el - (d + 1)) - 1 = d by omega]
    have hsplit := div_two_pow (num mem0 6144 el) d
    have hsq : num mem 3072 ml * num mem 3072 ml % num mem0 1024 ml =
        num mem0 2048 ml ^ (2 * (num mem0 6144 el / 2 ^ (d + 1))) % num mem0 1024 ml :=
      sq_step hv
    have hsqlt : num mem 3072 ml * num mem 3072 ml % num mem0 1024 ml <
        num mem0 1024 ml := Nat.mod_lt _ (by omega)
    by_cases hb : num mem0 6144 el / 2 ^ d % 2 = 0
    · -- exponent bit clear: square only
      have r4 := reach_run henv (run_e2_skip s (8 * el - (d + 1)) el ml rest mem1 (by omega)
        hml (by omega) (by rw [hbit, hb]) henv.code henv.run)
      have r5 := reach_run henv (run_e3 s (8 * el - (d + 1)) el ml rest
        (MachineState.writeBytes mem1 (MachineState.readPadded mem1 0 ml) 3072) (by omega)
        (by omega) henv.code henv.run)
      rw [hstep] at r5
      obtain ⟨mem', r6, hmsv', hf', hR', hv'⟩ := ih (by omega) _ hmsv1c hf1c
        (by rw [hR1c]; exact le_of_lt hsqlt)
        (by rw [hR1c, Nat.mod_mod, hsplit, hb, Nat.add_zero]; exact hsq)
      exact ⟨mem', r1.tr (r2.tr (r3.tr (r4.tr (r5.tr r6)))), hmsv', hf', hR', hv'⟩
    · -- exponent bit set: square then multiply by the reduced base
      have hb1 : num mem0 6144 el / 2 ^ d % 2 = 1 := by omega
      have r4 := reach_run henv (run_e2_mul s (8 * el - (d + 1)) el ml rest mem1 (by omega)
        hml (by omega) (by rw [hbit, hb1]; norm_num) henv.code henv.run)
      have r5 := reach_run henv (run_eMul s (8 * el - (d + 1)) el ml rest
        (MachineState.writeBytes mem1 (MachineState.readPadded mem1 0 ml) 3072) (by omega)
        henv.code henv.run)
      have hM1c : num (MachineState.writeBytes mem1 (MachineState.readPadded mem1 0 ml) 3072)
          1024 ml = num mem0 1024 ml := num_congr ml (fun i _ => hf1c _ (by omega) (by omega))
      have hX1c : num (MachineState.writeBytes mem1 (MachineState.readPadded mem1 0 ml) 3072)
          2048 ml = num mem0 2048 ml := num_congr ml (fun i _ => hf1c _ (by omega) (by omega))
      obtain ⟨mem2, r6, hv2, hf2⟩ := mulm henv hcds ml 3072 2048 ml 439
        (UInt256.ofNat (8 * el - (d + 1)) :: UInt256.ofNat el :: UInt256.ofNat ml :: rest)
        (MachineState.writeBytes mem1 (MachineState.readPadded mem1 0 ml) 3072)
        (by simp; omega) hml1 hml hml (by norm_num) (Or.inl (by omega)) (by norm_num)
        (Or.inl (by omega)) (by norm_num) jump447 hmsv1c (by rw [hM1c]; exact hM)
        (by rw [hM1c, hR1c]; exact le_of_lt hsqlt)
      rw [hM1c, hX1c, hR1c] at hv2
      have r7 := reach_run henv (run_e4 s (8 * el - (d + 1)) el ml rest mem2 (by omega) hml
        henv.code henv.run)
      have r8 := reach_run henv (run_e3 s (8 * el - (d + 1)) el ml rest
        (MachineState.writeBytes mem2 (MachineState.readPadded mem2 0 ml) 3072) (by omega)
        (by omega) henv.code henv.run)
      rw [hstep] at r8
      have hf2c : ∀ a, ml ≤ a → (a < 3072 ∨ 5120 ≤ a) →
          bget (MachineState.writeBytes mem2 (MachineState.readPadded mem2 0 ml) 3072) a =
            bget mem0 a := by
        intro a h1 h2
        rw [bget_copy, if_neg (by omega), hf2 a h1 (by omega), hf1c a h1 h2]
      have hmsv2c : MachineState.readWord
          (MachineState.writeBytes mem2 (MachineState.readPadded mem2 0 ml) 3072) 9216 =
            UInt256.ofNat ml := by
        rw [msvE hml hf2c, ← msvE hml hf, hmsv]
      have hR2c : num (MachineState.writeBytes mem2 (MachineState.readPadded mem2 0 ml) 3072)
          3072 ml = num mem0 2048 ml *
            (num mem 3072 ml * num mem 3072 ml % num mem0 1024 ml) % num mem0 1024 ml := by
        rw [num_copy, hv2]
      obtain ⟨mem', r9, hmsv', hf', hR', hv'⟩ := ih (by omega) _ hmsv2c hf2c
        (by rw [hR2c]; exact le_of_lt (Nat.mod_lt _ (by omega)))
        (by
          rw [hR2c, Nat.mod_mod, hsplit, hb1]
          exact mul_step (by rw [Nat.mod_mod]; exact hsq))
      exact ⟨mem', r1.tr (r2.tr (r3.tr (r4.tr (r5.tr (r6.tr (r7.tr (r8.tr r9))))))), hmsv',
        hf', hR', hv'⟩

end Challenge.Modexp.Submission.Proofs.Bytecode.BigC
