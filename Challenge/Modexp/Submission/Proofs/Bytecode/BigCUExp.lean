import Challenge.Modexp.Submission.Proofs.Bytecode.BigCUExpRun
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
/-!
# Compact multi-limb fallback: exponent loop

Left-to-right square-and-multiply over the exponent bits.  The running power
lives in the result window; its residue tracks the original base raised to the
exponent prefix read so far.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.BigC.U

open EvmSemantics
open EvmSemantics.EVM Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs.Bytecode.BigC WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Bytecode

theorem sq_step {R M v p : Nat} (h : R % M = v ^ p % M) :
    R * R % M = v ^ (2 * p) % M := by
  rw [Nat.mul_mod, h, ← Nat.mul_mod, ← pow_add, two_mul]

theorem mul_step {R M v q : Nat} (h : R % M = v ^ q % M) :
    v * R % M = v ^ (q + 1) % M := by
  rw [Nat.mul_mod, h, ← Nat.mul_mod, pow_succ']

theorem expLoop {artifact : ProgramArtifact} (eb : ExpBlocks artifact)
    (mb : MulBlocks artifact) (ab : Unsigned.Blocks artifact)
    {s : State} (env : Environment artifact .Osaka s) (hcds : s.executionEnv.calldata.size < 2 ^ 64)
    (ml bl el : Nat) (rest : List UInt256) (mem0 : ByteArray)
    (hcap : rest.length < 980) (hml1 : 1 ≤ ml) (hml : ml ≤ 1024) (hbl : bl ≤ 1024) (hel : el ≤ 1024)
    (hM : 1 ≤ num mem0 1024 ml)
    (hm : MachineState.readWord s.executionEnv.calldata 64 = UInt256.ofNat ml)
    (hbase : MachineState.readWord s.executionEnv.calldata 0 = UInt256.ofNat bl)
    (hzero : num mem0 8192 ml = 0) :
    ∀ d, d ≤ 8 * el → ∀ mem : ByteArray,
      (∀ a, ml ≤ a → (a < 3072 ∨ 5120 ≤ a) → bget mem a = bget mem0 a) →
      num mem 3072 ml ≤ num mem0 1024 ml →
      num mem 3072 ml % num mem0 1024 ml =
        num mem0 5120 bl ^ (num s.executionEnv.calldata (96 + bl) el / 2 ^ d) % num mem0 1024 ml →
      ∃ mem', Reach (st s 310 (UInt256.ofNat (8 * el - d) :: UInt256.ofNat el ::
            UInt256.ofNat ml :: rest) mem AW)
          (st s 394 (UInt256.ofNat (8 * el) :: UInt256.ofNat el :: UInt256.ofNat ml :: rest)
            mem' AW) ∧
        (∀ a, ml ≤ a → (a < 3072 ∨ 5120 ≤ a) → bget mem' a = bget mem0 a) ∧
        num mem' 3072 ml ≤ num mem0 1024 ml ∧
        num mem' 3072 ml % num mem0 1024 ml =
          num mem0 5120 bl ^ num s.executionEnv.calldata (96 + bl) el % num mem0 1024 ml := by
  have hJ : ExpJumps s.executionEnv.code := by rw [env.code]; exact eb.jumps
  intro d
  induction d with
  | zero =>
    intro _ mem hf hR hv
    refine ⟨mem, ?_, hf, hR, ?_⟩
    · rw [Nat.sub_zero]
      exact Unsigned.lift_run env eb.eGuard (run_eGuard_done s (8 * el) el ml rest mem (by omega) hel
        (by omega) hJ)
    · rw [hv, pow_zero, Nat.div_one]
  | succ d ih =>
    intro hd mem hf hR hv
    have hi : 8 * el - (d + 1) < 8 * el := by omega
    have hstep : 8 * el - (d + 1) + 1 = 8 * el - d := by omega
    have hMm : num mem 1024 ml = num mem0 1024 ml :=
      num_congr ml (fun i _ => hf _ (by omega) (by omega))
    have r1 := Unsigned.lift_run env eb.eGuard (run_eGuard_go s (8 * el - (d + 1)) el ml rest mem (by omega)
      hel (by omega) (by omega) hJ)
    have r2 := Unsigned.lift_run env eb.eSquare (run_eSquare s (8 * el - (d + 1)) el ml rest mem (by omega)
      hJ)
    have hZm : num mem 8192 ml = 0 := by
      exact (num_congr ml (fun i _ => hf _ (by omega) (by omega))).trans hzero
    obtain ⟨mem1, r3, hv1, hf1⟩ := mulm mb ab env hcds ml 3072 3072 ml 333
      (UInt256.ofNat (8 * el - (d + 1)) :: UInt256.ofNat el :: UInt256.ofNat ml :: rest) mem
      (by simp; omega) hml1 hml hml (by decide) (by decide) (by decide) (by decide)
      (by decide) hJ.j333 hm hZm (by rw [hMm]; exact hM) (by rw [hMm]; exact hR)
    rw [hMm] at hv1
    -- the squared power is copied into the result window
    have hf1c : ∀ a, ml ≤ a → (a < 3072 ∨ 5120 ≤ a) →
        bget (MachineState.writeBytes mem1 (MachineState.readPadded mem1 0 ml) 3072) a =
          bget mem0 a := by
      intro a h1 h2
      rw [bget_copy, if_neg (by omega), hf1 a h1, hf a h1 h2]
    have hR1c : num (MachineState.writeBytes mem1 (MachineState.readPadded mem1 0 ml) 3072)
        3072 ml = num mem 3072 ml * num mem 3072 ml % num mem0 1024 ml := by
      rw [num_copy, hv1]
    have hbit : (bitWord s.executionEnv.calldata
        (96 + (bl + (8 * el - (d + 1)) / 8)) ((8 * el - (d + 1)) % 8)).toNat =
          num s.executionEnv.calldata (96 + bl) el / 2 ^ d % 2 := by
      rw [← Nat.add_assoc, ← num_bit s.executionEnv.calldata (96 + bl) el _ hi,
        show 8 * el - (8 * el - (d + 1)) - 1 = d by omega]
    have hsplit := div_two_pow (num s.executionEnv.calldata (96 + bl) el) d
    have hsq : num mem 3072 ml * num mem 3072 ml % num mem0 1024 ml =
        num mem0 5120 bl ^ (2 * (num s.executionEnv.calldata (96 + bl) el / 2 ^ (d + 1))) % num mem0 1024 ml :=
      sq_step hv
    have hsqlt : num mem 3072 ml * num mem 3072 ml % num mem0 1024 ml <
        num mem0 1024 ml := Nat.mod_lt _ (by omega)
    by_cases hb : num s.executionEnv.calldata (96 + bl) el / 2 ^ d % 2 = 0
    · -- exponent bit clear: square only
      have r4 := Unsigned.lift_run env eb.e2 (run_e2_skip s (8 * el - (d + 1)) bl el ml rest mem1 (by omega)
        hml (by omega) hbl hbase (by rw [hbit, hb]) hJ)
      have r5 := Unsigned.lift_run env eb.e3 (run_e3 s (8 * el - (d + 1)) el ml rest
        (MachineState.writeBytes mem1 (MachineState.readPadded mem1 0 ml) 3072) (by omega)
        (by omega) hJ)
      rw [hstep] at r5
      obtain ⟨mem', r6, hf', hR', hv'⟩ := ih (by omega) _ hf1c
        (by rw [hR1c]; exact le_of_lt hsqlt)
        (by rw [hR1c, Nat.mod_mod, hsplit, hb, Nat.add_zero]; exact hsq)
      exact ⟨mem', r1.tr (r2.tr (r3.tr (r4.tr (r5.tr r6)))), hf', hR', hv'⟩
    · -- exponent bit set: square then multiply by the original base
      have hb1 : num s.executionEnv.calldata (96 + bl) el / 2 ^ d % 2 = 1 := by omega
      have r4 := Unsigned.lift_run env eb.e2 (run_e2_mul s (8 * el - (d + 1)) bl el ml rest mem1 (by omega)
        hml (by omega) hbl hbase (by rw [hbit, hb1]; norm_num) hJ)
      have r5 := Unsigned.lift_run env eb.eMul (run_eMul s (8 * el - (d + 1)) bl el ml rest
        (MachineState.writeBytes mem1 (MachineState.readPadded mem1 0 ml) 3072) (by omega)
        hbase hJ)
      have hM1c : num (MachineState.writeBytes mem1 (MachineState.readPadded mem1 0 ml) 3072)
          1024 ml = num mem0 1024 ml := num_congr ml (fun i _ => hf1c _ (by omega) (by omega))
      have hX1c : num (MachineState.writeBytes mem1 (MachineState.readPadded mem1 0 ml) 3072)
          5120 bl = num mem0 5120 bl := num_congr bl (fun i _ => hf1c _ (by omega) (by omega))
      have hZ1c : num (MachineState.writeBytes mem1 (MachineState.readPadded mem1 0 ml) 3072)
          8192 ml = 0 := by
        exact (num_congr ml (fun i _ => hf1c _ (by omega) (by omega))).trans hzero
      obtain ⟨mem2, r6, hv2, hf2⟩ := mulm mb ab env hcds ml 3072 5120 bl 379
        (UInt256.ofNat (8 * el - (d + 1)) :: UInt256.ofNat el :: UInt256.ofNat ml :: rest)
        (MachineState.writeBytes mem1 (MachineState.readPadded mem1 0 ml) 3072)
        (by simp; omega) hml1 hml hbl (by decide) (by decide) (by decide) (by decide)
        (by decide) hJ.j379 hm hZ1c (by rw [hM1c]; exact hM)
        (by rw [hM1c, hR1c]; exact le_of_lt hsqlt)
      rw [hM1c, hX1c, hR1c] at hv2
      have r7 := Unsigned.lift_run env eb.e4 (run_e4 s (8 * el - (d + 1)) el ml rest mem2 (by omega) hml
        hJ)
      have r8 := Unsigned.lift_run env eb.e3 (run_e3 s (8 * el - (d + 1)) el ml rest
        (MachineState.writeBytes mem2 (MachineState.readPadded mem2 0 ml) 3072) (by omega)
        (by omega) hJ)
      rw [hstep] at r8
      have hf2c : ∀ a, ml ≤ a → (a < 3072 ∨ 5120 ≤ a) →
          bget (MachineState.writeBytes mem2 (MachineState.readPadded mem2 0 ml) 3072) a =
            bget mem0 a := by
        intro a h1 h2
        rw [bget_copy, if_neg (by omega), hf2 a h1, hf1c a h1 h2]
      have hR2c : num (MachineState.writeBytes mem2 (MachineState.readPadded mem2 0 ml) 3072)
          3072 ml = num mem0 5120 bl *
            (num mem 3072 ml * num mem 3072 ml % num mem0 1024 ml) % num mem0 1024 ml := by
        rw [num_copy, hv2]
      obtain ⟨mem', r9, hf', hR', hv'⟩ := ih (by omega) _ hf2c
        (by rw [hR2c]; exact le_of_lt (Nat.mod_lt _ (by omega)))
        (by
          rw [hR2c, Nat.mod_mod, hsplit, hb1]
          exact mul_step (by rw [Nat.mod_mod]; exact hsq))
      exact ⟨mem', r1.tr (r2.tr (r3.tr (r4.tr (r5.tr (r6.tr (r7.tr (r8.tr r9))))))), hf', hR', hv'⟩


#print axioms expLoop
end Challenge.Modexp.Submission.Proofs.Bytecode.BigC.U
