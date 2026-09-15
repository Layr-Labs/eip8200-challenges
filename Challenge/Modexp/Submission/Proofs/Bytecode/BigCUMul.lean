import Challenge.Modexp.Submission.Proofs.Bytecode.BigCUMulRun

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.Proofs.Bytecode.BigC.U
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Bytecode.BigC

theorem num_frameU {m m0 : ByteArray} {ml a n : Nat}
    (hf : ∀ k, ml ≤ k → bget m k = bget m0 k) (ha : ml ≤ a) :
    num m a n = num m0 a n := num_congr n (fun i _ => hf _ (by omega))

theorem div_two_pow (Y d : Nat) :
    Y / 2 ^ d = 2 * (Y / 2 ^ (d + 1)) + Y / 2 ^ d % 2 := by
  rw [pow_succ, ← Nat.div_div_eq_div_mul]
  exact (Nat.div_add_mod (Y / 2 ^ d) 2).symm

theorem mulLoop {artifact : ProgramArtifact} (mb : MulBlocks artifact)
    (ab : Unsigned.Blocks artifact) {s : State} (env : Environment artifact .Osaka s)
    (ml x y k retPc : Nat) (rest : List UInt256) (mem0 : ByteArray)
    (hcap : rest.length < 990) (hml1 : 1 ≤ ml) (hml : ml ≤ 1024) (hk : k ≤ 1024)
    (hx : 1024 ≤ x) (hx' : x ≤ 8192) (hy : 1024 ≤ y) (hy' : y ≤ 7168)
    (hm : MachineState.readWord s.executionEnv.calldata 64 = UInt256.ofNat ml)
    (hzero : num mem0 8192 ml = 0)
    (hM : 1 ≤ num mem0 1024 ml) (hX : num mem0 x ml ≤ num mem0 1024 ml) :
    ∀ d, d ≤ 8 * k → ∀ mem : ByteArray,
      (∀ a, ml ≤ a → bget mem a = bget mem0 a) →
      num mem 0 ml = num mem0 y k / 2 ^ d * num mem0 x ml % num mem0 1024 ml →
      ∃ mem', Reach (st s 421 (UInt256.ofNat (8 * k - d) :: UInt256.ofNat retPc ::
            UInt256.ofNat x :: UInt256.ofNat y :: UInt256.ofNat k :: rest) mem AW)
          (st s 477 (UInt256.ofNat (8 * k) :: UInt256.ofNat retPc ::
            UInt256.ofNat x :: UInt256.ofNat y :: UInt256.ofNat k :: rest) mem' AW) ∧
        (∀ a, ml ≤ a → bget mem' a = bget mem0 a) ∧
        num mem' 0 ml = num mem0 y k * num mem0 x ml % num mem0 1024 ml := by
  have hJ : MulJumps s.executionEnv.code := by rw [env.code]; exact mb.jumps
  intro d
  induction d with
  | zero =>
    intro _ mem hf hv
    refine ⟨mem, ?_, hf, ?_⟩
    · rw [Nat.sub_zero]
      exact Unsigned.lift_run env mb.mGuard (run_mGuard_done s (8 * k) k _ _ _ rest mem
        (by omega) hk (by omega) hJ)
    · rw [hv, pow_zero, Nat.div_one]
  | succ d ih =>
    intro hd mem hf hv
    have hj : 8 * k - (d + 1) < 8 * k := by omega
    have hrest : (UInt256.ofNat (8 * k - (d + 1)) :: UInt256.ofNat retPc :: UInt256.ofNat x ::
        UInt256.ofNat y :: UInt256.ofNat k :: rest).length < 1000 := by simp; omega
    have hMm : num mem 1024 ml = num mem0 1024 ml := num_frameU hf (by omega)
    have hZm : num mem 8192 ml = 0 := by rw [num_frameU hf (by omega), hzero]
    have r1 := Unsigned.lift_run env mb.mGuard (run_mGuard_go s (8 * k - (d + 1)) k
      (UInt256.ofNat retPc) (UInt256.ofNat x) (UInt256.ofNat y) rest mem
      (by omega) hk (by omega) (by omega) hJ)
    have r2 := Unsigned.lift_run env mb.mDouble (run_mDouble s (8 * k - (d + 1))
      (UInt256.ofNat retPc :: UInt256.ofNat x :: UInt256.ofNat y :: UInt256.ofNat k :: rest)
      mem (by simp; omega) hJ)
    have hacc : num mem 0 ml < num mem0 1024 ml := by
      rw [hv]
      exact Nat.mod_lt _ (by omega)
    obtain ⟨mem1, r3, hv1, hf1⟩ := Unsigned.addm ab s env ml 0 440
      (UInt256.ofNat (8 * k - (d + 1)) :: UInt256.ofNat retPc :: UInt256.ofNat x ::
        UInt256.ofNat y :: UInt256.ofNat k :: rest)
      mem hrest hml1 hml (Or.inl rfl) (by decide) (by decide) hJ.j438 hm hZm
      (by rw [hMm]; omega)
    have hf1' : ∀ a, ml ≤ a → bget mem1 a = bget mem0 a :=
      fun a h1 => (hf1 a h1).trans (hf a h1)
    have hY1 : num mem1 y k = num mem0 y k := num_frameU hf1' (by omega)
    have hX1 : num mem1 x ml = num mem0 x ml := num_frameU hf1' (by omega)
    have hbit : (bitWord mem1 (y + (8 * k - (d + 1)) / 8) ((8 * k - (d + 1)) % 8)).toNat =
        num mem0 y k / 2 ^ d % 2 := by
      rw [← num_bit mem1 y k _ hj, hY1, show 8 * k - (8 * k - (d + 1)) - 1 = d by omega]
    have hsplit := div_two_pow (num mem0 y k) d
    rw [hMm, hv] at hv1
    have hstep : 8 * k - (d + 1) + 1 = 8 * k - d := by omega
    by_cases hb : num mem0 y k / 2 ^ d % 2 = 0
    · have r4 := Unsigned.lift_run env mb.m2 (run_m2_skip s (8 * k - (d + 1)) y
        (UInt256.ofNat retPc) (UInt256.ofNat x) (UInt256.ofNat k) rest mem1
        (by omega) (by omega) (by omega) (by rw [hbit, hb]) hJ)
      have r5 := Unsigned.lift_run env mb.m3 (run_m3 s (8 * k - (d + 1))
        (UInt256.ofNat retPc :: UInt256.ofNat x :: UInt256.ofNat y :: UInt256.ofNat k :: rest)
        mem1 (by simp; omega) (by omega) hJ)
      rw [hstep] at r5
      obtain ⟨mem', r6, hf', hv'⟩ := ih (by omega) mem1 hf1' (by
        rw [hv1, Nat.mod_add_mod, Nat.add_mod_mod, hsplit, hb, Nat.add_zero]
        congr 1
        ring)
      exact ⟨mem', r1.tr (r2.tr (r3.tr (r4.tr (r5.tr r6)))), hf', hv'⟩
    · have hb1 : num mem0 y k / 2 ^ d % 2 = 1 := by omega
      have r4 := Unsigned.lift_run env mb.m2 (run_m2_add s (8 * k - (d + 1)) y
        (UInt256.ofNat retPc) (UInt256.ofNat x) (UInt256.ofNat k) rest mem1
        (by omega) (by omega) (by omega) (by rw [hbit, hb1]; norm_num) hJ)
      have r5 := Unsigned.lift_run env mb.mAdd (run_mAdd s (8 * k - (d + 1))
        (UInt256.ofNat retPc) (UInt256.ofNat x) (UInt256.ofNat y) (UInt256.ofNat k)
        rest mem1 (by omega) hJ)
      have hMm1 : num mem1 1024 ml = num mem0 1024 ml := num_frameU hf1' (by omega)
      have hZm1 : num mem1 8192 ml = 0 := by rw [num_frameU hf1' (by omega), hzero]
      have hacc1 : num mem1 0 ml < num mem0 1024 ml := by
        rw [hv1]
        exact Nat.mod_lt _ (by omega)
      obtain ⟨mem2, r6, hv2, hf2⟩ := Unsigned.addm ab s env ml x 469
        (UInt256.ofNat (8 * k - (d + 1)) :: UInt256.ofNat retPc :: UInt256.ofNat x ::
          UInt256.ofNat y :: UInt256.ofNat k :: rest)
        mem1 hrest hml1 hml (Or.inr (by omega)) hx' (by decide) hJ.j467 hm hZm1
        (by rw [hMm1, hX1]; omega)
      have hf2' : ∀ a, ml ≤ a → bget mem2 a = bget mem0 a :=
        fun a h1 => (hf2 a h1).trans (hf1' a h1)
      have r7 := Unsigned.lift_run env mb.m3 (run_m3 s (8 * k - (d + 1))
        (UInt256.ofNat retPc :: UInt256.ofNat x :: UInt256.ofNat y :: UInt256.ofNat k :: rest)
        mem2 (by simp; omega) (by omega) hJ)
      rw [hstep] at r7
      obtain ⟨mem', r8, hf', hv'⟩ := ih (by omega) mem2 hf2' (by
        rw [hv2, hMm1, hX1, hv1, Nat.mod_add_mod, Nat.add_assoc, Nat.mod_add_mod,
          Nat.add_left_comm, Nat.mod_add_mod, hsplit, hb1]
        congr 1
        ring)
      exact ⟨mem', r1.tr (r2.tr (r3.tr (r4.tr (r5.tr (r6.tr (r7.tr r8)))))), hf', hv'⟩

theorem mulm {artifact : ProgramArtifact} (mb : MulBlocks artifact)
    (ab : Unsigned.Blocks artifact) {s : State} (env : Environment artifact .Osaka s)
    (hcds : s.executionEnv.calldata.size < 2 ^ 64)
    (ml x y k retPc : Nat) (rest : List UInt256) (mem : ByteArray)
    (hcap : rest.length < 990) (hml1 : 1 ≤ ml) (hml : ml ≤ 1024) (hk : k ≤ 1024)
    (hx : 1024 ≤ x) (hx' : x ≤ 8192) (hy : 1024 ≤ y) (hy' : y ≤ 7168)
    (hret : retPc < 2 ^ 16) (hjump : Decode.isValidJumpDest s.executionEnv.code retPc = true)
    (hm : MachineState.readWord s.executionEnv.calldata 64 = UInt256.ofNat ml)
    (hzero : num mem 8192 ml = 0)
    (hM : 1 ≤ num mem 1024 ml) (hX : num mem x ml ≤ num mem 1024 ml) :
    ∃ mem', Reach (st s 413 (UInt256.ofNat retPc :: UInt256.ofNat x :: UInt256.ofNat y ::
          UInt256.ofNat k :: rest) mem AW) (st s retPc rest mem' AW) ∧
      num mem' 0 ml = num mem y k * num mem x ml % num mem 1024 ml ∧
      (∀ a, ml ≤ a → bget mem' a = bget mem a) := by
  have hJ : MulJumps s.executionEnv.code := by rw [env.code]; exact mb.jumps
  have r0 := Unsigned.lift_run env mb.mEntry (run_mEntry s ml (UInt256.ofNat retPc)
    (UInt256.ofNat x) (UInt256.ofNat y) (UInt256.ofNat k) rest mem
    (by omega) hml hm hcds hJ)
  have hf0 : ∀ a, ml ≤ a →
      bget (MachineState.writeBytes mem (MachineState.readPadded s.executionEnv.calldata
        s.executionEnv.calldata.size ml) 0) a = bget mem a := by
    intro a ha
    rw [bget_zeroCopy, if_neg (by omega)]
  have hY : num mem y k < 2 ^ (8 * k) := by
    have := num_lt mem y k
    rwa [show (256 : Nat) = 2 ^ 8 by norm_num, ← pow_mul] at this
  have h0 : num (MachineState.writeBytes mem (MachineState.readPadded s.executionEnv.calldata
      s.executionEnv.calldata.size ml) 0) 0 ml = 0 :=
    num_eq_zero ml (fun i hi => by rw [bget_zeroCopy, if_pos (by omega)])
  obtain ⟨mem', r1, hf', hv'⟩ := mulLoop mb ab env ml x y k retPc rest mem hcap hml1 hml hk
    hx hx' hy hy' hm hzero hM hX (8 * k) (le_refl _) _ hf0 (by
      rw [h0, Nat.div_eq_of_lt hY, Nat.zero_mul, Nat.zero_mod])
  rw [Nat.sub_self] at r1
  have r2 := Unsigned.lift_run env mb.m9 (run_m9 s (8 * k) retPc (UInt256.ofNat x)
    (UInt256.ofNat y) (UInt256.ofNat k) rest mem' (by omega) hret hjump hJ)
  exact ⟨mem', r0.tr (r1.tr r2), hv', hf'⟩

#print axioms mulm
end Challenge.Modexp.Submission.Proofs.Bytecode.BigC.U
