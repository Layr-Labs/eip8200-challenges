import Challenge.Modexp.Submission.Proofs.Bytecode.BigCMem
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
/-!
# Compact multi-limb fallback: modular addition

`ADDM` adds a window into the accumulator with a byte-serial carry chain,
subtracts the modulus into scratch with a byte-serial borrow chain, and keeps
whichever of the two is the reduced sum.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.BigC

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

theorem lt_word {n : Nat} (h : n < 65536) : n < 2 ^ 256 :=
  lt_of_lt_of_le h (by norm_num)

theorem shr_toNat (x : UInt256) (k : Nat) (hk : k < 256) :
    (UInt256.shiftRight x (UInt256.ofNat k)).toNat = x.toNat / 2 ^ k := by
  rw [Challenge.EvmProof.Word.shiftRight_toNat _ hk, Nat.shiftRight_eq_div_pow]

theorem shr8_toNat (x : UInt256) :
    (UInt256.shiftRight x (UInt256.ofNat 8)).toNat = x.toNat / 256 := by
  rw [shr_toNat _ 8 (by norm_num)]
  norm_num

theorem ofNat_zero_toNat : (UInt256.ofNat 0).toNat = 0 := by simp

/-- One carry step. -/
theorem addSum_toNat (mem : ByteArray) (src i : Nat) (c : UInt256) (hc : c.toNat ≤ 1) :
    (addSum mem src i c).toNat = c.toNat + bget mem i + bget mem (src + i) := by
  unfold addSum
  have h1 := bget_lt mem i
  have h2 := bget_lt mem (src + i)
  rw [Challenge.EvmProof.Word.word_toNat_add, Challenge.EvmProof.Word.word_toNat_add,
    byteW_toNat, byteW_toNat,
    Nat.mod_eq_of_lt (lt_word (by omega : bget mem i + bget mem (src + i) < 65536)),
    Nat.mod_eq_of_lt (lt_word (by omega :
      c.toNat + (bget mem i + bget mem (src + i)) < 65536))]
  omega

/-- One borrow step: written byte plus subtrahend equals minuend plus the
outgoing borrow. -/
theorem subDiff_step (mem : ByteArray) (i : Nat) (b : UInt256) (hb : b.toNat ≤ 1) :
    (subDiff mem i b).toNat % 256 + bget mem (1024 + i) + b.toNat =
        bget mem i + 256 * ((subDiff mem i b).toNat / 2 ^ 255) ∧
      (subDiff mem i b).toNat / 2 ^ 255 ≤ 1 := by
  unfold subDiff
  have h1 := bget_lt mem i
  have h2 := bget_lt mem (1024 + i)
  have hbl : b.toNat < 2 ^ 256 := b.val.isLt
  simp only [Challenge.EvmProof.Word.word_toNat_sub_cond, byteW_toNat]
  norm_num at hbl ⊢
  split_ifs <;> omega

/-! ## Carry chain `A1` -/

theorem addLoop {s : State} (henv : Env s) (src : Nat) (ret : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1000) (hsrc : src ≤ 8192) :
    ∀ i, 1 ≤ i → i ≤ 1024 → ∀ (mem : ByteArray) (c : UInt256), c.toNat ≤ 1 →
      (src = 0 ∨ i ≤ src) →
      ∃ mem' c', Reach (st s 554 (UInt256.ofNat i :: c :: ret :: UInt256.ofNat src :: rest)
          mem AW)
          (st s 584 (UInt256.ofNat 0 :: c' :: ret :: UInt256.ofNat src :: rest) mem' AW) ∧
        c'.toNat ≤ 1 ∧
        num mem' 0 i + c'.toNat * 256 ^ i = num mem 0 i + num mem src i + c.toNat ∧
        (∀ k, i ≤ k → bget mem' k = bget mem k) := by
  intro i hi
  induction i, hi using Nat.le_induction with
  | base =>
    intro _ mem c hc _
    have hsum := addSum_toNat mem src 0 c hc
    have hb0 := bget_lt mem 0
    have hbs := bget_lt mem src
    refine ⟨_, _, reach_run henv
      (run_aLoop_exit s src c ret rest mem hcap hsrc henv.code henv.run), ?_, ?_, ?_⟩
    · rw [shr8_toNat _, hsum]
      simp only [Nat.add_zero] at hsum ⊢
      omega
    · rw [shr8_toNat _, num_one, num_one, num_one, bget_write1, if_pos rfl,
        hsum]
      simp only [Nat.add_zero, pow_one]
      omega
    · intro k hk
      rw [bget_write1, if_neg (by omega)]
  | succ i hi ih =>
    intro hi' mem c hc hs
    have hrun := run_aLoop_back s (i + 1) src c ret rest mem hcap (by omega) hi' hsrc
      henv.code henv.run
    simp only [Nat.add_sub_cancel] at hrun
    have hsum := addSum_toNat mem src i c hc
    have hbi := bget_lt mem i
    have hbs := bget_lt mem (src + i)
    have hc1 : (UInt256.shiftRight (addSum mem src i c) (UInt256.ofNat 8)).toNat ≤ 1 := by
      rw [shr8_toNat _, hsum]
      omega
    obtain ⟨mem', c', hreach, hc', heq, hframe⟩ := ih (by omega) _ _ hc1 (by omega)
    refine ⟨mem', c', (reach_run henv hrun).tr hreach, hc', ?_, ?_⟩
    · have hA : num (MachineState.writeBytes mem
          (ByteArray.mk #[UInt8.ofNat ((addSum mem src i c).toNat % 256)]) i) 0 i =
          num mem 0 i :=
        num_congr i (fun j hj => by rw [bget_write1, if_neg (by omega)])
      have hS : num (MachineState.writeBytes mem
          (ByteArray.mk #[UInt8.ofNat ((addSum mem src i c).toNat % 256)]) i) src i =
          num mem src i :=
        num_congr i (fun j hj => by rw [bget_write1, if_neg (by omega)])
      have hlast : bget mem' i = (addSum mem src i c).toNat % 256 := by
        rw [hframe i (le_refl _), bget_write1, if_pos rfl, Nat.mod_mod]
      rw [hA, hS, shr8_toNat _, hsum] at heq
      rw [num_succ, num_succ mem, num_succ mem, Nat.zero_add, hlast, hsum, pow_succ]
      rw [show c'.toNat * (256 ^ i * 256) = c'.toNat * 256 ^ i * 256 by ring]
      generalize c'.toNat * 256 ^ i = Q at *
      omega
    · intro k hk
      rw [hframe k (by omega), bget_write1, if_neg (by omega)]

/-! ## Borrow chain `S1` -/

theorem subLoop {s : State} (henv : Env s) (c ret src : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1000) :
    ∀ i, 1 ≤ i → i ≤ 1024 → ∀ (mem : ByteArray) (b : UInt256), b.toNat ≤ 1 →
      ∃ mem' b', Reach (st s 590 (UInt256.ofNat i :: b :: c :: ret :: src :: rest) mem AW)
          (st s 627 (UInt256.ofNat 0 :: b' :: c :: ret :: src :: rest) mem' AW) ∧
        b'.toNat ≤ 1 ∧
        num mem' 4096 i + num mem 1024 i + b.toNat = num mem 0 i + b'.toNat * 256 ^ i ∧
        (∀ k, ¬ (4096 ≤ k ∧ k < 4096 + i) → bget mem' k = bget mem k) := by
  intro i hi
  induction i, hi using Nat.le_induction with
  | base =>
    intro _ mem b hb
    obtain ⟨hs1, hs2⟩ := subDiff_step mem 0 b hb
    refine ⟨_, _, reach_run henv
      (run_sLoop_exit s b c ret src rest mem hcap henv.code henv.run), ?_, ?_, ?_⟩
    · rw [shr_toNat _ 255 (by norm_num)]
      exact hs2
    · rw [shr_toNat _ 255 (by norm_num), num_one, num_one, num_one, bget_write1, if_pos rfl,
        Nat.mod_mod, pow_one]
      simp only [Nat.add_zero] at hs1
      omega
    · intro k hk
      rw [bget_write1, if_neg (by omega)]
  | succ i hi ih =>
    intro hi' mem b hb
    have hrun := run_sLoop_back s (i + 1) b c ret src rest mem hcap (by omega) hi'
      henv.code henv.run
    simp only [Nat.add_sub_cancel] at hrun
    obtain ⟨hs1, hs2⟩ := subDiff_step mem i b hb
    have hb1 : (UInt256.shiftRight (subDiff mem i b) (UInt256.ofNat 255)).toNat ≤ 1 := by
      rw [shr_toNat _ 255 (by norm_num)]
      exact hs2
    obtain ⟨mem', b', hreach, hb', heq, hframe⟩ := ih (by omega) _ _ hb1
    refine ⟨mem', b', (reach_run henv hrun).tr hreach, hb', ?_, ?_⟩
    · have hM : num (MachineState.writeBytes mem
          (ByteArray.mk #[UInt8.ofNat ((subDiff mem i b).toNat % 256)]) (4096 + i)) 1024 i =
          num mem 1024 i :=
        num_congr i (fun j hj => by rw [bget_write1, if_neg (by omega)])
      have hA : num (MachineState.writeBytes mem
          (ByteArray.mk #[UInt8.ofNat ((subDiff mem i b).toNat % 256)]) (4096 + i)) 0 i =
          num mem 0 i :=
        num_congr i (fun j hj => by rw [bget_write1, if_neg (by omega)])
      have hlast : bget mem' (4096 + i) = (subDiff mem i b).toNat % 256 := by
        rw [hframe (4096 + i) (by omega), bget_write1, if_pos rfl, Nat.mod_mod]
      rw [hM, hA, shr_toNat _ 255 (by norm_num)] at heq
      rw [num_succ, num_succ mem, num_succ mem, Nat.zero_add, hlast, pow_succ]
      rw [show b'.toNat * (256 ^ i * 256) = b'.toNat * 256 ^ i * 256 by ring]
      generalize b'.toNat * 256 ^ i = Q at *
      omega
    · intro k hk
      rw [hframe k (by omega), bget_write1, if_neg (by omega)]

/-! ## The whole subroutine -/

theorem mod_of_lt_two {x m : Nat} (h1 : m ≤ x) (h2 : x < 2 * m) : x % m = x - m := by
  rw [Nat.mod_eq_sub_mod h1, Nat.mod_eq_of_lt (by omega)]

/-- `ADDM`: accumulator := (accumulator + source) mod modulus, for a sum below
twice the modulus.  Only the accumulator and the scratch window change. -/
theorem addm {s : State} (henv : Env s) (ml src retPc : Nat) (rest : List UInt256)
    (mem : ByteArray) (hcap : rest.length < 1000) (hml1 : 1 ≤ ml) (hml : ml ≤ 1024)
    (hsrc : src = 0 ∨ ml ≤ src) (hsrc' : src ≤ 8192)
    (hret : retPc < 2 ^ 16) (hjump : Decode.isValidJumpDest submissionBytecode retPc = true)
    (hmsv : MachineState.readWord mem 9216 = UInt256.ofNat ml)
    (hlt : num mem 0 ml + num mem src ml < 2 * num mem 1024 ml) :
    ∃ mem', Reach (st s 548 (UInt256.ofNat retPc :: UInt256.ofNat src :: rest) mem AW)
        (st s retPc rest mem' AW) ∧
      num mem' 0 ml = (num mem 0 ml + num mem src ml) % num mem 1024 ml ∧
      (∀ k, ml ≤ k → (k < 4096 ∨ 5120 ≤ k) → bget mem' k = bget mem k) := by
  have r0 := reach_run henv (run_aEntry s ml (UInt256.ofNat retPc) (UInt256.ofNat src) rest
    mem hcap hmsv henv.code henv.run)
  obtain ⟨mem1, c1, r1, hc1, heq1, hf1⟩ := addLoop henv src (UInt256.ofNat retPc) rest hcap
    hsrc' ml hml1 hml mem (UInt256.ofNat 0) (by simp) (by omega)
  have hmsv1 : MachineState.readWord mem1 9216 = UInt256.ofNat ml := by
    rw [← hmsv]
    exact readWord_frame (fun k => ml ≤ k) hf1 (fun i _ => by omega)
  have rX := reach_run henv (run_aExit s ml c1 (UInt256.ofNat retPc) (UInt256.ofNat src)
    rest mem1 hcap hmsv1 henv.code henv.run)
  obtain ⟨mem2, b2, r2, hb2, heq2, hf2⟩ := subLoop henv c1 (UInt256.ofNat retPc)
    (UInt256.ofNat src) rest hcap ml hml1 hml mem1 (UInt256.ofNat 0) (by simp)
  have hmsv2 : MachineState.readWord mem2 9216 = UInt256.ofNat ml := by
    rw [← hmsv1]
    exact readWord_frame (fun k => ¬ (4096 ≤ k ∧ k < 4096 + ml)) hf2 (fun i _ => by omega)
  have hM1 : num mem1 1024 ml = num mem 1024 ml :=
    num_frame (fun k => ml ≤ k) hf1 (fun i _ => by omega)
  have hA2 : num mem2 0 ml = num mem1 0 ml :=
    num_frame (fun k => ¬ (4096 ≤ k ∧ k < 4096 + ml)) hf2 (fun i _ => by omega)
  have hMlt := num_lt mem 1024 ml
  have hTlt := num_lt mem2 4096 ml
  have hframe2 : ∀ k, ml ≤ k → (k < 4096 ∨ 5120 ≤ k) → bget mem2 k = bget mem k := by
    intro k hk hk'
    rw [hf2 k (by omega), hf1 k hk]
  rw [ofNat_zero_toNat, Nat.add_zero] at heq1 heq2
  rw [hM1] at heq2
  have hc1' : c1.toNat = 0 ∨ c1.toNat = 1 := by omega
  have hb2' : b2.toNat = 0 ∨ b2.toNat = 1 := by omega
  generalize hP : 256 ^ ml = P at heq1 heq2 hMlt hTlt
  rcases hc1' with hc | hc <;> rcases hb2' with hb | hb <;>
    rw [hc] at heq1 <;> rw [hb] at heq2 <;> simp only [zero_mul, one_mul, Nat.add_zero] at heq1 heq2
  · -- no carry, no borrow: the difference is the reduced sum
    have hkeep : ¬ ((if b2.toNat = 0 then 1 else 0) ||| c1.toNat) = 0 := by
      rw [hb, hc]; simp
    have r3 := reach_run henv (run_sExit_copy s b2 c1 (UInt256.ofNat retPc)
      (UInt256.ofNat src) rest mem2 hcap hkeep henv.code henv.run)
    have r4 := reach_run henv (run_copy s ml (UInt256.ofNat retPc) (UInt256.ofNat src) rest
      mem2 hcap hml hmsv2 henv.code henv.run)
    have r5 := reach_run henv (run_a3 s retPc (UInt256.ofNat src) rest
      (MachineState.writeBytes mem2 (MachineState.readPadded mem2 4096 ml) 0) hcap hret hjump
      henv.code henv.run)
    refine ⟨_, r0.tr (r1.tr (rX.tr (r2.tr (r3.tr (r4.tr r5))))), ?_, ?_⟩
    · rw [num_copy, mod_of_lt_two (by omega) hlt]
      omega
    · intro k hk hk'
      rw [bget_copy, if_neg (by omega), hframe2 k hk hk']
  · -- no carry, borrow: the sum was already reduced
    have hkeep : ((if b2.toNat = 0 then 1 else 0) ||| c1.toNat) = 0 := by
      rw [hb, hc]; simp
    have r3 := reach_run henv (run_sExit_keep s b2 c1 (UInt256.ofNat retPc)
      (UInt256.ofNat src) rest mem2 hcap hkeep henv.code henv.run)
    have r5 := reach_run henv (run_a3 s retPc (UInt256.ofNat src) rest mem2 hcap hret hjump
      henv.code henv.run)
    refine ⟨_, r0.tr (r1.tr (rX.tr (r2.tr (r3.tr r5)))), ?_, hframe2⟩
    rw [hA2, Nat.mod_eq_of_lt (by omega)]
    omega
  · -- carry without borrow is impossible below twice the modulus
    exfalso
    omega
  · -- carry and borrow: the wrapped difference is the reduced sum
    have hkeep : ¬ ((if b2.toNat = 0 then 1 else 0) ||| c1.toNat) = 0 := by
      rw [hb, hc]; simp
    have r3 := reach_run henv (run_sExit_copy s b2 c1 (UInt256.ofNat retPc)
      (UInt256.ofNat src) rest mem2 hcap hkeep henv.code henv.run)
    have r4 := reach_run henv (run_copy s ml (UInt256.ofNat retPc) (UInt256.ofNat src) rest
      mem2 hcap hml hmsv2 henv.code henv.run)
    have r5 := reach_run henv (run_a3 s retPc (UInt256.ofNat src) rest
      (MachineState.writeBytes mem2 (MachineState.readPadded mem2 4096 ml) 0) hcap hret hjump
      henv.code henv.run)
    refine ⟨_, r0.tr (r1.tr (rX.tr (r2.tr (r3.tr (r4.tr r5))))), ?_, ?_⟩
    · rw [num_copy, mod_of_lt_two (by omega) hlt]
      omega
    · intro k hk hk'
      rw [bget_copy, if_neg (by omega), hframe2 k hk hk']

end Challenge.Modexp.Submission.Proofs.Bytecode.BigC
