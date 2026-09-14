import Challenge.Modexp.Submission.Proofs.Bytecode.BigCUSetupRun

set_option warningAsError true
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.Proofs.Bytecode.BigC.U
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs.Bytecode WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Bytecode.BigC

theorem num_congr2 {m1 m2 : ByteArray} {a b : Nat} :
    ∀ n, (∀ i, i < n → bget m1 (a + i) = bget m2 (b + i)) → num m1 a n = num m2 b n
  | 0, _ => by rw [num_zero, num_zero]
  | n + 1, h => by
    rw [num_succ, num_succ, num_congr2 n (fun i hi => h i (by omega)), h n (by omega)]

theorem num_eq_zero_iff (mem : ByteArray) (a n : Nat) :
    num mem a n = 0 ↔ ∀ j, j < n → bget mem (a + j) = 0 := by
  constructor
  · intro h j hj
    rw [bget_of_num mem a n j hj, h, Nat.zero_div, Nat.zero_mod]
  · exact num_eq_zero n

theorem setup_zero (mem cd : ByteArray) (bl el ml a : Nat)
    (ha : a < 9248) (hM : a < 1024 ∨ 1024 + ml ≤ a)
    (hB : a < 5120 ∨ 5120 + bl ≤ a) :
    bget (setupMem mem cd bl el ml) a = 0 := by
  unfold setupMem
  rw [bget_copy, if_neg (by omega), bget_copy, if_neg (by omega),
    bget_zeroCopy, if_pos (by omega)]

theorem setup_M (mem cd : ByteArray) (bl el ml : Nat) (hml : ml ≤ 1024) :
    num (setupMem mem cd bl el ml) 1024 ml = num cd (96 + (el + bl)) ml :=
  num_congr2 ml (fun i hi => by
    unfold setupMem
    rw [bget_copy, if_neg (by omega), bget_copy, if_pos (by omega), Nat.add_sub_cancel_left])

theorem setup_B (mem cd : ByteArray) (bl el ml : Nat) :
    num (setupMem mem cd bl el ml) 5120 bl = num cd 96 bl :=
  num_congr2 bl (fun i hi => by
    unfold setupMem
    rw [bget_copy, if_pos (by omega), Nat.add_sub_cancel_left])

theorem lor_toNat_eq_zero (a b : UInt256) :
    (UInt256.lor a b).toNat = 0 ↔ a.toNat = 0 ∧ b.toNat = 0 := by
  rw [Challenge.EvmProof.Word.word_toNat_lor]
  constructor
  · intro h
    have h1 := @Nat.left_le_or a.toNat b.toNat
    have h2 := @Nat.right_le_or a.toNat b.toNat
    omega
  · rintro ⟨h1, h2⟩
    rw [h1, h2]
    simp

theorem zLoop {artifact : ProgramArtifact} (sb : SetupBlocks artifact) {s : State}
    (env : Environment artifact .Osaka s) (rest : List UInt256) (mem : ByteArray)
    (hcap : rest.length < 1000) :
    ∀ i, 1 ≤ i → i ≤ 1024 → ∀ acc : UInt256,
      ∃ acc', Reach (st s 273 (UInt256.ofNat i :: acc :: rest) mem AW)
          (st s 292 (UInt256.ofNat 0 :: acc' :: rest) mem AW) ∧
        (acc'.toNat = 0 ↔ acc.toNat = 0 ∧
          ∀ j, j < i → (MachineState.readWord mem (1024 + j)).toNat = 0) := by
  have hJ : SetupJumps s.executionEnv.code := by rw [env.code]; exact sb.jumps
  intro i hi
  induction i, hi using Nat.le_induction with
  | base =>
    intro _ acc
    refine ⟨_, Unsigned.lift_run env sb.zLoop (run_zLoop_exit s acc rest mem hcap hJ), ?_⟩
    rw [lor_toNat_eq_zero]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, fun j hj => ?_⟩
      obtain rfl : j = 0 := by omega
      simpa using h2
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by simpa using h2 0 (by omega)⟩
  | succ i hi ih =>
    intro hi' acc
    have hrun := run_zLoop_back s (i + 1) acc rest mem hcap (by omega) hi' hJ
    simp only [Nat.add_sub_cancel] at hrun
    obtain ⟨acc', r, h⟩ := ih (by omega) (UInt256.lor acc (MachineState.readWord mem (1024 + i)))
    refine ⟨acc', (Unsigned.lift_run env sb.zLoop hrun).tr r, ?_⟩
    rw [h, lor_toNat_eq_zero]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨h1, fun j hj => ?_⟩
      by_cases hji : j < i
      · exact h3 j hji
      · obtain rfl : j = i := by omega
        exact h2
    · rintro ⟨h1, h3⟩
      exact ⟨⟨h1, h3 i (by omega)⟩, fun j hj => h3 j (by omega)⟩

/-- Scanning a word at each modulus byte is exactly a zero test when its final
31 bytes of over-read are known zero. No equality with the old byte scan is assumed. -/
theorem word_scan_zero_iff (mem : ByteArray) (ml : Nat)
    (hpad : ∀ a, 1024 + ml ≤ a → a < 1024 + ml + 31 → bget mem a = 0) :
    (∀ j, j < ml → (MachineState.readWord mem (1024 + j)).toNat = 0) ↔
      num mem 1024 ml = 0 := by
  constructor
  · intro h
    apply (num_eq_zero_iff mem 1024 ml).mpr
    intro j hj
    have hw := h j hj
    rw [Challenge.EvmProof.Bytes.readWord_toNat] at hw
    have hb := (num_eq_zero_iff mem (1024 + j) 32).mp hw 0 (by decide)
    simpa only [Nat.add_zero] using hb
  · intro h j hj
    rw [Challenge.EvmProof.Bytes.readWord_toNat]
    apply (num_eq_zero_iff mem (1024 + j) 32).mpr
    intro k hk
    by_cases hkm : j + k < ml
    · simpa only [Nat.add_assoc] using (num_eq_zero_iff mem 1024 ml).mp h (j + k) hkm
    · exact hpad _ (by omega) (by omega)

#print axioms zLoop
#print axioms word_scan_zero_iff
end Challenge.Modexp.Submission.Proofs.Bytecode.BigC.U
