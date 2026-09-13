import Challenge.Modexp.Submission.Proofs.Bytecode.BigCExp
import Challenge.Modexp.Submission.Proofs.Bytecode.BigCSetup
set_option warningAsError true
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
/-!
# Compact multi-limb fallback: end-to-end correctness

From the fallback entry (pc 258) every valid input reaches a `RETURN` of the
MODEXP result: an all-zero modulus returns the zero scratch window, otherwise
`base mod m` is formed by one `MULM`, raised by the exponent loop, reduced by a
final `ADDM` and returned.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.BigC

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

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

/-! ## Operand loading -/

section setup
variable (mem cd : ByteArray) (bl el ml : Nat)

theorem setup_zero (hbl : bl ≤ 1024) (hel : el ≤ 1024) (hml : ml ≤ 1024) (a : Nat)
    (h1 : 7168 ≤ a) (h2 : a < 9216) : bget (setupMem mem cd bl el ml) a = 0 := by
  dsimp only [setupMem]
  rw [bget_copy, if_neg (by omega), bget_copy, if_neg (by omega), bget_copy, if_neg (by omega),
    bget_write, YulEvmCompiler.BytesLemmas.natToBytesPadded_size, if_neg (by omega),
    bget_zeroCopy, if_pos (by omega)]

theorem setup_msv (hbl : bl ≤ 1024) (hel : el ≤ 1024) (hml : ml ≤ 1024) :
    MachineState.readWord (setupMem mem cd bl el ml) 9216 = UInt256.ofNat ml := by
  have h : MachineState.readWord (setupMem mem cd bl el ml) 9216 =
      MachineState.readWord (MachineState.writeBytes
        (MachineState.writeBytes mem (MachineState.readPadded cd cd.size 9248) 0)
        (Data.Bytes.natToBytesPadded ml 32) 9216) 9216 :=
    readWord_congr (fun i _ => by
      dsimp only [setupMem]
      rw [bget_copy, if_neg (by omega), bget_copy, if_neg (by omega), bget_copy,
        if_neg (by omega)])
  rw [h, Challenge.EvmProof.Memory.readWord_writeBytes_of_lt _ 9216 ml
    (lt_of_le_of_lt hml (by norm_num : (1024 : Nat) < 256 ^ 32))]

theorem setup_M (hbl : bl ≤ 1024) (hel : el ≤ 1024) (hml : ml ≤ 1024) :
    num (setupMem mem cd bl el ml) 1024 ml = num cd (96 + (el + bl)) ml :=
  num_congr2 ml (fun i hi => by
    dsimp only [setupMem]
    rw [bget_copy, if_neg (by omega), bget_copy, if_neg (by omega), bget_copy,
      if_pos (by omega)]
    rw [Nat.add_sub_cancel_left])

theorem setup_B (hbl : bl ≤ 1024) (hel : el ≤ 1024) (hml : ml ≤ 1024) :
    num (setupMem mem cd bl el ml) 5120 bl = num cd 96 bl :=
  num_congr2 bl (fun i hi => by
    dsimp only [setupMem]
    rw [bget_copy, if_neg (by omega), bget_copy, if_pos (by omega)]
    rw [Nat.add_sub_cancel_left])

theorem setup_E (hbl : bl ≤ 1024) (hel : el ≤ 1024) (hml : ml ≤ 1024) :
    num (setupMem mem cd bl el ml) 6144 el = num cd (96 + bl) el :=
  num_congr2 el (fun i hi => by
    dsimp only [setupMem]
    rw [bget_copy, if_pos (by omega)]
    rw [Nat.add_sub_cancel_left])

end setup

/-! ## Modulus scan (`Z1`) -/

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

theorem zLoop {s : State} (henv : Env s) (rest : List UInt256) (mem : ByteArray)
    (hcap : rest.length < 1000) :
    ∀ i, 1 ≤ i → i ≤ 1024 → ∀ acc : UInt256,
      ∃ acc', Reach (st s 307 (UInt256.ofNat i :: acc :: rest) mem AW)
          (st s 328 (UInt256.ofNat 0 :: acc' :: rest) mem AW) ∧
        (acc'.toNat = 0 ↔ acc.toNat = 0 ∧ ∀ j, j < i → bget mem (1024 + j) = 0) := by
  intro i hi
  induction i, hi using Nat.le_induction with
  | base =>
    intro _ acc
    refine ⟨_, reach_run henv (run_zLoop_exit s acc rest mem hcap henv.code henv.run), ?_⟩
    rw [lor_toNat_eq_zero, byteW_toNat]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, fun j hj => ?_⟩
      obtain rfl : j = 0 := by omega
      simpa using h2
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by simpa using h2 0 (by omega)⟩
  | succ i hi ih =>
    intro hi' acc
    have hrun := run_zLoop_back s (i + 1) acc rest mem hcap (by omega) hi' henv.code henv.run
    simp only [Nat.add_sub_cancel] at hrun
    obtain ⟨acc', r, h⟩ := ih (by omega) (UInt256.lor acc (byteW mem (1024 + i)))
    refine ⟨acc', (reach_run henv hrun).tr r, ?_⟩
    rw [h, lor_toNat_eq_zero, byteW_toNat]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨h1, fun j hj => ?_⟩
      by_cases hji : j < i
      · exact h3 j hji
      · obtain rfl : j = i := by omega
        exact h2
    · rintro ⟨h1, h3⟩
      exact ⟨⟨h1, h3 i (by omega)⟩, fun j hj => h3 j (by omega)⟩

/-! ## Nonzero modulus -/

theorem nonzero_path {s : State} (henv : Env s)
    (hcds : s.executionEnv.calldata.size < 2 ^ 64)
    (bl el ml : Nat) (stk : List UInt256) (mem : ByteArray)
    (hcap : stk.length < 900) (hbl : bl ≤ 1024) (hel : el ≤ 1024) (hml1 : 1 ≤ ml)
    (hml : ml ≤ 1024)
    (hmsv : MachineState.readWord mem 9216 = UInt256.ofNat ml)
    (hzero : ∀ a, 7168 ≤ a → a < 9216 → bget mem a = 0)
    (hM : 1 ≤ num mem 1024 ml) :
    ∃ memF, Reach (st s 338 (UInt256.ofNat bl :: UInt256.ofNat el :: UInt256.ofNat ml :: stk)
          mem AW)
        (rt s 482 (UInt256.ofNat (8 * el) :: UInt256.ofNat el :: UInt256.ofNat ml :: stk) memF
          AW (MachineState.readPadded memF 0 ml)) ∧
      num memF 0 ml = num mem 5120 bl ^ num mem 6144 el % num mem 1024 ml := by
  have r1 := reach_run henv (run_nz s bl el ml stk mem (by omega) hml henv.code henv.run)
  set memN := MachineState.writeBytes mem (ByteArray.mk #[UInt8.ofNat 1]) (7167 + ml) with hN
  have hfN : ∀ a, a ≠ 7167 + ml → bget memN a = bget mem a := by
    intro a ha
    rw [hN, bget_write1, if_neg ha]
  have hONE : num memN 7168 ml = 1 := by
    have hz : num memN 7168 (ml - 1) = 0 :=
      num_eq_zero (ml - 1) (fun j hj => by
        rw [hfN _ (by omega), hzero _ (by omega) (by omega)])
    have hb : bget memN (7168 + (ml - 1)) = 1 := by
      rw [hN, bget_write1, if_pos (by omega)]
    have h := num_succ memN 7168 (ml - 1)
    rw [Nat.sub_add_cancel hml1] at h
    rw [h, hz, hb]
  have hMN : num memN 1024 ml = num mem 1024 ml := num_congr ml (fun i _ => hfN _ (by omega))
  have hBN : num memN 5120 bl = num mem 5120 bl := num_congr bl (fun i _ => hfN _ (by omega))
  have hmsvN : MachineState.readWord memN 9216 = UInt256.ofNat ml := by
    rw [← hmsv]
    exact readWord_congr (fun i _ => hfN _ (by omega))
  -- base mod m
  obtain ⟨mem3, r2, hv3, hf3⟩ := mulm henv hcds ml 7168 5120 bl 361
    (UInt256.ofNat bl :: UInt256.ofNat el :: UInt256.ofNat ml :: stk) memN (by simp; omega)
    hml1 hml hbl (by norm_num) (Or.inr ⟨by norm_num, by norm_num⟩) (by norm_num)
    (Or.inr ⟨le_refl _, by norm_num⟩) (by norm_num) jump361 hmsvN (by rw [hMN]; exact hM)
    (by rw [hONE, hMN]; exact hM)
  rw [hONE, hMN, hBN, Nat.mul_one] at hv3
  have hmsv3 : MachineState.readWord mem3 9216 = UInt256.ofNat ml := by
    rw [msv_out hml hf3, hmsvN]
  have r3 := reach_run henv (run_x1 s bl el ml stk mem3 (by omega) hml hmsv3 henv.code
    henv.run)
  dsimp only at r3
  set m1 := MachineState.writeBytes mem3 (MachineState.readPadded mem3 0 ml) 2048 with hm1
  set memX := MachineState.writeBytes m1 (MachineState.readPadded m1 7168 ml) 3072 with hmX
  have hfX : ∀ a, ml ≤ a → (a < 2048 ∨ 5120 ≤ a) → a ≠ 7167 + ml → bget memX a = bget mem a := by
    intro a h1 h2 h3
    rw [hmX, bget_copy, if_neg (by omega), hm1, bget_copy, if_neg (by omega),
      hf3 a h1 (by omega), hfN a h3]
  have hXv : num memX 2048 ml = num mem 5120 bl % num mem 1024 ml := by
    have e1 : num memX 2048 ml = num m1 2048 ml :=
      num_congr ml (fun i _ => by rw [hmX, bget_copy, if_neg (by omega)])
    rw [e1, hm1, num_copy, hv3]
  have hR0 : num memX 3072 ml = 1 := by
    have e2 : num m1 7168 ml = num memN 7168 ml :=
      num_congr ml (fun i _ => by
        rw [hm1, bget_copy, if_neg (by omega), hf3 _ (by omega) (by omega)])
    rw [hmX, num_copy, e2, hONE]
  have hMX : num memX 1024 ml = num mem 1024 ml :=
    num_congr ml (fun i _ => hfX _ (by omega) (by omega) (by omega))
  have hEX : num memX 6144 el = num mem 6144 el :=
    num_congr el (fun i _ => hfX _ (by omega) (by omega) (by omega))
  have hmsvX : MachineState.readWord memX 9216 = UInt256.ofNat ml := by
    rw [← hmsv]
    exact readWord_congr (fun i _ => hfX _ (by omega) (by omega) (by omega))
  -- exponent loop
  have hElt : num memX 6144 el / 2 ^ (8 * el) = 0 := by
    apply Nat.div_eq_of_lt
    have := num_lt memX 6144 el
    rwa [show (256 : Nat) = 2 ^ 8 by norm_num, ← pow_mul] at this
  obtain ⟨memE, r4, hmsvE, hfE, hRE, hvE⟩ := expLoop henv hcds ml el stk memX (by omega) hml1
    hml hel (by rw [hMX]; exact hM) (8 * el) (le_refl _) memX hmsvX (fun a _ _ => rfl)
    (by rw [hR0, hMX]; exact hM) (by rw [hElt, pow_zero, hR0])
  rw [Nat.sub_self] at r4
  -- final reduction and return
  have r5 := reach_run henv (run_e9 s (8 * el) el ml stk memE (by omega) hml henv.code
    henv.run)
  set memA := MachineState.writeBytes memE (MachineState.readPadded memE 3072 ml) 0 with hmA
  have hfA : ∀ a, ml ≤ a → (a < 2048 ∨ 5120 ≤ a) → a ≠ 7167 + ml → bget memA a = bget mem a := by
    intro a h1 h2 h3
    rw [hmA, bget_copy, if_neg (by omega), hfE a h1 (by omega), hfX a h1 h2 h3]
  have hmsvA : MachineState.readWord memA 9216 = UInt256.ofNat ml := by
    rw [← hmsv]
    exact readWord_congr (fun i _ => hfA _ (by omega) (by omega) (by omega))
  have hA0 : num memA 0 ml = num memE 3072 ml := by rw [hmA, num_copy]
  have hZ : num memA 8192 ml = 0 :=
    num_eq_zero ml (fun i _ => by
      rw [hfA _ (by omega) (by omega) (by omega), hzero _ (by omega) (by omega)])
  have hMA : num memA 1024 ml = num mem 1024 ml :=
    num_congr ml (fun i _ => hfA _ (by omega) (by omega) (by omega))
  rw [hMX] at hRE hvE
  rw [hXv, hEX] at hvE
  obtain ⟨memF, r6, hvF, _⟩ := addm henv ml 8192 479
    (UInt256.ofNat (8 * el) :: UInt256.ofNat el :: UInt256.ofNat ml :: stk) memA
    (by simp; omega) hml1 hml (Or.inr (by omega)) (by norm_num) (by norm_num) jump479 hmsvA
    (by rw [hA0, hZ, hMA]; omega)
  have r7 := reach_run henv (run_e5 s (8 * el) el ml stk memF (by omega) hml henv.code
    henv.run)
  refine ⟨memF, r1.tr (r2.tr (r3.tr (r4.tr (r5.tr (r6.tr r7))))), ?_⟩
  rw [hvF, hA0, hZ, hMA, Nat.add_zero, hvE, ← Nat.pow_mod]

/-! ## End to end -/

theorem rt_isDone (s : State) (pc : Nat) (stk : List UInt256) (mem : ByteArray)
    (aw : UInt256) (out : ByteArray) (hcs : s.callStack = []) :
    (rt s pc stk mem aw out).isDone = true := by
  simp [State.isDone, State.isHalted, State.isRunning, rt, hcs]

theorem rt_result (s : State) (pc : Nat) (stk : List UInt256) (mem : ByteArray)
    (aw : UInt256) (out : ByteArray) :
    (rt s pc stk mem aw out).toResult = .returned out :=
  State.toResult_returned _ rfl

/-- **Fallback correctness.**  From the fallback entry, every valid input with a
nonempty modulus returns the MODEXP result. -/
theorem bigC_correct (s : State) (henv : Env s) (hpc : s.pc = UInt256.ofNat 258)
    (hstk : s.stack.length < 900) (haw : s.activeWords.toNat ≤ 289)
    (hcs : s.callStack = []) (hvalid : ValidInput s.executionEnv.calldata)
    (hpos : 0 < modulusSize s.executionEnv.calldata) :
    ∃ final : State, Nonempty (Challenge.EvmProof.GasSteps s final) ∧
      final.isDone = true ∧ final.toResult = .returned (spec s.executionEnv.calldata) := by
  obtain ⟨hsz, hbl, hel, hml⟩ := hvalid
  have hs : st s 258 s.stack s.memory s.activeWords = s := by
    unfold st
    rw [← hpc]
  have hb : MachineState.readWord s.executionEnv.calldata 0 =
      UInt256.ofNat (baseSize s.executionEnv.calldata) := rfl
  have he : MachineState.readWord s.executionEnv.calldata 32 =
      UInt256.ofNat (exponentSize s.executionEnv.calldata) := rfl
  have hm : MachineState.readWord s.executionEnv.calldata 64 =
      UInt256.ofNat (modulusSize s.executionEnv.calldata) := rfl
  have hspec0 := (rfl : spec s.executionEnv.calldata = spec s.executionEnv.calldata)
  generalize hB : baseSize s.executionEnv.calldata = bl at hbl hb
  generalize hE : exponentSize s.executionEnv.calldata = el at hel he
  generalize hMs : modulusSize s.executionEnv.calldata = ml at hml hm hpos
  have r0 := reach_run henv (run_setup s bl el ml s.stack s.memory s.activeWords (by omega)
    hbl hel hml haw hsz hb he hm henv.code henv.run)
  rw [hs] at r0
  have hmsvS := setup_msv s.memory s.executionEnv.calldata bl el ml hbl hel hml
  have hzS := setup_zero s.memory s.executionEnv.calldata bl el ml hbl hel hml
  have eB : Precompile.bytesToNatPadded s.executionEnv.calldata 96 bl =
      num (setupMem s.memory s.executionEnv.calldata bl el ml) 5120 bl :=
    (setup_B s.memory s.executionEnv.calldata bl el ml hbl hel hml).symm
  have eE : Precompile.bytesToNatPadded s.executionEnv.calldata (96 + bl) el =
      num (setupMem s.memory s.executionEnv.calldata bl el ml) 6144 el :=
    (setup_E s.memory s.executionEnv.calldata bl el ml hbl hel hml).symm
  have eM : Precompile.bytesToNatPadded s.executionEnv.calldata (96 + bl + el) ml =
      num (setupMem s.memory s.executionEnv.calldata bl el ml) 1024 ml := by
    rw [show 96 + bl + el = 96 + (el + bl) by omega]
    exact (setup_M s.memory s.executionEnv.calldata bl el ml hbl hel hml).symm
  have hspec : spec s.executionEnv.calldata =
      Precompile.natToBytes (Precompile.modPow
        (num (setupMem s.memory s.executionEnv.calldata bl el ml) 5120 bl)
        (num (setupMem s.memory s.executionEnv.calldata bl el ml) 6144 el)
        (num (setupMem s.memory s.executionEnv.calldata bl el ml) 1024 ml)) ml := by
    simp only [spec, hB, hE, hMs]
    rw [if_neg (by omega), eB, eE, eM]
  clear hspec0
  set memS := setupMem s.memory s.executionEnv.calldata bl el ml with hmS
  obtain ⟨acc', rz, hacc⟩ := zLoop henv
    (UInt256.ofNat bl :: UInt256.ofNat el :: UInt256.ofNat ml :: s.stack) memS
    (by simp; omega) ml hpos hml (UInt256.ofNat 0)
  have hMz := num_eq_zero_iff memS 1024 ml
  by_cases hM0 : num memS 1024 ml = 0
  · -- zero modulus: return the zero window
    have hacc0 : acc'.toNat = 0 := hacc.mpr ⟨by simp, hMz.mp hM0⟩
    have r1 := reach_run henv (run_zExit_zero s acc'
      (UInt256.ofNat bl :: UInt256.ofNat el :: UInt256.ofNat ml :: s.stack) memS
      (by simp; omega) hacc0 henv.code henv.run)
    have r2 := reach_run henv (run_zeroRet s bl el ml s.stack memS (by omega) hml henv.code
      henv.run)
    refine ⟨_, r0.tr (rz.tr (r1.tr r2)), rt_isDone _ _ _ _ _ _ hcs, ?_⟩
    have hZ : num memS 8192 ml = 0 :=
      num_eq_zero ml (fun i _ => hzS _ (by omega) (by omega))
    rw [rt_result, hspec, readPadded_eq_natToBytes, hZ, hM0,
      Challenge.Modexp.Submission.Proofs.Algorithm.modPow_eq, if_pos rfl]
  · -- nonzero modulus
    have hne : acc'.toNat ≠ 0 := fun h => hM0 (hMz.mpr (hacc.mp h).2)
    have r1 := reach_run henv (run_zExit_nz s acc'
      (UInt256.ofNat bl :: UInt256.ofNat el :: UInt256.ofNat ml :: s.stack) memS
      (by simp; omega) hne henv.code henv.run)
    obtain ⟨memF, r2, hvF⟩ := nonzero_path henv hsz bl el ml s.stack memS hstk hbl hel
      (by omega) hml hmsvS hzS (by omega)
    refine ⟨_, r0.tr (rz.tr (r1.tr r2)), rt_isDone _ _ _ _ _ _ hcs, ?_⟩
    rw [rt_result, hspec, readPadded_eq_natToBytes, hvF,
      Challenge.Modexp.Submission.Proofs.Algorithm.modPow_eq, if_neg hM0]

end Challenge.Modexp.Submission.Proofs.Bytecode.BigC
