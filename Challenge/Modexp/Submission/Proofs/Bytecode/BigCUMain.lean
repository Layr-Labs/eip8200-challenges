import Challenge.Modexp.Submission.Proofs.Bytecode.BigCUExp
import Challenge.Modexp.Submission.Proofs.Bytecode.BigCUSetup

set_option warningAsError true
set_option maxHeartbeats 4000000
set_option maxRecDepth 40000
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.Proofs.Bytecode.BigC.U
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs.Bytecode WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Bytecode.BigC

theorem nonzero_path {artifact : ProgramArtifact} (sb : SetupBlocks artifact)
    (eb : ExpBlocks artifact) (mb : MulBlocks artifact) (ab : Unsigned.Blocks artifact)
    {s : State} (env : Environment artifact .Osaka s)
    (hcds : s.executionEnv.calldata.size < 2 ^ 64)
    (bl el ml : Nat) (stk : List UInt256) (mem : ByteArray)
    (hcap : stk.length < 900) (hbl : bl ≤ 1024) (hel : el ≤ 1024) (hml1 : 1 ≤ ml)
    (hml : ml ≤ 1024)
    (hm : MachineState.readWord s.executionEnv.calldata 64 = UInt256.ofNat ml)
    (hb : MachineState.readWord s.executionEnv.calldata 0 = UInt256.ofNat bl)
    (hOneZero : ∀ a, 3072 ≤ a → a < 4096 → bget mem a = 0)
    (hzero : num mem 8192 ml = 0) (hM : 1 ≤ num mem 1024 ml) :
    ∃ memF, Reach (st s 301 (UInt256.ofNat bl :: UInt256.ofNat el :: UInt256.ofNat ml :: stk)
          mem AW)
        (rt s 300 (UInt256.ofNat (8 * el) :: UInt256.ofNat el :: UInt256.ofNat ml :: stk) memF
          AW (MachineState.readPadded memF 0 ml)) ∧
      num memF 0 ml = num mem 5120 bl ^ num s.executionEnv.calldata (96 + bl) el % num mem 1024 ml := by
  have hSJ : SetupJumps s.executionEnv.code := by rw [env.code]; exact sb.jumps
  have hEJ : ExpJumps s.executionEnv.code := by rw [env.code]; exact eb.jumps
  have r1 := Unsigned.lift_run env sb.nz (run_nz s bl el ml stk mem (by omega) hml hSJ)
  set memN := MachineState.writeBytes mem (ByteArray.mk #[UInt8.ofNat 1]) (3071 + ml) with hN
  have hfN : ∀ a, a ≠ 3071 + ml → bget memN a = bget mem a := by
    intro a ha
    rw [hN, bget_write1, if_neg ha]
  have hONE : num memN 3072 ml = 1 := by
    have hz : num memN 3072 (ml - 1) = 0 :=
      num_eq_zero (ml - 1) (fun j hj => by
        rw [hfN _ (by omega), hOneZero _ (by omega) (by omega)])
    have hb1 : bget memN (3072 + (ml - 1)) = 1 := by
      rw [hN, bget_write1, if_pos (by omega)]
    have h := num_succ memN 3072 (ml - 1)
    rw [Nat.sub_add_cancel hml1] at h
    rw [h, hz, hb1]
  have hMN : num memN 1024 ml = num mem 1024 ml := num_congr ml (fun i _ => hfN _ (by omega))
  have hBN : num memN 5120 bl = num mem 5120 bl := num_congr bl (fun i _ => hfN _ (by omega))
  have hZN : num memN 8192 ml = 0 :=
    (num_congr ml (fun i _ => hfN _ (by omega))).trans hzero
  have hElt : num s.executionEnv.calldata (96 + bl) el / 2 ^ (8 * el) = 0 := by
    apply Nat.div_eq_of_lt
    have := num_lt s.executionEnv.calldata (96 + bl) el
    rwa [show (256 : Nat) = 2 ^ 8 by norm_num, ← pow_mul] at this
  obtain ⟨memE, r2, hfE, hRE, hvE⟩ := expLoop eb mb ab env hcds ml bl el stk memN
    (by omega) hml1 hml hbl hel (by rw [hMN]; exact hM) hm hb hZN
    (8 * el) (le_refl _) memN (fun _ _ _ => rfl)
    (by rw [hONE, hMN]; exact hM) (by rw [hElt, pow_zero, hONE])
  rw [Nat.sub_self] at r2
  have r3 := Unsigned.lift_run env eb.e9 (run_e9 s (8 * el) el ml stk memE (by omega) hml hEJ)
  set memA := MachineState.writeBytes memE (MachineState.readPadded memE 3072 ml) 0 with hA
  have hfA : ∀ a, ml ≤ a → (a < 3072 ∨ 5120 ≤ a) → bget memA a = bget memN a := by
    intro a h1 h2
    rw [hA, bget_copy, if_neg (by omega), hfE a h1 h2]
  have hA0 : num memA 0 ml = num memE 3072 ml := by rw [hA, num_copy]
  have hZA : num memA 8192 ml = 0 :=
    (num_congr ml (fun i _ => hfA _ (by omega) (by omega))).trans hZN
  have hMA : num memA 1024 ml = num mem 1024 ml :=
    (num_congr ml (fun i _ => hfA _ (by omega) (by omega))).trans hMN
  rw [hMN] at hRE hvE
  rw [hBN] at hvE
  obtain ⟨memF, r4, hvF, _⟩ := Unsigned.addm ab s env ml 8192 297
    (UInt256.ofNat (8 * el) :: UInt256.ofNat el :: UInt256.ofNat ml :: stk) memA
    (by simp; omega) hml1 hml (Or.inr (by omega)) (by decide) (by decide) hSJ.j295 hm hZA
    (by rw [hA0, hZA, hMA]; omega)
  have r5 := Unsigned.lift_run env sb.zeroRet (run_zeroRet s (8 * el) el ml stk memF
    (by omega) hml hSJ)
  refine ⟨memF, r1.tr (r2.tr (r3.tr (r4.tr r5))), ?_⟩
  rw [hvF, hA0, hZA, hMA, Nat.add_zero, hvE]

theorem rt_isDone (s : State) (pc : Nat) (stk : List UInt256) (mem : ByteArray)
    (aw : UInt256) (out : ByteArray) (hcs : s.callStack = []) :
    (rt s pc stk mem aw out).isDone = true := by
  simp [State.isDone, State.isHalted, State.isRunning, rt, hcs]

theorem rt_result (s : State) (pc : Nat) (stk : List UInt256) (mem : ByteArray)
    (aw : UInt256) (out : ByteArray) :
    (rt s pc stk mem aw out).toResult = .returned out := State.toResult_returned _ rfl

/-- Complete cold fallback for the frozen U instruction programs. All execution
is metered, and the only integration parameters are certified artifact blocks. -/
theorem bigC_correct {artifact : ProgramArtifact} (sb : SetupBlocks artifact)
    (eb : ExpBlocks artifact) (mb : MulBlocks artifact) (ab : Unsigned.Blocks artifact)
    (s : State) (env : Environment artifact .Osaka s) (hpc : s.pc = UInt256.ofNat 238)
    (hstk : s.stack.length < 900) (haw : s.activeWords.toNat ≤ 289)
    (hcs : s.callStack = []) (hvalid : ValidInput s.executionEnv.calldata)
    (hpos : 0 < modulusSize s.executionEnv.calldata) :
    ∃ final : State, Nonempty (GasSteps s final) ∧
      final.isDone = true ∧ final.toResult = .returned (spec s.executionEnv.calldata) := by
  obtain ⟨hsz, hbl, hel, hml⟩ := hvalid
  have hs : st s 238 s.stack s.memory s.activeWords = s := by
    unfold st
    rw [← hpc]
  have hb : MachineState.readWord s.executionEnv.calldata 0 =
      UInt256.ofNat (baseSize s.executionEnv.calldata) := rfl
  have he : MachineState.readWord s.executionEnv.calldata 32 =
      UInt256.ofNat (exponentSize s.executionEnv.calldata) := rfl
  have hm : MachineState.readWord s.executionEnv.calldata 64 =
      UInt256.ofNat (modulusSize s.executionEnv.calldata) := rfl
  generalize hB : baseSize s.executionEnv.calldata = bl at hbl hb
  generalize hE : exponentSize s.executionEnv.calldata = el at hel he
  generalize hMs : modulusSize s.executionEnv.calldata = ml at hml hm hpos
  have r0 := lift_any env sb.setup (run_setup s bl el ml s.stack s.memory s.activeWords
    (by omega) hbl hel hml haw hsz hb he hm)
  rw [hs] at r0
  have hzS := setup_zero s.memory s.executionEnv.calldata bl el ml
  have eB : Precompile.bytesToNatPadded s.executionEnv.calldata 96 bl =
      num (setupMem s.memory s.executionEnv.calldata bl el ml) 5120 bl :=
    (setup_B s.memory s.executionEnv.calldata bl el ml).symm
  have eM : Precompile.bytesToNatPadded s.executionEnv.calldata (96 + bl + el) ml =
      num (setupMem s.memory s.executionEnv.calldata bl el ml) 1024 ml := by
    rw [show 96 + bl + el = 96 + (el + bl) by omega]
    exact (setup_M s.memory s.executionEnv.calldata bl el ml hml).symm
  have hspec : spec s.executionEnv.calldata =
      Precompile.natToBytes (Precompile.modPow
        (num (setupMem s.memory s.executionEnv.calldata bl el ml) 5120 bl)
        (num s.executionEnv.calldata (96 + bl) el)
        (num (setupMem s.memory s.executionEnv.calldata bl el ml) 1024 ml)) ml := by
    simp only [spec, hB, hE, hMs]
    rw [if_neg (by omega), eB, eM]
  set memS := setupMem s.memory s.executionEnv.calldata bl el ml with hS
  have hSJ : SetupJumps s.executionEnv.code := by rw [env.code]; exact sb.jumps
  obtain ⟨acc', rz, hacc⟩ := zLoop sb env
    (UInt256.ofNat bl :: UInt256.ofNat el :: UInt256.ofNat ml :: s.stack) memS
    (by simp; omega) ml hpos hml (UInt256.ofNat 0)
  have hMz := word_scan_zero_iff memS ml (fun a ha ha' => hzS a (by omega) (by omega) (by omega))
  by_cases hM0 : num memS 1024 ml = 0
  · have hacc0 : acc'.toNat = 0 := hacc.mpr ⟨by simp, hMz.mpr hM0⟩
    have r1 := Unsigned.lift_run env sb.zExit (run_zExit_zero s acc'
      (UInt256.ofNat bl :: UInt256.ofNat el :: UInt256.ofNat ml :: s.stack) memS
      (by simp; omega) hacc0 hSJ)
    have r2 := Unsigned.lift_run env sb.zeroRet (run_zeroRet s bl el ml s.stack memS
      (by omega) hml hSJ)
    refine ⟨_, r0.tr (rz.tr (r1.tr r2)), rt_isDone _ _ _ _ _ _ hcs, ?_⟩
    have hZ : num memS 0 ml = 0 := num_eq_zero ml (fun i hi => hzS _ (by omega) (by omega) (by omega))
    rw [rt_result, hspec, readPadded_eq_natToBytes, hZ, hM0,
      Challenge.Modexp.Submission.Proofs.Algorithm.modPow_eq, if_pos rfl]
  · have hne : acc'.toNat ≠ 0 := fun h => hM0 (hMz.mp (hacc.mp h).2)
    have r1 := Unsigned.lift_run env sb.zExit (run_zExit_nz s acc'
      (UInt256.ofNat bl :: UInt256.ofNat el :: UInt256.ofNat ml :: s.stack) memS
      (by simp; omega) hne hSJ)
    have hO : ∀ a, 3072 ≤ a → a < 4096 → bget memS a = 0 :=
      fun a ha ha' => hzS a (by omega) (by omega) (by omega)
    have hZ : num memS 8192 ml = 0 :=
      num_eq_zero ml (fun i hi => hzS _ (by omega) (by omega) (by omega))
    obtain ⟨memF, r2, hvF⟩ := nonzero_path sb eb mb ab env hsz bl el ml s.stack memS
      hstk hbl hel hpos hml hm hb hO hZ (by omega)
    refine ⟨_, r0.tr (rz.tr (r1.tr r2)), rt_isDone _ _ _ _ _ _ hcs, ?_⟩
    rw [rt_result, hspec, readPadded_eq_natToBytes, hvF,
      Challenge.Modexp.Submission.Proofs.Algorithm.modPow_eq, if_neg hM0]

#print axioms bigC_correct
end Challenge.Modexp.Submission.Proofs.Bytecode.BigC.U
