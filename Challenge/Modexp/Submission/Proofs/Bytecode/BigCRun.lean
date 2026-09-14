import Challenge.Modexp.Submission.Proofs.Bytecode.BigCDefs
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
/-!
# Compact multi-limb fallback: block runs

Each lemma executes one located block of the fallback symbolically.  States are
written with `st`, which only replaces pc, stack, memory and active words of
the fallback entry state.  Results are kept literal (EVM words and memory
writes exactly as the instructions produce them); the arithmetic meaning is
established separately.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.BigC

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- A fallback state: everything but pc, stack, memory and active words is
inherited from the entry state `s`. -/
def st (s : State) (pc : Nat) (stack : List UInt256) (mem : ByteArray)
    (aw : UInt256) : State :=
  { s with pc := UInt256.ofNat pc, stack := stack, memory := mem, activeWords := aw }

/-- A halted fallback state after `RETURN`. -/
def rt (s : State) (pc : Nat) (stack : List UInt256) (mem : ByteArray)
    (aw : UInt256) (out : ByteArray) : State :=
  { s with pc := UInt256.ofNat pc, stack := stack, memory := mem, activeWords := aw,
           halt := .Returned, hReturn := out }

/-- Active words once the fallback has zero-filled its 9248-byte arena. -/
abbrev AW : UInt256 := UInt256.ofNat 289

/-- `2 ^ 256` as the literal that `simp` normalizes to. -/
abbrev LIM : Nat :=
  115792089237316195423570985008687907853269984665640564039457584007913129639936

/-- The bit selected by `MLOAD a; SHL j; PUSH1 255; SHR`. -/
def bitWord (mem : ByteArray) (a j : Nat) : UInt256 :=
  UInt256.shiftRight
    (UInt256.shiftLeft (MachineState.readWord mem a) (UInt256.ofNat j))
    (UInt256.ofNat 255)

/-- Byte `k` of memory as a word (`MLOAD k; PUSH0; BYTE`). -/
def byteW (mem : ByteArray) (k : Nat) : UInt256 :=
  UInt256.byteAt (UInt256.ofNat 0) (MachineState.readWord mem k)

theorem aw_keep (off sz : Nat) (h : off + sz ≤ 9248) :
    MachineState.activeWordsAfter 289 off sz = 289 := by
  unfold MachineState.activeWordsAfter
  split
  · rfl
  · dsimp only
    rw [show Nat.max 289 ((off + sz - 1) / 32 + 1) =
      max 289 ((off + sz - 1) / 32 + 1) from rfl]
    omega

theorem dec_ofNat (i : Nat) (hi : 1 ≤ i) (hi' : i < 2 ^ 256) :
    UInt256.lnot (UInt256.ofNat 0) + UInt256.ofNat i = UInt256.ofNat (i - 1) := by
  apply Challenge.EvmProof.Word.word_ext
  rw [Challenge.EvmProof.Word.word_toNat_add]
  simp only [UInt256.lnot, Challenge.EvmProof.Word.word_toNat_ofNat, UInt256.size]
  have h1 : (2 ^ 256 - 1 - 0 % 2 ^ 256) % 2 ^ 256 = 2 ^ 256 - 1 := by norm_num
  rw [h1, Nat.mod_eq_of_lt hi', Nat.mod_eq_of_lt (by omega : i - 1 < 2 ^ 256)]
  omega

theorem shl3_ofNat (n : Nat) (h : n < 2 ^ 240) :
    UInt256.shiftLeft (UInt256.ofNat n) (UInt256.ofNat 3) = UInt256.ofNat (n * 8) := by
  have := Challenge.EvmProof.Word.shiftLeft_ofNat (value := n) (shift := 3)
    (by omega) (by omega) (by omega)
  simpa using this

theorem shr3_ofNat (n : Nat) (h : n < 2 ^ 256) :
    UInt256.shiftRight (UInt256.ofNat n) (UInt256.ofNat 3) = UInt256.ofNat (n / 8) := by
  have := Challenge.EvmProof.Word.shiftRight_ofNat (value := n) (shift := 3) h (by omega)
  rw [this, Nat.shiftRight_eq_div_pow]

theorem and7_ofNat (n : Nat) (h : n < 2 ^ 256) :
    UInt256.land (UInt256.ofNat 7) (UInt256.ofNat n) = UInt256.ofNat (n % 8) := by
  apply Challenge.EvmProof.Word.word_ext
  rw [Challenge.EvmProof.Word.word_toNat_land]
  simp only [Challenge.EvmProof.Word.word_toNat_ofNat]
  rw [Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt (by norm_num : 7 < 2 ^ 256),
    Nat.mod_eq_of_lt (by omega : n % 8 < 2 ^ 256)]
  rw [show (7 : Nat) = 2 ^ 3 - 1 by norm_num, Nat.and_comm,
    Nat.and_two_pow_sub_one_eq_mod]

theorem eq_ofNat_toNat (a b : Nat) (ha : a < 2 ^ 256) (hb : b < 2 ^ 256) :
    (UInt256.eq (UInt256.ofNat a) (UInt256.ofNat b)).toNat = if a = b then 1 else 0 := by
  unfold UInt256.eq
  simp only [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt ha,
    Nat.mod_eq_of_lt hb]
  split <;> simp

/-! ## Common simp set -/

syntax "bigc_run" "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| bigc_run [$ts,*]) =>
    `(tactic| simp (config := { maxSteps := 2000000 })
        [opAt, pushAt, wfOp,
          Challenge.EvmProof.Stepper.runLocatedBlock,
          Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
          st, rt, AW, LIM, bitWord, byteW, bigCPCs, UInt256.isTrue, List.exchange,
          State.activeWordsAfterUInt256, State.activeWordsAfterUInt256_2,
          Challenge.EvmProof.Word.literal_eq_ofNat,
          Challenge.EvmProof.Word.succ_ofNat_mod,
          Challenge.EvmProof.Word.ofNat_add_mod,
          Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt, $ts,*])

theorem caps (n : Nat) (h : n < 1000) :
    n + 1 < 1024 ∧
    n + 1 + 1 < 1024 ∧
    n + 1 + 1 + 1 < 1024 ∧
    n + 1 + 1 + 1 + 1 < 1024 ∧
    n + 1 + 1 + 1 + 1 + 1 < 1024 ∧
    n + 1 + 1 + 1 + 1 + 1 + 1 < 1024 ∧
    n + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 ∧
    n + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 ∧
    n + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 ∧
    n + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 ∧
    n + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 ∧
    n + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩

theorem zero_lit : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide

/-! ## Modulus scan (`Z1`) -/

theorem run_zLoop_back (s : State) (i : Nat) (acc : UInt256)
    (rest : List UInt256) (mem : ByteArray)
    (hcap : rest.length < 1000) (hi : 2 ≤ i) (hi' : i ≤ 1024)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock zLoopPath
      (st s 300 (UInt256.ofNat i :: acc :: rest) mem AW) =
        some (st s 300 (UInt256.ofNat (i - 1) ::
          UInt256.lor acc (byteW mem (1024 + (i - 1))) :: rest) mem AW) := by
  have hc := caps _ hcap
  have hdec := dec_ofNat i (by omega) (by omega)
  have hadd : UInt256.ofNat 1024 + UInt256.ofNat (i - 1) =
      UInt256.ofNat (1024 + (i - 1)) :=
    Challenge.EvmProof.Word.ofNat_add_ofNat (by omega)
  have h1 : 1024 + (i - 1) < LIM := by simp only [LIM]; omega
  have h2 : i - 1 < LIM := by simp only [LIM]; omega
  have hne : ¬ i - 1 = 0 := by omega
  have haw : MachineState.activeWordsAfter 289 (1024 + (i - 1)) 32 = 289 :=
    aw_keep _ _ (by omega)
  bigc_run [zLoopPath, hc, hcode, hrun, zero_lit, hdec, hadd, h1, h2, hne, haw]

theorem run_zLoop_exit (s : State) (acc : UInt256)
    (rest : List UInt256) (mem : ByteArray)
    (hcap : rest.length < 1000)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock zLoopPath
      (st s 300 (UInt256.ofNat 1 :: acc :: rest) mem AW) =
        some (st s 321 (UInt256.ofNat 0 ::
          UInt256.lor acc (byteW mem 1024) :: rest) mem AW) := by
  have hc := caps _ hcap
  have hdec := dec_ofNat 1 (by omega) (by norm_num)
  have hadd : UInt256.ofNat 1024 + UInt256.ofNat 0 = UInt256.ofNat 1024 := by decide
  have haw : MachineState.activeWordsAfter 289 1024 32 = 289 := aw_keep _ _ (by omega)
  bigc_run [zLoopPath, hc, hcode, hrun, zero_lit, hdec, hadd, haw]

theorem run_zExit_nz (s : State) (acc : UInt256) (rest : List UInt256)
    (mem : ByteArray) (hcap : rest.length < 1000) (hacc : acc.toNat ≠ 0)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock zExitPath
      (st s 321 (UInt256.ofNat 0 :: acc :: rest) mem AW) =
        some (st s 331 rest mem AW) := by
  have hc := caps _ hcap
  bigc_run [zExitPath, hc, hcode, hrun, hacc]

theorem run_zExit_zero (s : State) (acc : UInt256) (rest : List UInt256)
    (mem : ByteArray) (hcap : rest.length < 1000) (hacc : acc.toNat = 0)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock zExitPath
      (st s 321 (UInt256.ofNat 0 :: acc :: rest) mem AW) =
        some (st s 326 rest mem AW) := by
  have hc := caps _ hcap
  bigc_run [zExitPath, hc, hcode, hrun, hacc]

theorem run_zeroRet (s : State) (bl el ml : Nat) (rest : List UInt256)
    (mem : ByteArray) (hcap : rest.length < 1000) (hml : ml ≤ 1024)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock zeroRetPath
      (st s 326 (UInt256.ofNat bl :: UInt256.ofNat el :: UInt256.ofNat ml :: rest) mem AW) =
        some (rt s 330 (UInt256.ofNat bl :: UInt256.ofNat el :: UInt256.ofNat ml :: rest)
          mem AW (MachineState.readPadded mem 8192 ml)) := by
  have hc := caps _ hcap
  have h1 : ml < LIM := by simp only [LIM]; omega
  have haw : MachineState.activeWordsAfter 289 8192 ml = 289 := aw_keep _ _ (by omega)
  bigc_run [zeroRetPath, hc, hcode, hrun, h1, haw]

/-! ## Base reduction call and exponent loop -/

theorem run_nz (s : State) (bl el ml : Nat) (rest : List UInt256)
    (mem : ByteArray) (hcap : rest.length < 1000) (hml : ml ≤ 1024)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock nzPath
      (st s 331 (UInt256.ofNat bl :: UInt256.ofNat el :: UInt256.ofNat ml :: rest) mem AW) =
        some (st s 476 (UInt256.ofNat 354 :: UInt256.ofNat 7168 :: UInt256.ofNat 5120 ::
          UInt256.ofNat bl :: UInt256.ofNat bl :: UInt256.ofNat el :: UInt256.ofNat ml :: rest)
          (MachineState.writeBytes mem (ByteArray.mk #[UInt8.ofNat 1]) (7167 + ml)) AW) := by
  have hc := caps _ hcap
  have hadd : UInt256.ofNat 7167 + UInt256.ofNat ml = UInt256.ofNat (7167 + ml) :=
    Challenge.EvmProof.Word.ofNat_add_ofNat (by omega)
  have h1 : 7167 + ml < LIM := by simp only [LIM]; omega
  have haw : MachineState.activeWordsAfter 289 (7167 + ml) 1 = 289 := aw_keep _ _ (by omega)
  bigc_run [nzPath, hc, hcode, hrun, hadd, h1, haw]

theorem run_x1 (s : State) (bl el ml : Nat) (rest : List UInt256)
    (mem : ByteArray) (hcap : rest.length < 1000) (hml : ml ≤ 1024)
    (hmsv : MachineState.readWord mem 9216 = UInt256.ofNat ml)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock x1Path
      (st s 354 (UInt256.ofNat bl :: UInt256.ofNat el :: UInt256.ofNat ml :: rest) mem AW) =
        some (st s 374 (UInt256.ofNat 0 :: UInt256.ofNat el :: UInt256.ofNat ml :: rest)
          (let m1 := MachineState.writeBytes mem (MachineState.readPadded mem 0 ml) 2048
           MachineState.writeBytes m1 (MachineState.readPadded m1 7168 ml) 3072) AW) := by
  have hc := caps _ hcap
  have h1 : ml < LIM := by simp only [LIM]; omega
  have haw0 : MachineState.activeWordsAfter 289 9216 32 = 289 := aw_keep _ _ (by omega)
  have haw1 : MachineState.activeWordsAfter 289 2048 ml = 289 := aw_keep _ _ (by omega)
  have haw2 : MachineState.activeWordsAfter 289 0 ml = 289 := aw_keep _ _ (by omega)
  have haw3 : MachineState.activeWordsAfter 289 3072 ml = 289 := aw_keep _ _ (by omega)
  have haw4 : MachineState.activeWordsAfter 289 7168 ml = 289 := aw_keep _ _ (by omega)
  bigc_run [x1Path, hc, hcode, hrun, zero_lit, hmsv, h1, haw0, haw1, haw2, haw3, haw4]

theorem run_eGuard_done (s : State) (i el ml : Nat) (rest : List UInt256)
    (mem : ByteArray) (hcap : rest.length < 1000) (hel : el ≤ 1024)
    (hi : i = el * 8)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock eGuardPath
      (st s 374 (UInt256.ofNat i :: UInt256.ofNat el :: UInt256.ofNat ml :: rest) mem AW) =
        some (st s 455 (UInt256.ofNat i :: UInt256.ofNat el :: UInt256.ofNat ml :: rest)
          mem AW) := by
  have hc := caps _ hcap
  have hshl := shl3_ofNat el (by omega)
  have heq := eq_ofNat_toNat i (el * 8) (by omega) (by omega)
  have hcond : (UInt256.eq (UInt256.ofNat i) (UInt256.ofNat (el * 8))).toNat ≠ 0 := by
    rw [heq, if_pos hi]; norm_num
  bigc_run [eGuardPath, hc, hcode, hrun, hshl, hcond]

theorem run_eGuard_go (s : State) (i el ml : Nat) (rest : List UInt256)
    (mem : ByteArray) (hcap : rest.length < 1000) (hel : el ≤ 1024)
    (hi : i ≠ el * 8) (hi' : i < 2 ^ 256)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock eGuardPath
      (st s 374 (UInt256.ofNat i :: UInt256.ofNat el :: UInt256.ofNat ml :: rest) mem AW) =
        some (st s 385 (UInt256.ofNat i :: UInt256.ofNat el :: UInt256.ofNat ml :: rest)
          mem AW) := by
  have hc := caps _ hcap
  have hshl := shl3_ofNat el (by omega)
  have heq := eq_ofNat_toNat i (el * 8) hi' (by omega)
  have hcond : (UInt256.eq (UInt256.ofNat i) (UInt256.ofNat (el * 8))).toNat = 0 := by
    rw [heq, if_neg hi]
  bigc_run [eGuardPath, hc, hcode, hrun, hshl, hcond]

theorem run_eSquare (s : State) (i el ml : Nat) (rest : List UInt256)
    (mem : ByteArray) (hcap : rest.length < 1000)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock eSquarePath
      (st s 385 (UInt256.ofNat i :: UInt256.ofNat el :: UInt256.ofNat ml :: rest) mem AW) =
        some (st s 476 (UInt256.ofNat 397 :: UInt256.ofNat 3072 :: UInt256.ofNat 3072 ::
          UInt256.ofNat ml :: UInt256.ofNat i :: UInt256.ofNat el :: UInt256.ofNat ml :: rest)
          mem AW) := by
  have hc := caps _ hcap
  bigc_run [eSquarePath, hc, hcode, hrun]

theorem run_e2_skip (s : State) (i el ml : Nat) (rest : List UInt256)
    (mem : ByteArray) (hcap : rest.length < 1000) (hml : ml ≤ 1024)
    (hi : i < 8192)
    (hbit : (bitWord (MachineState.writeBytes mem (MachineState.readPadded mem 0 ml) 3072)
      (6144 + i / 8) (i % 8)).toNat = 0)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock e2Path
      (st s 397 (UInt256.ofNat i :: UInt256.ofNat el :: UInt256.ofNat ml :: rest) mem AW) =
        some (st s 447 (UInt256.ofNat i :: UInt256.ofNat el :: UInt256.ofNat ml :: rest)
          (MachineState.writeBytes mem (MachineState.readPadded mem 0 ml) 3072) AW) := by
  have hc := caps _ hcap
  have hshr := shr3_ofNat i (by omega)
  have hand := and7_ofNat i (by omega)
  have hadd : UInt256.ofNat 6144 + UInt256.ofNat (i / 8) = UInt256.ofNat (6144 + i / 8) :=
    Challenge.EvmProof.Word.ofNat_add_ofNat (by omega)
  have h1 : 6144 + i / 8 < LIM := by simp only [LIM]; omega
  have h2 : ml < LIM := by simp only [LIM]; omega
  have h3 : i % 8 < LIM := by simp only [LIM]; omega
  have haw1 : MachineState.activeWordsAfter 289 3072 ml = 289 := aw_keep _ _ (by omega)
  have haw2 : MachineState.activeWordsAfter 289 0 ml = 289 := aw_keep _ _ (by omega)
  have haw3 : MachineState.activeWordsAfter 289 (6144 + i / 8) 32 = 289 :=
    aw_keep _ _ (by omega)
  have hz := hbit
  simp only [bitWord] at hz
  bigc_run [e2Path, hc, hcode, hrun, zero_lit, hshr, hand, hadd, h1, h2, h3,
    haw1, haw2, haw3, hz]

theorem run_e2_mul (s : State) (i el ml : Nat) (rest : List UInt256)
    (mem : ByteArray) (hcap : rest.length < 1000) (hml : ml ≤ 1024)
    (hi : i < 8192)
    (hbit : (bitWord (MachineState.writeBytes mem (MachineState.readPadded mem 0 ml) 3072)
      (6144 + i / 8) (i % 8)).toNat ≠ 0)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock e2Path
      (st s 397 (UInt256.ofNat i :: UInt256.ofNat el :: UInt256.ofNat ml :: rest) mem AW) =
        some (st s 426 (UInt256.ofNat i :: UInt256.ofNat el :: UInt256.ofNat ml :: rest)
          (MachineState.writeBytes mem (MachineState.readPadded mem 0 ml) 3072) AW) := by
  have hc := caps _ hcap
  have hshr := shr3_ofNat i (by omega)
  have hand := and7_ofNat i (by omega)
  have hadd : UInt256.ofNat 6144 + UInt256.ofNat (i / 8) = UInt256.ofNat (6144 + i / 8) :=
    Challenge.EvmProof.Word.ofNat_add_ofNat (by omega)
  have h1 : 6144 + i / 8 < LIM := by simp only [LIM]; omega
  have h2 : ml < LIM := by simp only [LIM]; omega
  have h3 : i % 8 < LIM := by simp only [LIM]; omega
  have haw1 : MachineState.activeWordsAfter 289 3072 ml = 289 := aw_keep _ _ (by omega)
  have haw2 : MachineState.activeWordsAfter 289 0 ml = 289 := aw_keep _ _ (by omega)
  have haw3 : MachineState.activeWordsAfter 289 (6144 + i / 8) 32 = 289 :=
    aw_keep _ _ (by omega)
  have hz := hbit
  simp only [bitWord] at hz
  bigc_run [e2Path, hc, hcode, hrun, zero_lit, hshr, hand, hadd, h1, h2, h3,
    haw1, haw2, haw3, hz]

theorem run_eMul (s : State) (i el ml : Nat) (rest : List UInt256)
    (mem : ByteArray) (hcap : rest.length < 1000)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock eMulPath
      (st s 426 (UInt256.ofNat i :: UInt256.ofNat el :: UInt256.ofNat ml :: rest) mem AW) =
        some (st s 476 (UInt256.ofNat 440 :: UInt256.ofNat 3072 :: UInt256.ofNat 2048 ::
          UInt256.ofNat ml :: UInt256.ofNat i :: UInt256.ofNat el :: UInt256.ofNat ml :: rest)
          mem AW) := by
  have hc := caps _ hcap
  bigc_run [eMulPath, hc, hcode, hrun]

theorem run_e4 (s : State) (i el ml : Nat) (rest : List UInt256)
    (mem : ByteArray) (hcap : rest.length < 1000) (hml : ml ≤ 1024)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock e4Path
      (st s 440 (UInt256.ofNat i :: UInt256.ofNat el :: UInt256.ofNat ml :: rest) mem AW) =
        some (st s 447 (UInt256.ofNat i :: UInt256.ofNat el :: UInt256.ofNat ml :: rest)
          (MachineState.writeBytes mem (MachineState.readPadded mem 0 ml) 3072) AW) := by
  have hc := caps _ hcap
  have h2 : ml < LIM := by simp only [LIM]; omega
  have haw1 : MachineState.activeWordsAfter 289 3072 ml = 289 := aw_keep _ _ (by omega)
  have haw2 : MachineState.activeWordsAfter 289 0 ml = 289 := aw_keep _ _ (by omega)
  bigc_run [e4Path, hc, hcode, hrun, zero_lit, h2, haw1, haw2]

theorem run_e3 (s : State) (i el ml : Nat) (rest : List UInt256)
    (mem : ByteArray) (hcap : rest.length < 1000) (hi : i < 8192)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock e3Path
      (st s 447 (UInt256.ofNat i :: UInt256.ofNat el :: UInt256.ofNat ml :: rest) mem AW) =
        some (st s 374 (UInt256.ofNat (i + 1) :: UInt256.ofNat el :: UInt256.ofNat ml :: rest)
          mem AW) := by
  have hc := caps _ hcap
  have hadd : UInt256.ofNat 1 + UInt256.ofNat i = UInt256.ofNat (i + 1) := by
    rw [Challenge.EvmProof.Word.ofNat_add_ofNat (by omega), Nat.add_comm]
  bigc_run [e3Path, hc, hcode, hrun, hadd]

theorem run_e9 (s : State) (i el ml : Nat) (rest : List UInt256)
    (mem : ByteArray) (hcap : rest.length < 1000) (hml : ml ≤ 1024)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock e9Path
      (st s 455 (UInt256.ofNat i :: UInt256.ofNat el :: UInt256.ofNat ml :: rest) mem AW) =
        some (st s 548 (UInt256.ofNat 472 :: UInt256.ofNat 8192 ::
          UInt256.ofNat i :: UInt256.ofNat el :: UInt256.ofNat ml :: rest)
          (MachineState.writeBytes mem (MachineState.readPadded mem 3072 ml) 0) AW) := by
  have hc := caps _ hcap
  have h2 : ml < LIM := by simp only [LIM]; omega
  have haw1 : MachineState.activeWordsAfter 289 0 ml = 289 := aw_keep _ _ (by omega)
  have haw2 : MachineState.activeWordsAfter 289 3072 ml = 289 := aw_keep _ _ (by omega)
  bigc_run [e9Path, hc, hcode, hrun, zero_lit, h2, haw1, haw2]

theorem run_e5 (s : State) (i el ml : Nat) (rest : List UInt256)
    (mem : ByteArray) (hcap : rest.length < 1000) (hml : ml ≤ 1024)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock e5Path
      (st s 472 (UInt256.ofNat i :: UInt256.ofNat el :: UInt256.ofNat ml :: rest) mem AW) =
        some (rt s 475 (UInt256.ofNat i :: UInt256.ofNat el :: UInt256.ofNat ml :: rest)
          mem AW (MachineState.readPadded mem 0 ml)) := by
  have hc := caps _ hcap
  have h2 : ml < LIM := by simp only [LIM]; omega
  have haw : MachineState.activeWordsAfter 289 0 ml = 289 := aw_keep _ _ (by omega)
  bigc_run [e5Path, hc, hcode, hrun, zero_lit, h2, haw]

/-! ## Modular multiplication (`MULM`) -/

theorem run_mEntry (s : State) (ml : Nat) (ret x y k : UInt256) (rest : List UInt256)
    (mem : ByteArray) (hcap : rest.length < 1000) (hml : ml ≤ 1024)
    (hmsv : MachineState.readWord mem 9216 = UInt256.ofNat ml)
    (hcds : s.executionEnv.calldata.size < 2 ^ 64)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock mEntryPath
      (st s 476 (ret :: x :: y :: k :: rest) mem AW) =
        some (st s 485 (UInt256.ofNat 0 :: ret :: x :: y :: k :: rest)
          (MachineState.writeBytes mem
            (MachineState.readPadded s.executionEnv.calldata
              s.executionEnv.calldata.size ml) 0) AW) := by
  have hc := caps _ hcap
  have h2 : ml < LIM := by simp only [LIM]; omega
  have h3 : s.executionEnv.calldata.size < LIM := by simp only [LIM]; omega
  have haw0 : MachineState.activeWordsAfter 289 9216 32 = 289 := aw_keep _ _ (by omega)
  have haw1 : MachineState.activeWordsAfter 289 0 ml = 289 := aw_keep _ _ (by omega)
  bigc_run [mEntryPath, hc, hcode, hrun, zero_lit, hmsv, h2, h3, haw0, haw1]

theorem run_mGuard_done (s : State) (j k : Nat) (ret x y : UInt256)
    (rest : List UInt256) (mem : ByteArray) (hcap : rest.length < 1000)
    (hk : k ≤ 1024) (hj : j = k * 8)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock mGuardPath
      (st s 485 (UInt256.ofNat j :: ret :: x :: y :: UInt256.ofNat k :: rest) mem AW) =
        some (st s 541 (UInt256.ofNat j :: ret :: x :: y :: UInt256.ofNat k :: rest)
          mem AW) := by
  have hc := caps _ hcap
  have hshl := shl3_ofNat k (by omega)
  have heq := eq_ofNat_toNat j (k * 8) (by omega) (by omega)
  have hcond : (UInt256.eq (UInt256.ofNat j) (UInt256.ofNat (k * 8))).toNat ≠ 0 := by
    rw [heq, if_pos hj]; norm_num
  bigc_run [mGuardPath, hc, hcode, hrun, hshl, hcond]

theorem run_mGuard_go (s : State) (j k : Nat) (ret x y : UInt256)
    (rest : List UInt256) (mem : ByteArray) (hcap : rest.length < 1000)
    (hk : k ≤ 1024) (hj : j ≠ k * 8) (hj' : j < 2 ^ 256)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock mGuardPath
      (st s 485 (UInt256.ofNat j :: ret :: x :: y :: UInt256.ofNat k :: rest) mem AW) =
        some (st s 496 (UInt256.ofNat j :: ret :: x :: y :: UInt256.ofNat k :: rest)
          mem AW) := by
  have hc := caps _ hcap
  have hshl := shl3_ofNat k (by omega)
  have heq := eq_ofNat_toNat j (k * 8) hj' (by omega)
  have hcond : (UInt256.eq (UInt256.ofNat j) (UInt256.ofNat (k * 8))).toNat = 0 := by
    rw [heq, if_neg hj]
  bigc_run [mGuardPath, hc, hcode, hrun, hshl, hcond]

theorem run_mDouble (s : State) (j : Nat) (rest : List UInt256) (mem : ByteArray)
    (hcap : rest.length < 1000)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock mDoublePath
      (st s 496 (UInt256.ofNat j :: rest) mem AW) =
        some (st s 548 (UInt256.ofNat 504 :: UInt256.ofNat 0 :: UInt256.ofNat j :: rest)
          mem AW) := by
  have hc := caps _ hcap
  bigc_run [mDoublePath, hc, hcode, hrun, zero_lit]

theorem run_m2_skip (s : State) (j yb : Nat) (ret x k : UInt256) (rest : List UInt256)
    (mem : ByteArray) (hcap : rest.length < 1000) (hj : j < 8192) (hy : yb ≤ 7168)
    (hbit : (bitWord mem (yb + j / 8) (j % 8)).toNat = 0)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock m2Path
      (st s 504 (UInt256.ofNat j :: ret :: x :: UInt256.ofNat yb :: k :: rest) mem AW) =
        some (st s 533 (UInt256.ofNat j :: ret :: x :: UInt256.ofNat yb :: k :: rest)
          mem AW) := by
  have hc := caps _ hcap
  have hshr := shr3_ofNat j (by omega)
  have hand := and7_ofNat j (by omega)
  have hadd : UInt256.ofNat yb + UInt256.ofNat (j / 8) = UInt256.ofNat (yb + j / 8) :=
    Challenge.EvmProof.Word.ofNat_add_ofNat (by omega)
  have h1 : yb + j / 8 < LIM := by simp only [LIM]; omega
  have h3 : j % 8 < LIM := by simp only [LIM]; omega
  have haw : MachineState.activeWordsAfter 289 (yb + j / 8) 32 = 289 :=
    aw_keep _ _ (by omega)
  have hz := hbit
  simp only [bitWord] at hz
  bigc_run [m2Path, hc, hcode, hrun, hshr, hand, hadd, h1, h3, haw, hz]

theorem run_m2_add (s : State) (j yb : Nat) (ret x k : UInt256) (rest : List UInt256)
    (mem : ByteArray) (hcap : rest.length < 1000) (hj : j < 8192) (hy : yb ≤ 7168)
    (hbit : (bitWord mem (yb + j / 8) (j % 8)).toNat ≠ 0)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock m2Path
      (st s 504 (UInt256.ofNat j :: ret :: x :: UInt256.ofNat yb :: k :: rest) mem AW) =
        some (st s 525 (UInt256.ofNat j :: ret :: x :: UInt256.ofNat yb :: k :: rest)
          mem AW) := by
  have hc := caps _ hcap
  have hshr := shr3_ofNat j (by omega)
  have hand := and7_ofNat j (by omega)
  have hadd : UInt256.ofNat yb + UInt256.ofNat (j / 8) = UInt256.ofNat (yb + j / 8) :=
    Challenge.EvmProof.Word.ofNat_add_ofNat (by omega)
  have h1 : yb + j / 8 < LIM := by simp only [LIM]; omega
  have h3 : j % 8 < LIM := by simp only [LIM]; omega
  have haw : MachineState.activeWordsAfter 289 (yb + j / 8) 32 = 289 :=
    aw_keep _ _ (by omega)
  have hz := hbit
  simp only [bitWord] at hz
  bigc_run [m2Path, hc, hcode, hrun, hshr, hand, hadd, h1, h3, haw, hz]

theorem run_mAdd (s : State) (j : Nat) (ret x y k : UInt256) (rest : List UInt256)
    (mem : ByteArray) (hcap : rest.length < 1000)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock mAddPath
      (st s 525 (UInt256.ofNat j :: ret :: x :: y :: k :: rest) mem AW) =
        some (st s 548 (UInt256.ofNat 533 :: x :: UInt256.ofNat j :: ret :: x :: y :: k :: rest)
          mem AW) := by
  have hc := caps _ hcap
  bigc_run [mAddPath, hc, hcode, hrun]

theorem run_m3 (s : State) (j : Nat) (rest : List UInt256) (mem : ByteArray)
    (hcap : rest.length < 1000) (hj : j < 8192)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock m3Path
      (st s 533 (UInt256.ofNat j :: rest) mem AW) =
        some (st s 485 (UInt256.ofNat (j + 1) :: rest) mem AW) := by
  have hc := caps _ hcap
  have hadd : UInt256.ofNat 1 + UInt256.ofNat j = UInt256.ofNat (j + 1) := by
    rw [Challenge.EvmProof.Word.ofNat_add_ofNat (by omega), Nat.add_comm]
  bigc_run [m3Path, hc, hcode, hrun, hadd]

theorem run_m9 (s : State) (j retPc : Nat) (x y k : UInt256) (rest : List UInt256)
    (mem : ByteArray) (hcap : rest.length < 1000) (hret : retPc < 2 ^ 16)
    (hjump : Decode.isValidJumpDest submissionBytecode retPc = true)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock m9Path
      (st s 541 (UInt256.ofNat j :: UInt256.ofNat retPc :: x :: y :: k :: rest) mem AW) =
        some (st s retPc rest mem AW) := by
  have hc := caps _ hcap
  have h1 : retPc < LIM := by simp only [LIM]; omega
  bigc_run [m9Path, hc, hcode, hrun, h1, hjump]

/-! ## Modular addition (`ADDM`) -/

theorem run_aEntry (s : State) (ml : Nat) (ret src : UInt256) (rest : List UInt256)
    (mem : ByteArray) (hcap : rest.length < 1000)
    (hmsv : MachineState.readWord mem 9216 = UInt256.ofNat ml)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock aEntryPath
      (st s 548 (ret :: src :: rest) mem AW) =
        some (st s 554 (UInt256.ofNat ml :: UInt256.ofNat 0 :: ret :: src :: rest) mem AW) := by
  have hc := caps _ hcap
  have haw0 : MachineState.activeWordsAfter 289 9216 32 = 289 := aw_keep _ _ (by omega)
  bigc_run [aEntryPath, hc, hcode, hrun, zero_lit, hmsv, haw0]

/-- The byte sum written by one `A1` iteration. -/
def addSum (mem : ByteArray) (src i : Nat) (c : UInt256) : UInt256 :=
  c + (byteW mem i + byteW mem (src + i))

theorem run_aLoop_back (s : State) (i src : Nat) (c ret : UInt256) (rest : List UInt256)
    (mem : ByteArray) (hcap : rest.length < 1000) (hi : 2 ≤ i) (hi' : i ≤ 1024)
    (hsrc : src ≤ 8192)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock aLoopPath
      (st s 554 (UInt256.ofNat i :: c :: ret :: UInt256.ofNat src :: rest) mem AW) =
        some (st s 554 (UInt256.ofNat (i - 1) ::
          UInt256.shiftRight (addSum mem src (i - 1) c) (UInt256.ofNat 8) ::
          ret :: UInt256.ofNat src :: rest)
          (MachineState.writeBytes mem
            (ByteArray.mk #[UInt8.ofNat ((addSum mem src (i - 1) c).toNat % 256)]) (i - 1))
          AW) := by
  have hc := caps _ hcap
  have hdec := dec_ofNat i (by omega) (by omega)
  have hadd : UInt256.ofNat src + UInt256.ofNat (i - 1) = UInt256.ofNat (src + (i - 1)) :=
    Challenge.EvmProof.Word.ofNat_add_ofNat (by omega)
  have h1 : src + (i - 1) < LIM := by simp only [LIM]; omega
  have h2 : i - 1 < LIM := by simp only [LIM]; omega
  have hne : ¬ i - 1 = 0 := by omega
  have haw1 : MachineState.activeWordsAfter 289 (src + (i - 1)) 32 = 289 :=
    aw_keep _ _ (by omega)
  have haw2 : MachineState.activeWordsAfter 289 (i - 1) 32 = 289 := aw_keep _ _ (by omega)
  have haw3 : MachineState.activeWordsAfter 289 (i - 1) 1 = 289 := aw_keep _ _ (by omega)
  bigc_run [aLoopPath, addSum, hc, hcode, hrun, zero_lit, hdec, hadd, h1, h2, hne,
    haw1, haw2, haw3]

theorem run_aLoop_exit (s : State) (src : Nat) (c ret : UInt256) (rest : List UInt256)
    (mem : ByteArray) (hcap : rest.length < 1000) (hsrc : src ≤ 8192)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock aLoopPath
      (st s 554 (UInt256.ofNat 1 :: c :: ret :: UInt256.ofNat src :: rest) mem AW) =
        some (st s 584 (UInt256.ofNat 0 ::
          UInt256.shiftRight (addSum mem src 0 c) (UInt256.ofNat 8) ::
          ret :: UInt256.ofNat src :: rest)
          (MachineState.writeBytes mem
            (ByteArray.mk #[UInt8.ofNat ((addSum mem src 0 c).toNat % 256)]) 0)
          AW) := by
  have hc := caps _ hcap
  have hdec := dec_ofNat 1 (by omega) (by norm_num)
  have hadd : UInt256.ofNat src + UInt256.ofNat 0 = UInt256.ofNat src := by
    rw [Challenge.EvmProof.Word.ofNat_add_ofNat (by omega), Nat.add_zero]
  have h1 : src < LIM := by simp only [LIM]; omega
  have haw1 : MachineState.activeWordsAfter 289 src 32 = 289 := aw_keep _ _ (by omega)
  have haw2 : MachineState.activeWordsAfter 289 0 32 = 289 := aw_keep _ _ (by omega)
  have haw3 : MachineState.activeWordsAfter 289 0 1 = 289 := aw_keep _ _ (by omega)
  bigc_run [aLoopPath, addSum, hc, hcode, hrun, zero_lit, hdec, hadd, h1,
    haw1, haw2, haw3]

theorem run_aExit (s : State) (ml : Nat) (c ret src : UInt256) (rest : List UInt256)
    (mem : ByteArray) (hcap : rest.length < 1000)
    (hmsv : MachineState.readWord mem 9216 = UInt256.ofNat ml)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock aExitPath
      (st s 584 (UInt256.ofNat 0 :: c :: ret :: src :: rest) mem AW) =
        some (st s 590 (UInt256.ofNat ml :: UInt256.ofNat 0 :: c :: ret :: src :: rest)
          mem AW) := by
  have hc := caps _ hcap
  have haw0 : MachineState.activeWordsAfter 289 9216 32 = 289 := aw_keep _ _ (by omega)
  bigc_run [aExitPath, hc, hcode, hrun, zero_lit, hmsv, haw0]

/-- The byte difference written by one `S1` iteration. -/
def subDiff (mem : ByteArray) (i : Nat) (b : UInt256) : UInt256 :=
  (byteW mem i - byteW mem (1024 + i)) - b

theorem run_sLoop_back (s : State) (i : Nat) (b c ret src : UInt256) (rest : List UInt256)
    (mem : ByteArray) (hcap : rest.length < 1000) (hi : 2 ≤ i) (hi' : i ≤ 1024)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock sLoopPath
      (st s 590 (UInt256.ofNat i :: b :: c :: ret :: src :: rest) mem AW) =
        some (st s 590 (UInt256.ofNat (i - 1) ::
          UInt256.shiftRight (subDiff mem (i - 1) b) (UInt256.ofNat 255) ::
          c :: ret :: src :: rest)
          (MachineState.writeBytes mem
            (ByteArray.mk #[UInt8.ofNat ((subDiff mem (i - 1) b).toNat % 256)])
            (4096 + (i - 1))) AW) := by
  have hc := caps _ hcap
  have hdec := dec_ofNat i (by omega) (by omega)
  have hadd : UInt256.ofNat 1024 + UInt256.ofNat (i - 1) = UInt256.ofNat (1024 + (i - 1)) :=
    Challenge.EvmProof.Word.ofNat_add_ofNat (by omega)
  have hadd2 : UInt256.ofNat 4096 + UInt256.ofNat (i - 1) = UInt256.ofNat (4096 + (i - 1)) :=
    Challenge.EvmProof.Word.ofNat_add_ofNat (by omega)
  have h1 : 1024 + (i - 1) < LIM := by simp only [LIM]; omega
  have h1' : 4096 + (i - 1) < LIM := by simp only [LIM]; omega
  have h2 : i - 1 < LIM := by simp only [LIM]; omega
  have hne : ¬ i - 1 = 0 := by omega
  have haw1 : MachineState.activeWordsAfter 289 (1024 + (i - 1)) 32 = 289 :=
    aw_keep _ _ (by omega)
  have haw2 : MachineState.activeWordsAfter 289 (i - 1) 32 = 289 := aw_keep _ _ (by omega)
  have haw3 : MachineState.activeWordsAfter 289 (4096 + (i - 1)) 1 = 289 :=
    aw_keep _ _ (by omega)
  bigc_run [sLoopPath, subDiff, hc, hcode, hrun, zero_lit, hdec, hadd, hadd2, h1, h1', h2,
    hne, haw1, haw2, haw3]

theorem run_sLoop_exit (s : State) (b c ret src : UInt256) (rest : List UInt256)
    (mem : ByteArray) (hcap : rest.length < 1000)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock sLoopPath
      (st s 590 (UInt256.ofNat 1 :: b :: c :: ret :: src :: rest) mem AW) =
        some (st s 627 (UInt256.ofNat 0 ::
          UInt256.shiftRight (subDiff mem 0 b) (UInt256.ofNat 255) ::
          c :: ret :: src :: rest)
          (MachineState.writeBytes mem
            (ByteArray.mk #[UInt8.ofNat ((subDiff mem 0 b).toNat % 256)]) 4096) AW) := by
  have hc := caps _ hcap
  have hdec := dec_ofNat 1 (by omega) (by norm_num)
  have hadd : UInt256.ofNat 1024 + UInt256.ofNat 0 = UInt256.ofNat 1024 := by decide
  have hadd2 : UInt256.ofNat 4096 + UInt256.ofNat 0 = UInt256.ofNat 4096 := by decide
  have haw1 : MachineState.activeWordsAfter 289 1024 32 = 289 := aw_keep _ _ (by omega)
  have haw2 : MachineState.activeWordsAfter 289 0 32 = 289 := aw_keep _ _ (by omega)
  have haw3 : MachineState.activeWordsAfter 289 4096 1 = 289 := aw_keep _ _ (by omega)
  bigc_run [sLoopPath, subDiff, hc, hcode, hrun, zero_lit, hdec, hadd, hadd2,
    haw1, haw2, haw3]

/-- The `sExit` decision word: nonzero means keep the sum (no final copy). -/
def keepWord (b c : UInt256) : UInt256 :=
  UInt256.isZero (UInt256.lor (UInt256.isZero b) c)

theorem run_sExit_keep (s : State) (b c ret src : UInt256) (rest : List UInt256)
    (mem : ByteArray) (hcap : rest.length < 1000)
    (hkeep : ((if b.toNat = 0 then 1 else 0) ||| c.toNat) = 0)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock sExitPath
      (st s 627 (UInt256.ofNat 0 :: b :: c :: ret :: src :: rest) mem AW) =
        some (st s 644 (ret :: src :: rest) mem AW) := by
  have hc := caps _ hcap
  bigc_run [sExitPath, hc, hcode, hrun, hkeep]

theorem run_sExit_copy (s : State) (b c ret src : UInt256) (rest : List UInt256)
    (mem : ByteArray) (hcap : rest.length < 1000)
    (hkeep : ¬ ((if b.toNat = 0 then 1 else 0) ||| c.toNat) = 0)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock sExitPath
      (st s 627 (UInt256.ofNat 0 :: b :: c :: ret :: src :: rest) mem AW) =
        some (st s 635 (ret :: src :: rest) mem AW) := by
  have hc := caps _ hcap
  bigc_run [sExitPath, hc, hcode, hrun, hkeep]

theorem run_copy (s : State) (ml : Nat) (ret src : UInt256) (rest : List UInt256)
    (mem : ByteArray) (hcap : rest.length < 1000) (hml : ml ≤ 1024)
    (hmsv : MachineState.readWord mem 9216 = UInt256.ofNat ml)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock copyPath
      (st s 635 (ret :: src :: rest) mem AW) =
        some (st s 644 (ret :: src :: rest)
          (MachineState.writeBytes mem (MachineState.readPadded mem 4096 ml) 0) AW) := by
  have hc := caps _ hcap
  have h2 : ml < LIM := by simp only [LIM]; omega
  have haw0 : MachineState.activeWordsAfter 289 9216 32 = 289 := aw_keep _ _ (by omega)
  have haw1 : MachineState.activeWordsAfter 289 0 ml = 289 := aw_keep _ _ (by omega)
  have haw2 : MachineState.activeWordsAfter 289 4096 ml = 289 := aw_keep _ _ (by omega)
  bigc_run [copyPath, hc, hcode, hrun, zero_lit, hmsv, h2, haw0, haw1, haw2]

theorem run_a3 (s : State) (retPc : Nat) (src : UInt256) (rest : List UInt256)
    (mem : ByteArray) (hcap : rest.length < 1000) (hret : retPc < 2 ^ 16)
    (hjump : Decode.isValidJumpDest submissionBytecode retPc = true)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock a3Path
      (st s 644 (UInt256.ofNat retPc :: src :: rest) mem AW) =
        some (st s retPc rest mem AW) := by
  have hc := caps _ hcap
  have h1 : retPc < LIM := by simp only [LIM]; omega
  bigc_run [a3Path, hc, hcode, hrun, h1, hjump]

end Challenge.Modexp.Submission.Proofs.Bytecode.BigC
