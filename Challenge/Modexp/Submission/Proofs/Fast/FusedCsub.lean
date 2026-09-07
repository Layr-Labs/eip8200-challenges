import Challenge.Modexp.Submission.Proofs.Fast.Csub
import Challenge.Modexp.Submission.Proofs.Fast.Paths.P21
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-!
# Fused ADDMOD and conditional subtraction

The live pc-2467 entry jumps to pc 4643.  The appended routine walks the input
blocks, the modulus, `TS`, and `SUBB` once, maintaining the ADDMOD carry and the
conditional-subtraction borrow together.  This specialization depends only on
the public fast-path shape (`2 ≤ n ≤ 32`) and not on corpus bytes or their seed.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.FusedCsub

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Fast

/-- Wrapped offset from `TS = 8256`; adding this to the live `TS` pointer
recovers the corresponding limb address in an operand block. -/
def addrDelta (p : Nat) : UInt256 :=
  UInt256.ofNat p - UInt256.ofNat 8256

/-- Memory plus the two one-bit flags carried by the fused limb walk. -/
structure LimbState where
  memory : ByteArray
  carry : UInt256
  borrow : UInt256

/-- Operational memory model of the fused loop.  Step `j` consumes the
`j`-th limb from the least-significant end, writes the sum to `TS`, and writes
the conditional-subtraction candidate to `SUBB`. -/
def limbStep (memory : ByteArray) (pa pb n : Nat) : Nat → LimbState
  | 0 => ⟨memory, UInt256.ofNat 0, UInt256.ofNat 0⟩
  | j + 1 =>
      let prev := limbStep memory pa pb n j
      let x := MachineState.readWord prev.memory (pa + 32 * (n - 1 - j))
      let y := MachineState.readWord prev.memory (pb + 32 * (n - 1 - j))
      let sum := x + y
      let total := sum + prev.carry
      let carry := UInt256.lor (UInt256.lt total sum) (UInt256.lt sum x)
      let md := MachineState.readWord prev.memory (32 * (n - 1 - j))
      let d1 := total - md
      let d2 := d1 - prev.borrow
      -- The bytecode detects the second underflow as `d1 < d2`; for a one-bit
      -- incoming borrow this is equivalent to `d1 < borrow`, but keeping the
      -- instruction-exact expression makes the reduction theorem definitional.
      let borrow := UInt256.lor (UInt256.lt d1 d2) (UInt256.lt total d1)
      let withSub := MachineState.writeBytes prev.memory
        (Data.Bytes.natToBytesPadded d2.toNat 32) (7168 + 32 * (n - 1 - j))
      { memory := MachineState.writeBytes withSub
          (Data.Bytes.natToBytesPadded total.toNat 32) (8256 + 32 * (n - 1 - j))
        carry := carry
        borrow := borrow }

/-- State immediately after the pc-2467 trampoline. -/
def entryState (s : State) (memory : ByteArray) (pa pb : Nat)
    (pd ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 4643
           stack := [UInt256.ofNat pa, UInt256.ofNat pb, pd, ret] ++ rest
           memory := memory }

/-- Fused loop head at pc 4665 after `j` completed limbs. -/
def loopState (s : State) (memory : ByteArray) (pa pb n j : Nat)
    (pd ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 4665
           stack := [UInt256.ofNat (8224 + 32 * (n - j)),
                     (limbStep memory pa pb n j).carry,
                     (limbStep memory pa pb n j).borrow,
                     addrDelta pa, addrDelta pb, pd, ret] ++ rest
           memory := (limbStep memory pa pb n j).memory }

/-- Fused tail at pc 4729 after all `n` limbs. -/
def tailState (s : State) (memory : ByteArray) (pa pb n j : Nat)
    (pd ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 4729
           stack := [UInt256.ofNat (8224 + 32 * (n - j)),
                     (limbStep memory pa pb n j).carry,
                     (limbStep memory pa pb n j).borrow,
                     addrDelta pa, addrDelta pb, pd, ret] ++ rest
           memory := (limbStep memory pa pb n j).memory }

/-- The tail preserves the historical `TN` scratch word. -/
def tnMemory (memory : ByteArray) (pa pb n j : Nat) : ByteArray :=
  MachineState.writeBytes (limbStep memory pa pb n j).memory
    (Data.Bytes.natToBytesPadded (limbStep memory pa pb n j).carry.toNat 32) 8224

/-- Nonzero exactly when the candidate in `SUBB` must be selected. -/
def useSub (memory : ByteArray) (pa pb n j : Nat) : UInt256 :=
  UInt256.lor (limbStep memory pa pb n j).carry
    (UInt256.isZero (limbStep memory pa pb n j).borrow)

/-- `TS` when `useSub = 0`, otherwise `SUBB`. -/
def resultSrc (memory : ByteArray) (pa pb n j : Nat) : UInt256 :=
  (8256 : UInt256) - (1088 : UInt256) * useSub memory pa pb n j

/-- Returned caller state, including the historical scratch-memory effects. -/
def returnedState (s : State) (memory : ByteArray) (pa pb n j : Nat)
    (pd ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := ret
           stack := rest
           memory := MachineState.writeBytes (tnMemory memory pa pb n j)
             (MachineState.readPadded (tnMemory memory pa pb n j)
               (resultSrc memory pa pb n j).toNat (32 * n)) pd.toNat }

/-! ## Word-address arithmetic -/

/-- EVM subtraction wraps exactly when the minuend is below the subtrahend. -/
theorem lt_sub_eq_lt (x y : UInt256) :
    UInt256.lt x (x - y) = UInt256.lt x y := by
  apply Challenge.EvmProof.Word.word_ext
  rw [Challenge.EvmProof.Word.word_toNat_lt,
    Challenge.EvmProof.Word.word_toNat_lt,
    Challenge.EvmProof.Word.word_toNat_sub_cond]
  by_cases hxy : x.toNat < y.toNat
  · rw [if_pos hxy]
    have hxlt : x.toNat < 2 ^ 256 + x.toNat - y.toNat := by
      have hy : y.toNat < 2 ^ 256 := y.val.isLt
      omega
    rw [if_pos hxlt, if_pos hxy]
  · rw [if_neg hxy]
    have hnlt : ¬x.toNat < x.toNat - y.toNat := by omega
    rw [if_neg hnlt, if_neg hxy]

theorem ptr_add_addrDelta (p n j : Nat) (hj : j < n)
    (hp : p + 32 * n ≤ 9472) :
    UInt256.ofNat (8224 + 32 * (n - j)) + addrDelta p =
      UInt256.ofNat (p + 32 * (n - 1 - j)) := by
  unfold addrDelta
  calc
    UInt256.ofNat (8224 + 32 * (n - j)) +
          (UInt256.ofNat p - UInt256.ofNat 8256) =
        (UInt256.ofNat (8224 + 32 * (n - j)) - UInt256.ofNat 8256) +
          UInt256.ofNat p := by
      cases UInt256.ofNat (8224 + 32 * (n - j)) with
      | mk av =>
        cases UInt256.ofNat p with
        | mk pv =>
          cases UInt256.ofNat 8256 with
          | mk cv =>
            change UInt256.mk (av + (pv - cv)) = UInt256.mk ((av - cv) + pv)
            congr 1
            rw [← add_sub_assoc]
            exact add_sub_right_comm av pv cv
    _ = UInt256.ofNat (8224 + 32 * (n - j) - 8256) + UInt256.ofNat p := by
      rw [Challenge.EvmProof.Word.ofNat_sub_ofNat (by omega) (by omega)]
    _ = UInt256.ofNat ((8224 + 32 * (n - j) - 8256) + p) := by
      rw [Challenge.EvmProof.Word.ofNat_add_mod]
    _ = UInt256.ofNat (p + 32 * (n - 1 - j)) := by
      congr 1
      omega

theorem ptr_sub_limb (n j : Nat) (hj : j < n) (hn32 : n ≤ 32) :
    UInt256.ofNat (8224 + 32 * (n - j)) - UInt256.ofNat 32 =
      UInt256.ofNat (8224 + 32 * (n - (j + 1))) := by
  have heq : 8224 + 32 * (n - j) - 32 = 8224 + 32 * (n - (j + 1)) := by
    omega
  rw [Challenge.EvmProof.Word.ofNat_sub_ofNat (by omega) (by omega), heq]

/-! ## Concrete block reductions -/

set_option linter.unusedSimpArgs false in
theorem run_trampoline (s : State) (memory : ByteArray) (pa pb : Nat)
    (pd ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk1600
      (Csub.amEntryState s memory pa pb pd ret rest) =
      some (entryState s memory pa pb pd ret rest) := by
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have h4057 : (4643 : UInt256).toNat = 4643 := by decide
  have h4057' : (4643 : UInt256) = UInt256.ofNat 4643 := by decide
  have hjump : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode
      (4643 : UInt256).toNat = true := by
    rw [h4057]
    exact jumpDest4643
  simp (config := { maxSteps := 100000 })
    [blk1600, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      Csub.amEntryState, entryState, fastPC15, hc4, hc5, hrun, hcode, h4057,
      h4057', hjump,
      jumpDest4643, Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt, List.exchange]

set_option linter.unusedSimpArgs false in
theorem run_entry (s : State) (memory : ByteArray) (pa pb n : Nat)
    (pd ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hact : 296 ≤ s.activeWords.toNat)
    (htl : MachineState.readWord memory 9440 = UInt256.ofNat (8224 + 32 * n)) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk2862
      (entryState s memory pa pb pd ret rest) =
      some (loopState s memory pa pb n 0 pd ret rest) := by
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have h9440 : (9440 : UInt256).toNat = 9440 := by decide
  have hzero : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have h8256 : (8256 : UInt256) = UInt256.ofNat 8256 := by decide
  have hactTL : UInt256.ofNat
      (MachineState.activeWordsAfter s.activeWords.toNat 9440 32) = s.activeWords :=
    Csub.activeWords_fix s 9440 32 (by decide) (by omega) hact
  simp (config := { maxSteps := 300000 })
    [blk2862, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      entryState, loopState, limbStep, addrDelta, fusedCsubPC0,
      hc4, hc5, hc6, hc7, hrun, h9440, hzero, h8256, htl, hactTL,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt, List.exchange]

set_option linter.unusedSimpArgs false in
theorem run_loop_body (s : State) (memory : ByteArray) (pa pb n j : Nat)
    (pd ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hact : 296 ≤ s.activeWords.toNat)
    (hj : j + 1 < n) (hn32 : n ≤ 32)
    (hpaFit : pa + 32 * n ≤ 9472) (hpbFit : pb + 32 * n ≤ 9472) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk2878
      (loopState s memory pa pb n j pd ret rest) =
      some (loopState s memory pa pb n (j + 1) pd ret rest) := by
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have h32 : (32 : UInt256) = UInt256.ofNat 32 := by decide
  have h1088 : (1088 : UInt256) = UInt256.ofNat 1088 := by decide
  have h8256 : (8256 : UInt256) = UInt256.ofNat 8256 := by decide
  have h8224 : (8224 : UInt256).toNat = 8224 := by decide
  have hA := ptr_add_addrDelta pa n j (by omega) hpaFit
  have hB := ptr_add_addrDelta pb n j (by omega) hpbFit
  have hM : UInt256.ofNat (8224 + 32 * (n - j)) - UInt256.ofNat 8256 =
      UInt256.ofNat (32 * (n - 1 - j)) := by
    rw [Challenge.EvmProof.Word.ofNat_sub_ofNat (by omega) (by omega)]
    congr 1
    omega
  have hD : UInt256.ofNat (8224 + 32 * (n - j)) - UInt256.ofNat 1088 =
      UInt256.ofNat (7168 + 32 * (n - 1 - j)) := by
    rw [Challenge.EvmProof.Word.ofNat_sub_ofNat (by omega) (by omega)]
    congr 1
    omega
  have hnext := ptr_sub_limb n j (by omega) hn32
  have hTaddr : 8224 + 32 * (n - j) = 8256 + 32 * (n - 1 - j) := by omega
  have haddrT : (8224 + 32 * (n - j)) % 2 ^ 256 =
      8256 + 32 * (n - 1 - j) := by rw [hTaddr, Nat.mod_eq_of_lt (by omega)]
  have hnextMod : (8224 + 32 * (n - (j + 1))) % 2 ^ 256 =
      8224 + 32 * (n - (j + 1)) := Nat.mod_eq_of_lt (by omega)
  have hgt : 8224 < 8224 + 32 * (n - (j + 1)) := by omega
  have haddrA : (pa + 32 * (n - 1 - j)) % 2 ^ 256 =
      pa + 32 * (n - 1 - j) := Nat.mod_eq_of_lt (by omega)
  have haddrB : (pb + 32 * (n - 1 - j)) % 2 ^ 256 =
      pb + 32 * (n - 1 - j) := Nat.mod_eq_of_lt (by omega)
  have haddrM : (32 * (n - 1 - j)) % 2 ^ 256 =
      32 * (n - 1 - j) := Nat.mod_eq_of_lt (by omega)
  have haddrP : (8256 + 32 * (n - 1 - j)) % 2 ^ 256 =
      8256 + 32 * (n - 1 - j) := Nat.mod_eq_of_lt (by omega)
  have h8256N : 8256 % 2 ^ 256 = 8256 := Nat.mod_eq_of_lt (by omega)
  have h1088N : 1088 % 2 ^ 256 = 1088 := Nat.mod_eq_of_lt (by omega)
  have h32N : 32 % 2 ^ 256 = 32 := Nat.mod_eq_of_lt (by omega)
  have hAN : (8256 + 32 * (n - 1 - j) + (addrDelta pa).toNat) % 2 ^ 256 =
      pa + 32 * (n - 1 - j) := by
    have hh := congrArg UInt256.toNat hA
    rw [hTaddr] at hh
    simpa only [Challenge.EvmProof.Word.word_toNat_add,
      Challenge.EvmProof.Word.word_toNat_ofNat, haddrP, haddrA] using hh
  have hBN : (8256 + 32 * (n - 1 - j) + (addrDelta pb).toNat) % 2 ^ 256 =
      pb + 32 * (n - 1 - j) := by
    have hh := congrArg UInt256.toNat hB
    rw [hTaddr] at hh
    simpa only [Challenge.EvmProof.Word.word_toNat_add,
      Challenge.EvmProof.Word.word_toNat_ofNat, haddrP, haddrB] using hh
  have hMN : (2 ^ 256 + (8256 + 32 * (n - 1 - j)) - 8256) % 2 ^ 256 =
      32 * (n - 1 - j) := by
    have hh := congrArg UInt256.toNat hM
    rw [hTaddr] at hh
    simpa only [Challenge.EvmProof.Word.word_toNat_sub,
      Challenge.EvmProof.Word.word_toNat_ofNat, haddrP, h8256N, haddrM] using hh
  have hDN : (2 ^ 256 + (8256 + 32 * (n - 1 - j)) - 1088) % 2 ^ 256 =
      7168 + 32 * (n - 1 - j) := by
    have hh := congrArg UInt256.toNat hD
    rw [hTaddr] at hh
    simpa only [Challenge.EvmProof.Word.word_toNat_sub,
      Challenge.EvmProof.Word.word_toNat_ofNat, haddrP, h1088N,
      Nat.mod_eq_of_lt (show 7168 + 32 * (n - 1 - j) < 2 ^ 256 by omega)] using hh
  have hnextN : (2 ^ 256 + (8256 + 32 * (n - 1 - j)) - 32) % 2 ^ 256 =
      8224 + 32 * (n - (j + 1)) := by
    have hh := congrArg UInt256.toNat hnext
    rw [hTaddr] at hh
    simpa only [Challenge.EvmProof.Word.word_toNat_sub,
      Challenge.EvmProof.Word.word_toNat_ofNat, haddrP, h32N, hnextMod] using hh
  have hnextP : UInt256.ofNat (8256 + 32 * (n - 1 - j)) - UInt256.ofNat 32 =
      UInt256.ofNat (8224 + 32 * (n - (j + 1))) := by
    rw [← hTaddr]
    exact hnext
  norm_num at haddrT hnextMod haddrA haddrB haddrM haddrP h8256N h1088N h32N hAN hBN hMN hDN hnextN
  have h4079 : (4665 : UInt256).toNat = 4665 := by decide
  have h4079' : (4665 : UInt256) = UInt256.ofNat 4665 := by decide
  have hjump : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode
      (4665 : UInt256).toNat = true := by
    rw [h4079]
    exact jumpDest4665
  have hactA : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      (pa + 32 * (n - 1 - j)) 32) = s.activeWords :=
    Csub.activeWords_fix s _ 32 (by decide) (by omega) hact
  have hactB : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      (pb + 32 * (n - 1 - j)) 32) = s.activeWords :=
    Csub.activeWords_fix s _ 32 (by decide) (by omega) hact
  have hactM : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      (32 * (n - 1 - j)) 32) = s.activeWords :=
    Csub.activeWords_fix s _ 32 (by decide) (by omega) hact
  have hactD : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      (7168 + 32 * (n - 1 - j)) 32) = s.activeWords :=
    Csub.activeWords_fix s _ 32 (by decide) (by omega) hact
  have hactT : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      (8256 + 32 * (n - 1 - j)) 32) = s.activeWords :=
    Csub.activeWords_fix s _ 32 (by decide) (by omega) hact
  simp (config := { maxSteps := 800000 })
    [blk2878, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      loopState, limbStep, fusedCsubPC1, hc7, hc8, hc9, hc10, hc11, hc12,
      hrun, hcode, h32, h1088, h8256, h8224, hA, hB, hM, hD, hnext, hTaddr, haddrT,
      hnextMod, hgt, haddrP, hAN, hBN, hMN, hDN, hnextN, hnextP,
      haddrA, haddrB, haddrM, h4079, h4079', hjump,
      jumpDest4665, hactA, hactB, hactM, hactD, hactT,
      UInt256.gt, UInt256.lt, UInt256.isTrue, State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt, List.exchange]

set_option linter.unusedSimpArgs false in
theorem run_loop_exit (s : State) (memory : ByteArray) (pa pb n j : Nat)
    (pd ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (_hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hact : 296 ≤ s.activeWords.toNat)
    (hj : j + 1 = n) (hn32 : n ≤ 32)
    (hpaFit : pa + 32 * n ≤ 9472) (hpbFit : pb + 32 * n ≤ 9472) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk2878
      (loopState s memory pa pb n j pd ret rest) =
      some (tailState s memory pa pb n (j + 1) pd ret rest) := by
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have h32 : (32 : UInt256) = UInt256.ofNat 32 := by decide
  have h1088 : (1088 : UInt256) = UInt256.ofNat 1088 := by decide
  have h8256 : (8256 : UInt256) = UInt256.ofNat 8256 := by decide
  have h8224 : (8224 : UInt256).toNat = 8224 := by decide
  have hA := ptr_add_addrDelta pa n j (by omega) hpaFit
  have hB := ptr_add_addrDelta pb n j (by omega) hpbFit
  have hM : UInt256.ofNat (8224 + 32 * (n - j)) - UInt256.ofNat 8256 =
      UInt256.ofNat (32 * (n - 1 - j)) := by
    rw [Challenge.EvmProof.Word.ofNat_sub_ofNat (by omega) (by omega)]
    congr 1
    omega
  have hD : UInt256.ofNat (8224 + 32 * (n - j)) - UInt256.ofNat 1088 =
      UInt256.ofNat (7168 + 32 * (n - 1 - j)) := by
    rw [Challenge.EvmProof.Word.ofNat_sub_ofNat (by omega) (by omega)]
    congr 1
    omega
  have hnext := ptr_sub_limb n j (by omega) hn32
  have hTaddr : 8224 + 32 * (n - j) = 8256 + 32 * (n - 1 - j) := by omega
  have haddrT : (8224 + 32 * (n - j)) % 2 ^ 256 =
      8256 + 32 * (n - 1 - j) := by rw [hTaddr, Nat.mod_eq_of_lt (by omega)]
  have hnextMod : (8224 + 32 * (n - (j + 1))) % 2 ^ 256 =
      8224 + 32 * (n - (j + 1)) := Nat.mod_eq_of_lt (by omega)
  have hngt : ¬8224 < 8224 + 32 * (n - (j + 1)) := by omega
  have h4143' : (4729 : UInt256) = UInt256.ofNat 4729 := by decide
  have haddrA : (pa + 32 * (n - 1 - j)) % 2 ^ 256 =
      pa + 32 * (n - 1 - j) := Nat.mod_eq_of_lt (by omega)
  have haddrB : (pb + 32 * (n - 1 - j)) % 2 ^ 256 =
      pb + 32 * (n - 1 - j) := Nat.mod_eq_of_lt (by omega)
  have haddrM : (32 * (n - 1 - j)) % 2 ^ 256 =
      32 * (n - 1 - j) := Nat.mod_eq_of_lt (by omega)
  have haddrP : (8256 + 32 * (n - 1 - j)) % 2 ^ 256 =
      8256 + 32 * (n - 1 - j) := Nat.mod_eq_of_lt (by omega)
  have h8256N : 8256 % 2 ^ 256 = 8256 := Nat.mod_eq_of_lt (by omega)
  have h1088N : 1088 % 2 ^ 256 = 1088 := Nat.mod_eq_of_lt (by omega)
  have h32N : 32 % 2 ^ 256 = 32 := Nat.mod_eq_of_lt (by omega)
  have hAN : (8256 + 32 * (n - 1 - j) + (addrDelta pa).toNat) % 2 ^ 256 =
      pa + 32 * (n - 1 - j) := by
    have hh := congrArg UInt256.toNat hA
    rw [hTaddr] at hh
    simpa only [Challenge.EvmProof.Word.word_toNat_add,
      Challenge.EvmProof.Word.word_toNat_ofNat, haddrP, haddrA] using hh
  have hBN : (8256 + 32 * (n - 1 - j) + (addrDelta pb).toNat) % 2 ^ 256 =
      pb + 32 * (n - 1 - j) := by
    have hh := congrArg UInt256.toNat hB
    rw [hTaddr] at hh
    simpa only [Challenge.EvmProof.Word.word_toNat_add,
      Challenge.EvmProof.Word.word_toNat_ofNat, haddrP, haddrB] using hh
  have hMN : (2 ^ 256 + (8256 + 32 * (n - 1 - j)) - 8256) % 2 ^ 256 =
      32 * (n - 1 - j) := by
    have hh := congrArg UInt256.toNat hM
    rw [hTaddr] at hh
    simpa only [Challenge.EvmProof.Word.word_toNat_sub,
      Challenge.EvmProof.Word.word_toNat_ofNat, haddrP, h8256N, haddrM] using hh
  have hDN : (2 ^ 256 + (8256 + 32 * (n - 1 - j)) - 1088) % 2 ^ 256 =
      7168 + 32 * (n - 1 - j) := by
    have hh := congrArg UInt256.toNat hD
    rw [hTaddr] at hh
    simpa only [Challenge.EvmProof.Word.word_toNat_sub,
      Challenge.EvmProof.Word.word_toNat_ofNat, haddrP, h1088N,
      Nat.mod_eq_of_lt (show 7168 + 32 * (n - 1 - j) < 2 ^ 256 by omega)] using hh
  have hnextN : (2 ^ 256 + (8256 + 32 * (n - 1 - j)) - 32) % 2 ^ 256 =
      8224 + 32 * (n - (j + 1)) := by
    have hh := congrArg UInt256.toNat hnext
    rw [hTaddr] at hh
    simpa only [Challenge.EvmProof.Word.word_toNat_sub,
      Challenge.EvmProof.Word.word_toNat_ofNat, haddrP, h32N, hnextMod] using hh
  have hnextP : UInt256.ofNat (8256 + 32 * (n - 1 - j)) - UInt256.ofNat 32 =
      UInt256.ofNat (8224 + 32 * (n - (j + 1))) := by
    rw [← hTaddr]
    exact hnext
  norm_num at haddrT hnextMod haddrA haddrB haddrM haddrP h8256N h1088N h32N hAN hBN hMN hDN hnextN
  have hactA : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      (pa + 32 * (n - 1 - j)) 32) = s.activeWords :=
    Csub.activeWords_fix s _ 32 (by decide) (by omega) hact
  have hactB : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      (pb + 32 * (n - 1 - j)) 32) = s.activeWords :=
    Csub.activeWords_fix s _ 32 (by decide) (by omega) hact
  have hactM : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      (32 * (n - 1 - j)) 32) = s.activeWords :=
    Csub.activeWords_fix s _ 32 (by decide) (by omega) hact
  have hactD : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      (7168 + 32 * (n - 1 - j)) 32) = s.activeWords :=
    Csub.activeWords_fix s _ 32 (by decide) (by omega) hact
  have hactT : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      (8256 + 32 * (n - 1 - j)) 32) = s.activeWords :=
    Csub.activeWords_fix s _ 32 (by decide) (by omega) hact
  simp (config := { maxSteps := 800000 })
    [blk2878, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      loopState, tailState, limbStep, fusedCsubPC1,
      hc7, hc8, hc9, hc10, hc11, hc12, hrun,
      h32, h1088, h8256, h8224, hA, hB, hM, hD, hnext, hTaddr, haddrT, hnextMod,
      haddrP, hAN, hBN, hMN, hDN, hnextN, hnextP,
      hngt, h4143',
      haddrA, haddrB, haddrM, hactA, hactB, hactM, hactD, hactT,
      UInt256.gt, UInt256.lt, UInt256.isTrue, State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt, List.exchange]

/-! ## Selection word and return block -/

theorem useSub_le_one (memory : ByteArray) (pa pb n j : Nat)
    (hcarry : (limbStep memory pa pb n j).carry.toNat ≤ 1) :
    (useSub memory pa pb n j).toNat ≤ 1 := by
  rw [useSub, Challenge.EvmProof.Word.word_toNat_lor]
  have hz : (UInt256.isZero (limbStep memory pa pb n j).borrow).toNat ≤ 1 := by
    rw [Challenge.EvmProof.Word.word_toNat_isZero]
    split <;> omega
  rw [Csub.or_of_le_one hcarry hz]
  omega

theorem resultSrc_toNat (memory : ByteArray) (pa pb n j : Nat)
    (huse : (useSub memory pa pb n j).toNat ≤ 1) :
    (resultSrc memory pa pb n j).toNat =
      if (useSub memory pa pb n j).toNat = 0 then 8256 else 7168 := by
  have h8256 : (8256 : UInt256).toNat = 8256 := by decide
  have h1088 : (1088 : UInt256).toNat = 1088 := by decide
  rw [resultSrc, Challenge.EvmProof.Word.word_toNat_sub_cond,
    Csub.word_toNat_mul, h8256, h1088]
  rcases Nat.lt_or_ge (useSub memory pa pb n j).toNat 1 with h | h
  · rw [show (useSub memory pa pb n j).toNat = 0 from by omega, if_pos rfl]
    norm_num
  · rw [show (useSub memory pa pb n j).toNat = 1 from by omega,
      if_neg (by norm_num)]
    norm_num

set_option linter.unusedSimpArgs false in
theorem run_tail (s : State) (memory : ByteArray) (pa pb n j : Nat)
    (pd ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hact : 296 ≤ s.activeWords.toNat) (hn : 2 ≤ n) (hn32 : n ≤ 32)
    (hjump : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode ret.toNat = true)
    (hs32 : MachineState.readWord (tnMemory memory pa pb n j) 9344 =
      UInt256.ofNat (32 * n))
    (hdstFit : pd.toNat + 32 * n ≤ 9472)
    (hcarry : (limbStep memory pa pb n j).carry.toNat ≤ 1) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk2933
      (tailState s memory pa pb n j pd ret rest) =
      some (returnedState s memory pa pb n j pd ret rest) := by
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have h8224 : (8224 : UInt256).toNat = 8224 := by decide
  have h9344 : (9344 : UInt256).toNat = 9344 := by decide
  have h4169 : (4755 : UInt256).toNat = 4755 := by decide
  have h4170 : (4756 : UInt256).toNat = 4756 := by decide
  have h4171 : (4757 : UInt256).toNat = 4757 := by decide
  have h4172 : (4758 : UInt256).toNat = 4758 := by decide
  have h4173 : (4759 : UInt256).toNat = 4759 := by decide
  have huse := useSub_le_one memory pa pb n j hcarry
  have hsrcFit : (resultSrc memory pa pb n j).toNat + 32 * n ≤ 9472 := by
    rw [resultSrc_toNat memory pa pb n j huse]
    split <;> omega
  have hsz : 32 * n % 2 ^ 256 = 32 * n := Nat.mod_eq_of_lt (by omega)
  have hs32N : (MachineState.readWord (tnMemory memory pa pb n j) 9344).toNat =
      32 * n := by
    rw [hs32, Challenge.EvmProof.Word.word_toNat_ofNat, hsz]
  have hs32U : (MachineState.readWord
      (MachineState.writeBytes (limbStep memory pa pb n j).memory
        (Data.Bytes.natToBytesPadded (limbStep memory pa pb n j).carry.toNat 32) 8224)
      9344).toNat = 32 * n := by
    simpa only [tnMemory] using hs32N
  have hactN : UInt256.ofNat
      (MachineState.activeWordsAfter s.activeWords.toNat 8224 32) = s.activeWords :=
    Csub.activeWords_fix s 8224 32 (by decide) (by omega) hact
  have hactS : UInt256.ofNat
      (MachineState.activeWordsAfter s.activeWords.toNat 9344 32) = s.activeWords :=
    Csub.activeWords_fix s 9344 32 (by decide) (by omega) hact
  have hactC1 : MachineState.activeWordsAfter s.activeWords.toNat pd.toNat (32 * n) =
      s.activeWords.toNat :=
    Csub.activeWordsAfter_fix s.activeWords.toNat pd.toNat (32 * n) (by omega)
      hdstFit hact
  have hactC2 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      (resultSrc memory pa pb n j).toNat (32 * n)) = s.activeWords :=
    Csub.activeWords_fix s _ (32 * n) (by omega) hsrcFit hact
  have hactC2N : MachineState.activeWordsAfter s.activeWords.toNat
      (resultSrc memory pa pb n j).toNat (32 * n) = s.activeWords.toNat :=
    Csub.activeWordsAfter_fix s.activeWords.toNat _ (32 * n) (by omega) hsrcFit hact
  have hsrcEq : (8256 : UInt256) - (1088 : UInt256) *
      UInt256.lor (limbStep memory pa pb n j).carry
        (UInt256.isZero (limbStep memory pa pb n j).borrow) =
      resultSrc memory pa pb n j := rfl
  simp (config := { maxSteps := 500000 })
    [blk2933, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      tailState, returnedState, tnMemory, hsrcEq, fusedCsubPC2,
      hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hrun, hcode, h8224,
      h9344, h4169, h4170, h4171, h4172, h4173, hjump, hs32, hs32N, hs32U, hsz,
      hactN, hactS, hactC1, hactC2, hactC2N,
      State.activeWordsAfterUInt256, State.activeWordsAfterUInt256_2,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt, List.exchange]
  all_goals exact (Challenge.EvmProof.Word.word_eq_ofNat_toNat s.activeWords).symm

/-! ## Flag and frame invariants -/

theorem flags_le_one (memory : ByteArray) (pa pb n : Nat) :
    ∀ j, j ≤ n →
      (limbStep memory pa pb n j).carry.toNat ≤ 1 ∧
      (limbStep memory pa pb n j).borrow.toNat ≤ 1 := by
  intro j
  induction j with
  | zero => intro _; simp [limbStep]
  | succ j ih =>
      intro hj
      obtain ⟨hc, hb⟩ := ih (by omega)
      let prev := limbStep memory pa pb n j
      let x := MachineState.readWord prev.memory (pa + 32 * (n - 1 - j))
      let y := MachineState.readWord prev.memory (pb + 32 * (n - 1 - j))
      let md := MachineState.readWord prev.memory (32 * (n - 1 - j))
      have hc1 : (UInt256.lt ((x + y) + prev.carry) (x + y)).toNat ≤ 1 := by
        rw [Challenge.EvmProof.Word.word_toNat_lt]
        split <;> omega
      have hc2 : (UInt256.lt (x + y) x).toNat ≤ 1 := by
        rw [Challenge.EvmProof.Word.word_toNat_lt]
        split <;> omega
      have hcarry :
          (UInt256.lor (UInt256.lt ((x + y) + prev.carry) (x + y))
            (UInt256.lt (x + y) x)).toNat ≤ 1 := by
        rw [Challenge.EvmProof.Word.word_toNat_lor, Csub.or_of_le_one hc1 hc2]
        omega
      let d1 := ((x + y) + prev.carry) - md
      let d2 := d1 - prev.borrow
      have hb1 : (UInt256.lt d1 d2).toNat ≤ 1 := by
        rw [Challenge.EvmProof.Word.word_toNat_lt]
        split <;> omega
      have hb2 : (UInt256.lt ((x + y) + prev.carry)
          (((x + y) + prev.carry) - md)).toNat ≤ 1 := by
        rw [Challenge.EvmProof.Word.word_toNat_lt]
        split <;> omega
      have hborrow :
          (UInt256.lor (UInt256.lt d1 d2)
            (UInt256.lt ((x + y) + prev.carry) d1)).toNat ≤ 1 := by
        rw [Challenge.EvmProof.Word.word_toNat_lor, Csub.or_of_le_one hb1 hb2]
        omega
      simpa only [limbStep, prev, x, y, d1, d2] using And.intro hcarry hborrow

/-- The fused walk writes only `SUBB` and `TS`. -/
theorem limbStep_readWord_disjoint (memory : ByteArray) (pa pb n addr : Nat)
    (hsub : addr + 32 ≤ 7168 ∨ 7168 + 32 * n ≤ addr)
    (hts : addr + 32 ≤ 8256 ∨ 8256 + 32 * n ≤ addr) :
    ∀ j, j ≤ n → MachineState.readWord (limbStep memory pa pb n j).memory addr =
      MachineState.readWord memory addr := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
      intro hj
      simp only [limbStep]
      rw [Csub.readWord_write_disjoint _ _ _ _ (by omega)]
      rw [Csub.readWord_write_disjoint _ _ _ _ (by omega)]
      exact ih (by omega)

theorem tnMemory_readWord_disjoint (memory : ByteArray) (pa pb n j addr : Nat)
    (hsub : addr + 32 ≤ 7168 ∨ 7168 + 32 * n ≤ addr)
    (hts : addr + 32 ≤ 8256 ∨ 8256 + 32 * n ≤ addr)
    (htn : addr + 32 ≤ 8224 ∨ 8256 ≤ addr) (hj : j ≤ n) :
    MachineState.readWord (tnMemory memory pa pb n j) addr =
      MachineState.readWord memory addr := by
  rw [tnMemory, Csub.readWord_write_disjoint _ _ _ _ htn]
  exact limbStep_readWord_disjoint memory pa pb n addr hsub hts j hj

/-! ## GasSteps certificates -/

def gasSteps_trampoline (s : State) (memory : ByteArray) (pa pb : Nat)
    (pd ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (Csub.amEntryState s memory pa pb pd ret rest)
      (entryState s memory pa pb pd ret rest) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka blk1600
    (by simpa [Csub.amEntryState, Artifact.submissionArtifact] using hcode)
    (by simpa [Csub.amEntryState, State.fork] using hfork)
    (run_trampoline s memory pa pb pd ret rest hcap hrun hcode)
    (by simpa [Csub.amEntryState] using hrun)
    (by simpa [Csub.amEntryState, State.fork] using hnp)

def gasSteps_entry (s : State) (memory : ByteArray) (pa pb n : Nat)
    (pd ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat)
    (htl : MachineState.readWord memory 9440 = UInt256.ofNat (8224 + 32 * n)) :
    Challenge.EvmProof.GasSteps (entryState s memory pa pb pd ret rest)
      (loopState s memory pa pb n 0 pd ret rest) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka blk2862
    (by simpa [entryState, Artifact.submissionArtifact] using hcode)
    (by simpa [entryState, State.fork] using hfork)
    (run_entry s memory pa pb n pd ret rest hcap hrun hact htl)
    (by simpa [entryState] using hrun)
    (by simpa [entryState, State.fork] using hnp)

def gasSteps_iteration (s : State) (memory : ByteArray) (pa pb n j : Nat)
    (pd ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat) (hj : j + 1 < n) (hn32 : n ≤ 32)
    (hpaFit : pa + 32 * n ≤ 9472) (hpbFit : pb + 32 * n ≤ 9472) :
    Challenge.EvmProof.GasSteps (loopState s memory pa pb n j pd ret rest)
      (loopState s memory pa pb n (j + 1) pd ret rest) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka blk2878
    (by simpa [loopState, Artifact.submissionArtifact] using hcode)
    (by simpa [loopState, State.fork] using hfork)
    (run_loop_body s memory pa pb n j pd ret rest hcap hrun hcode hact hj hn32
      hpaFit hpbFit)
    (by simpa [loopState] using hrun)
    (by simpa [loopState, State.fork] using hnp)

def gasSteps_loop (s : State) (memory : ByteArray) (pa pb n : Nat)
    (pd ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat) (hn : 2 ≤ n) (hn32 : n ≤ 32)
    (hpaFit : pa + 32 * n ≤ 9472) (hpbFit : pb + 32 * n ≤ 9472) :
    Challenge.EvmProof.GasSteps (loopState s memory pa pb n 0 pd ret rest)
      (loopState s memory pa pb n (n - 1) pd ret rest) := by
  exact Challenge.EvmProof.GasSteps.iterateBounded (n - 1) fun i hi =>
    gasSteps_iteration s memory pa pb n i pd ret rest hcap hcode hfork hrun hnp hact
      (by omega) hn32 hpaFit hpbFit

def gasSteps_exit (s : State) (memory : ByteArray) (pa pb n : Nat)
    (pd ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat) (hn : 2 ≤ n) (hn32 : n ≤ 32)
    (hpaFit : pa + 32 * n ≤ 9472) (hpbFit : pb + 32 * n ≤ 9472) :
    Challenge.EvmProof.GasSteps (loopState s memory pa pb n (n - 1) pd ret rest)
      (tailState s memory pa pb n (n - 1 + 1) pd ret rest) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka blk2878
    (by simpa [loopState, Artifact.submissionArtifact] using hcode)
    (by simpa [loopState, State.fork] using hfork)
    (run_loop_exit s memory pa pb n (n - 1) pd ret rest hcap hrun hcode hact
      (by omega) hn32 hpaFit hpbFit)
    (by simpa [loopState] using hrun)
    (by simpa [loopState, State.fork] using hnp)

def gasSteps_tail (s : State) (memory : ByteArray) (pa pb n j : Nat)
    (pd ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat) (hn : 2 ≤ n) (hn32 : n ≤ 32)
    (hjump : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode ret.toNat = true)
    (hs32 : MachineState.readWord (tnMemory memory pa pb n j) 9344 =
      UInt256.ofNat (32 * n))
    (hdstFit : pd.toNat + 32 * n ≤ 9472)
    (hcarry : (limbStep memory pa pb n j).carry.toNat ≤ 1) :
    Challenge.EvmProof.GasSteps (tailState s memory pa pb n j pd ret rest)
      (returnedState s memory pa pb n j pd ret rest) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka blk2933
    (by simpa [tailState, Artifact.submissionArtifact] using hcode)
    (by simpa [tailState, State.fork] using hfork)
    (run_tail s memory pa pb n j pd ret rest hcap hrun hcode hact hn hn32 hjump hs32
      hdstFit hcarry)
    (by simpa [tailState] using hrun)
    (by simpa [tailState, State.fork] using hnp)

end Challenge.Modexp.Submission.Proofs.Fast.FusedCsub
