import Challenge.Modexp.Submission.Proofs.Fast.CompactConstants
import Challenge.Modexp.Submission.Proofs.Fast.CsubModel
import Challenge.Modexp.Submission.Proofs.Fast.CsubAffineStep
import Challenge.Modexp.Submission.Proofs.Fast.CsubPairsBlocks
import Challenge.Modexp.Submission.Proofs.Fast.Model
import Challenge.Modexp.Submission.Proofs.Fast.Paths.P11
import Challenge.Modexp.Submission.Proofs.Fast.Paths.P12
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-!
# The `ADDMOD` and `CSUB` subroutines of the appended Montgomery path

`ADDMOD` occupies instruction indices 1600..1666 (pc 2224..2308) and `CSUB`
indices 1667..1741 (pc 2309..2500); `ADDMOD` falls through into `CSUB`.

`ADDMOD` is entered with stack `[pa, pb, pd, ret]`.  It adds the `n`-limb
big-endian blocks at `pa` and `pb` limb by limb from the least significant
limb upwards into the CIOS `t` area, stores the carry-out at `TN = 0x2020`
and falls into `CSUB`.

`CSUB` is entered with stack `[pd, ret]` and the value
`t = t[n] * radix ^ n + t_low` held as `t[n]` at `TN` and `t_low` in the
`n`-limb block at `TS = 0x2040`.  It computes `t - m` with borrow
propagation into `SUBB = 0x1C00`, selects `SUBB` when `t ≥ m` and `TS`
otherwise without branching, `MCOPY`s `32 * n` bytes to `pd`, and jumps to
`ret`.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.Csub

attribute [local simp]
  CompactConstants.notThirtyOne CompactConstants.not1087

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Fast.CsubAffineStep

/-! ## Pointer arithmetic

Every loop pointer walks downwards by one limb per iteration.  The EVM adds
the wrapped constant `2 ^ 256 - 32`, so the `j`-th pointer of a walk starting
at `base` is `UInt256.ofNat (ptrAt base j)`; `ptrAt` needs no side condition
because `UInt256.ofNat` already reduces modulo `2 ^ 256`. -/
def ptrAt (base j : Nat) : Nat :=
  base + j * 115792089237316195423570985008687907853269984665640564039457584007913129639904

@[simp] theorem ptrAt_zero (base : Nat) : ptrAt base 0 = base := by
  simp [ptrAt]

/-- One downward step, in the shape the `PUSH32 (2 ^ 256 - 32); ADD` pair
produces. -/
theorem ptrAt_succ (base j : Nat) :
    115792089237316195423570985008687907853269984665640564039457584007913129639904 +
        ptrAt base j = ptrAt base (j + 1) := by
  simp only [ptrAt, Nat.succ_mul]
  omega

/-- The address a downward pointer walk has reached, as long as it has not
yet stepped below the base of the block. -/
theorem ptrAt_toNat (base j : Nat) (hj : 32 * j ≤ base) (hbase : base < 2 ^ 256) :
    (UInt256.ofNat (ptrAt base j)).toNat = base - 32 * j := by
  rw [Challenge.EvmProof.Word.word_toNat_ofNat, ptrAt]
  have hlit : (115792089237316195423570985008687907853269984665640564039457584007913129639904 :
      Nat) = 2 ^ 256 - 32 := by norm_num
  have hmul : j * 115792089237316195423570985008687907853269984665640564039457584007913129639904
      = j * 2 ^ 256 - 32 * j := by
    rw [hlit, Nat.mul_sub, Nat.mul_comm j 32]
  rw [hmul]
  have hrewrite : base + (j * 2 ^ 256 - 32 * j) = (base - 32 * j) + j * 2 ^ 256 := by
    have : 32 * j ≤ j * 2 ^ 256 := by
      have := Nat.mul_le_mul_right j (show 32 ≤ 2 ^ 256 by norm_num)
      omega
    omega
  rw [hrewrite, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]

/-! ## Basic blocks -/





/-! ## Memory progression of the `ADDMOD` limb loop (pure model lives in
`CsubModel`; the concrete `ADDMOD` trace below is unchanged). -/

/-! ## Active words (fix lemmas live in `CsubModel`). -/

/-! ## States at the `ADDMOD` block boundaries -/

/-- Subroutine entry (pc 2224) with stack `[pa, pb, pd, ret]`. -/
def amEntryState (s : State) (memory : ByteArray) (pa pb : Nat)
    (pd ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 2142
           stack := [UInt256.ofNat pa, UInt256.ofNat pb, pd, ret] ++ rest
           memory := memory }

/-- The `ADDMOD` loop head (pc 2257) after `j` limb steps. -/
def amLoopState (s : State) (memory : ByteArray) (pa pb n j : Nat)
    (pd ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 2173
           stack := [UInt256.ofNat (ptrAt (8224 + 32 * n) j),
                     UInt256.ofNat (ptrAt (pa + 32 * n - 32) j),
                     UInt256.ofNat (ptrAt (pb + 32 * n - 32) j),
                     (amStep memory pa pb n j).flag, pd, ret] ++ rest
           memory := (amStep memory pa pb n j).memory }

set_option linter.unusedSimpArgs false in
theorem run_amEntry (s : State) (memory : ByteArray) (pa pb n : Nat)
    (pd ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hact : 296 ≤ s.activeWords.toNat)
    (hn : 2 ≤ n) (hpa : 32 ≤ pa) (hpaFit : pa + 32 * n ≤ 9472)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * n ≤ 9472)
    (hs32 : MachineState.readWord memory 9344 = UInt256.ofNat (32 * n))
    (htl : MachineState.readWord memory 9440 = UInt256.ofNat (8224 + 32 * n)) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk1600
      (amEntryState s memory pa pb pd ret rest) =
      some (amLoopState s memory pa pb n 0 pd ret rest) := by
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have h32 : (32 : UInt256) = UInt256.ofNat 32 := by decide
  have h9344 : (9344 : UInt256).toNat = 9344 := by decide
  have h9440 : (9440 : UInt256).toNat = 9440 := by decide
  have hzero : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hactA : UInt256.ofNat
      (MachineState.activeWordsAfter s.activeWords.toNat 9344 32) =
      s.activeWords := activeWords_fix s 9344 32 (by decide) (by omega) hact
  have hactB : UInt256.ofNat
      (MachineState.activeWordsAfter s.activeWords.toNat 9440 32) =
      s.activeWords := activeWords_fix s 9440 32 (by decide) (by omega) hact
  have hsuba : UInt256.ofNat (pa + 32 * n) - UInt256.ofNat 32 =
      UInt256.ofNat (pa + 32 * n - 32) :=
    Challenge.EvmProof.Word.ofNat_sub_ofNat (by omega) (by omega)
  have hsubb : UInt256.ofNat (pb + 32 * n) - UInt256.ofNat 32 =
      UInt256.ofNat (pb + 32 * n - 32) :=
    Challenge.EvmProof.Word.ofNat_sub_ofNat (by omega) (by omega)
  simp (config := { maxSteps := 800000 })
    [blk1600, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      amEntryState, amLoopState, amStep, fastPC15, fastPC16,
      hc4, hc5, hc6, hc7, hc8, hrun, h32, h9344, h9440, hzero,
      hs32, htl, hactA, hactB, hsuba, hsubb,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      List.exchange]



/-! ### The `ADDMOD` limb loop -/

/-- `ptrAt` in the shape `simp` leaves a `UInt256.toNat` in. -/
theorem ptrAt_mod (base j : Nat) (hj : 32 * j ≤ base) (hbase : base < 2 ^ 256) :
    ptrAt base j %
        115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      base - 32 * j := by
  have hlit : (115792089237316195423570985008687907853269984665640564039457584007913129639936 :
      Nat) = 2 ^ 256 := by norm_num
  rw [hlit, ← Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ptrAt_toNat base j hj hbase

set_option linter.unusedSimpArgs false in
theorem run_amLoopBody (s : State) (memory : ByteArray) (pa pb n j : Nat)
    (pd ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hact : 296 ≤ s.activeWords.toNat)
    (hj : j + 1 < n) (hn32 : n ≤ 32)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * n ≤ 9472)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * n ≤ 9472) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk1627
      (amLoopState s memory pa pb n j pd ret rest) =
      some (amLoopState s memory pa pb n (j + 1) pd ret rest) := by
  have hbig : (9472 : Nat) < 2 ^ 256 := by norm_num
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hK : (115792089237316195423570985008687907853269984665640564039457584007913129639904 :
      UInt256) = UInt256.ofNat
        115792089237316195423570985008687907853269984665640564039457584007913129639904 := by
    decide
  have h8224 : (8224 : UInt256).toNat = 8224 := by decide
  have h2500 : (2173 : UInt256).toNat = 2173 := by decide
  have h2500' : (2173 : UInt256) = UInt256.ofNat 2173 := by decide
  have hjump : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode
      (2173 : UInt256).toNat = true := by
    rw [h2500]; exact jumpDest2500
  have hta : ptrAt (pa + 32 * n - 32) j %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      pa + 32 * (n - 1 - j) := by
    rw [ptrAt_mod _ _ (by omega) (by omega)]; omega
  have htb : ptrAt (pb + 32 * n - 32) j %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      pb + 32 * (n - 1 - j) := by
    rw [ptrAt_mod _ _ (by omega) (by omega)]; omega
  have htt : ptrAt (8224 + 32 * n) j %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      8256 + 32 * (n - 1 - j) := by
    rw [ptrAt_mod _ _ (by omega) (by omega)]; omega
  have hnext : ptrAt (8224 + 32 * n) (j + 1) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      8224 + 32 * (n - 1 - j) := by
    rw [ptrAt_mod _ _ (by omega) (by omega)]; omega
  have hgt : 8224 < 8224 + 32 * (n - 1 - j) := by omega
  have hactA : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      (pa + 32 * (n - 1 - j)) 32) = s.activeWords :=
    activeWords_fix s _ 32 (by decide) (by omega) hact
  have hactB : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      (pb + 32 * (n - 1 - j)) 32) = s.activeWords :=
    activeWords_fix s _ 32 (by decide) (by omega) hact
  have hactT : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      (8256 + 32 * (n - 1 - j)) 32) = s.activeWords :=
    activeWords_fix s _ 32 (by decide) (by omega) hact
  simp (config := { maxSteps := 400000 })
    [blk1627, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      amLoopState, amStep, fastPC16, fastPC17,
      hc6, hc7, hc8, hc9, hrun, hcode, hK, h8224, h2500, h2500', hjump, jumpDest2500,
      hta, htb, htt, hnext, hgt, hactA, hactB, hactT, ptrAt_succ,
      UInt256.gt, UInt256.isTrue,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      List.exchange]


/-- The `ADDMOD` loop exit (pc 2635): the loop has run `n` times and the three
pointers plus the carry are still on the stack. -/
def amTailState (s : State) (memory : ByteArray) (pa pb n j : Nat)
    (pd ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 2218
           stack := [UInt256.ofNat (ptrAt (8224 + 32 * n) j),
                     UInt256.ofNat (ptrAt (pa + 32 * n - 32) j),
                     UInt256.ofNat (ptrAt (pb + 32 * n - 32) j),
                     (amStep memory pa pb n j).flag, pd, ret] ++ rest
           memory := (amStep memory pa pb n j).memory }

/- `csEntryState` lives in `CsubModel` (reused by the affine trace). -/

set_option linter.unusedSimpArgs false in
theorem run_amLoopExit (s : State) (memory : ByteArray) (pa pb n j : Nat)
    (pd ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (_hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hact : 296 ≤ s.activeWords.toNat)
    (hj : j + 1 = n) (hn32 : n ≤ 32)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * n ≤ 9472)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * n ≤ 9472) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk1627
      (amLoopState s memory pa pb n j pd ret rest) =
      some (amTailState s memory pa pb n (j + 1) pd ret rest) := by
  have hbig : (9472 : Nat) < 2 ^ 256 := by norm_num
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hnj : n - 1 - j = 0 := by omega
  have hK : (115792089237316195423570985008687907853269984665640564039457584007913129639904 :
      UInt256) = UInt256.ofNat
        115792089237316195423570985008687907853269984665640564039457584007913129639904 := by
    decide
  have h8224 : (8224 : UInt256).toNat = 8224 := by decide
  have hta : ptrAt (pa + 32 * n - 32) j %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      pa + 32 * (n - 1 - j) := by
    rw [ptrAt_mod _ _ (by omega) (by omega)]; omega
  have htb : ptrAt (pb + 32 * n - 32) j %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      pb + 32 * (n - 1 - j) := by
    rw [ptrAt_mod _ _ (by omega) (by omega)]; omega
  have htt : ptrAt (8224 + 32 * n) j %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      8256 + 32 * (n - 1 - j) := by
    rw [ptrAt_mod _ _ (by omega) (by omega)]; omega
  have hnext : ptrAt (8224 + 32 * n) (j + 1) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      8224 + 32 * (n - 1 - j) := by
    rw [ptrAt_mod _ _ (by omega) (by omega)]; omega
  have hactA : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat pa 32) =
      s.activeWords := activeWords_fix s pa 32 (by decide) (by omega) hact
  have hactB : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat pb 32) =
      s.activeWords := activeWords_fix s pb 32 (by decide) (by omega) hact
  have hactT : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 8256 32) =
      s.activeWords := activeWords_fix s 8256 32 (by decide) (by omega) hact
  simp (config := { maxSteps := 400000 })
    [blk1627, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      amLoopState, amTailState, amStep, fastPC16, fastPC17,
      hc6, hc7, hc8, hc9, hrun, hK, h8224, hnj,
      hta, htb, htt, hnext, hactA, hactB, hactT, ptrAt_succ,
      UInt256.gt, UInt256.isTrue,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      List.exchange]

set_option linter.unusedSimpArgs false in
theorem run_amTail (s : State) (memory : ByteArray) (pa pb n j : Nat)
    (pd ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hact : 296 ≤ s.activeWords.toNat) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk1662
      (amTailState s memory pa pb n j pd ret rest) =
      some (csEntryState s
        (MachineState.writeBytes (amStep memory pa pb n j).memory
          (Data.Bytes.natToBytesPadded (amStep memory pa pb n j).flag.toNat 32) 8224)
        pd ret rest) := by
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have h8224 : (8224 : UInt256).toNat = 8224 := by decide
  have hactT : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 8224 32) =
      s.activeWords := activeWords_fix s 8224 32 (by decide) (by omega) hact
  simp (config := { maxSteps := 400000 })
    [blk1662, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      amTailState, csEntryState, fastPC17,
      hc2, hc3, hc4, hc5, hc6, hrun, h8224, hactT,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      List.exchange]


/-! ## The `CSUB` subroutine -/




/- `csStep` pure model lives in `CsubModel`. -/

/-! ## The `CSUB` execution trace (located affine bindings)

The superseded three-pointer execution lemmas are removed; the live trace uses
`affineLoopState` / `affineGuardExitState` with the located transitions in
`CsubAffineLocations`, composed as `GasSteps` below. -/

/-! ## Partial limb values -/

/-- The value of the low `j` limbs of the `n`-limb big-endian block at `ptr`
(limb `k` sits at `ptr + 32 * (n - 1 - k)`). -/
def lowValue (memory : ByteArray) (ptr n j : Nat) : Nat :=
  Nat.ofDigits Limbs.radix ((List.range j).map fun k =>
    (MachineState.readWord memory (ptr + 32 * (n - 1 - k))).toNat)

@[simp] theorem lowValue_zero (memory : ByteArray) (ptr n : Nat) :
    lowValue memory ptr n 0 = 0 := by
  simp [lowValue]

theorem lowValue_succ (memory : ByteArray) (ptr n j : Nat) :
    lowValue memory ptr n (j + 1) =
      lowValue memory ptr n j +
        (MachineState.readWord memory (ptr + 32 * (n - 1 - j))).toNat *
          Limbs.radix ^ j := by
  simp only [lowValue, List.range_succ, List.map_append, List.map_cons,
    List.map_nil, Nat.ofDigits_append, List.length_map, List.length_range,
    Nat.ofDigits_singleton]
  ring

theorem lowValue_full (memory : ByteArray) (ptr n : Nat) :
    lowValue memory ptr n n =
      Nat.ofDigits Limbs.radix (Model.fastLimbs memory ptr n) := rfl

theorem lowValue_congr {a b : ByteArray} {ptr n j : Nat}
    (h : ∀ k, k < j → MachineState.readWord a (ptr + 32 * (n - 1 - k)) =
      MachineState.readWord b (ptr + 32 * (n - 1 - k))) :
    lowValue a ptr n j = lowValue b ptr n j := by
  unfold lowValue
  congr 1
  apply List.map_congr_left
  intro k hk
  rw [h k (by simpa using hk)]

theorem lowValue_lt (memory : ByteArray) (ptr n j : Nat) :
    lowValue memory ptr n j < Limbs.radix ^ j := by
  have hdigits : ∀ d ∈ (List.range j).map (fun k =>
      (MachineState.readWord memory (ptr + 32 * (n - 1 - k))).toNat),
      d < Limbs.radix := by
    intro d hd
    simp only [List.mem_map] at hd
    rcases hd with ⟨k, _, rfl⟩
    exact (MachineState.readWord memory (ptr + 32 * (n - 1 - k))).val.isLt
  have h := Nat.ofDigits_lt_base_pow_length Limbs.radix_gt_one hdigits
  simpa [lowValue] using h

/-- A block always represents the value of its own limbs. -/
theorem fastRepresents_lowValue (memory : ByteArray) (ptr n : Nat) :
    Model.FastRepresents memory ptr n (lowValue memory ptr n n) :=
  (Model.fastRepresents_iff_value (lowValue_lt memory ptr n n)).2
    (lowValue_full memory ptr n).symm

/-! ## The limb steps -/

/- `or_of_le_one` lives in `CsubModel`. -/

/-- One `ADDMOD` limb: the stored word and the two overflow tests realise the
three-term natural sum with its carry. -/
theorem addLimb_spec (x y c : UInt256) (hc : c.toNat ≤ 1) :
    (c + (x + y)).toNat + Limbs.radix *
        (UInt256.lor (UInt256.lt (c + (x + y)) c) (UInt256.lt (x + y) x)).toNat =
      x.toNat + y.toNat + c.toNat ∧
    (UInt256.lor (UInt256.lt (c + (x + y)) c) (UInt256.lt (x + y) x)).toNat ≤ 1 := by
  have hx : x.toNat < 2 ^ 256 := x.val.isLt
  have hy : y.toNat < 2 ^ 256 := y.val.isLt
  have h1 : (UInt256.lt (c + (x + y)) c).toNat ≤ 1 := by
    rw [Challenge.EvmProof.Word.word_toNat_lt]
    split <;> omega
  have h2 : (UInt256.lt (x + y) x).toNat ≤ 1 := by
    rw [Challenge.EvmProof.Word.word_toNat_lt]
    split <;> omega
  rw [Challenge.EvmProof.Word.word_toNat_lor, or_of_le_one h1 h2]
  simp only [Challenge.EvmProof.Word.word_toNat_lt,
    Challenge.EvmProof.Word.word_toNat_add, Limbs.radix]
  constructor
  · split_ifs <;> omega
  · split_ifs <;> omega

/-- One `CSUB` limb: the stored word and the two borrow tests realise the
three-term natural difference with its borrow. -/
theorem subLimb_spec (x y b : UInt256) (hb : b.toNat ≤ 1) :
    (x - y - b).toNat + y.toNat + b.toNat =
      x.toNat + Limbs.radix *
        (UInt256.lor (UInt256.lt x y) (UInt256.lt (x - y) b)).toNat ∧
    (UInt256.lor (UInt256.lt x y) (UInt256.lt (x - y) b)).toNat ≤ 1 := by
  have hx : x.toNat < 2 ^ 256 := x.val.isLt
  have hy : y.toNat < 2 ^ 256 := y.val.isLt
  have h1 : (UInt256.lt x y).toNat ≤ 1 := by
    rw [Challenge.EvmProof.Word.word_toNat_lt]
    split <;> omega
  have h2 : (UInt256.lt (x - y) b).toNat ≤ 1 := by
    rw [Challenge.EvmProof.Word.word_toNat_lt]
    split <;> omega
  rw [Challenge.EvmProof.Word.word_toNat_lor, or_of_le_one h1 h2]
  simp only [Challenge.EvmProof.Word.word_toNat_lt,
    Challenge.EvmProof.Word.word_toNat_sub_cond, Limbs.radix]
  constructor
  · split_ifs <;> omega
  · split_ifs <;> omega

/-- A 32-byte write outside a 32-byte read window is invisible. -/
theorem readWord_write_disjoint (memory : ByteArray) (w addr wr : Nat)
    (hdisj : addr + 32 ≤ wr ∨ wr + 32 ≤ addr) :
    MachineState.readWord (MachineState.writeBytes memory
      (Data.Bytes.natToBytesPadded w 32) wr) addr =
      MachineState.readWord memory addr := by
  apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
  rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  exact hdisj


/-! ## The `ADDMOD` loop invariant -/

/-- The algebraic core of one carry step. -/
theorem am_algebra (L A B P R T F xa xb c : Nat)
    (hlimb : T + R * F = xa + xb + c) (hinv : L + c * P = A + B) :
    L + T * P + F * (P * R) = A + xa * P + (B + xb * P) := by
  have h1 : L + T * P + F * (P * R) = L + (T + R * F) * P := by ring
  rw [h1, hlimb]
  have h2 : L + (xa + xb + c) * P = L + c * P + (xa * P + xb * P) := by ring
  rw [h2, hinv]
  ring

/-- The algebraic core of one borrow step. -/
theorem cs_algebra (D M T P R d2 md t b F : Nat)
    (hlimb : d2 + md + b = t + R * F) (hinv : D + M = T + b * P) :
    D + d2 * P + (M + md * P) = T + t * P + F * (P * R) := by
  have h1 : D + d2 * P + (M + md * P) = D + M + (d2 + md) * P := by ring
  rw [h1, hinv]
  have h2 : T + b * P + (d2 + md) * P = T + (d2 + md + b) * P := by ring
  rw [h2, hlimb]
  ring

/-- The `ADDMOD` loop only writes into the `t` block. -/
theorem amStep_readWord_disjoint (memory : ByteArray) (pa pb n addr : Nat)
    (_hn : 1 ≤ n) (hdisj : addr + 32 ≤ 8256 ∨ 8256 + 32 * n ≤ addr) :
    ∀ j, j ≤ n → MachineState.readWord (amStep memory pa pb n j).memory addr =
      MachineState.readWord memory addr := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
      intro hj
      have hstep : MachineState.readWord (amStep memory pa pb n (j + 1)).memory addr =
          MachineState.readWord (amStep memory pa pb n j).memory addr := by
        simp only [amStep]
        exact readWord_write_disjoint _ _ _ _ (by omega)
      rw [hstep, ih (by omega)]

/-- Step `j` does not disturb the limbs below `j`. -/
theorem amStep_lowValue_stable (memory : ByteArray) (pa pb n j : Nat) (hj : j < n) :
    lowValue (amStep memory pa pb n (j + 1)).memory 8256 n j =
      lowValue (amStep memory pa pb n j).memory 8256 n j := by
  apply lowValue_congr
  intro k hk
  simp only [amStep]
  exact readWord_write_disjoint _ _ _ _ (by omega)

theorem amStep_readWord_new (memory : ByteArray) (pa pb n j : Nat) :
    MachineState.readWord (amStep memory pa pb n (j + 1)).memory
        (8256 + 32 * (n - 1 - j)) =
      (amStep memory pa pb n j).flag +
        (MachineState.readWord (amStep memory pa pb n j).memory (pa + 32 * (n - 1 - j)) +
          MachineState.readWord (amStep memory pa pb n j).memory
            (pb + 32 * (n - 1 - j))) := by
  simp only [amStep]
  exact Challenge.EvmProof.Memory.readWord_writeWord _ _ _

theorem amStep_flag_succ (memory : ByteArray) (pa pb n j : Nat) :
    (amStep memory pa pb n (j + 1)).flag =
      UInt256.lor
        (UInt256.lt ((amStep memory pa pb n j).flag +
          (MachineState.readWord (amStep memory pa pb n j).memory (pa + 32 * (n - 1 - j)) +
            MachineState.readWord (amStep memory pa pb n j).memory (pb + 32 * (n - 1 - j))))
          (amStep memory pa pb n j).flag)
        (UInt256.lt
          (MachineState.readWord (amStep memory pa pb n j).memory (pa + 32 * (n - 1 - j)) +
            MachineState.readWord (amStep memory pa pb n j).memory (pb + 32 * (n - 1 - j)))
          (MachineState.readWord (amStep memory pa pb n j).memory
            (pa + 32 * (n - 1 - j)))) := by
  simp only [amStep]

/-- The carry-propagating addition invariant:
`Σ_{k<j} a[k] rad^k + Σ_{k<j} b[k] rad^k = Σ_{k<j} t[k] rad^k + carry · rad^j`
with `carry ∈ {0, 1}`. -/
theorem amStep_invariant (memory : ByteArray) (pa pb n : Nat)
    (hn : 1 ≤ n) (hpa : pa + 32 * n ≤ 8256) (hpb : pb + 32 * n ≤ 8256) :
    ∀ j, j ≤ n →
      lowValue (amStep memory pa pb n j).memory 8256 n j +
            (amStep memory pa pb n j).flag.toNat * Limbs.radix ^ j =
          lowValue memory pa n j + lowValue memory pb n j ∧
        (amStep memory pa pb n j).flag.toNat ≤ 1 := by
  intro j
  induction j with
  | zero => intro _; simp [amStep]
  | succ j ih =>
      intro hj
      obtain ⟨ihEq, ihLe⟩ := ih (by omega)
      have hxa : MachineState.readWord (amStep memory pa pb n j).memory
          (pa + 32 * (n - 1 - j)) =
          MachineState.readWord memory (pa + 32 * (n - 1 - j)) :=
        amStep_readWord_disjoint memory pa pb n _ hn (by omega) j (by omega)
      have hxb : MachineState.readWord (amStep memory pa pb n j).memory
          (pb + 32 * (n - 1 - j)) =
          MachineState.readWord memory (pb + 32 * (n - 1 - j)) :=
        amStep_readWord_disjoint memory pa pb n _ hn (by omega) j (by omega)
      have hlimb := addLimb_spec (MachineState.readWord memory (pa + 32 * (n - 1 - j)))
        (MachineState.readWord memory (pb + 32 * (n - 1 - j)))
        (amStep memory pa pb n j).flag ihLe
      rw [lowValue_succ (amStep memory pa pb n (j + 1)).memory 8256 n j,
        amStep_lowValue_stable memory pa pb n j (by omega),
        amStep_readWord_new, amStep_flag_succ,
        lowValue_succ memory pa n j, lowValue_succ memory pb n j, pow_succ]
      simp only [hxa, hxb]
      exact ⟨am_algebra _ _ _ _ _ _ _ _ _ _ hlimb.1 ihEq, hlimb.2⟩

/-! ## The `CSUB` loop invariant -/

/-- The `CSUB` loop only writes into the `SUBB` block. -/
theorem csStep_readWord_disjoint (memory : ByteArray) (n addr : Nat)
    (_hn : 1 ≤ n) (hdisj : addr + 32 ≤ 7168 ∨ 7168 + 32 * n ≤ addr) :
    ∀ j, j ≤ n → MachineState.readWord (csStep memory n j).memory addr =
      MachineState.readWord memory addr := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
      intro hj
      have hstep : MachineState.readWord (csStep memory n (j + 1)).memory addr =
          MachineState.readWord (csStep memory n j).memory addr := by
        simp only [csStep]
        exact readWord_write_disjoint _ _ _ _ (by omega)
      rw [hstep, ih (by omega)]

theorem csStep_lowValue_stable (memory : ByteArray) (n j : Nat) (hj : j < n) :
    lowValue (csStep memory n (j + 1)).memory 7168 n j =
      lowValue (csStep memory n j).memory 7168 n j := by
  apply lowValue_congr
  intro k hk
  simp only [csStep]
  exact readWord_write_disjoint _ _ _ _ (by omega)

theorem csStep_readWord_new (memory : ByteArray) (n j : Nat) :
    MachineState.readWord (csStep memory n (j + 1)).memory (7168 + 32 * (n - 1 - j)) =
      MachineState.readWord (csStep memory n j).memory (8256 + 32 * (n - 1 - j)) -
        MachineState.readWord (csStep memory n j).memory (32 * (n - 1 - j)) -
        (csStep memory n j).flag := by
  simp only [csStep]
  exact Challenge.EvmProof.Memory.readWord_writeWord _ _ _

theorem csStep_flag_succ (memory : ByteArray) (n j : Nat) :
    (csStep memory n (j + 1)).flag =
      UInt256.lor
        (UInt256.lt (MachineState.readWord (csStep memory n j).memory (8256 + 32 * (n - 1 - j)))
          (MachineState.readWord (csStep memory n j).memory (32 * (n - 1 - j))))
        (UInt256.lt
          (MachineState.readWord (csStep memory n j).memory (8256 + 32 * (n - 1 - j)) -
            MachineState.readWord (csStep memory n j).memory (32 * (n - 1 - j)))
          (csStep memory n j).flag) := by
  simp only [csStep]

/-- The borrow-propagating subtraction invariant:
`Σ_{k<j} d[k] rad^k + Σ_{k<j} m[k] rad^k = Σ_{k<j} t_low[k] rad^k + borrow · rad^j`
with `borrow ∈ {0, 1}`. -/
theorem csStep_invariant (memory : ByteArray) (n : Nat) (hn : 1 ≤ n) (hn32 : n ≤ 32) :
    ∀ j, j ≤ n →
      lowValue (csStep memory n j).memory 7168 n j + lowValue memory 0 n j =
          lowValue memory 8256 n j +
            (csStep memory n j).flag.toNat * Limbs.radix ^ j ∧
        (csStep memory n j).flag.toNat ≤ 1 := by
  intro j
  induction j with
  | zero => intro _; simp [csStep]
  | succ j ih =>
      intro hj
      obtain ⟨ihEq, ihLe⟩ := ih (by omega)
      have hxt : MachineState.readWord (csStep memory n j).memory
          (8256 + 32 * (n - 1 - j)) =
          MachineState.readWord memory (8256 + 32 * (n - 1 - j)) :=
        csStep_readWord_disjoint memory n _ hn (by omega) j (by omega)
      have hxm : MachineState.readWord (csStep memory n j).memory (32 * (n - 1 - j)) =
          MachineState.readWord memory (32 * (n - 1 - j)) :=
        csStep_readWord_disjoint memory n _ hn (by omega) j (by omega)
      have hlimb := subLimb_spec (MachineState.readWord memory (8256 + 32 * (n - 1 - j)))
        (MachineState.readWord memory (32 * (n - 1 - j)))
        (csStep memory n j).flag ihLe
      rw [lowValue_succ (csStep memory n (j + 1)).memory 7168 n j,
        csStep_lowValue_stable memory n j (by omega),
        csStep_readWord_new, csStep_flag_succ,
        lowValue_succ memory 0 n j, lowValue_succ memory 8256 n j, pow_succ]
      simp only [Nat.zero_add, hxt, hxm]
      exact ⟨cs_algebra _ _ _ _ _ _ _ _ _ _ hlimb.1 ihEq, hlimb.2⟩


/-! ## Region preservation -/

theorem fastRepresents_amStep (memory : ByteArray) (pa pb n ptr cnt v : Nat)
    (hn : 1 ≤ n)
    (hdisj : ptr + 32 * cnt ≤ 8256 ∨ 8256 + 32 * n ≤ ptr)
    (hrep : Model.FastRepresents memory ptr cnt v) (j : Nat) (hj : j ≤ n) :
    Model.FastRepresents (amStep memory pa pb n j).memory ptr cnt v := by
  refine (Model.fastRepresents_congr ?_ v).2 hrep
  intro i hi
  exact amStep_readWord_disjoint memory pa pb n _ hn (by omega) j hj

theorem fastRepresents_csStep (memory : ByteArray) (n ptr cnt v : Nat)
    (hn : 1 ≤ n)
    (hdisj : ptr + 32 * cnt ≤ 7168 ∨ 7168 + 32 * n ≤ ptr)
    (hrep : Model.FastRepresents memory ptr cnt v) (j : Nat) (hj : j ≤ n) :
    Model.FastRepresents (csStep memory n j).memory ptr cnt v := by
  refine (Model.fastRepresents_congr ?_ v).2 hrep
  intro i hi
  exact csStep_readWord_disjoint memory n _ hn (by omega) j hj

/-! ## `MCOPY` -/

theorem readPadded_mcopy (memory : ByteArray) (src dst sz i : Nat)
    (h : 32 * i + 32 ≤ sz) :
    MachineState.readPadded (MachineState.writeBytes memory
        (MachineState.readPadded memory src sz) dst) (dst + 32 * i) 32 =
      MachineState.readPadded memory (src + 32 * i) 32 := by
  apply ByteArray.ext_getElem
  · simp
  · intro k hk1 hk2
    have hk : k < 32 := by simpa using hk1
    rw [← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hk1,
      ← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hk2,
      Challenge.EvmProof.Memory.readPadded_getElem?_getD,
      Challenge.EvmProof.Memory.readPadded_getElem?_getD, if_pos hk, if_pos hk,
      MachineState.writeBytes_getElem?_getD,
      Challenge.EvmProof.Memory.readPadded_size,
      if_pos (show dst ≤ dst + 32 * i + k ∧ dst + 32 * i + k < dst + sz from
        ⟨by omega, by omega⟩),
      show dst + 32 * i + k - dst = 32 * i + k from by omega,
      Challenge.EvmProof.Memory.readPadded_getElem?_getD, if_pos (show 32 * i + k < sz from by omega)]
    simp only [Nat.add_assoc]

theorem readWord_mcopy (memory : ByteArray) (src dst sz i : Nat)
    (h : 32 * i + 32 ≤ sz) :
    MachineState.readWord (MachineState.writeBytes memory
        (MachineState.readPadded memory src sz) dst) (dst + 32 * i) =
      MachineState.readWord memory (src + 32 * i) := by
  unfold MachineState.readWord
  rw [readPadded_mcopy memory src dst sz i h]

/-- The `MCOPY` reproduces the source block at the destination. -/
theorem fastRepresents_mcopy (memory : ByteArray) (src dst n v : Nat) (_hn : 1 ≤ n)
    (hrep : Model.FastRepresents memory src n v) :
    Model.FastRepresents (MachineState.writeBytes memory
      (MachineState.readPadded memory src (32 * n)) dst) dst n v := by
  apply Model.fastRepresents_of_limbs hrep.1
  intro k hk
  rw [readWord_mcopy memory src dst (32 * n) (n - 1 - k) (by omega)]
  exact Model.readLimb_of_fastRepresents hrep hk

/-- The `MCOPY` leaves every block outside the destination alone. -/
theorem fastRepresents_mcopy_disjoint (memory : ByteArray) (src dst sz ptr cnt v : Nat)
    (hdisj : dst + sz ≤ ptr ∨ ptr + 32 * cnt ≤ dst)
    (hrep : Model.FastRepresents memory ptr cnt v) :
    Model.FastRepresents (MachineState.writeBytes memory
      (MachineState.readPadded memory src sz) dst) ptr cnt v := by
  apply Model.fastRepresents_writeBytes_disjoint
  · rw [Challenge.EvmProof.Memory.readPadded_size]
    exact hdisj
  · exact hrep

/-! ## The selection word -/

/- `word_toNat_mul` and the `csUse`/`csSrc` projection lemmas live in
`CsubModel`. -/


/-! ## Execution certificates -/

def gasSteps_amEntry (s : State) (memory : ByteArray) (pa pb n : Nat)
    (pd ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat)
    (hn : 2 ≤ n) (hpa : 32 ≤ pa) (hpaFit : pa + 32 * n ≤ 9472)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * n ≤ 9472)
    (hs32 : MachineState.readWord memory 9344 = UInt256.ofNat (32 * n))
    (htl : MachineState.readWord memory 9440 = UInt256.ofNat (8224 + 32 * n)) :
    Challenge.EvmProof.GasSteps (amEntryState s memory pa pb pd ret rest)
      (amLoopState s memory pa pb n 0 pd ret rest) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka blk1600
    (by simpa [amEntryState, Artifact.submissionArtifact] using hcode)
    (by simpa [amEntryState, State.fork] using hfork)
    (run_amEntry s memory pa pb n pd ret rest hcap hrun hact hn hpa hpaFit hpb hpbFit
      hs32 htl)
    (by simpa [amEntryState] using hrun)
    (by simpa [amEntryState, State.fork] using hnp)

def gasSteps_amIteration (s : State) (memory : ByteArray) (pa pb n j : Nat)
    (pd ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat)
    (hj : j + 1 < n) (hn32 : n ≤ 32)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * n ≤ 9472)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * n ≤ 9472) :
    Challenge.EvmProof.GasSteps (amLoopState s memory pa pb n j pd ret rest)
      (amLoopState s memory pa pb n (j + 1) pd ret rest) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka blk1627
    (by simpa [amLoopState, Artifact.submissionArtifact] using hcode)
    (by simpa [amLoopState, State.fork] using hfork)
    (run_amLoopBody s memory pa pb n j pd ret rest hcap hrun hcode hact hj hn32
      hpa hpaFit hpb hpbFit)
    (by simpa [amLoopState] using hrun)
    (by simpa [amLoopState, State.fork] using hnp)

def gasSteps_amLoop (s : State) (memory : ByteArray) (pa pb n : Nat)
    (pd ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat)
    (hn32 : n ≤ 32)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * n ≤ 9472)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * n ≤ 9472) :
    Challenge.EvmProof.GasSteps (amLoopState s memory pa pb n 0 pd ret rest)
      (amLoopState s memory pa pb n (n - 1) pd ret rest) := by
  exact Challenge.EvmProof.GasSteps.iterateBounded (n - 1) fun i hi =>
    gasSteps_amIteration s memory pa pb n i pd ret rest hcap hcode hfork hrun hnp hact
      (by omega) hn32 hpa hpaFit hpb hpbFit

def gasSteps_amExit (s : State) (memory : ByteArray) (pa pb n : Nat)
    (pd ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat)
    (hn : 2 ≤ n) (hn32 : n ≤ 32)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * n ≤ 9472)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * n ≤ 9472) :
    Challenge.EvmProof.GasSteps (amLoopState s memory pa pb n (n - 1) pd ret rest)
      (amTailState s memory pa pb n (n - 1 + 1) pd ret rest) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka blk1627
    (by simpa [amLoopState, Artifact.submissionArtifact] using hcode)
    (by simpa [amLoopState, State.fork] using hfork)
    (run_amLoopExit s memory pa pb n (n - 1) pd ret rest hcap hrun hcode hact
      (by omega) hn32 hpa hpaFit hpb hpbFit)
    (by simpa [amLoopState] using hrun)
    (by simpa [amLoopState, State.fork] using hnp)

def gasSteps_amTailStep (s : State) (memory : ByteArray) (pa pb n j : Nat)
    (pd ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat) :
    Challenge.EvmProof.GasSteps (amTailState s memory pa pb n j pd ret rest)
      (csEntryState s (MachineState.writeBytes (amStep memory pa pb n j).memory
        (Data.Bytes.natToBytesPadded (amStep memory pa pb n j).flag.toNat 32) 8224)
        pd ret rest) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka blk1662
    (by simpa [amTailState, Artifact.submissionArtifact] using hcode)
    (by simpa [amTailState, State.fork] using hfork)
    (run_amTail s memory pa pb n j pd ret rest hcap hrun hact)
    (by simpa [amTailState] using hrun)
    (by simpa [amTailState, State.fork] using hnp)

/-- Whole-subroutine trace for `ADDMOD`: from the entry `[pa, pb, pd, ret]` to
the fall-through entry of `CSUB`, with the sum limbs in the `t` block and the
carry stored at `TN`. -/
def gasSteps_addmod (s : State) (memory : ByteArray) (pa pb n : Nat)
    (pd ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat)
    (hn : 2 ≤ n) (hn32 : n ≤ 32)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * n ≤ 9472)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * n ≤ 9472)
    (hs32 : MachineState.readWord memory 9344 = UInt256.ofNat (32 * n))
    (htl : MachineState.readWord memory 9440 = UInt256.ofNat (8224 + 32 * n)) :
    Challenge.EvmProof.GasSteps (amEntryState s memory pa pb pd ret rest)
      (csEntryState s (MachineState.writeBytes (amStep memory pa pb n n).memory
        (Data.Bytes.natToBytesPadded (amStep memory pa pb n n).flag.toNat 32) 8224)
        pd ret rest) := by
  have hnn : n - 1 + 1 = n := by omega
  exact Challenge.EvmProof.GasSteps.cast
    ((((gasSteps_amEntry s memory pa pb n pd ret rest hcap hcode hfork hrun hnp hact
          hn hpa hpaFit hpb hpbFit hs32 htl).trans
        (gasSteps_amLoop s memory pa pb n pd ret rest hcap hcode hfork hrun hnp hact
          hn32 hpa hpaFit hpb hpbFit)).trans
      (gasSteps_amExit s memory pa pb n pd ret rest hcap hcode hfork hrun hnp hact
        hn hn32 hpa hpaFit hpb hpbFit)).trans
      (gasSteps_amTailStep s memory pa pb n (n - 1 + 1) pd ret rest hcap hcode hfork
        hrun hnp hact))
    rfl (by rw [hnn])

/-- Whole-subroutine trace for `CSUB`: from the entry `[pd, ret]` to the return
jump, with `t mod m` copied into the block at `pd`. -/
def gasSteps_csub (s : State) (memory : ByteArray) (n : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat) (hn : 2 ≤ n) (hn32 : n ≤ 32)
    (hjump : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode ret.toNat = true)
    (hml : MachineState.readWord memory 9408 = UInt256.ofNat (32 * n - 32))
    (htl : MachineState.readWord memory 9440 = UInt256.ofNat (8224 + 32 * n))
    (hs32 : MachineState.readWord (csStep memory n n).memory 9344 =
      UInt256.ofNat (32 * n))
    (hdstFit : pdst.toNat + 32 * n ≤ 9472)
    (htn : (MachineState.readWord (csStep memory n n).memory 8224).toNat ≤ 1) :
    Challenge.EvmProof.GasSteps (csEntryState s memory pdst ret rest)
      (csReturnedState s memory n n pdst ret rest) := by
  have _hml := hml
  have hsrcFit : (csSrc memory n n).toNat + 32 * n ≤ 9472 := by
    rw [csSrc_toNat memory n n (csUse_le_one memory n n htn)]
    split <;> omega
  exact CsubPairsTrace.gasSteps_csub CsubPairsBlocks.blocks s memory n pdst ret rest
    (CsubPairsBlocks.environment s hcode hfork hrun hnp) hcap hact hn hn32
    (by rw [hcode]; exact CsubPairsBlocks.jumpFirst)
    (by rw [hcode]; exact CsubPairsBlocks.jumpSecond)
    (by rw [hcode]; exact hjump) htl hs32 hdstFit hsrcFit

/-! ## Functional correctness -/

/-- The memory `ADDMOD` hands to `CSUB`: the sum limbs in the `t` block and the
carry-out at `TN`. -/
def amResultMemory (memory : ByteArray) (pa pb n : Nat) : ByteArray :=
  MachineState.writeBytes (amStep memory pa pb n n).memory
    (Data.Bytes.natToBytesPadded (amStep memory pa pb n n).flag.toNat 32) 8224

theorem amResultMemory_def (memory : ByteArray) (pa pb n : Nat) :
    amResultMemory memory pa pb n =
      MachineState.writeBytes (amStep memory pa pb n n).memory
        (Data.Bytes.natToBytesPadded (amStep memory pa pb n n).flag.toNat 32) 8224 := rfl

/-- The memory `CSUB` leaves behind. -/
def csResultMemory (memory : ByteArray) (n pdst : Nat) : ByteArray :=
  MachineState.writeBytes (csStep memory n n).memory
    (MachineState.readPadded (csStep memory n n).memory
      (csSrc memory n n).toNat (32 * n)) pdst

theorem csReturnedState_memory (s : State) (memory : ByteArray) (n : Nat)
    (pdst ret : UInt256) (rest : List UInt256) :
    (csReturnedState s memory n n pdst ret rest).memory =
      csResultMemory memory n pdst.toNat := rfl

theorem addmod_carry_le_one (memory : ByteArray) (pa pb n : Nat) (hn : 2 ≤ n)
    (hpa : pa + 32 * n ≤ 8256) (hpb : pb + 32 * n ≤ 8256) :
    (amStep memory pa pb n n).flag.toNat ≤ 1 :=
  (amStep_invariant memory pa pb n (by omega) hpa hpb n le_rfl).2

/-- `ADDMOD` computes `a + b` as an `(n+1)`-limb value: the `t` block holds the
low `n` limbs and `TN` holds the carry. -/
theorem addmod_value (memory : ByteArray) (pa pb n a b : Nat) (hn : 2 ≤ n)
    (hpa : pa + 32 * n ≤ 8256) (hpb : pb + 32 * n ≤ 8256)
    (ha : Model.FastRepresents memory pa n a)
    (hb : Model.FastRepresents memory pb n b) :
    lowValue (amStep memory pa pb n n).memory 8256 n n +
        (amStep memory pa pb n n).flag.toNat * Limbs.radix ^ n = a + b := by
  have h := (amStep_invariant memory pa pb n (by omega) hpa hpb n le_rfl).1
  have hA : lowValue memory pa n n = a := by
    rw [lowValue_full]; exact Model.value_of_fastRepresents ha
  have hB : lowValue memory pb n n = b := by
    rw [lowValue_full]; exact Model.value_of_fastRepresents hb
  rw [hA, hB] at h
  exact h

theorem addmod_represents (memory : ByteArray) (pa pb n : Nat) :
    Model.FastRepresents (amResultMemory memory pa pb n) 8256 n
      (lowValue (amStep memory pa pb n n).memory 8256 n n) := by
  unfold amResultMemory
  exact Model.fastRepresents_writeWord_disjoint _ 8224 8256 n _ _ (by omega)
    (fastRepresents_lowValue _ _ _)

theorem addmod_tn (memory : ByteArray) (pa pb n : Nat) :
    MachineState.readWord (amResultMemory memory pa pb n) 8224 =
      (amStep memory pa pb n n).flag :=
  Challenge.EvmProof.Memory.readWord_writeWord _ _ _

/-- Every named block outside the `t` area survives `ADDMOD` unchanged. -/
theorem addmod_preserves_region (memory : ByteArray) (pa pb n ptr cnt v : Nat)
    (hn : 2 ≤ n)
    (hdisj : ptr + 32 * cnt ≤ 8224 ∨ 8256 + 32 * n ≤ ptr)
    (hrep : Model.FastRepresents memory ptr cnt v) :
    Model.FastRepresents (amResultMemory memory pa pb n) ptr cnt v := by
  unfold amResultMemory
  exact Model.fastRepresents_writeWord_disjoint _ 8224 ptr cnt v _ (by omega)
    (fastRepresents_amStep memory pa pb n ptr cnt v (by omega) (by omega) hrep n le_rfl)

/-- `CSUB` writes `t mod m` into the block at `pd`. -/
theorem csub_correct (memory : ByteArray) (n tlow mm tn pdst : Nat)
    (hn : 2 ≤ n) (hn32 : n ≤ 32)
    (ht : Model.FastRepresents memory 8256 n tlow)
    (hm : Model.FastRepresents memory 0 n mm)
    (htnv : (MachineState.readWord memory 8224).toNat = tn) (htn1 : tn ≤ 1)
    (_hmpos : 0 < mm)
    (hbound : tn * Limbs.radix ^ n + tlow < 2 * mm) :
    Model.FastRepresents (csResultMemory memory n pdst) pdst n
      ((tn * Limbs.radix ^ n + tlow) % mm) := by
  have hn1 : 1 ≤ n := by omega
  obtain ⟨hinv, hbor⟩ := csStep_invariant memory n hn1 hn32 n le_rfl
  have hM : lowValue memory 0 n n = mm := by
    rw [lowValue_full]; exact Model.value_of_fastRepresents hm
  have hT : lowValue memory 8256 n n = tlow := by
    rw [lowValue_full]; exact Model.value_of_fastRepresents ht
  rw [hM, hT] at hinv
  have hDlt : lowValue (csStep memory n n).memory 7168 n n < Limbs.radix ^ n :=
    lowValue_lt _ _ _ _
  have hmmlt : mm < Limbs.radix ^ n := hm.1
  have htnStep : MachineState.readWord (csStep memory n n).memory 8224 =
      MachineState.readWord memory 8224 :=
    csStep_readWord_disjoint memory n 8224 hn1 (by omega) n le_rfl
  have htnStep' : (MachineState.readWord (csStep memory n n).memory 8224).toNat ≤ 1 := by
    rw [htnStep, htnv]; exact htn1
  have huseLe : (csUse memory n n).toNat ≤ 1 := csUse_le_one memory n n htnStep'
  have huse : (csUse memory n n).toNat =
      max tn (if (csStep memory n n).flag.toNat = 0 then 1 else 0) := by
    rw [csUse_toNat memory n n htnStep', htnStep, htnv]
  have hsubb : Model.FastRepresents (csStep memory n n).memory 7168 n
      (lowValue (csStep memory n n).memory 7168 n n) := fastRepresents_lowValue _ _ _
  have htsblk : Model.FastRepresents (csStep memory n n).memory 8256 n tlow :=
    fastRepresents_csStep memory n 8256 n tlow hn1 (by omega) ht n le_rfl
  by_cases huse0 : (csUse memory n n).toNat = 0
  · have huse0' : max tn (if (csStep memory n n).flag.toNat = 0 then 1 else 0) = 0 := by
      rw [← huse]; exact huse0
    have htn0 : tn = 0 := by omega
    have hbor1 : (csStep memory n n).flag.toNat = 1 := by
      by_contra hc
      have hb : (csStep memory n n).flag.toNat = 0 := by omega
      rw [hb, if_pos rfl] at huse0'
      omega
    rw [hbor1, Nat.one_mul] at hinv
    have hlt : tlow < mm := by omega
    have hmod : (tn * Limbs.radix ^ n + tlow) % mm = tlow := by
      rw [htn0, Nat.zero_mul, Nat.zero_add, Nat.mod_eq_of_lt hlt]
    rw [hmod]
    unfold csResultMemory
    rw [csSrc_toNat memory n n huseLe, if_pos huse0]
    exact fastRepresents_mcopy _ _ _ _ _ hn1 htsblk
  · have huse1' : max tn (if (csStep memory n n).flag.toNat = 0 then 1 else 0) = 1 := by
      rw [← huse]; omega
    have hcases : tn = 1 ∨ (csStep memory n n).flag.toNat = 0 := by
      by_cases hb : (csStep memory n n).flag.toNat = 0
      · exact Or.inr hb
      · rw [if_neg hb] at huse1'
        left; omega
    have hval : lowValue (csStep memory n n).memory 7168 n n + mm =
        tn * Limbs.radix ^ n + tlow := by
      rcases hcases with h1 | h0
      · rw [h1, Nat.one_mul] at hbound ⊢
        have hb1 : (csStep memory n n).flag.toNat = 1 := by
          by_contra hc
          have hb : (csStep memory n n).flag.toNat = 0 := by omega
          rw [hb, Nat.zero_mul, Nat.add_zero] at hinv
          omega
        rw [hb1, Nat.one_mul] at hinv
        omega
      · rw [h0, Nat.zero_mul, Nat.add_zero] at hinv
        have htn0 : tn = 0 := by
          by_contra hc
          have h1 : tn = 1 := by omega
          rw [h1, Nat.one_mul] at hbound
          omega
        rw [htn0, Nat.zero_mul, Nat.zero_add]
        omega
    have hmod : (tn * Limbs.radix ^ n + tlow) % mm =
        lowValue (csStep memory n n).memory 7168 n n := by
      rw [Model.mod_eq_cond_sub_of_lt_twice hbound, if_neg (by omega)]
      omega
    rw [hmod]
    unfold csResultMemory
    rw [csSrc_toNat memory n n huseLe, if_neg huse0]
    exact fastRepresents_mcopy _ _ _ _ _ hn1 hsubb

/-- Every block outside `SUBB` and outside the destination survives `CSUB`. -/
theorem csub_preserves_region (memory : ByteArray) (n pdst ptr cnt v : Nat)
    (hn : 2 ≤ n)
    (hdisjSubb : ptr + 32 * cnt ≤ 7168 ∨ 7168 + 32 * n ≤ ptr)
    (hdisjDst : pdst + 32 * n ≤ ptr ∨ ptr + 32 * cnt ≤ pdst)
    (hrep : Model.FastRepresents memory ptr cnt v) :
    Model.FastRepresents (csResultMemory memory n pdst) ptr cnt v := by
  unfold csResultMemory
  exact fastRepresents_mcopy_disjoint _ _ _ _ _ _ _ hdisjDst
    (fastRepresents_csStep memory n ptr cnt v (by omega) hdisjSubb hrep n le_rfl)

/-- End-to-end: entering `ADDMOD` with `a` at `pa`, `b` at `pb` and `a + b < 2m`
leaves `(a + b) mod m` in the block at `pd`. -/
theorem addmod_csub_correct (memory : ByteArray) (pa pb n a b mm pdst : Nat)
    (hn : 2 ≤ n) (hn32 : n ≤ 32)
    (hpa : pa + 32 * n ≤ 8192) (hpb : pb + 32 * n ≤ 8192)
    (ha : Model.FastRepresents memory pa n a)
    (hb : Model.FastRepresents memory pb n b)
    (hm : Model.FastRepresents memory 0 n mm) (hmpos : 0 < mm)
    (hab : a + b < 2 * mm) :
    Model.FastRepresents (csResultMemory (amResultMemory memory pa pb n) n pdst)
      pdst n ((a + b) % mm) := by
  have hcarry := addmod_carry_le_one memory pa pb n hn (by omega) (by omega)
  have hvalue := addmod_value memory pa pb n a b hn (by omega) (by omega) ha hb
  have hts := addmod_represents memory pa pb n
  have hmblk : Model.FastRepresents (amResultMemory memory pa pb n) 0 n mm :=
    addmod_preserves_region memory pa pb n 0 n mm hn (by omega) hm
  have htn : (MachineState.readWord (amResultMemory memory pa pb n) 8224).toNat =
      (amStep memory pa pb n n).flag.toNat := by
    rw [addmod_tn]
  have hbound : (amStep memory pa pb n n).flag.toNat * Limbs.radix ^ n +
      lowValue (amStep memory pa pb n n).memory 8256 n n < 2 * mm := by
    omega
  have h := csub_correct (amResultMemory memory pa pb n) n
    (lowValue (amStep memory pa pb n n).memory 8256 n n) mm
    (amStep memory pa pb n n).flag.toNat pdst hn hn32 hts hmblk htn hcarry hmpos hbound
  rwa [show (amStep memory pa pb n n).flag.toNat * Limbs.radix ^ n +
      lowValue (amStep memory pa pb n n).memory 8256 n n = a + b from by omega] at h

/-- Region preservation across the whole `ADDMOD`/`CSUB` pair. -/
theorem addmod_csub_preserves_region (memory : ByteArray) (pa pb n pdst ptr cnt v : Nat)
    (hn : 2 ≤ n)
    (hdisjT : ptr + 32 * cnt ≤ 8224 ∨ 8256 + 32 * n ≤ ptr)
    (hdisjSubb : ptr + 32 * cnt ≤ 7168 ∨ 7168 + 32 * n ≤ ptr)
    (hdisjDst : pdst + 32 * n ≤ ptr ∨ ptr + 32 * cnt ≤ pdst)
    (hrep : Model.FastRepresents memory ptr cnt v) :
    Model.FastRepresents (csResultMemory (amResultMemory memory pa pb n) n pdst)
      ptr cnt v :=
  csub_preserves_region _ n pdst ptr cnt v hn hdisjSubb hdisjDst
    (addmod_preserves_region memory pa pb n ptr cnt v hn hdisjT hrep)

end Challenge.Modexp.Submission.Proofs.Fast.Csub
