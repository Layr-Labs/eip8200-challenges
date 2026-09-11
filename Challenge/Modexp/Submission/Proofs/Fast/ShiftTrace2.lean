import Challenge.Modexp.Submission.Proofs.Fast.CompactConstants
import Challenge.Modexp.Submission.Proofs.Fast.ShiftTrace1

set_option warningAsError false
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
# Block reductions of the shift-reduce base conversion, part 2

The shift loop: `u` construction, the quotient estimate, the limb pass, the
middle block, the repair rounds, the `CSUB` call and the exits.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.Shift

attribute [local simp] CompactConstants.notThirtyOne notThirtyOneOfNat
attribute [local simp] CompactConstants.notZero CompactConstants.notZeroStruct

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Fast
attribute [local simp] jumpDestGuardResume jumpDestFourResume
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs

/-- `blk3013` with steps to go: fall into the body. -/
theorem run_shiftHead_go (s : State) (mem : ByteArray) (n bsize esize msize k : Nat)
    (hk : k ≠ 0) (hk32 : k ≤ 32)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk3013
      (shiftLoopState s mem n bsize esize msize k) =
      some (shiftBodyState s mem n bsize esize msize k) := by
  have hkmod : k % 115792089237316195423570985008687907853269984665640564039457584007913129639936
      = k := Nat.mod_eq_of_lt (by omega)
  simp (config := { maxSteps := 200000 })
    [blk3013, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      shiftLoopState, shiftBodyState, kState, pcShiftLoop, pcShiftBody,
      outer, Exp.outer, hcode, hrun, hk, hkmod, UInt256.isZero, UInt256.isTrue,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod, jumpDest5366]

/-- `blk3013` with no steps to go: jump to `SHIFT_DONE`. -/
theorem run_shiftHead_done (s : State) (mem : ByteArray) (n bsize esize msize : Nat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk3013
      (shiftLoopState s mem n bsize esize msize 0) =
      some (shiftDoneState s mem n bsize esize msize) := by
  simp (config := { maxSteps := 200000 })
    [blk3013, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      shiftLoopState, shiftDoneState, kState, pcShiftLoop, pcShiftDone,
      outer, Exp.outer, hcode, hrun, jumpDest5366, UInt256.isZero, UInt256.isTrue,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod]

/-- `blk3018`: `MCOPY(TN, BASE, s32)` and `t[0] := 0`. -/
theorem run_shiftBody (s : State) (mem : ByteArray) (n bsize esize msize k : Nat)
    (hn : 2 ≤ n) (hn32 : n ≤ 32) (hact : 298 ≤ s.activeWords.toNat)
    (htl : MachineState.readWord mem 9440 = UInt256.ofNat (8224 + 32 * n))
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk3018
      (shiftBodyState s mem n bsize esize msize k) =
      some (estimateState s mem n bsize esize msize k) := by
  have hmod : (32 * n) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936
      = 32 * n := Exp.mod_word_self (Nat.lt_of_le_of_lt (show 32 * n ≤ 1024 by omega) (by norm_num))
  have hfix2 : UInt256.ofNat (MachineState.activeWordsAfter
      (MachineState.activeWordsAfter s.activeWords.toNat 8224 (32 * n)) 2048
      (32 * n)) = s.activeWords :=
    Exp.activeWords_fix2 s 8224 (32 * n) 2048 (32 * n) (by omega) (by omega) (by omega)
      (by omega) hact
  have hfixTL : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 9440 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) (by omega)
  have hfixT0 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      (8224 + 32 * n) 32) = s.activeWords :=
    Monpro.activeWords_fix s _ 32 (by decide) (by omega) (by omega)
  have htl' : MachineState.readWord
      (MachineState.writeBytes mem (MachineState.readPadded mem 2048 (32 * n)) 8224) 9440 =
      UInt256.ofNat (8224 + 32 * n) := by
    rw [show MachineState.writeBytes mem (MachineState.readPadded mem 2048 (32 * n)) 8224 =
      Exp.mcopyMem mem 8224 2048 (32 * n) from rfl]
    rw [Exp.readWord_mcopyMem_disjoint mem 8224 2048 (32 * n) 9440 (Or.inr (by omega))]
    exact htl
  have hmodTL : (8224 + 32 * n) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936
      = 8224 + 32 * n := Nat.mod_eq_of_lt (by omega)
  simp (config := { maxSteps := 400000 })
    [blk3018, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      shiftBodyState, estimateState, kState, pcShiftBody, pcEstimate, uMem,
      Exp.mcopyMem, Exp.storeWord, outer, Exp.outer, hcode, hrun, hmod, hfix2, hfixTL,
      hfixT0, htl', hmodTL, Exp.push0_word,
      State.activeWordsAfterUInt256, State.activeWordsAfterUInt256_2,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod]

/-- Generic word identity; the quotient clamp itself is unchanged. -/
private theorem saturation_gt_eq_lt (a b : UInt256) : UInt256.gt a b = UInt256.lt b a := by
  rfl

private theorem ofNat_zero_lt_eq_double_isZero (x : UInt256) :
    UInt256.lt (UInt256.ofNat 0) x = UInt256.isZero (UInt256.isZero x) :=
  Monpro.zero_lt_eq_double_isZero x

private theorem addMod_comm (a b m : UInt256) :
    UInt256.addMod a b m = UInt256.addMod b a m := by
  simp only [UInt256.addMod, Nat.add_comm]

@[simp] private theorem newEstimatePC2960 : Artifact.submissionArtifact.instructionPC 2846 = 3761 := by rfl
@[simp] private theorem newEstimatePC2961 : Artifact.submissionArtifact.instructionPC 2847 = 3762 := by rfl
@[simp] private theorem newEstimatePC2962 : Artifact.submissionArtifact.instructionPC 2848 = 3763 := by rfl
@[simp] private theorem newEstimatePC2963 : Artifact.submissionArtifact.instructionPC 2849 = 3764 := by rfl
@[simp] private theorem newEstimatePC2964 : Artifact.submissionArtifact.instructionPC 2850 = 3767 := by rfl
@[simp] private theorem newEstimatePC2965 : Artifact.submissionArtifact.instructionPC 2851 = 3768 := by rfl
@[simp] private theorem newEstimatePC2966 : Artifact.submissionArtifact.instructionPC 2852 = 3769 := by rfl
@[simp] private theorem newEstimatePC2967 : Artifact.submissionArtifact.instructionPC 2853 = 3771 := by rfl
@[simp] private theorem newEstimatePC2968 : Artifact.submissionArtifact.instructionPC 2854 = 3772 := by rfl
@[simp] private theorem newEstimatePC2969 : Artifact.submissionArtifact.instructionPC 2855 = 3774 := by rfl
@[simp] private theorem newEstimatePC2970 : Artifact.submissionArtifact.instructionPC 2856 = 3775 := by rfl
@[simp] private theorem newEstimatePC2971 : Artifact.submissionArtifact.instructionPC 2857 = 3776 := by rfl
@[simp] private theorem newEstimatePC2972 : Artifact.submissionArtifact.instructionPC 2858 = 3778 := by rfl
@[simp] private theorem newEstimatePC2973 : Artifact.submissionArtifact.instructionPC 2859 = 3779 := by rfl
@[simp] private theorem newEstimatePC2974 : Artifact.submissionArtifact.instructionPC 2860 = 3780 := by rfl
@[simp] private theorem newEstimatePC2975 : Artifact.submissionArtifact.instructionPC 2861 = 3781 := by rfl

/-- State after forming the low half of the quotient numerator. -/
private def estimateLoState (s : State) (mem : ByteArray)
    (n bsize esize msize k : Nat) : State :=
  let um := uMem mem n
  let utop := MachineState.readWord um 2048
  let L := MachineState.readWord um PRE_L
  let hi := utop / L
  let r := utop % L
  let X := MachineState.readWord um PRE_X
  let xr := X * r
  let unext := MachineState.readWord um 2080
  let uL := unext / L
  let lo := uL + xr
  { s with pc := UInt256.ofNat 3740
           stack := lo :: hi :: UInt256.ofNat k :: outer n bsize esize msize
           memory := um }

/-- State immediately before the quotient-correction sequence.  Keeping this
trace boundary explicit prevents the symbolic quotient expression from being
duplicated through every instruction in `blk3026`. -/
private def estimateCorrectionState (s : State) (mem : ByteArray)
    (n bsize esize msize k : Nat) : State :=
  let um := uMem mem n
  let utop := MachineState.readWord um 2048
  let L := MachineState.readWord um PRE_L
  let hi := utop / L
  let r := utop % L
  let X := MachineState.readWord um PRE_X
  let xr := X * r
  let unext := MachineState.readWord um 2080
  let uL := unext / L
  let lo := uL + xr
  let dodd := MachineState.readWord um PRE_DODD
  let bmod := MachineState.readWord um PRE_BMOD
  let mm := UInt256.mulMod hi bmod dodd
  let rho := UInt256.addMod mm lo dodd
  let diff := lo - rho
  let dinv := MachineState.readWord um PRE_DINV
  let q := dinv * diff
  let rhat := unext - MachineState.readWord um 0 * q
  { s with pc := UInt256.ofNat 3769
           stack := rhat :: q :: hi :: UInt256.ofNat k :: outer n bsize esize msize
           memory := um }

/-- `blk3026`: quotient estimate with a branchless saturation mask. -/
theorem run_estimate (s : State) (mem : ByteArray) (n bsize esize msize k : Nat)
    (hact : 296 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk3026
      (estimateState s mem n bsize esize msize k) =
      some (macSetupState s mem n bsize esize msize k) := by
  have hA : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 2048 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  have hB : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 6144 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  have hC : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 6208 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  have hD : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 2080 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  have hE : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 6176 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  have hF : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 6240 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  have hG : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 6272 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  have hH : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 0 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  have hI : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 32 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  have hhead : Challenge.EvmProof.Stepper.runLocatedBlock (blk3026.take 19)
      (estimateState s mem n bsize esize msize k) =
      some (estimateLoState s mem n bsize esize msize k) := by
    simp (config := { maxSteps := 250000 })
      [blk3026, opAt, pushAt, wfOp,
        Challenge.EvmProof.Stepper.runLocatedBlock,
        Challenge.EvmProof.Stepper.runLocated,
        Challenge.EvmProof.Stepper.runInstr,
        estimateState, estimateLoState, kState, pcEstimate,
        PRE_L, PRE_X,
        outer, Exp.outer, hcode, hrun, hA, hB, hC, hD,
        State.activeWordsAfterUInt256,
        Challenge.EvmProof.Word.literal_eq_ofNat,
        Challenge.EvmProof.Word.word_toNat_ofNat,
        Challenge.EvmProof.Word.succ_ofNat_mod,
        Challenge.EvmProof.Word.ofNat_add_mod, List.exchange]
  have hmiddle : Challenge.EvmProof.Stepper.runLocatedBlock
      ((blk3026.drop 19).take 21)
      (estimateLoState s mem n bsize esize msize k) =
      some (estimateCorrectionState s mem n bsize esize msize k) := by
    simp (config := { maxSteps := 250000 })
      [blk3026, opAt, pushAt, wfOp,
        Challenge.EvmProof.Stepper.runLocatedBlock,
        Challenge.EvmProof.Stepper.runLocated,
        Challenge.EvmProof.Stepper.runInstr,
        estimateLoState, estimateCorrectionState,
        PRE_L, PRE_DODD, PRE_X, PRE_BMOD, PRE_DINV,
        outer, Exp.outer, hcode, hrun, hE, hF, hG, hH,
        State.activeWordsAfterUInt256,
        Challenge.EvmProof.Word.literal_eq_ofNat,
        Challenge.EvmProof.Word.word_toNat_ofNat,
        Challenge.EvmProof.Word.succ_ofNat_mod,
        Challenge.EvmProof.Word.ofNat_add_mod, List.exchange, addMod_comm]
  have hfinish : Challenge.EvmProof.Stepper.runLocatedBlock (blk3026.drop 40)
      (estimateCorrectionState s mem n bsize esize msize k) =
      some (macSetupState s mem n bsize esize msize k) := by
    simp (config := { maxSteps := 300000 })
      [blk3026, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      estimateCorrectionState, macSetupState, pcMacSetup, qhatOf,
      PRE_L, PRE_DODD, PRE_X, PRE_BMOD, PRE_DINV,
      outer, Exp.outer, hcode, hrun, hE, hI, Exp.push0_word, ofNat_zero_lt_eq_double_isZero,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod, List.exchange, saturation_gt_eq_lt, addMod_comm]
  have htail := Challenge.EvmProof.Stepper.runLocatedBlock_append
    ((blk3026.drop 19).take 21) (blk3026.drop 40)
    (estimateLoState s mem n bsize esize msize k)
    (estimateCorrectionState s mem n bsize esize msize k)
    (macSetupState s mem n bsize esize msize k)
    hmiddle (by simp [estimateCorrectionState, hrun]) hfinish
  have hprogram : blk3026 = blk3026.take 19 ++
      ((blk3026.drop 19).take 21 ++ blk3026.drop 40) := by rfl
  rw [hprogram]
  exact Challenge.EvmProof.Stepper.runLocatedBlock_append _ _ _ _ _ hhead
    (by simp [estimateLoState, hrun]) htail

/-- `blk3069`: the limb-pass frame `[paj, ptj, 0, q]`. -/
theorem run_macSetup (s : State) (mem : ByteArray) (n bsize esize msize k : Nat)
    (hn : 1 ≤ n) (hn32 : n ≤ 32) (hact : 296 ≤ s.activeWords.toNat)
    (htl : MachineState.readWord (uMem mem n) 9440 = UInt256.ofNat (8224 + 32 * n))
    (hml : MachineState.readWord (uMem mem n) 9408 = UInt256.ofNat (32 * n - 32))
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk3069
      (macSetupState s mem n bsize esize msize k) =
      some (macLoopState s (uMem mem n) (qhatOf (uMem mem n)) n bsize esize msize k 0) := by
  have hTL : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 9440 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  have hML : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 9408 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  have hpa : UInt256.ofNat (5120 + (32 * n - 32)) = UInt256.ofNat (NEG + 32 * n - 32) := by
    unfold NEG; congr 1; omega
  simp (config := { maxSteps := 300000 })
    [blk3069, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      macSetupState, macLoopState, pcMacSetup, pcMacLoop, Monpro.l1Step,
      outer, Exp.outer, hcode, hrun, htl, hml, hTL, hML, Exp.push0_word, hpa,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod]
  all_goals (try (congr 1; unfold NEG; omega))

/-- `blk3077a`: one limb of `t += q * NEG` with both pointer steps, up to the
exit test.  The pointers stay abstract. -/
theorem run_macBodyA (s : State) (um : ByteArray) (q pa pt pa' pt' : UInt256)
    (n bsize esize msize k j : Nat)
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hact : 296 ≤ s.activeWords.toNat)
    (hn32 : n ≤ 32) (hj : j < n)
    (hpa : pa.toNat = NEG + 32 * (n - 1 - j)) (hpt : pt.toNat = 8256 + 32 * (n - 1 - j))
    (hpa' : UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904 + pa = pa')
    (hpt' : UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904 + pt = pt') :
    Challenge.EvmProof.Stepper.runLocatedBlock blk3077a
      { s with pc := UInt256.ofNat pcMacLoop
               stack := pa :: pt :: (Monpro.l1Step um q NEG n j).carry :: q :: UInt256.ofNat k ::
                 outer n bsize esize msize
               memory := (Monpro.l1Step um q NEG n j).memory } =
      some { s with pc := UInt256.ofNat pcMacTail
                    stack := pa' :: pt' :: (Monpro.l1Step um q NEG n (j + 1)).carry :: q ::
                      UInt256.ofNat k :: outer n bsize esize msize
                    memory := (Monpro.l1Step um q NEG n (j + 1)).memory } := by
  have hactA : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      (NEG + 32 * (n - 1 - j)) 32) = s.activeWords :=
    Monpro.activeWords_fix s _ 32 (by decide) (by unfold NEG; omega) hact
  have hactT : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      (8256 + 32 * (n - 1 - j)) 32) = s.activeWords :=
    Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  have h3837 : (3837 : UInt256).toNat = 3837 := by decide
  have heq3837 : (3837 : UInt256) = UInt256.ofNat 3837 := by decide
  have h3898 : (3898 : UInt256).toNat = 3898 := by decide
  have heq3898 : (3898 : UInt256) = UInt256.ofNat 3898 := by decide
  simp (config := { maxSteps := 800000 })
    [blk3077a, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      pcMacLoop, pcMacTail, Monpro.l1Step, Monpro.macSum, Monpro.macCarry, Monpro.mulHi,
      Monpro.maxWord_literal, outer, Exp.outer,
      hrun, hcode, negK_literal, hpa, hpt, hpa', hpt', hactA, hactT,
      h3837, heq3837, h3898, heq3898,
      UInt256.gt, UInt256.isTrue,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      List.exchange]
  exact Monpro.MacAlt.macCarryFix
    (MachineState.readWord (Monpro.l1Step um q NEG n j).memory
      (NEG + 32 * (n - 1 - j)))
    q
    (MachineState.readWord (Monpro.l1Step um q NEG n j).memory
      (8256 + 32 * (n - 1 - j)))
    (Monpro.l1Step um q NEG n j).carry

/-- `blk3077b` with limbs to go: back to the loop head. -/
theorem run_macTail_go (s : State) (mm : ByteArray) (pa pt c q : UInt256)
    (n bsize esize msize k : Nat) (hgt : 8224 < pt.toNat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk3077b
      { s with pc := UInt256.ofNat pcMacTail
               stack := pa :: pt :: c :: q :: UInt256.ofNat k :: outer n bsize esize msize
               memory := mm } =
      some { s with pc := UInt256.ofNat pcMacLoop
                    stack := pa :: pt :: c :: q :: UInt256.ofNat k :: outer n bsize esize msize
                    memory := mm } := by
  simp (config := { maxSteps := 200000 })
    [blk3077b, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      pcMacTail, pcMacLoop, outer, Exp.outer, hcode, hrun, hgt, jumpDest4933,
      UInt256.gt, UInt256.isTrue,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod, Nat.mod_eq_of_lt]

/-- `blk3077b` after the last limb: fall through into the middle block. -/
theorem run_macTail_exit (s : State) (mm : ByteArray) (pa pt c q : UInt256)
    (n bsize esize msize k : Nat) (hpt : pt.toNat = 8224)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk3077b
      { s with pc := UInt256.ofNat pcMacTail
               stack := pa :: pt :: c :: q :: UInt256.ofNat k :: outer n bsize esize msize
               memory := mm } =
      some { s with pc := UInt256.ofNat pcMid
                    stack := pa :: pt :: c :: q :: UInt256.ofNat k :: outer n bsize esize msize
                    memory := mm } := by
  simp (config := { maxSteps := 200000 })
    [blk3077b, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      pcMacTail, pcMid, outer, Exp.outer, hcode, hrun, hpt, jumpDest4933,
      UInt256.gt, UInt256.isTrue,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod, Nat.mod_eq_of_lt]

end Challenge.Modexp.Submission.Proofs.Fast.Shift
