import Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.PaddingTraceCore
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
/-!
# Direct execution of the RIPEMD-160 padding function: footer image and gas

Continues `HoistedInherited.PaddingTraceCore` (split for memory: one module peaked above 10 GB).
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.PaddingTrace
@[simp] private theorem inherited_tail_pc_5417 : HoistedInherited.Artifact.submissionArtifact.instructionPC 5381 = 9725 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl

@[simp] private theorem inherited_tail_pc_5418 : HoistedInherited.Artifact.submissionArtifact.instructionPC 5382 = 9726 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl

@[simp] private theorem inherited_tail_pc_5419 : HoistedInherited.Artifact.submissionArtifact.instructionPC 5383 = 9728 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl

@[simp] private theorem inherited_tail_pc_5420 : HoistedInherited.Artifact.submissionArtifact.instructionPC 5384 = 9729 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl

@[simp] private theorem inherited_tail_pc_5421 : HoistedInherited.Artifact.submissionArtifact.instructionPC 5385 = 9730 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl

@[simp] private theorem inherited_tail_pc_5422 : HoistedInherited.Artifact.submissionArtifact.instructionPC 5386 = 9733 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl

@[simp] private theorem inherited_tail_pc_5423 : HoistedInherited.Artifact.submissionArtifact.instructionPC 5387 = 9734 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl

@[simp] private theorem inherited_tail_pc_5424 : HoistedInherited.Artifact.submissionArtifact.instructionPC 5388 = 9736 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl


open EvmSemantics
open EvmSemantics.EVM

/-! ## The footer window is beyond the sentinel image -/

@[simp] private theorem oneByte_size (b : UInt8) :
    (ByteArray.mk #[b]).size = 1 := rfl

private theorem mod64_div_byte (x j : Nat) (hj : j < 8) :
    x % 2 ^ 64 / 2 ^ (8 * j) % 256 = x / 2 ^ (8 * j) % 256 := by
  have hsplit : (2:Nat) ^ 64 = 2 ^ (8 * j) * 2 ^ (64 - 8 * j) := by
    rw [← Nat.pow_add]; congr 1; omega
  have hdvd : (256:Nat) ∣ 2 ^ (64 - 8 * j) := by
    have h8 : 8 ≤ 64 - 8 * j := by omega
    simpa using Nat.pow_dvd_pow 2 h8
  rw [hsplit, Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ hdvd]

private theorem padLengthReady_size_le (input : ByteArray) :
    (padLengthReady input).memory.size ≤ Padding.messageOffset := by
  exact Nat.zero_le _

private theorem sentinel_size_le (input : ByteArray) (_hfit : CalldataFits input) :
    (padSentinel input).memory.size ≤
      Padding.messageOffset + Padding.paddedLength input.size - 8 := by
  have hbase := padLengthReady_size_le input
  have hlen : input.size + 9 ≤ Padding.paddedLength input.size := by
    unfold Padding.paddedLength
    omega
  have e1 : ∀ b : UInt8, (ByteArray.mk #[b]).size = 1 := fun _ => rfl
  simp only [padSentinel, padDirty, padGuardMiss, HoistedInherited.ColdGuardFixup.wMemory, padCopied, padCopyDone,
    MachineState.writeBytes_size, Challenge.EvmProof.Memory.readPadded_size, oneByte_size, e1]
  split_ifs <;>
    unfold Padding.messageOffset at hbase ⊢ <;> omega

/-! ## Final footer image -/

theorem lengthBytes_of_shift_zero (input : ByteArray) (hfit : CalldataFits input)
    (i j : Nat) (hij : i ≤ j) (hj : j < 8) (hz : lengthShift input i = ⟨0⟩) :
    (Padding.lengthBytes input)[j]?.getD 0 = 0 := by
  have hzn : input.size * 8 / 2 ^ (8 * i) = 0 := by
    have := lengthShift_toNat input hfit i
    rw [hz] at this
    simpa using this.symm
  have hlt : input.size * 8 < 2 ^ (8 * i) := by
    exact Nat.lt_of_div_eq_zero (by positivity) hzn
  rw [Challenge.EvmProof.Memory.getD0_eq_getElem _ _
    (by simpa using hj : j < (Padding.lengthBytes input).size),
    Padding.lengthByte input j hj]
  have : input.size * 8 / 2 ^ (8 * j) = 0 := by
    apply Nat.div_eq_of_lt
    exact Nat.lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by norm_num) (by omega))
  rw [this]
  rfl

theorem topByte_eq (input : ByteArray) (hfit : CalldataFits input) :
    UInt8.ofNat ((topByteWord input).toNat % 256) =
      (Padding.lengthBytes input)[7]?.getD 0 := by
  have hlt : (bitLengthWord input).toNat < 2 ^ 256 := (bitLengthWord input).val.isLt
  have hshift : (topByteWord input).toNat = input.size * 8 / 2 ^ 56 := by
    rw [topByteWord,
      Challenge.EvmProof.Word.word_eq_ofNat_toNat (bitLengthWord input),
      Challenge.EvmProof.Word.shiftRight_ofNat hlt (by norm_num : (0x38 : Nat) < 256),
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.shiftRight_eq_div_pow,
      bitLengthWord_toNat input hfit]
    rw [Nat.mod_eq_of_lt]
    have hbits : input.size * 8 < 2 ^ 256 := by
      have hto := bitLengthWord_toNat input hfit
      omega
    exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hbits
  rw [hshift,
    Challenge.EvmProof.Memory.getD0_eq_getElem _ _
      (by simp : (7 : Nat) < (Padding.lengthBytes input).size),
    Padding.lengthByte input 7 (by norm_num)]

theorem lengthShift_byte_eq (input : ByteArray) (hfit : CalldataFits input)
    (i : Nat) (hi : i < 8) :
    UInt8.ofNat ((lengthShift input i).toNat % 256) =
      (Padding.lengthBytes input)[i]?.getD 0 := by
  rw [lengthShift_toNat input hfit i,
    Challenge.EvmProof.Memory.getD0_eq_getElem _ _
      (by simpa using hi : i < (Padding.lengthBytes input).size),
    Padding.lengthByte input i hi]

/-- Pointwise image of the footer memory after `i` loop steps. -/
theorem lengthLoopMemory_getD (input : ByteArray) (hfit : CalldataFits input)
    (i : Nat) (hi : i ≤ 9) (a : Nat) :
    (lengthLoopMemory input i)[a]?.getD 0 =
      if (Padding.messageOffset + Padding.paddedLength input.size - 8) ≤ a ∧ a < (Padding.messageOffset + Padding.paddedLength input.size - 8) + i then
        if a - (Padding.messageOffset + Padding.paddedLength input.size - 8) < 8 then
          (Padding.lengthBytes input)[a - (Padding.messageOffset + Padding.paddedLength input.size - 8)]?.getD 0
        else UInt8.ofNat ((lengthShift input 8).toNat % 256)
      else (padSentinel input).memory[a]?.getD 0 := by
  induction i with
  | zero =>
      have hzero : ¬ ((Padding.messageOffset + Padding.paddedLength input.size - 8) ≤ a ∧
          a < (Padding.messageOffset + Padding.paddedLength input.size - 8) + 0) := by
        omega
      rw [lengthLoopMemory, if_neg hzero]
  | succ i ih =>
      have hii : i < 9 := by omega
      rw [lengthLoopMemory, MachineState.writeBytes_getElem?_getD,
        lengthAddr_toNat input hfit i (by omega)]
      simp only [oneByte_size]
      by_cases h8 : i < 8
      · rw [lengthShift_byte_eq input hfit i h8, ih (by omega)]
        by_cases hin : (Padding.messageOffset + Padding.paddedLength input.size - 8) + i ≤ a ∧ a < (Padding.messageOffset + Padding.paddedLength input.size - 8) + i + 1
        · have haeq : a = (Padding.messageOffset + Padding.paddedLength input.size - 8) + i := by omega
          subst haeq
          simp [h8]
          rfl
        · rw [if_neg (by omega)]
          by_cases hlt : (Padding.messageOffset + Padding.paddedLength input.size - 8) ≤ a ∧ a < (Padding.messageOffset + Padding.paddedLength input.size - 8) + i
          · rw [if_pos hlt, if_pos (by omega), if_pos (by omega)]
          · have hne : ¬ ((Padding.messageOffset + Padding.paddedLength input.size - 8) ≤ a ∧ a < (Padding.messageOffset + Padding.paddedLength input.size - 8) + (i + 1)) := by
              omega
            rw [if_neg hlt, if_neg hne]
      · have hi8 : i = 8 := by omega
        subst hi8
        rw [ih (by omega)]
        by_cases hin : (Padding.messageOffset + Padding.paddedLength input.size - 8) + 8 ≤ a ∧ a < (Padding.messageOffset + Padding.paddedLength input.size - 8) + 8 + 1
        · have haeq : a = (Padding.messageOffset + Padding.paddedLength input.size - 8) + 8 := by omega
          subst haeq
          simp
          rfl
        · rw [if_neg (by omega)]
          by_cases hlt : (Padding.messageOffset + Padding.paddedLength input.size - 8) ≤ a ∧ a < (Padding.messageOffset + Padding.paddedLength input.size - 8) + 8
          · rw [if_pos hlt, if_pos (by omega), if_pos (by omega)]
          · have hne : ¬ ((Padding.messageOffset + Padding.paddedLength input.size - 8) ≤ a ∧ a < (Padding.messageOffset + Padding.paddedLength input.size - 8) + 9) := by
              omega
            rw [if_neg hlt, if_neg hne]

theorem padFinalMemory_getD (input : ByteArray) (_hfit : CalldataFits input) (a : Nat)
    (ha : a < Padding.messageOffset + Padding.paddedLength input.size) :
    (padFinalMemory input)[a]?.getD 0 =
      if (Padding.messageOffset + Padding.paddedLength input.size - 8) ≤ a ∧ a < (Padding.messageOffset + Padding.paddedLength input.size - 8) + 8 then
        (Padding.lengthBytes input)[a - (Padding.messageOffset + Padding.paddedLength input.size - 8)]?.getD 0
      else (padSentinel input).memory[a]?.getD 0 := by
  have hstop : lengthStop input ≤ 9 := lengthStop_le input
  have hzero := lengthShift_stop_zero input _hfit
  change (lengthLoopMemory input (lengthStop input))[a]?.getD 0 = _
  rw [lengthLoopMemory_getD input _hfit (lengthStop input) hstop a]
  by_cases hin :
      (Padding.messageOffset + Padding.paddedLength input.size - 8) ≤ a ∧
        a < (Padding.messageOffset + Padding.paddedLength input.size - 8) + lengthStop input
  · rw [if_pos hin, if_pos (by omega), if_pos (by omega)]
  · rw [if_neg hin]
    by_cases hfull :
        (Padding.messageOffset + Padding.paddedLength input.size - 8) ≤ a ∧
          a < (Padding.messageOffset + Padding.paddedLength input.size - 8) + 8
    · rw [if_pos hfull]
      have hj : a - (Padding.messageOffset + Padding.paddedLength input.size - 8) < 8 := by
        omega
      have hij : lengthStop input ≤
          a - (Padding.messageOffset + Padding.paddedLength input.size - 8) := by
        omega
      have hbyte := lengthBytes_of_shift_zero input _hfit (lengthStop input)
        (a - (Padding.messageOffset + Padding.paddedLength input.size - 8)) hij hj hzero
      have hs := sentinel_size_le input _hfit
      have hsent := Challenge.EvmProof.Memory.getElem?_getD_eq_zero_of_size_le
        (padSentinel input).memory a (by omega)
      rw [hsent, hbyte]
    · rw [if_neg hfull]

theorem padFinalMemory_getD_paddedMemory (input : ByteArray)
    (hfit : CalldataFits input) (a : Nat)
    (ha : a < Padding.messageOffset + Padding.paddedLength input.size)
    (hd : a ≠ 165 ∧ a ≠ 188) :
    (padFinalMemory input)[a]?.getD 0 =
      (Padding.paddedMemory (padLengthReady input).memory input)[a]?.getD 0 := by
  have hclean : (padGuardMiss input).memory =
      Padding.copiedMemory (padLengthReady input).memory input := by
    simp [padGuardMiss, padCopied, padCopyDone,
      Padding.copiedMemory, Challenge.EvmProof.Memory.readPadded_zero_size]
  have hsentinel : (padSentinel input).memory[a]?.getD 0 =
      (Padding.sentinelMemory (padLengthReady input).memory input)[a]?.getD 0 := by
    change (MachineState.writeBytes (HoistedInherited.ColdGuardFixup.wMemory (padGuardMiss input).memory
      HoistedInherited.ColdGuardFixup.dirtyB HoistedInherited.ColdGuardFixup.dirtyC) (ByteArray.mk #[0x80])
      (Padding.messageOffset + input.size))[a]?.getD 0 = _
    rw [hclean, Padding.sentinelMemory, MachineState.writeBytes_getElem?_getD,
      MachineState.writeBytes_getElem?_getD, HoistedInherited.ColdGuardFixup.wMemory_getD _ _ _ a hd.1 hd.2]
  rw [padFinalMemory_getD input hfit a ha, Padding.paddedMemory,
    MachineState.writeBytes_getElem?_getD, hsentinel]
  simp only [Padding.lengthBytes_size]

theorem padReturned_memory (input : ByteArray) (_hfit : CalldataFits input) :
    (padReturned input).memory = padFinalMemory input := by
  rfl

theorem padReturned_readPadded (input : ByteArray) (hfit : CalldataFits input)
    (a n : Nat) (ha : a + n ≤ Padding.messageOffset + Padding.paddedLength input.size)
    (hd : a + n ≤ 165 ∨ 189 ≤ a) :
    MachineState.readPadded (padReturned input).memory a n =
      MachineState.readPadded
        (Padding.paddedMemory (padLengthReady input).memory input) a n := by
  apply Challenge.EvmProof.Memory.readPadded_congr
  intro i hi
  rw [padReturned_memory input hfit]
  exact padFinalMemory_getD_paddedMemory input hfit (a + i) (by omega) ⟨by omega, by omega⟩

theorem padReturned_readWord (input : ByteArray) (hfit : CalldataFits input)
    (a : Nat) (ha : a + 32 ≤ Padding.messageOffset + Padding.paddedLength input.size)
    (hd : a + 32 ≤ 165 ∨ 189 ≤ a) :
    MachineState.readWord (padReturned input).memory a =
      MachineState.readWord
        (Padding.paddedMemory (padLengthReady input).memory input) a := by
  unfold MachineState.readWord
  rw [padReturned_readPadded input hfit a 32 ha hd]

theorem padReturned_getD_window (input : ByteArray) (hfit : CalldataFits input)
    (a : Nat) (ha : a < Padding.messageOffset + Padding.paddedLength input.size)
    (hd : a ≠ 165 ∧ a ≠ 188) :
    (padReturned input).memory[a]?.getD 0 =
      (Padding.paddedMemory (padLengthReady input).memory input)[a]?.getD 0 := by
  rw [padReturned_memory input hfit]
  exact padFinalMemory_getD_paddedMemory input hfit a ha hd

theorem lengthLoopMemory_size (input : ByteArray) (hfit : CalldataFits input)
    (i : Nat) (hi : i ≤ 9) :
    (lengthLoopMemory input i).size =
      if i = 0 then (padSentinel input).memory.size
      else (Padding.messageOffset + Padding.paddedLength input.size - 8) + i := by
  induction i with
  | zero =>
      simp [lengthLoopMemory]
  | succ i ih =>
      have hii : i < 9 := by omega
      rw [lengthLoopMemory, MachineState.writeBytes_size,
        lengthAddr_toNat input hfit i (by omega), ih (by omega)]
      simp only [oneByte_size, if_neg (by decide : ¬ (1 = 0))]
      by_cases hi0 : i = 0
      · subst i
        have hs := sentinel_size_le input hfit
        simp at ih ⊢
        omega
      · simp only [if_neg hi0]
        simp at ih ⊢
        omega

theorem padFinalMemory_size (input : ByteArray) (hfit : CalldataFits input) :
    (padFinalMemory input).size =
      footerStart input + lengthStop input := by
  have hstop : lengthStop input ≤ 9 := lengthStop_le input
  have hs := lengthLoopMemory_size input hfit (lengthStop input) hstop
  have hstop0 : lengthStop input ≠ 0 := Nat.ne_of_gt (lengthStop_pos input)
  change (lengthLoopMemory input (lengthStop input)).size = _
  unfold footerStart
  rw [hs, if_neg hstop0]

theorem lengthLoopMemory_final_at_stop (input : ByteArray) :
    lengthLoopMemory input (lengthStop input) = padFinalMemory input := by
  rfl

private theorem lengthExitReturned_eq_stop (input : ByteArray)
    (_hfit : CalldataFits input) :
    lengthExitReturned input (lengthStop input) = padReturned input := by
  unfold lengthExitReturned lengthExitEntered padReturned
  rfl

def gasSteps_lengthExitEntered (input : ByteArray) (i : Nat) :
    Challenge.EvmProof.GasSteps (lengthExitEntered input i)
      (lengthExitReturned input i) := by
  have g1raw := Challenge.EvmProof.DataStepper.runLocatedBlock_sound
    HoistedInherited.Artifact.submissionArtifact .Osaka lengthExitPath (by rfl) (by rfl)
    (run_lengthExitPop input i) (by rfl) (by rfl)
  exact Challenge.EvmProof.GasSteps.cast g1raw rfl rfl

def gasSteps_lengthIterationExit (input : ByteArray) (hfit : CalldataFits input)
    (i : Nat) (hi : i < 9) (hz : lengthShift input (i + 1) = ⟨0⟩) :
    Challenge.EvmProof.GasSteps (lengthLoopState input i)
      (lengthExitReturned input (i + 1)) := by
  have g₁ := Challenge.EvmProof.DataStepper.runLocatedBlock_sound
    HoistedInherited.Artifact.submissionArtifact .Osaka lengthBodyPath (by rfl) (by rfl)
    (run_lengthBody input hfit i hi) (by rfl) (by rfl)
  have g2raw := Challenge.EvmProof.DataStepper.runLocatedBlock_sound
    HoistedInherited.Artifact.submissionArtifact .Osaka lengthBranchPath (by rfl) (by rfl)
    (run_lengthBranchExit input i hz) (by rfl) (by rfl)
  have g₂ := Challenge.EvmProof.GasSteps.cast g2raw rfl
    (lengthExitPending_eq input i)
  exact g₁.trans (g₂.trans
    (gasSteps_lengthExitEntered input (i + 1)))

/-- Run the footer loop from a known nonzero residual with bounded shifts left. -/
noncomputable def gasSteps_lengthLoopFrom (input : ByteArray)
    (hfit : CalldataFits input) :
    (fuel i : Nat) → i + fuel = 9 →
      (∀ j, 0 < j → j ≤ i → lengthShift input j ≠ ⟨0⟩) →
      lengthShift input i ≠ ⟨0⟩ →
    Challenge.EvmProof.GasSteps (lengthLoopState input i) (padReturned input)
  | 0, i, hsum, _hprior, hne => by
      have hi : i = 9 := by omega
      subst hi
      exact False.elim (hne (lengthShift_nine input hfit))
  | fuel + 1, i, hsum, hprior, hne =>
      if hz : lengthShift input (i + 1) = ⟨0⟩ then
        have hstop := lengthStop_eq_succ_of_nonzero input i (by omega) hprior hz
        have hret : lengthExitReturned input (i + 1) = padReturned input := by
          rw [← hstop]
          exact lengthExitReturned_eq_stop input hfit
        Challenge.EvmProof.GasSteps.cast
          (gasSteps_lengthIterationExit input hfit i (by omega) hz) rfl hret
      else
        have hprior' : ∀ j, 0 < j → j ≤ i + 1 →
            lengthShift input j ≠ ⟨0⟩ := by
          intro j hj hjle
          by_cases hji : j ≤ i
          · exact hprior j hj hji
          · have hjeq : j = i + 1 := by omega
            subst hjeq
            exact hz
        (gasSteps_lengthIteration input hfit i (by omega) hz).trans
          (gasSteps_lengthLoopFrom input hfit fuel (i + 1) (by omega)
            hprior' hz)

noncomputable def gasSteps_lengthLoop (input : ByteArray) (hfit : CalldataFits input) :
    Challenge.EvmProof.GasSteps (lengthLoopState input 0) (padReturned input) :=
  if hz : lengthShift input 1 = ⟨0⟩ then
    have hstop := lengthStop_eq_succ_of_nonzero input 0 (by norm_num)
      (fun j hj hle => by omega) hz
    have hstop' : lengthStop input = 1 := by simpa using hstop
    have hret : lengthExitReturned input 1 = padReturned input := by
      rw [← hstop']
      exact lengthExitReturned_eq_stop input hfit
    Challenge.EvmProof.GasSteps.cast
      (gasSteps_lengthIterationExit input hfit 0 (by norm_num) hz) rfl hret
  else
    (gasSteps_lengthIteration input hfit 0 (by norm_num) hz).trans
      (gasSteps_lengthLoopFrom input hfit 8 1 (by norm_num)
        (fun j hj hle => by
          have hj1 : j = 1 := by omega
          subst hj1
          exact hz) hz)

/-- The footer setup (172..191) pushes the loop head 4547, the bit length and the rounded length
offset; at 187 the offset gets its `+ 89` and `DUP3 JUMP` enters the loop head. -/
def footerA := lengthFooterSetupPath.take 9
def footerB := lengthFooterSetupPath.drop 9

theorem lengthFooterSetupPath_split : lengthFooterSetupPath = footerA ++ footerB :=
  (List.take_append_drop 9 _).symm

def footerRounded (input : ByteArray) : State :=
  { padSentinel input with
    pc := UInt256.ofNat 9737
    stack := PadLimitArithmetic.coldRounded (UInt256.ofNat input.size) :: bitLengthWord input ::
      UInt256.ofNat 4583 :: padFrame input }

set_option maxHeartbeats 800000 in
private theorem run_footerA (input : ByteArray) :
    Challenge.EvmProof.DataStepper.runLocatedBlock footerA (padSentinel input) =
      some (footerRounded input) := by
  simp [footerA, lengthFooterSetupPath, HoistedInherited.Artifact.padFooterSetupPath,
    Challenge.EvmProof.DataStepper.runLocatedBlock,
    Challenge.EvmProof.DataStepper.runLocated, Challenge.EvmProof.DataStepper.runInstr,
    footerRounded, padFrame, StaggerPersistentFrame.frame, bitLengthWord,
    PadLimitArithmetic.coldRounded]

/-- The state at the loop head right after `DUP3 JUMP`, written as an update of the sentinel state
(same shape as `footerRounded`), so the block run below never unfolds the loop's memory recursion. -/
def footerEntered (input : ByteArray) : State :=
  { padSentinel input with
    pc := UInt256.ofNat 4583
    stack := (PadLimitArithmetic.coldRounded (UInt256.ofNat input.size) + UInt256.ofNat 89) ::
      bitLengthWord input :: UInt256.ofNat 4583 :: padFrame input }

private theorem footerEntered_eq (input : ByteArray) :
    footerEntered input = lengthLoopState input 0 := by
  have hm : lengthLoopMemory input 0 = (padSentinel input).memory := rfl
  have ha : lengthLoopActiveWords input 0 = (padSentinel input).activeWords := rfl
  have haddr : lengthAddr input 0 =
      PadLimitArithmetic.coldRounded (UInt256.ofNat input.size) + UInt256.ofNat 89 := rfl
  have hshift : lengthShift input 0 = bitLengthWord input := rfl
  unfold footerEntered lengthLoopState
  rw [hm, ha, haddr, hshift]

/-- `footerB` is `PUSH1 89 ADD DUP3` (189..190) and then the `JUMP` at 191. The jump runs as its own
located step (as in the earlier layout's `run_footJump`): one `simp` over the whole block does not
finish inside the memory budget. -/
def footerPreJump (input : ByteArray) : State :=
  { padSentinel input with
    pc := UInt256.ofNat 9741
    stack := UInt256.ofNat 4583 ::
      (PadLimitArithmetic.coldRounded (UInt256.ofNat input.size) + UInt256.ofNat 89) ::
      bitLengthWord input :: UInt256.ofNat 4583 :: padFrame input }

set_option maxHeartbeats 800000 in
private theorem run_footerB3 (input : ByteArray) :
    Challenge.EvmProof.DataStepper.runLocatedBlock (footerB.take 3) (footerRounded input) =
      some (footerPreJump input) := by
  have haddressOrder : UInt256.ofNat 89 + PadLimitArithmetic.coldRounded (UInt256.ofNat input.size) =
      PadLimitArithmetic.coldRounded (UInt256.ofNat input.size) + UInt256.ofNat 89 :=
    Challenge.EvmProof.Word.word_add_comm _ _
  simp [footerB, lengthFooterSetupPath, HoistedInherited.Artifact.padFooterSetupPath,
    Challenge.EvmProof.DataStepper.runLocatedBlock,
    Challenge.EvmProof.DataStepper.runLocated, Challenge.EvmProof.DataStepper.runInstr,
    footerRounded, footerPreJump, padFrame, StaggerPersistentFrame.frame, haddressOrder]

private theorem run_footJump (input : ByteArray) :
    Challenge.EvmProof.DataStepper.runLocatedBlock (footerB.drop 3) (footerPreJump input) =
      some (footerEntered input) := by
  obtain ⟨loc, hloc, hidx, hins⟩ :
      ∃ loc, footerB.drop 3 = [loc] ∧ loc.index = 5392 ∧ loc.instruction = .op .JUMP :=
    ⟨_, rfl, rfl, rfl⟩
  have hpc : (footerPreJump input).pc.toNat =
      HoistedInherited.Artifact.submissionArtifact.instructionPC loc.index := by
    rw [hidx]
    change 9741 = HoistedInherited.Artifact.submissionArtifact.instructionPC 5392
    rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
  have hj : Challenge.EvmProof.DataStepper.runInstr (.op .JUMP) (footerPreJump input) =
      some (footerEntered input) := by
    simp [Challenge.EvmProof.DataStepper.runInstr, footerPreJump, footerEntered, padFrame,
      StaggerPersistentFrame.frame, validJump4949]
  have hl : Challenge.EvmProof.DataStepper.runLocated loc (footerPreJump input) =
      some (footerEntered input) := by
    unfold Challenge.EvmProof.DataStepper.runLocated
    rw [if_pos hpc, hins]
    exact hj
  rw [hloc, Challenge.EvmProof.DataStepper.runLocatedBlock, hl]

private theorem run_footerB (input : ByteArray) :
    Challenge.EvmProof.DataStepper.runLocatedBlock footerB (footerRounded input) =
      some (lengthLoopState input 0) := by
  rw [← footerEntered_eq input, ← List.take_append_drop 3 footerB]
  exact Challenge.EvmProof.DataStepper.runLocatedBlock_append _ _ _ _ _
    (run_footerB3 input) rfl (run_footJump input)

private theorem run_lengthFooterSetup (input : ByteArray) :
    Challenge.EvmProof.DataStepper.runLocatedBlock lengthFooterSetupPath
      (padSentinel input) = some (lengthLoopState input 0) := by
  rw [lengthFooterSetupPath_split]
  exact Challenge.EvmProof.DataStepper.runLocatedBlock_append _ _ _ _ _
    (run_footerA input) rfl (run_footerB input)

def gasSteps_lengthSetup (input : ByteArray) (hfit : CalldataFits input) :
    Challenge.EvmProof.GasSteps (padDirty input)
      (lengthLoopState input 0) := by
  have g₂ₐ := Challenge.EvmProof.DataStepper.runLocatedBlock_sound
    HoistedInherited.Artifact.submissionArtifact .Osaka lengthSentinelAddressPath (by rfl) (by rfl)
    (run_lengthSentinelAddress input) (by rfl) deployAddress_not_precompile
  have g2raw := Challenge.EvmProof.DataStepper.runLocatedBlock_sound
    HoistedInherited.Artifact.submissionArtifact .Osaka lengthSentinelStorePath (by rfl) (by rfl)
    (run_lengthSentinelStore input hfit) (by rfl) deployAddress_not_precompile
  have g2b := Challenge.EvmProof.GasSteps.cast g2raw rfl
    (padSentinelStored_eq input hfit)
  have g₃ := Challenge.EvmProof.DataStepper.runLocatedBlock_sound
    HoistedInherited.Artifact.submissionArtifact .Osaka lengthFooterSetupPath (by rfl) (by rfl)
    (run_lengthFooterSetup input) (by rfl) deployAddress_not_precompile
  exact g₂ₐ.trans (g2b.trans g₃)

def gasSteps_lengthReady (input : ByteArray) :
    Challenge.EvmProof.GasSteps (padEntry input) (padLengthReady input) :=
  Challenge.EvmProof.GasSteps.refl _

def gasSteps_lengthCopy (input : ByteArray) (hfit : CalldataFits input) :
    Challenge.EvmProof.GasSteps (padLengthReady input) (padCopyDone input) :=
  Challenge.EvmProof.DataStepper.runLocatedBlock_sound
    HoistedInherited.Artifact.submissionArtifact .Osaka lengthCopyPath (by rfl) (by rfl)
    (run_lengthCopy input hfit) (by rfl) deployAddress_not_precompile

/-- Complete certified execution from the challenge initial state through the
calldata copy and the frame pushes. -/
private def gasSteps_padPrefix (input : ByteArray) (hfit : CalldataFits input)
    (entryPrefix : Challenge.EvmProof.GasSteps (initialState submissionBytecode input 0)
      (HoistedInherited.Execution.atPC input 246)) :
    Challenge.EvmProof.GasSteps (initialState submissionBytecode input 0)
      (padFramed input) :=
  (HoistedInherited.Main.gasSteps_initialize input entryPrefix).trans
    ((gasSteps_enterPad input).trans ((gasSteps_lengthReady input).trans
      ((gasSteps_lengthCopy input hfit).trans (gasSteps_push input))))

noncomputable def gasSteps_padBody (input : ByteArray) (hfit : CalldataFits input)
    (hn32 : input.size ≠ 32) (hnz : ¬ (input.size % 64 = 0 ∧ input.size < 256)) :
    Challenge.EvmProof.GasSteps (padFramed input) (padReturned input) :=
  (gasSteps_guardMiss input hfit hn32 hnz).trans
    ((gasSteps_lengthSetup input hfit).trans (gasSteps_lengthLoop input hfit))

/-- Block-loop entry state.  A fast-entry input skips the sentinel and footer stores: its
pad-only block is scheduled from the table and never reads message memory.  Every other
input (including whole-block inputs of 256 bytes or more) writes the sentinel and footer. -/
def entryState (input : ByteArray) : State :=
  if input.size % 64 = 0 ∧ input.size < 256 then padSkip input else padReturned input

theorem entryState_skip (input : ByteArray) (hz : input.size % 64 = 0 ∧ input.size < 256) :
    entryState input = padSkip input := by
  unfold entryState
  rw [if_pos hz]

theorem entryState_miss (input : ByteArray) (hnz : ¬ (input.size % 64 = 0 ∧ input.size < 256)) :
    entryState input = padReturned input := by
  unfold entryState
  rw [if_neg hnz]

theorem entryState_eta (input : ByteArray) :
    entryState input = {entryState input with
      pc := UInt256.ofNat 461
      stack := if input.size % 64 = 0 ∧ input.size < 256 then initialFrame input else glFrame} := by
  by_cases hz : input.size % 64 = 0 ∧ input.size < 256
  · simp only [entryState_skip input hz, if_pos hz]
    rfl
  · simp only [entryState_miss input hz, if_neg hz]
    rfl

noncomputable def gasSteps_pad (input : ByteArray) (hfit : CalldataFits input)
    (hn32 : input.size ≠ 32)
    (entryPrefix : Challenge.EvmProof.GasSteps (initialState submissionBytecode input 0)
      (HoistedInherited.Execution.atPC input 246)) :
    Challenge.EvmProof.GasSteps (initialState submissionBytecode input 0)
      (entryState input) :=
  if hz : input.size % 64 = 0 ∧ input.size < 256 then
    Challenge.EvmProof.GasSteps.cast
      ((gasSteps_padPrefix input hfit entryPrefix).trans (gasSteps_guardSkip input hfit hz))
      rfl (entryState_skip input hz).symm
  else
    Challenge.EvmProof.GasSteps.cast
      ((gasSteps_padPrefix input hfit entryPrefix).trans (gasSteps_padBody input hfit hn32 hz))
      rfl (entryState_miss input hz).symm


/-! Stack suffix adapters reuse the established symbolic path evaluations. -/
private def liftTail (path : List (Challenge.EvmProof.DataStepper.Located
    HoistedInherited.Artifact.submissionArtifact .Osaka)) {s t : State}
    (hr : Challenge.EvmProof.DataStepper.runLocatedBlock path s = some t)
    (hsize : s.stack.length + path.length ≤ 100)
    (rho : List UInt256) (hcap : rho.length ≤ 20)
    (hcode : s.executionEnv.code = HoistedInherited.Artifact.submissionArtifact.code)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (StackTail.append s rho) (StackTail.append t rho) :=
  StackTail.gasSteps path rho (by omega) hr hcode hfork hrun hnp

def tail_enter (input : ByteArray)
    (rho : List UInt256) (hcap : rho.length ≤ 20) :
    Challenge.EvmProof.GasSteps (StackTail.append (HoistedInherited.Main.initializedState input) rho)
      (StackTail.append (padEntry input) rho) :=
  liftTail enterPath (run_enter input) (by change 2 ≤ 100; decide) rho hcap rfl rfl rfl deployAddress_not_precompile

def tail_length (input : ByteArray)
    (rho : List UInt256) (_hcap : rho.length ≤ 20) :
    Challenge.EvmProof.GasSteps (StackTail.append (padEntry input) rho)
      (StackTail.append (padLengthReady input) rho) :=
  Challenge.EvmProof.GasSteps.refl _

def tail_copy (input : ByteArray) (hfit : CalldataFits input)
    (rho : List UInt256) (hcap : rho.length ≤ 20) :
    Challenge.EvmProof.GasSteps (StackTail.append (padLengthReady input) rho)
      (StackTail.append (padCopied input) rho) :=
  liftTail lengthCopyPath (run_lengthCopy input hfit) (by change 8 ≤ 100; decide) rho hcap rfl rfl rfl
    deployAddress_not_precompile

def tail_guardSkip (input : ByteArray) (hfit : CalldataFits input) (hz : input.size % 64 = 0 ∧ input.size < 256)
    (rho : List UInt256) (hcap : rho.length ≤ 20) :
    Challenge.EvmProof.GasSteps (StackTail.append (padFramed input) rho)
      (StackTail.append (padSkip input) rho) :=
  liftTail guardPath (run_guardSkip input hfit hz) (by change 20 ≤ 100; decide) rho hcap rfl rfl rfl deployAddress_not_precompile

def tail_guardTaken (input : ByteArray) (hfit : CalldataFits input) (hnz : ¬ (input.size % 64 = 0 ∧ input.size < 256))
    (rho : List UInt256) (hcap : rho.length ≤ 20) :
    Challenge.EvmProof.GasSteps (StackTail.append (padFramed input) rho)
      (StackTail.append (padGuardTaken input) rho) :=
  liftTail guardPath (run_guardMiss input hfit hnz) (by change 20 ≤ 100; decide) rho hcap rfl rfl rfl deployAddress_not_precompile

def tail_sentinelAddress (input : ByteArray)
    (rho : List UInt256) (hcap : rho.length ≤ 20) :
    Challenge.EvmProof.GasSteps (StackTail.append (padDirty input) rho)
      (StackTail.append (padSentinelAddressReady input) rho) :=
  liftTail lengthSentinelAddressPath (run_lengthSentinelAddress input) (by change 19 ≤ 100; decide) rho hcap rfl rfl rfl deployAddress_not_precompile

def tail_sentinelStore (input : ByteArray) (hfit : CalldataFits input)
    (rho : List UInt256) (hcap : rho.length ≤ 20) :
    Challenge.EvmProof.GasSteps (StackTail.append (padSentinelAddressReady input) rho)
      (StackTail.append (padSentinelStored input) rho) :=
  liftTail lengthSentinelStorePath (run_lengthSentinelStore input hfit) (by change 18 ≤ 100; decide) rho hcap rfl rfl rfl deployAddress_not_precompile

def tail_footer (input : ByteArray)
    (rho : List UInt256) (hcap : rho.length ≤ 20) :
    Challenge.EvmProof.GasSteps (StackTail.append (padSentinel input) rho)
      (StackTail.append (lengthLoopState input 0) rho) :=
  liftTail lengthFooterSetupPath (run_lengthFooterSetup input) (by change 28 ≤ 100; decide) rho hcap rfl rfl rfl deployAddress_not_precompile

def tail_body (input : ByteArray) (hfit : CalldataFits input) (i : Nat) (hi : i < 9)
    (rho : List UInt256) (hcap : rho.length ≤ 20) :
    Challenge.EvmProof.GasSteps (StackTail.append (lengthLoopState input i) rho)
      (StackTail.append (lengthSteppedState input i) rho) :=
  liftTail lengthBodyPath (run_lengthBody input hfit i hi) (by change 28 ≤ 100; decide) rho hcap rfl rfl rfl deployAddress_not_precompile

def tail_back (input : ByteArray) (i : Nat) (hne : lengthShift input (i + 1) ≠ ⟨0⟩)
    (rho : List UInt256) (hcap : rho.length ≤ 20) :
    Challenge.EvmProof.GasSteps (StackTail.append (lengthSteppedState input i) rho)
      (StackTail.append (lengthBackReturned input i) rho) :=
  liftTail lengthBranchPath (run_lengthBranchBack input i hne) (by change 21 ≤ 100; decide) rho hcap rfl rfl rfl deployAddress_not_precompile

def tail_exitBranch (input : ByteArray) (i : Nat) (hz : lengthShift input (i + 1) = ⟨0⟩)
    (rho : List UInt256) (hcap : rho.length ≤ 20) :
    Challenge.EvmProof.GasSteps (StackTail.append (lengthSteppedState input i) rho)
      (StackTail.append (lengthExitPending input i) rho) :=
  liftTail lengthBranchPath (run_lengthBranchExit input i hz) (by change 21 ≤ 100; decide) rho hcap rfl rfl rfl deployAddress_not_precompile

def tail_exitPop (input : ByteArray) (i : Nat)
    (rho : List UInt256) (hcap : rho.length ≤ 20) :
    Challenge.EvmProof.GasSteps (StackTail.append (lengthExitEntered input i) rho)
      (StackTail.append (lengthExitReturned input i) rho) :=
  liftTail lengthExitPath (run_lengthExitPop input i) (by change 29 ≤ 100; decide) rho hcap rfl rfl rfl deployAddress_not_precompile

theorem tail_sentinel_eq (input : ByteArray) (hfit : CalldataFits input) : padSentinelStored input = padSentinel input := padSentinelStored_eq input hfit

theorem tail_back_eq (input : ByteArray) (i : Nat) : lengthBackReturned input i = lengthLoopState input (i + 1) := lengthBackReturned_eq input i

theorem tail_exit_eq (input : ByteArray) (i : Nat) : lengthExitPending input i = lengthExitEntered input (i + 1) := lengthExitPending_eq input i

theorem tail_returned_eq (input : ByteArray) (hfit : CalldataFits input) : lengthExitReturned input (lengthStop input) = padReturned input := lengthExitReturned_eq_stop input hfit

/-- The entry state's active size stays far below the word range, so `MSIZE` never wraps. -/
theorem entryState_active_le (input : ByteArray) (hfit : CalldataFits input) :
    (entryState input).activeWords.toNat ≤ 2 ^ 70 := by
  have hsize : input.size < 2 ^ 64 := hfit
  have hcopy : (padCopyDone input).activeWords.toNat ≤ 2 ^ 70 := by
    change (UInt256.ofNat (MachineState.activeWordsAfter
      (padLengthReady input).activeWords.toNat Padding.messageOffset input.size)).toNat ≤ _
    have h0 : (padLengthReady input).activeWords.toNat = 0 := by rfl
    rw [h0, Challenge.EvmProof.Word.word_toNat_ofNat]
    refine Nat.le_trans (Nat.mod_le _ _) ?_
    unfold MachineState.activeWordsAfter Padding.messageOffset
    split
    · omega
    · dsimp only
      exact Nat.max_le.mpr ⟨by omega, by omega⟩
  have hloop : ∀ j, j ≤ 9 → (lengthLoopActiveWords input j).toNat ≤ 2 ^ 70 := by
    intro j
    induction j with
    | zero =>
      intro _
      change (UInt256.ofNat (MachineState.activeWordsAfter
        (padCopyDone input).activeWords.toNat (Padding.messageOffset + input.size) 1)).toNat ≤ _
      rw [Challenge.EvmProof.Word.word_toNat_ofNat]
      refine Nat.le_trans (Nat.mod_le _ _) ?_
      unfold MachineState.activeWordsAfter Padding.messageOffset
      rw [if_neg (by decide)]
      dsimp only
      exact Nat.max_le.mpr ⟨hcopy, by omega⟩
    | succ j ih =>
      intro hj
      rw [lengthLoopActiveWords_succ_toNat input hfit j (by omega)]
      have hl := Padding.paddedLength_lt input.size
      exact Nat.max_le.mpr ⟨ih (by omega), by unfold Padding.messageOffset; omega⟩
  unfold entryState
  split
  · exact hcopy
  · exact hloop _ (lengthStop_le input)

/-- On the fast entry the active size ends exactly at the copied input. -/
theorem entryState_msize_aligned (input : ByteArray) (hfit : CalldataFits input)
    (hz : input.size % 64 = 0 ∧ input.size < 256) (hpos : 0 < input.size) :
    UInt256.ofNat (32 * (entryState input).activeWords.toNat) = UInt256.ofNat (1056 + input.size) := by
  rw [entryState_skip input hz]
  exact copiedMsize_aligned input hfit (by omega) hpos

/-- On the cold route the active size ends at most one word past the padded message: the
footer loop's ninth byte (bit lengths of 2^64 or more) lands on the padded end. -/
theorem padReturned_active_upper (input : ByteArray) (hfit : CalldataFits input) :
    (padReturned input).activeWords.toNat ≤
      (Padding.messageOffset + Padding.paddedLength input.size) / 32 + 1 := by
  have hsize : input.size < 2 ^ 64 := hfit
  have hP : input.size + 9 ≤ Padding.paddedLength input.size ∧
      Padding.paddedLength input.size % 64 = 0 ∧ Padding.paddedLength input.size < input.size + 73 := by
    unfold Padding.paddedLength; omega
  have hcopy : (padCopyDone input).activeWords.toNat ≤
      (Padding.messageOffset + Padding.paddedLength input.size) / 32 + 1 := by
    change (UInt256.ofNat (MachineState.activeWordsAfter
      (padLengthReady input).activeWords.toNat Padding.messageOffset input.size)).toNat ≤ _
    have h0 : (padLengthReady input).activeWords.toNat = 0 := by rfl
    rw [h0, Challenge.EvmProof.Word.word_toNat_ofNat]
    refine Nat.le_trans (Nat.mod_le _ _) ?_
    unfold MachineState.activeWordsAfter Padding.messageOffset
    split
    · omega
    · dsimp only
      exact Nat.max_le.mpr ⟨by omega, by omega⟩
  have hloop : ∀ j, j ≤ 9 → (lengthLoopActiveWords input j).toNat ≤
      (Padding.messageOffset + Padding.paddedLength input.size) / 32 + 1 := by
    intro j
    induction j with
    | zero =>
      intro _
      change (UInt256.ofNat (MachineState.activeWordsAfter
        (padCopyDone input).activeWords.toNat (Padding.messageOffset + input.size) 1)).toNat ≤ _
      rw [Challenge.EvmProof.Word.word_toNat_ofNat]
      refine Nat.le_trans (Nat.mod_le _ _) ?_
      unfold MachineState.activeWordsAfter
      rw [if_neg (by decide)]
      dsimp only
      exact Nat.max_le.mpr ⟨hcopy, by unfold Padding.messageOffset; omega⟩
    | succ j ih =>
      intro hj
      rw [lengthLoopActiveWords_succ_toNat input hfit j (by omega)]
      exact Nat.max_le.mpr ⟨ih (by omega), by unfold Padding.messageOffset; omega⟩
  exact hloop _ (lengthStop_le input)

#print axioms gasSteps_pad
#print axioms padReturned_active_upper

end Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.PaddingTrace
