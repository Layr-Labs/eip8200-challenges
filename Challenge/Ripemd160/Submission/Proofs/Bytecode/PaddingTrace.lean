import Challenge.Ripemd160.Submission.Proofs.Bytecode.PaddingTraceCore
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PaddingTrace

open EvmSemantics
open EvmSemantics.EVM

private theorem shiftLeft_ofNat_wrap {value shift : Nat}
    (hvalue : value < 2 ^ 256) (hshift : shift < 256) :
    UInt256.shiftLeft (UInt256.ofNat value) (UInt256.ofNat shift) =
      UInt256.ofNat ((value * 2 ^ shift) % 2 ^ 256) := by
  have hshift256 : shift < 2 ^ 256 := Nat.lt_trans hshift (by norm_num)
  have hshiftWord : (UInt256.ofNat shift).toNat = shift := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hshift256]
  unfold UInt256.shiftLeft
  rw [if_neg (by omega), hshiftWord, Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt hvalue, Nat.shiftLeft_eq,
    show UInt256.size = 2 ^ 256 by rfl]

/-- Unmasked bit length: `size <<< 3 = size * 8` on `CalldataFits`. -/
theorem bitLengthWord_toNat (input : ByteArray) (hfit : CalldataFits input) :
    (bitLengthWord input).toNat = input.size * 8 := by
  have hsize : input.size < 2 ^ 256 := Nat.lt_trans hfit (by norm_num)
  have hres : input.size * 2 ^ 3 < 2 ^ 256 := by
    have : input.size * 8 < 2 ^ 64 * 8 := Nat.mul_lt_mul_of_pos_right hfit (by decide)
    omega
  rw [bitLengthWord,
    Challenge.EvmProof.Word.shiftLeft_ofNat hsize (by decide : (3 : Nat) < 256) hres,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  have : input.size * 2 ^ 3 = input.size * 8 := by
    simp [show (8 : Nat) = 2 ^ 3 by norm_num]
  rw [this, Nat.mod_eq_of_lt]
  have : input.size * 8 < 2 ^ 64 * 8 := Nat.mul_lt_mul_of_pos_right hfit (by decide)
  omega

theorem lengthShift_toNat (input : ByteArray) (hfit : CalldataFits input) (i : Nat) :
    (lengthShift input i).toNat = input.size * 8 / 2 ^ (8 * i) := by
  induction i with
  | zero => simpa [lengthShift] using bitLengthWord_toNat input hfit
  | succ i ih =>
      have hlt : (lengthShift input i).toNat < 2 ^ 256 := (lengthShift input i).val.isLt
      rw [lengthShift,
        Challenge.EvmProof.Word.word_eq_ofNat_toNat (lengthShift input i),
        Challenge.EvmProof.Word.shiftRight_ofNat hlt (by norm_num : (8 : Nat) < 256),
        Challenge.EvmProof.Word.word_toNat_ofNat, Nat.shiftRight_eq_div_pow,
        Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hlt), ih,
        Nat.div_div_eq_div_mul, ← Nat.pow_add]
      congr 2

theorem lengthShift_eight (input : ByteArray) (hfit : CalldataFits input)
    (h : input.size < 2 ^ 61) :
    lengthShift input 8 = ⟨0⟩ := by
  have hto := lengthShift_toNat input hfit 8
  have hz : input.size * 8 / 2 ^ (8 * 8) = 0 := by
    apply Nat.div_eq_of_lt
    have : input.size * 8 < 2 ^ 61 * 8 := Nat.mul_lt_mul_of_pos_right h (by decide)
    have : (2 : Nat) ^ 64 = 2 ^ 61 * 8 := by
      rw [show (8 : Nat) = 2 ^ 3 by norm_num, ← Nat.pow_add]
    omega
  apply Challenge.EvmProof.Word.word_ext
  rw [hto, hz]
  rfl

theorem lengthShift_nine (input : ByteArray) (hfit : CalldataFits input) :
    lengthShift input 9 = ⟨0⟩ := by
  have hto := lengthShift_toNat input hfit 9
  have hz : input.size * 8 / 2 ^ (8 * 9) = 0 := by
    apply Nat.div_eq_of_lt
    have : input.size * 8 < 2 ^ 64 * 8 := Nat.mul_lt_mul_of_pos_right hfit (by decide)
    have : (2 : Nat) ^ 64 * 8 = 2 ^ 67 := by
      rw [show (8 : Nat) = 2 ^ 3 by norm_num, ← Nat.pow_add]
    have : (2 : Nat) ^ 67 < 2 ^ 72 := by decide
    omega
  apply Challenge.EvmProof.Word.word_ext
  rw [hto, hz]
  rfl

/-! The machine exits after the first zero residual byte.  This finite
selector is definitionally independent of the calldata bound; the bound is
used only to prove that its fallback branch (iteration eight) is zero. -/
def lengthStop (input : ByteArray) : Nat :=
  if lengthShift input 1 = ⟨0⟩ then 1 else
  if lengthShift input 2 = ⟨0⟩ then 2 else
  if lengthShift input 3 = ⟨0⟩ then 3 else
  if lengthShift input 4 = ⟨0⟩ then 4 else
  if lengthShift input 5 = ⟨0⟩ then 5 else
  if lengthShift input 6 = ⟨0⟩ then 6 else
  if lengthShift input 7 = ⟨0⟩ then 7 else
    if lengthShift input 8 = ⟨0⟩ then 8 else 9

theorem lengthStop_pos (input : ByteArray) : 0 < lengthStop input := by
  unfold lengthStop
  split
  · omega
  · split
    · omega
    · split
      · omega
      · split
        · omega
        · split
          · omega
          · split
            · omega
            · split
              · omega
              · split
                · omega
                · omega

theorem lengthStop_le (input : ByteArray) : lengthStop input ≤ 9 := by
  unfold lengthStop
  split
  · omega
  · split
    · omega
    · split
      · omega
      · split
        · omega
        · split
          · omega
          · split
            · omega
            · split
              · omega
              · split
                · omega
                · omega

theorem lengthShift_stop_zero (input : ByteArray) (hfit : CalldataFits input) :
    lengthShift input (lengthStop input) = ⟨0⟩ := by
  simp only [lengthStop]
  split
  · assumption
  · split
    · assumption
    · split
      · assumption
      · split
        · assumption
        · split
          · assumption
          · split
            · assumption
            · split
              · assumption
              · split
                · assumption
                · exact lengthShift_nine input hfit

theorem lengthStop_eq_succ_of_nonzero (input : ByteArray) (i : Nat)
    (hi : i < 9)
    (hprior : ∀ j, 0 < j → j ≤ i → lengthShift input j ≠ ⟨0⟩)
    (hz : lengthShift input (i + 1) = ⟨0⟩) :
    lengthStop input = i + 1 := by
  interval_cases i <;> simp_all [lengthStop]

theorem footerCount_spec (input : ByteArray) (hfit : CalldataFits input) :
    1 ≤ lengthStop input ∧ lengthStop input ≤ 9 ∧
      lengthShift input (lengthStop input) = ⟨0⟩ ∧
      ∀ j, 1 ≤ j → j < lengthStop input →
        lengthShift input j ≠ ⟨0⟩ := by
  have hpos := lengthStop_pos input
  have hle := lengthStop_le input
  refine ⟨by omega, hle,
    lengthShift_stop_zero input hfit, ?_⟩
  intro j hj hstop
  have hj8 : j < 9 := by omega
  simp only [lengthStop] at hstop
  all_goals repeat' first | split at hstop | simp_all
  all_goals interval_cases j <;> simp_all

theorem lengthOffsetWord_eq (input : ByteArray) (hfit : CalldataFits input) :
    (lengthOffsetWord input).toNat =
      Padding.messageOffset + Padding.paddedLength input.size - 8 := by
  have hlt := Padding.paddedLength_lt input.size
  have hsum : Padding.paddedLength input.size + 0x458 < 2 ^ 256 := by
    unfold CalldataFits at hfit
    norm_num at hfit ⊢
    omega
  rw [lengthOffsetWord, Padding.paddedWord_eq input hfit,
    Challenge.EvmProof.Word.ofNat_add_ofNat hsum,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hsum]
  unfold Padding.messageOffset
  omega

theorem lengthAddr_toNat (input : ByteArray) (hfit : CalldataFits input)
    (i : Nat) (hi : i ≤ 9) :
    (lengthAddr input i).toNat =
      Padding.messageOffset + Padding.paddedLength input.size - 8 + i := by
  induction i with
  | zero => simpa [lengthAddr] using lengthOffsetWord_eq input hfit
  | succ i ih =>
      have hlt := Padding.paddedLength_lt input.size
      have hbound : 1 + (Padding.messageOffset + Padding.paddedLength input.size - 8 + i)
          < 2 ^ 256 := by
        unfold CalldataFits at hfit
        unfold Padding.messageOffset
        norm_num at hfit ⊢
        omega
      rw [lengthAddr,
        Challenge.EvmProof.Word.word_eq_ofNat_toNat (lengthAddr input i),
        ih (by omega),
        Challenge.EvmProof.Word.ofNat_add_ofNat hbound,
        Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hbound]
      omega

theorem topByteAddr_toNat (input : ByteArray) (hfit : CalldataFits input) :
    (topByteAddr input).toNat =
      Padding.messageOffset + Padding.paddedLength input.size - 8 + 7 := by
  have hlt := Padding.paddedLength_lt input.size
  have hbound : 7 + (Padding.messageOffset + Padding.paddedLength input.size - 8)
      < 2 ^ 256 := by
    unfold CalldataFits at hfit
    unfold Padding.messageOffset
    norm_num at hfit ⊢
    omega
  rw [topByteAddr,
    Challenge.EvmProof.Word.word_eq_ofNat_toNat (lengthOffsetWord input),
    lengthOffsetWord_eq input hfit,
    Challenge.EvmProof.Word.ofNat_add_ofNat hbound,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hbound]
  omega

/-! The recursive definition above is deliberately transparent.  The
corresponding store-step theorem is useful to callers that need the machine's
wrapped representation rather than a pre-expanded approximation. -/
@[simp] private theorem lengthLoopActiveWords_zero (input : ByteArray) :
    lengthLoopActiveWords input 0 = (padSentinel input).activeWords := by rfl

@[simp] private theorem lengthLoopActiveWords_succ (input : ByteArray) (i : Nat) :
    lengthLoopActiveWords input (i + 1) =
      UInt256.ofNat (MachineState.activeWordsAfter
        (lengthLoopActiveWords input i).toNat (lengthAddr input i).toNat 1) := by rfl

private theorem zero_toNat : (⟨0⟩ : UInt256).toNat = 0 := rfl
private theorem ofNat_zero_eq : UInt256.ofNat 0 = (⟨0⟩ : UInt256) := rfl

private theorem toNat_ne_zero_of_ne (x : UInt256) (hne : x ≠ ⟨0⟩) :
    x.toNat ≠ 0 := by
  intro h
  exact hne (Challenge.EvmProof.Word.word_ext (h.trans zero_toNat.symm))

private theorem isZero_of_ne (x : UInt256) (hne : x ≠ ⟨0⟩) :
    UInt256.isZero x = UInt256.ofNat 0 := by
  unfold UInt256.isZero
  exact if_neg (toNat_ne_zero_of_ne x hne)

private theorem isZero_of_eq (x : UInt256) (hz : x = ⟨0⟩) :
    UInt256.isZero x = UInt256.ofNat 1 := by
  subst hz
  unfold UInt256.isZero
  exact if_pos zero_toNat

private theorem run_lengthBody (input : ByteArray) (_hfit : CalldataFits input)
    (i : Nat) (_hi : i < 9) :
    Challenge.EvmProof.DataStepper.runLocatedBlock lengthBodyPath
      (lengthLoopState input i) = some (lengthSteppedState input i) := by
  simp [lengthBodyPath, lengthIterationPath,
    Challenge.EvmProof.DataStepper.runLocatedBlock,
    Challenge.EvmProof.DataStepper.runLocated, Challenge.EvmProof.DataStepper.runInstr,
    lengthSteppedState, lengthLoopState, lengthLoopMemory, lengthAddr,
    lengthShift, List.exchange, State.activeWordsAfterUInt256,
    lengthLoopActiveWords]

private theorem run_lengthBranchBack (input : ByteArray) (i : Nat)
    (hne : lengthShift input (i + 1) ≠ ⟨0⟩) :
    Challenge.EvmProof.DataStepper.runLocatedBlock lengthBranchPath
      (lengthSteppedState input i) = some (lengthBackReturned input i) := by
  have htrue : UInt256.isTrue (lengthShift input (i + 1)) = true := by
    simp [UInt256.isTrue, toNat_ne_zero_of_ne _ hne]
  simp [lengthBranchPath, lengthIterationPath,
    Challenge.EvmProof.DataStepper.runLocatedBlock,
    Challenge.EvmProof.DataStepper.runLocated, Challenge.EvmProof.DataStepper.runInstr,
    lengthSteppedState, lengthBranchReady, lengthBackReturned, htrue]

private theorem run_lengthBranchExit (input : ByteArray) (i : Nat)
    (hz : lengthShift input (i + 1) = ⟨0⟩) :
    Challenge.EvmProof.DataStepper.runLocatedBlock lengthBranchPath
      (lengthSteppedState input i) = some (lengthExitPending input i) := by
  have hfalse : UInt256.isTrue (lengthShift input (i + 1)) = false := by
    simp [UInt256.isTrue, hz]
  simp [lengthBranchPath, lengthIterationPath,
    Challenge.EvmProof.DataStepper.runLocatedBlock,
    Challenge.EvmProof.DataStepper.runLocated, Challenge.EvmProof.DataStepper.runInstr,
    lengthSteppedState, lengthBranchReady, lengthExitPending, hfalse]

def gasSteps_lengthIteration (input : ByteArray) (hfit : CalldataFits input)
    (i : Nat) (hi : i < 9) (hne : lengthShift input (i + 1) ≠ ⟨0⟩) :
    Challenge.EvmProof.GasSteps (lengthLoopState input i)
      (lengthLoopState input (i + 1)) := by
  have g₁ := Challenge.EvmProof.DataStepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka lengthBodyPath (by rfl) (by rfl)
    (run_lengthBody input hfit i hi) (by rfl) (by rfl)
  have g2raw := Challenge.EvmProof.DataStepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka lengthBranchPath (by rfl) (by rfl)
    (run_lengthBranchBack input i hne) (by rfl) (by rfl)
  have g₂ := Challenge.EvmProof.GasSteps.cast g2raw rfl
    (lengthBackReturned_eq input i)
  exact g₁.trans g₂

/-! ## Loop exit and return -/

def padFinalMemory (input : ByteArray) : ByteArray :=
  (lengthLoopState input (lengthStop input)).memory

def padReturned (input : ByteArray) : State :=
  { lengthLoopState input (lengthStop input) with
    pc := UInt256.ofNat 376
    stack := padFrame input }

private theorem lengthLoopActiveWords_succ_toNat (input : ByteArray)
    (hfit : CalldataFits input) (i : Nat) (hi : i ≤ 9) :
    (lengthLoopActiveWords input (i + 1)).toNat =
      Nat.max (lengthLoopActiveWords input i).toNat
        ((Padding.messageOffset + Padding.paddedLength input.size - 8 + i) / 32 + 1) := by
  have hlt := Padding.paddedLength_lt input.size
  have hcur : (lengthLoopActiveWords input i).toNat < 2 ^ 256 :=
    (lengthLoopActiveWords input i).val.isLt
  have hdiv : (Padding.messageOffset + Padding.paddedLength input.size - 8 + i) / 32
      ≤ Padding.messageOffset + Padding.paddedLength input.size - 8 + i :=
    Nat.div_le_self _ _
  have hbig : Padding.messageOffset + Padding.paddedLength input.size - 8 + i + 1
      < 2 ^ 256 := by
    unfold CalldataFits at hfit
    unfold Padding.messageOffset
    norm_num at hfit ⊢
    omega
  rw [lengthLoopActiveWords, Challenge.EvmProof.Word.word_toNat_ofNat,
    lengthAddr_toNat input hfit i hi]
  unfold MachineState.activeWordsAfter
  rw [if_neg (by decide : (1 : Nat) ≠ 0)]
  dsimp only
  refine Nat.mod_eq_of_lt ?_
  simp only [Nat.add_sub_cancel]
  rw [Nat.max_lt]
  exact ⟨hcur, by omega⟩

theorem padReturned_allocated (input : ByteArray) (hfit : CalldataFits input) :
    (Padding.messageOffset + Padding.paddedLength input.size) / 32 ≤
      (padReturned input).activeWords.toNat := by
  have hp := lengthStop_pos input
  have hl := lengthStop_le input
  let j := lengthStop input - 1
  have hs : lengthStop input = j + 1 := by dsimp [j]; omega
  change _ ≤ (lengthLoopActiveWords input (lengthStop input)).toNat
  rw [hs, lengthLoopActiveWords_succ_toNat input hfit j (by dsimp [j]; omega)]
  apply Nat.le_trans ?_ (Nat.le_max_right _ _)
  unfold Padding.messageOffset
  omega

@[simp] theorem padReturned_pc (input : ByteArray) :
    (padReturned input).pc = UInt256.ofNat 376 := by rfl

@[simp] theorem padReturned_stack (input : ByteArray) :
    (padReturned input).stack = padFrame input := by rfl

@[simp] theorem padReturned_halt (input : ByteArray) :
    (padReturned input).halt = .Running := by rfl

@[simp] theorem padReturned_code (input : ByteArray) :
    (padReturned input).executionEnv.code = submissionBytecode := by rfl

@[simp] theorem padReturned_fork (input : ByteArray) :
    (padReturned input).fork = .Osaka := by rfl

@[simp] theorem padReturned_codeAddr (input : ByteArray) :
    (padReturned input).executionEnv.codeAddr = deployAddress := by rfl

@[simp] theorem padReturned_noPrecompile (input : ByteArray) :
    Precompile.isPrecompileWithConfig (padReturned input).executionEnv.precompileConfig
      (padReturned input).executionEnv.fork
      (padReturned input).executionEnv.codeAddr = false := by
  exact deployAddress_not_precompile

def lengthExitPath : List
    (Challenge.EvmProof.DataStepper.Located Artifact.submissionArtifact .Osaka) :=
  Artifact.padExitPath

def lengthExitEntered (input : ByteArray) (i : Nat) : State :=
  { lengthLoopState input i with pc := UInt256.ofNat 4753 }

private theorem lengthExitPending_eq (input : ByteArray) (i : Nat) :
    lengthExitPending input i = lengthExitEntered input (i + 1) := by
  unfold lengthExitPending lengthBranchReady lengthSteppedState
    lengthExitEntered lengthLoopState
  generalize padSentinel input = s
  cases s
  rfl

/-- After the two `POP`s the padding code jumps to the block-loop head with the
persistent frame. -/
def lengthExitReturned (input : ByteArray) (i : Nat) : State :=
  { lengthExitEntered input i with
    pc := UInt256.ofNat 376
    stack := padFrame input }

@[simp] private theorem lengthExitEntered_halt (input : ByteArray) (i : Nat) :
    (lengthExitEntered input i).halt = .Running := by rfl

@[simp] private theorem lengthExitEntered_pc (input : ByteArray) (i : Nat) :
    (lengthExitEntered input i).pc = UInt256.ofNat 4753 := by rfl

@[simp] private theorem lengthExitEntered_code (input : ByteArray) (i : Nat) :
    (lengthExitEntered input i).executionEnv.code = submissionBytecode := by rfl

set_option maxHeartbeats 400000 in
private theorem run_lengthExitPop (input : ByteArray) (i : Nat) :
    Challenge.EvmProof.DataStepper.runLocatedBlock lengthExitPath
      (lengthExitEntered input i) = some (lengthExitReturned input i) := by
  simp [lengthExitPath, Artifact.padExitPath,
    Challenge.EvmProof.DataStepper.runLocatedBlock,
    Challenge.EvmProof.DataStepper.runLocated, Challenge.EvmProof.DataStepper.runInstr,
    lengthExitEntered, lengthExitReturned, lengthLoopState]

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
  rw [padSentinel, padCopied]
  rw [MachineState.writeBytes_size, MachineState.writeBytes_size]
  simp only [Challenge.EvmProof.Memory.readPadded_size, oneByte_size]
  split <;> split <;>
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
    (ha : a < Padding.messageOffset + Padding.paddedLength input.size) :
    (padFinalMemory input)[a]?.getD 0 =
      (Padding.paddedMemory (padLengthReady input).memory input)[a]?.getD 0 := by
  have hsentinel : (padSentinel input).memory =
      Padding.sentinelMemory (padLengthReady input).memory input := by
    simp [padSentinel, padCopied, Padding.sentinelMemory,
      Padding.copiedMemory, Challenge.EvmProof.Memory.readPadded_zero_size]
  rw [padFinalMemory_getD input hfit a ha, Padding.paddedMemory,
    MachineState.writeBytes_getElem?_getD, hsentinel]
  simp only [Padding.lengthBytes_size]

theorem padReturned_memory (input : ByteArray) (_hfit : CalldataFits input) :
    (padReturned input).memory = padFinalMemory input := by
  rfl

theorem padReturned_readPadded (input : ByteArray) (hfit : CalldataFits input)
    (a n : Nat) (ha : a + n ≤ Padding.messageOffset + Padding.paddedLength input.size) :
    MachineState.readPadded (padReturned input).memory a n =
      MachineState.readPadded
        (Padding.paddedMemory (padLengthReady input).memory input) a n := by
  apply Challenge.EvmProof.Memory.readPadded_congr
  intro i hi
  rw [padReturned_memory input hfit]
  exact padFinalMemory_getD_paddedMemory input hfit (a + i) (by omega)

theorem padReturned_readWord (input : ByteArray) (hfit : CalldataFits input)
    (a : Nat) (ha : a + 32 ≤ Padding.messageOffset + Padding.paddedLength input.size) :
    MachineState.readWord (padReturned input).memory a =
      MachineState.readWord
        (Padding.paddedMemory (padLengthReady input).memory input) a := by
  unfold MachineState.readWord
  rw [padReturned_readPadded input hfit a 32 ha]

theorem padReturned_getD_window (input : ByteArray) (hfit : CalldataFits input)
    (a : Nat) (ha : a < Padding.messageOffset + Padding.paddedLength input.size) :
    (padReturned input).memory[a]?.getD 0 =
      (Padding.paddedMemory (padLengthReady input).memory input)[a]?.getD 0 := by
  rw [padReturned_memory input hfit]
  exact padFinalMemory_getD_paddedMemory input hfit a ha

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
    Artifact.submissionArtifact .Osaka lengthExitPath (by rfl) (by rfl)
    (run_lengthExitPop input i) (by rfl) (by rfl)
  exact Challenge.EvmProof.GasSteps.cast g1raw rfl rfl

def gasSteps_lengthIterationExit (input : ByteArray) (hfit : CalldataFits input)
    (i : Nat) (hi : i < 9) (hz : lengthShift input (i + 1) = ⟨0⟩) :
    Challenge.EvmProof.GasSteps (lengthLoopState input i)
      (lengthExitReturned input (i + 1)) := by
  have g₁ := Challenge.EvmProof.DataStepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka lengthBodyPath (by rfl) (by rfl)
    (run_lengthBody input hfit i hi) (by rfl) (by rfl)
  have g2raw := Challenge.EvmProof.DataStepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka lengthBranchPath (by rfl) (by rfl)
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

set_option maxHeartbeats 800000 in
private theorem run_lengthFooterSetup (input : ByteArray) :
    Challenge.EvmProof.DataStepper.runLocatedBlock lengthFooterSetupPath
      (padSentinel input) = some (lengthLoopState input 0) := by
  have haddressOrder : UInt256.ofNat 1112 + Padding.paddedWord input =
      Padding.paddedWord input + UInt256.ofNat 1112 := Challenge.EvmProof.Word.word_add_comm _ _
  simp [lengthFooterSetupPath, Artifact.padFooterSetupPath,
    Challenge.EvmProof.DataStepper.runLocatedBlock,
    Challenge.EvmProof.DataStepper.runLocated, Challenge.EvmProof.DataStepper.runInstr,
    lengthLoopState, lengthLoopMemory, lengthLoopActiveWords,
    lengthAddr, lengthShift, padFrame,
    lengthOffsetWord, bitLengthWord, haddressOrder]

def gasSteps_lengthSetup (input : ByteArray) (hfit : CalldataFits input) :
    Challenge.EvmProof.GasSteps (padGuardMiss input)
      (lengthLoopState input 0) := by
  have g₂ₐ := Challenge.EvmProof.DataStepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka lengthSentinelAddressPath (by rfl) (by rfl)
    (run_lengthSentinelAddress input) (by rfl) deployAddress_not_precompile
  have g2raw := Challenge.EvmProof.DataStepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka lengthSentinelStorePath (by rfl) (by rfl)
    (run_lengthSentinelStore input hfit) (by rfl) deployAddress_not_precompile
  have g2b := Challenge.EvmProof.GasSteps.cast g2raw rfl
    (padSentinelStored_eq input hfit)
  have g₃ := Challenge.EvmProof.DataStepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka lengthFooterSetupPath (by rfl) (by rfl)
    (run_lengthFooterSetup input) (by rfl) deployAddress_not_precompile
  exact g₂ₐ.trans (g2b.trans g₃)

def gasSteps_lengthCopy (input : ByteArray) (hfit : CalldataFits input) :
    Challenge.EvmProof.GasSteps (padLengthReady input) (padCopied input) :=
  Challenge.EvmProof.DataStepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka lengthCopyPath (by rfl) (by rfl)
    (run_lengthCopy input hfit) (by rfl) deployAddress_not_precompile

/-- Complete certified execution from the challenge initial state through the
calldata copy and the frame pushes. -/
private def gasSteps_padPrefix (input : ByteArray) (hfit : CalldataFits input)
    (entryPrefix : Challenge.EvmProof.GasSteps (initialState submissionBytecode input 0)
      (Execution.atPC input 351)) :
    Challenge.EvmProof.GasSteps (initialState submissionBytecode input 0)
      (padFramed input) :=
  (Main.gasSteps_initialize input entryPrefix).trans
    ((gasSteps_enterPad input).trans ((gasSteps_paddedLength input).trans
      ((gasSteps_lengthCopy input hfit).trans (gasSteps_push input))))

noncomputable def gasSteps_padBody (input : ByteArray) (hfit : CalldataFits input)
    (hnz : input.size % 64 ≠ 0) :
    Challenge.EvmProof.GasSteps (padFramed input) (padReturned input) :=
  (gasSteps_guardMiss input hfit hnz).trans
    ((gasSteps_lengthSetup input hfit).trans (gasSteps_lengthLoop input hfit))

/-- Block-loop entry state.  A whole-block input skips the sentinel and footer stores: its
pad-only block is scheduled from the table and never reads message memory. -/
def entryState (input : ByteArray) : State :=
  if input.size % 64 = 0 then padSkip input else padReturned input

theorem entryState_skip (input : ByteArray) (hz : input.size % 64 = 0) :
    entryState input = padSkip input := by
  unfold entryState
  rw [if_pos hz]

theorem entryState_miss (input : ByteArray) (hnz : input.size % 64 ≠ 0) :
    entryState input = padReturned input := by
  unfold entryState
  rw [if_neg hnz]

theorem entryState_eta (input : ByteArray) :
    entryState input = {entryState input with
      pc := UInt256.ofNat (if input.size % 64 = 0 then 374 else 376)
      stack := padFrame input} := by
  by_cases hz : input.size % 64 = 0
  · rw [entryState_skip input hz, if_pos hz]
    rfl
  · rw [entryState_miss input hz, if_neg hz]
    rfl

noncomputable def gasSteps_pad (input : ByteArray) (hfit : CalldataFits input)
    (entryPrefix : Challenge.EvmProof.GasSteps (initialState submissionBytecode input 0)
      (Execution.atPC input 351)) :
    Challenge.EvmProof.GasSteps (initialState submissionBytecode input 0)
      (entryState input) :=
  if hz : input.size % 64 = 0 then
    Challenge.EvmProof.GasSteps.cast
      ((gasSteps_padPrefix input hfit entryPrefix).trans (gasSteps_guardSkip input hfit hz))
      rfl (entryState_skip input hz).symm
  else
    Challenge.EvmProof.GasSteps.cast
      ((gasSteps_padPrefix input hfit entryPrefix).trans (gasSteps_padBody input hfit hz))
      rfl (entryState_miss input hz).symm

#print axioms gasSteps_pad

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PaddingTrace
