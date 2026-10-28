import Challenge.Ripemd160.Submission.Local20261028.ColdPaddingCore4
import Challenge.Ripemd160.Submission.Local20261028.ColdShared32Scratch
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PcEncoding
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Padding
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackTail
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RawExpressionAC
import Challenge.Ripemd160.Submission.Local20261028.ColdTrace
import Challenge.Ripemd160.Submission.Local20261028.ColdMain
import Challenge.Ripemd160.Submission.Local20261028.ColdStaggerPersistentStart
import Challenge.Ripemd160.Submission.Local20261028.ColdGuardFinish
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DataStepper
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Msize
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadLimitArithmetic
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
/-!
# Direct execution of the RIPEMD-160 padding function (setup, guard, sentinel, footer loop and exit)

The fixed setup and the eight-iteration little-endian footer loop are exposed
as located paths.  The resulting state is shared by correctness and exact gas
accounting.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.Control.PaddingTrace
open EvmSemantics EvmSemantics.EVM
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
  have hsum : Padding.paddedLength input.size + 1048 < 2 ^ 256 := by
    unfold CalldataFits at hfit
    norm_num at hfit ⊢
    omega
  rw [lengthOffsetWord, PadLimitArithmetic.coldRounded_input input hfit,
    PadLimitArithmetic.footer_addr input hfit, Padding.paddedWord_eq input hfit,
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
@[simp] theorem lengthLoopActiveWords_zero (input : ByteArray) :
    lengthLoopActiveWords input 0 = (padSentinel input).activeWords := by rfl

@[simp] theorem lengthLoopActiveWords_succ (input : ByteArray) (i : Nat) :
    lengthLoopActiveWords input (i + 1) =
      UInt256.ofNat (MachineState.activeWordsAfter
        (lengthLoopActiveWords input i).toNat (lengthAddr input i).toNat 1) := by rfl

theorem zero_toNat : (⟨0⟩ : UInt256).toNat = 0 := rfl
theorem ofNat_zero_eq : UInt256.ofNat 0 = (⟨0⟩ : UInt256) := rfl

theorem toNat_ne_zero_of_ne (x : UInt256) (hne : x ≠ ⟨0⟩) :
    x.toNat ≠ 0 := by
  intro h
  exact hne (Challenge.EvmProof.Word.word_ext (h.trans zero_toNat.symm))

theorem isZero_of_ne (x : UInt256) (hne : x ≠ ⟨0⟩) :
    UInt256.isZero x = UInt256.ofNat 0 := by
  unfold UInt256.isZero
  exact if_neg (toNat_ne_zero_of_ne x hne)

theorem isZero_of_eq (x : UInt256) (hz : x = ⟨0⟩) :
    UInt256.isZero x = UInt256.ofNat 1 := by
  subst hz
  unfold UInt256.isZero
  exact if_pos zero_toNat

set_option maxHeartbeats 800000 in
theorem run_lengthBody (input : ByteArray) (_hfit : CalldataFits input)
    (i : Nat) (_hi : i < 9) :
    Challenge.EvmProof.DataStepper.runLocatedBlock lengthBodyPath
      (lengthLoopState input i) = some (lengthSteppedState input i) := by
  simp [lengthBodyPath, lengthIterationPath,
    Challenge.EvmProof.DataStepper.runLocatedBlock,
    Challenge.EvmProof.DataStepper.runLocated, Challenge.EvmProof.DataStepper.runInstr,
    lengthSteppedState, lengthLoopState, lengthLoopMemory, lengthAddr, lengthShift,
    List.exchange, State.activeWordsAfterUInt256, lengthLoopActiveWords]

set_option maxHeartbeats 400000 in
theorem run_lengthBranchBack (input : ByteArray) (i : Nat)
    (hne : lengthShift input (i + 1) ≠ ⟨0⟩) :
    Challenge.EvmProof.DataStepper.runLocatedBlock lengthBranchPath
      (lengthSteppedState input i) = some (lengthBackReturned input i) := by
  have htrue : UInt256.isTrue (lengthShift input (i + 1)) = true := by
    simp [UInt256.isTrue, toNat_ne_zero_of_ne _ hne]
  simp [lengthBranchPath, lengthIterationPath,
    Challenge.EvmProof.DataStepper.runLocatedBlock,
    Challenge.EvmProof.DataStepper.runLocated, Challenge.EvmProof.DataStepper.runInstr,
    lengthSteppedState, lengthBackReturned, htrue, validJump4949]

set_option maxHeartbeats 400000 in
theorem run_lengthBranchExit (input : ByteArray) (i : Nat)
    (hz : lengthShift input (i + 1) = ⟨0⟩) :
    Challenge.EvmProof.DataStepper.runLocatedBlock lengthBranchPath
      (lengthSteppedState input i) = some (lengthExitPending input i) := by
  have hfalse : UInt256.isTrue (lengthShift input (i + 1)) = false := by
    simp [UInt256.isTrue, hz]
  simp [lengthBranchPath, lengthIterationPath,
    Challenge.EvmProof.DataStepper.runLocatedBlock,
    Challenge.EvmProof.DataStepper.runLocated, Challenge.EvmProof.DataStepper.runInstr,
    lengthSteppedState, lengthExitPending, hfalse]

def gasSteps_lengthIteration (input : ByteArray) (hfit : CalldataFits input)
    (i : Nat) (hi : i < 9) (hne : lengthShift input (i + 1) ≠ ⟨0⟩) :
    Challenge.EvmProof.GasSteps (lengthLoopState input i)
      (lengthLoopState input (i + 1)) := by
  have g₁ := Challenge.EvmProof.DataStepper.runLocatedBlock_sound
    Control.Artifact.submissionArtifact .Osaka lengthBodyPath (by rfl) (by rfl)
    (run_lengthBody input hfit i hi) (by rfl) (by rfl)
  have g2raw := Challenge.EvmProof.DataStepper.runLocatedBlock_sound
    Control.Artifact.submissionArtifact .Osaka lengthBranchPath (by rfl) (by rfl)
    (run_lengthBranchBack input i hne) (by rfl) (by rfl)
  have g₂ := Challenge.EvmProof.GasSteps.cast g2raw rfl
    (lengthBackReturned_eq input i)
  exact g₁.trans g₂

/-! ## Loop exit and return -/

def padFinalMemory (input : ByteArray) : ByteArray :=
  (lengthLoopState input (lengthStop input)).memory

def padReturned (input : ByteArray) : State :=
  { lengthLoopState input (lengthStop input) with
    pc := UInt256.ofNat 461
    stack := glFrame }

theorem lengthLoopActiveWords_succ_toNat (input : ByteArray)
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
    (Padding.messageOffset + Padding.paddedLength input.size + 31) / 32 ≤
      (padReturned input).activeWords.toNat := by
  have hp := lengthStop_pos input
  have hl := lengthStop_le input
  let j := lengthStop input - 1
  have hs : lengthStop input = j + 1 := by dsimp [j]; omega
  change _ ≤ (lengthLoopActiveWords input (lengthStop input)).toNat
  rw [hs, lengthLoopActiveWords_succ_toNat input hfit j (by dsimp [j]; omega)]
  apply Nat.le_trans ?_ (Nat.le_max_right _ _)
  have halign : Padding.paddedLength input.size % 64 = 0 := by
    unfold Padding.paddedLength
    omega
  unfold Padding.messageOffset
  omega

@[simp] theorem padReturned_pc (input : ByteArray) :
    (padReturned input).pc = UInt256.ofNat 461 := by rfl

@[simp] theorem padReturned_stack (input : ByteArray) :
    (padReturned input).stack = glFrame := by rfl

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
    (Challenge.EvmProof.DataStepper.Located Control.Artifact.submissionArtifact .Osaka) :=
  Control.Artifact.padExitPath

def lengthExitEntered (input : ByteArray) (i : Nat) : State :=
  { lengthLoopState input i with pc := UInt256.ofNat 4598 }

theorem lengthExitPending_eq (input : ByteArray) (i : Nat) :
    lengthExitPending input i = lengthExitEntered input (i + 1) := by
  unfold lengthExitPending lengthSteppedState
    lengthExitEntered lengthLoopState
  generalize padSentinel input = s
  cases s
  rfl

/-- After `PUSH1 198 JUMP`, the generic continuation 48 replaces the output entry (`SWAP16`), the
four `POP`s drop it and the three loop words, and the padding code jumps to the block-loop head. -/
def lengthExitReturned (input : ByteArray) (i : Nat) : State :=
  { lengthExitEntered input i with
    pc := UInt256.ofNat 461
    stack := glFrame }

@[simp] theorem lengthExitEntered_halt (input : ByteArray) (i : Nat) :
    (lengthExitEntered input i).halt = .Running := by rfl

@[simp] theorem lengthExitEntered_pc (input : ByteArray) (i : Nat) :
    (lengthExitEntered input i).pc = UInt256.ofNat 4598 := by rfl

@[simp] theorem lengthExitEntered_code (input : ByteArray) (i : Nat) :
    (lengthExitEntered input i).executionEnv.code = submissionBytecode := by rfl

set_option maxHeartbeats 400000 in
/-- Keep memory and the concrete bytecode opaque while checking the stack-only
exit.  Expanding the full padding state here duplicates the large code array
in the kernel's record-update reductions. -/
theorem run_lengthExitPop_opaque (s : State) (input : ByteArray)
    (a b : UInt256) (hrun : s.halt = .Running)
    (h198 : Decode.isValidJumpDest s.executionEnv.code 198 = true)
    (h461 : Decode.isValidJumpDest s.executionEnv.code 461 = true) :
    Challenge.EvmProof.DataStepper.runLocatedBlock lengthExitPath
      { s with
        pc := UInt256.ofNat 4598
        stack := a :: b :: UInt256.ofNat 4583 :: padFrame input } =
      some { s with pc := UInt256.ofNat 461, stack := glFrame } := by
  simp [lengthExitPath, Control.Artifact.padExitPath,
    Challenge.EvmProof.DataStepper.runLocatedBlock,
    Challenge.EvmProof.DataStepper.runLocated, Challenge.EvmProof.DataStepper.runInstr,
    padFrame, glFrame, StaggerPersistentFrame.frame,
    List.exchange, List.getElem?_cons_zero, List.getElem?_cons_succ,
    h198, h461, hrun]

set_option maxHeartbeats 400000 in
theorem run_lengthExitPop (input : ByteArray) (i : Nat) :
    Challenge.EvmProof.DataStepper.runLocatedBlock lengthExitPath
      (lengthExitEntered input i) = some (lengthExitReturned input i) := by
  exact run_lengthExitPop_opaque (lengthLoopState input i) input
    (lengthAddr input i) (lengthShift input i) (by rfl)
    validJump198 validJump461


end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.Control.PaddingTrace
