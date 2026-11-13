import Challenge.Modexp.Submission.Proofs.CycleGlobal.ZeroMod12
import Challenge.Modexp.Submission.Proofs.Prepared.StackArgs
import Challenge.Modexp.Submission.Proofs.CycleGlobal.SignedTopBit
import Challenge.Modexp.Submission.Proofs.CycleGlobal.LowBitFlag
import Challenge.Modexp.Submission.Proofs.CycleGlobal.Binding
import Challenge.Modexp.Submission.Proofs.Fast.NewtonSeed
import Challenge.Modexp.Submission.Proofs.CycleGlobal.FastDefs
import Challenge.Modexp.Submission.Proofs.CycleGlobal.FastP0
import Challenge.Modexp.Submission.Proofs.CycleGlobal.FastP1
import Challenge.Modexp.Submission.Proofs.CycleGlobal.FastP6
import Challenge.Modexp.Submission.Proofs.Fast.Model
import Challenge.Modexp.Submission.Proofs.CycleGlobal.MainDefs
import Challenge.EvmProof.Memory
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneMsize
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneSlice
import Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast
open CycleSubmission.SharedStackArgs

noncomputable section
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
namespace CycleSubmission.Global.Fast.Setup
private theorem signedTopRaw (x : EvmSemantics.UInt256) :
    EvmSemantics.UInt256.sgt ({val := 0} : EvmSemantics.UInt256) x =
      EvmSemantics.UInt256.shiftRight x (EvmSemantics.UInt256.ofNat 255) :=
  CycleSubmission.Global.Fast.SignedTopBit.sgt_zero_eq_shr x
open CycleSubmission.Global.Fast.SignedTopBit
open Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneMsize
open Challenge.Modexp
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode



attribute [local simp] List.getElem?_cons_zero
theorem pow_256_32 : (256 : Nat) ^ 32 = 2 ^ 256 := by norm_num
theorem toNat_ofNat_self {a : Nat} (ha : a < 2 ^ 256) :
    (UInt256.ofNat a).toNat = a := by
  rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt ha]
theorem gt_ofNat_of_lt {a b : Nat} (ha : a < 2 ^ 256) (hb : b < 2 ^ 256)
    (h : b < a) :
    UInt256.gt (UInt256.ofNat a) (UInt256.ofNat b) = UInt256.ofNat 1 := by
  rw [UInt256.gt, toNat_ofNat_self ha, toNat_ofNat_self hb, if_pos h]
theorem gt_ofNat_of_le {a b : Nat} (ha : a < 2 ^ 256) (hb : b < 2 ^ 256)
    (h : a ≤ b) :
    UInt256.gt (UInt256.ofNat a) (UInt256.ofNat b) = UInt256.ofNat 0 := by
  rw [UInt256.gt, toNat_ofNat_self ha, toNat_ofNat_self hb,
    if_neg (Nat.not_lt.mpr h)]
theorem lt_ofNat_of_lt {a b : Nat} (ha : a < 2 ^ 256) (hb : b < 2 ^ 256)
    (h : a < b) :
    UInt256.lt (UInt256.ofNat a) (UInt256.ofNat b) = UInt256.ofNat 1 := by
  rw [UInt256.lt, toNat_ofNat_self ha, toNat_ofNat_self hb, if_pos h]
theorem lt_ofNat_of_le {a b : Nat} (ha : a < 2 ^ 256) (hb : b < 2 ^ 256)
    (h : b ≤ a) :
    UInt256.lt (UInt256.ofNat a) (UInt256.ofNat b) = UInt256.ofNat 0 := by
  rw [UInt256.lt, toNat_ofNat_self ha, toNat_ofNat_self hb,
    if_neg (Nat.not_lt.mpr h)]
theorem isZero_ofNat_of_ne {a : Nat} (ha : a < 2 ^ 256) (h : a ≠ 0) :
    UInt256.isZero (UInt256.ofNat a) = UInt256.ofNat 0 := by
  rw [UInt256.isZero, toNat_ofNat_self ha, if_neg h]
theorem isZero_ofNat_zero : UInt256.isZero (UInt256.ofNat 0) = UInt256.ofNat 1 := by
  decide



theorem lnot_zero_raw :
    UInt256.lnot ⟨0⟩ = UInt256.ofNat (Limbs.radix - 1) := by
  unfold UInt256.lnot Limbs.radix
  norm_num [UInt256.size, UInt256.toNat]
theorem lnot_ofNat_zero :
    UInt256.lnot (UInt256.ofNat 0) = UInt256.ofNat (Limbs.radix - 1) :=
  lnot_zero_raw
theorem eq_maxWord_of_ne (w : UInt256)
    (h : w ≠ UInt256.ofNat (Limbs.radix - 1)) :
    UInt256.eq (UInt256.ofNat (Limbs.radix - 1)) w = UInt256.ofNat 0 := by
  rw [UInt256.eq, if_neg]
  intro hc
  exact h (Challenge.EvmProof.Word.word_ext hc).symm
theorem land_mask_of_mod (n : Nat) (hn : n < 2 ^ 256) (h : n % 128 = 0) :
    UInt256.land (UInt256.ofNat 127) (UInt256.ofNat n) = UInt256.ofNat 0 := by
  apply Challenge.EvmProof.Word.word_ext
  rw [Challenge.EvmProof.Word.word_toNat_land, toNat_ofNat_self (by norm_num),
    toNat_ofNat_self hn, toNat_ofNat_self (by norm_num)]
  have : (127 : Nat) = 2 ^ 7 - 1 := by norm_num
  rw [this, Nat.and_comm, Nat.and_two_pow_sub_one_eq_mod]
  simpa using h
theorem isZero_ofNat_one : UInt256.isZero (UInt256.ofNat 1) = UInt256.ofNat 0 := by
  decide
@[simp] theorem isTrue_one : UInt256.isTrue (UInt256.ofNat 1) := by decide
@[simp] theorem not_isTrue_zero : ¬ UInt256.isTrue (UInt256.ofNat 0) := by decide
@[simp] theorem lor_zero_zero :
    UInt256.lor (UInt256.ofNat 0) (UInt256.ofNat 0) = UInt256.ofNat 0 := by decide
@[simp] theorem lor_zero_one :
    UInt256.lor (UInt256.ofNat 0) (UInt256.ofNat 1) = UInt256.ofNat 1 := by decide
@[simp] theorem lor_one_zero :
    UInt256.lor (UInt256.ofNat 1) (UInt256.ofNat 0) = UInt256.ofNat 1 := by decide
@[simp] theorem lor_one_one :
    UInt256.lor (UInt256.ofNat 1) (UInt256.ofNat 1) = UInt256.ofNat 1 := by decide
theorem push0_word : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
theorem initial_code (input : ByteArray) :
    (initialState CycleSubmission.Artifact.bytecode input 0).executionEnv.code =
      CycleSubmission.Artifact.bytecode := rfl
theorem initial_halt (input : ByteArray) :
    (initialState CycleSubmission.Artifact.bytecode input 0).halt = .Running := rfl
theorem read_base (input : ByteArray) :
    MachineState.readWord input 0 = UInt256.ofNat (baseSize input) := rfl
theorem read_exponent (input : ByteArray) :
    MachineState.readWord input 32 = UInt256.ofNat (exponentSize input) := rfl
theorem read_modulus (input : ByteArray) :
    MachineState.readWord input 64 = UInt256.ofNat (modulusSize input) := rfl
theorem headerSize_lt (input : ByteArray) (offset : Nat) :
    Precompile.bytesToNatPadded input offset 32 < 2 ^ 256 := by
  have h := Challenge.EvmProof.Bytes.bytesToNatPadded_lt_pow input offset 32
  rwa [pow_256_32] at h
theorem baseSize_lt (input : ByteArray) : baseSize input < 2 ^ 256 :=
  headerSize_lt input 0
theorem exponentSize_lt (input : ByteArray) : exponentSize input < 2 ^ 256 :=
  headerSize_lt input 32
theorem modulusSize_lt (input : ByteArray) : modulusSize input < 2 ^ 256 :=
  headerSize_lt input 64
def limbs (input : ByteArray) : Nat := Limbs.limbCount (modulusSize input)
def s32 (input : ByteArray) : Nat := 32 * limbs input
def modOffset (input : ByteArray) : Nat := 96 + baseSize input + exponentSize input
def modulus (input : ByteArray) : Nat :=
  Precompile.bytesToNatPadded input (modOffset input) (modulusSize input)
def topWidth (input : ByteArray) : Nat := modulusSize input - 32 * (limbs input - 1)
def topLimb (input : ByteArray) : Nat :=
  Precompile.bytesToNatPadded input (modOffset input) (topWidth input)
def FastPath (input : ByteArray) : Prop :=
  32 < modulusSize input ∧
    (baseSize input ≤ 1024 ∧ exponentSize input ≤ 1024 ∧ modulusSize input ≤ 256) ∧
    Limbs.radix ^ (limbs input - 1) ≤ modulus input ∧
    modulus input % 2 = 1 ∧
    
    
    
    
    modulusSize input % 128 = 0 ∧
    MachineState.readWord input (modOffset input + modulusSize input - 32) ≠
      UInt256.ofNat (Limbs.radix - 1) ∧
    
    
    
    
    (MachineState.readWord input (modOffset input)).toNat >>> 255 ≠ 0
theorem fastPath_odd (input : ByteArray) (h : FastPath input) :
    modulus input % 2 = 1 := h.2.2.2.1
theorem fastPath_width (input : ByteArray) (h : FastPath input) :
    modulusSize input % 128 = 0 := h.2.2.2.2.1
theorem fastPath_nprime (input : ByteArray) (h : FastPath input) :
    MachineState.readWord input (modOffset input + modulusSize input - 32) ≠
      UInt256.ofNat (Limbs.radix - 1) := h.2.2.2.2.2.1
theorem fastPath_topBit (input : ByteArray) (h : FastPath input) :
    (MachineState.readWord input (modOffset input)).toNat >>> 255 ≠ 0 := h.2.2.2.2.2.2
theorem fastPath_modulus_le_1024 (input : ByteArray) (hpath : FastPath input) :
    modulusSize input ≤ 1024 := Nat.le_trans hpath.2.1.2.2 (by decide)
theorem limbs_le_8 (input : ByteArray) (h : modulusSize input ≤ 256) :
    limbs input ≤ 8 := by
  unfold limbs Limbs.limbCount
  omega
theorem s32_le_256 (input : ByteArray) (h : modulusSize input ≤ 256) :
    s32 input ≤ 256 := by
  unfold s32 limbs Limbs.limbCount
  omega
theorem limbs_ge_two (input : ByteArray) (h : 32 < modulusSize input) :
    2 ≤ limbs input := by
  unfold limbs Limbs.limbCount
  omega
theorem limbs_four_or_eight (input : ByteArray)
    (hlo : 32 < modulusSize input) (hhi : modulusSize input ≤ 256)
    (hmask : modulusSize input % 128 = 0) : limbs input = 4 ∨ limbs input = 8 := by
  unfold limbs Limbs.limbCount
  omega
theorem s32_eq_of_mask (input : ByteArray) (hmask : modulusSize input % 128 = 0) :
    s32 input = modulusSize input := by
  unfold s32 limbs Limbs.limbCount
  omega
theorem topWidth_eq_32_of_mask (input : ByteArray)
    (h32 : 32 < modulusSize input) (hmask : modulusSize input % 128 = 0) :
    topWidth input = 32 := by
  unfold topWidth limbs Limbs.limbCount
  omega
theorem lastWord_toNat (input : ByteArray) (h : 32 < modulusSize input) :
    (MachineState.readWord input (modOffset input + modulusSize input - 32)).toNat =
      modulus input % Limbs.radix := by
  have hsplit := Challenge.EvmProof.Bytes.bytesToNatPadded_add input (modOffset input)
    (modulusSize input - 32) 32
  rw [show modulusSize input - 32 + 32 = modulusSize input from by omega] at hsplit
  have haddr : modOffset input + modulusSize input - 32 =
      modOffset input + (modulusSize input - 32) := by omega
  rw [Challenge.EvmProof.Bytes.readWord_toNat, haddr]
  unfold modulus
  rw [hsplit, Limbs.radix, ← pow_256_32, Nat.mul_add_mod',
    Nat.mod_eq_of_lt (Challenge.EvmProof.Bytes.bytesToNatPadded_lt_pow input _ 32)]
theorem lowWord_ne_of_nprime (input : ByteArray) (h : 32 < modulusSize input)
    (hnprime : MachineState.readWord input (modOffset input + modulusSize input - 32) ≠
      UInt256.ofNat (Limbs.radix - 1)) :
    modulus input % Limbs.radix ≠ Limbs.radix - 1 := by
  intro hlow
  apply hnprime
  apply Challenge.EvmProof.Word.word_ext
  rw [lastWord_toNat input h, hlow, Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt (show Limbs.radix - 1 < 2 ^ 256 by unfold Limbs.radix; norm_num)]
theorem minv_ne_one_of_lowWord {mm minv : Nat}
    (hminvA : (mm % Limbs.radix * minv + 1) % 2 ^ 256 = 0)
    (hlow : mm % Limbs.radix ≠ Limbs.radix - 1) : minv ≠ 1 := by
  intro h1
  subst h1
  have hlt : mm % Limbs.radix < Limbs.radix := Nat.mod_lt _ Limbs.radix_pos
  have h256 : (2 : Nat) ^ 256 =
      115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
    norm_num
  unfold Limbs.radix at hminvA hlow hlt
  rw [Nat.mul_one, h256] at hminvA
  rw [h256] at hlow hlt
  omega
theorem minv_ne_one_of_entry (input : ByteArray) (minv : Nat) (h : 32 < modulusSize input)
    (hnprime : MachineState.readWord input (modOffset input + modulusSize input - 32) ≠
      UInt256.ofNat (Limbs.radix - 1))
    (hminvA : (modulus input % Limbs.radix * minv + 1) % 2 ^ 256 = 0) : minv ≠ 1 :=
  minv_ne_one_of_lowWord hminvA (lowWord_ne_of_nprime input h hnprime)
theorem limbs_le_32 (input : ByteArray) (h : modulusSize input ≤ 1024) :
    limbs input ≤ 32 := by
  unfold limbs Limbs.limbCount
  omega
theorem modulusSize_le_s32 (input : ByteArray) : modulusSize input ≤ s32 input := by
  unfold s32 limbs Limbs.limbCount
  omega
theorem s32_lt_modulusSize_add (input : ByteArray) :
    s32 input < modulusSize input + 32 := by
  unfold s32 limbs Limbs.limbCount
  omega
theorem s32_le_1024 (input : ByteArray) (h : modulusSize input ≤ 1024) :
    s32 input ≤ 1024 := by
  unfold s32 limbs Limbs.limbCount
  omega
theorem topWidth_pos (input : ByteArray) (h : 32 < modulusSize input) :
    0 < topWidth input := by
  unfold topWidth limbs Limbs.limbCount
  omega
theorem topWidth_le (input : ByteArray) : topWidth input ≤ 32 := by
  unfold topWidth limbs Limbs.limbCount
  omega
theorem topWidth_add (input : ByteArray) (h : 32 < modulusSize input) :
    topWidth input + 32 * (limbs input - 1) = modulusSize input := by
  unfold topWidth limbs Limbs.limbCount
  omega
def entryState (s : State) : State :=
  { s with pc := UInt256.ofNat 564, stack := [] }
def fallbackState (s : State) : State :=
  { s with pc := UInt256.ofNat 519, stack := [] }
def memoEntryState (s : State) : State :=
  { s with pc := UInt256.ofNat 674, stack := [] }
def zeroExpEntryState (s : State) : State :=
  { s with pc := UInt256.ofNat 3416, stack := [] }
def bail1State (s : State) (input : ByteArray) : State :=
  { s with pc := UInt256.ofNat 3461, stack := [UInt256.ofNat (modulusSize input)] }
def emptyModulusState (s : State) : State :=
  { s with
    pc := UInt256.ofNat 3468
    stack := []
    halt := .Returned
    hReturn := MachineState.readPadded s.memory 0 0
    activeWords := s.activeWordsAfterUInt256 0 0 }
theorem readPadded_zero_length (bs : ByteArray) (start : Nat) :
    MachineState.readPadded bs start 0 = ByteArray.empty := by
  apply ByteArray.ext
  simp [MachineState.readPadded]
@[simp] theorem emptyModulusState_isDone (s : State) (hcall : s.callStack = []) :
    (emptyModulusState s).isDone = true := by
  simp [emptyModulusState, State.isDone, State.isHalted, State.isRunning, hcall]
theorem emptyModulusState_result (s : State) (input : ByteArray)
    (hzero : modulusSize input = 0) :
    (emptyModulusState s).toResult = .returned (spec input) := by
  simp [emptyModulusState, State.toResult, spec, hzero, readPadded_zero_length]
set_option linter.unusedSimpArgs false in
theorem run_bail1_zero (s : State) (input : ByteArray)
    (hrun : s.halt = .Running) (hzero : modulusSize input = 0) :
    Challenge.EvmProof.Stepper.runLocatedBlock blkEmptyModulus (bail1State s input) =
      some (emptyModulusState s) := by
  have hz0 : (UInt256.ofNat (modulusSize input)).toNat = 0 := by rw [hzero]; rfl
  have hz : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := rfl
  simp (config := { maxSteps := 400000 })
    [blkEmptyModulus, opAt, pushAt, wfOp,
     Challenge.EvmProof.Stepper.runLocatedBlock,
     Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
     bail1State, emptyModulusState, hrun, hz0, hz, UInt256.isTrue, State.activeWordsAfterUInt256,
     Challenge.EvmProof.Word.literal_eq_ofNat,
     Challenge.EvmProof.Word.succ_ofNat_mod,
     Challenge.EvmProof.Word.ofNat_add_mod,
     Challenge.EvmProof.Word.word_toNat_ofNat]
def zeroExpModulus (input : ByteArray) : Nat :=
  Precompile.bytesToNatPadded input (96 + baseSize input) (modulusSize input)
def zeroExpWord (input : ByteArray) : UInt256 :=
  UInt256.lt (UInt256.ofNat 1) (UInt256.ofNat (zeroExpModulus input))
def zeroExpMemory (s : State) (input : ByteArray) : ByteArray :=
  MachineState.writeBytes s.memory
    (Data.Bytes.natToBytesPadded (zeroExpWord input).toNat 32) 0
def zeroExpStoreState (s : State) (input : ByteArray) : State :=
  { s with
    pc := UInt256.ofNat 3454
    stack := [UInt256.ofNat (modulusSize input)]
    memory := zeroExpMemory s input
    activeWords := s.activeWordsAfterUInt256 0 32 }
def zeroExpFinalState (s : State) (input : ByteArray) : State :=
  { zeroExpStoreState s input with
    stack := []
    pc := UInt256.ofNat 3457
    halt := .Returned
    hReturn := MachineState.readPadded (zeroExpMemory s input)
      (32 - modulusSize input) (modulusSize input)
    activeWords := (zeroExpStoreState s input).activeWordsAfterUInt256
      (32 - modulusSize input) (modulusSize input) }
set_option linter.unusedSimpArgs false in
theorem run_zeroExp_miss (s : State) (input : ByteArray)
    (hdata : s.executionEnv.calldata = input)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode) (hrun : s.halt = .Running)
    (hne : exponentSize input ≠ 0) :
    Challenge.EvmProof.Stepper.runLocatedBlock blkZeroExpMiss (zeroExpEntryState s) =
      some (memoEntryState s) := by
  have hword : MachineState.readWord input 32 = UInt256.ofNat (exponentSize input) := rfl
  have he : (UInt256.ofNat (exponentSize input)).toNat = exponentSize input :=
    toNat_ofNat_self (exponentSize_lt input)
  have htrue : (UInt256.ofNat (exponentSize input)).toNat ≠ 0 := by rw [he]; exact hne
  have hmod : exponentSize input %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
        exponentSize input := Nat.mod_eq_of_lt (exponentSize_lt input)
  simp (config := { maxSteps := 400000 })
    [blkZeroExpMiss, opAt, pushAt, wfOp,
     Challenge.EvmProof.Stepper.runLocatedBlock,
     Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
     zeroExpEntryState, memoEntryState, hrun, hcode, hdata, hword, htrue, hmod, hne, UInt256.isTrue, jumpDest698,
     Challenge.EvmProof.Word.literal_eq_ofNat,
     Challenge.EvmProof.Word.succ_ofNat_mod,
     Challenge.EvmProof.Word.ofNat_add_mod,
     Challenge.EvmProof.Word.word_toNat_ofNat]
set_option linter.unusedSimpArgs false in
theorem run_zeroExp_wide (s : State) (input : ByteArray)
    (hdata : s.executionEnv.calldata = input)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode) (hrun : s.halt = .Running)
    (hzero : exponentSize input = 0) (hwide : 32 < modulusSize input) :
    Challenge.EvmProof.Stepper.runLocatedBlock blkZeroExpWide (zeroExpEntryState s) =
      some (memoEntryState s) := by
  have hword : MachineState.readWord input 32 = UInt256.ofNat (exponentSize input) := rfl
  have hfalse : (UInt256.ofNat (exponentSize input)).toNat = 0 := by rw [hzero]; rfl
  have hlt := lt_ofNat_of_lt (by norm_num : (32 : Nat) < 2 ^ 256) (modulusSize_lt input) hwide
  have htrue : (UInt256.ofNat 1).toNat = 1 := rfl
  simp (config := { maxSteps := 400000 })
    [blkZeroExpWide, opAt, pushAt, wfOp,
     Challenge.EvmProof.Stepper.runLocatedBlock,
     Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
     zeroExpEntryState, memoEntryState, hrun, hcode, hdata, hword, hfalse, read_modulus,
     hlt, htrue, UInt256.isTrue, jumpDest698, jumpDestZeroExpCleanup,
     Challenge.EvmProof.Word.literal_eq_ofNat,
     Challenge.EvmProof.Word.succ_ofNat_mod,
     Challenge.EvmProof.Word.ofNat_add_mod,
     Challenge.EvmProof.Word.word_toNat_ofNat]
set_option linter.unusedSimpArgs false in
theorem run_zeroExp_hit (s : State) (input : ByteArray)
    (hdata : s.executionEnv.calldata = input)
    (_hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode) (hrun : s.halt = .Running)
    (hb : baseSize input ≤ 1024)
    (hzero : exponentSize input = 0) (hpos : 0 < modulusSize input)
    (hsmall : modulusSize input ≤ 32) :
    Challenge.EvmProof.Stepper.runLocatedBlock blkZeroExpHit (zeroExpEntryState s) =
      some (zeroExpStoreState s input) := by
  have hword : MachineState.readWord input 32 = UInt256.ofNat (exponentSize input) := rfl
  have hfalse : (UInt256.ofNat (exponentSize input)).toNat = 0 := by rw [hzero]; rfl
  have hle := lt_ofNat_of_le (by norm_num : (32 : Nat) < 2 ^ 256) (modulusSize_lt input) hsmall
  have hfalse0 : (UInt256.ofNat 0).toNat = 0 := rfl
  have hbase : MachineState.readWord input 0 = UInt256.ofNat (baseSize input) := rfl
  have hadd : UInt256.ofNat 96 + UInt256.ofNat (baseSize input) =
      UInt256.ofNat (96 + baseSize input) := by
    rw [Challenge.EvmProof.Word.ofNat_add_mod]
  have haddn : (UInt256.ofNat (96 + baseSize input)).toNat = 96 + baseSize input :=
    toNat_ofNat_self (by omega)
  have hsub := Challenge.EvmProof.Word.ofNat_sub_ofNat hsmall (by norm_num : 32 < 2 ^ 256)
  have hshift :
      UInt256.shiftLeft (UInt256.ofNat (32 - modulusSize input)) (UInt256.ofNat 3) =
        UInt256.ofNat ((32 - modulusSize input) * 8) := by
    rw [Challenge.EvmProof.Word.shiftLeft_ofNat] <;>
      norm_num [Nat.shiftLeft_eq] <;> omega
  have hshr := Challenge.EvmProof.Bytes.shiftRight_readWord input (96 + baseSize input)
    (modulusSize input) hpos hsmall
  have hz : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : (UInt256.ofNat 0).toNat = 0 := rfl
  simp (config := { maxSteps := 400000 })
    [blkZeroExpHit, opAt, pushAt, wfOp,
     Challenge.EvmProof.Stepper.runLocatedBlock,
     Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
     zeroExpEntryState, zeroExpStoreState, zeroExpMemory, zeroExpWord, zeroExpModulus,
     hrun, hdata, _hcode, hword, hfalse, read_modulus, hle, hfalse0, hbase, hadd, haddn, hsub,
     hshift, hshr, hz, hzn, List.exchange, UInt256.isTrue, State.activeWordsAfterUInt256,
     Challenge.EvmProof.Word.literal_eq_ofNat,
     Challenge.EvmProof.Word.ofNat_add_mod,
     Challenge.EvmProof.Word.succ_ofNat_mod,
     Challenge.EvmProof.Word.word_toNat_ofNat]
set_option linter.unusedSimpArgs false in
def zeroExpReturnProgram80 : List Instr :=
  [.op (.Dup dA0), .op .MSIZE, .op .SUB, .op .RETURN]

def zeroExpReturnBlock80 : WindowTwentyOneBinding.Block Artifact.artifact .Osaka 3454 zeroExpReturnProgram80 :=
  WindowTwentyOneSlice.block Artifact.wellFormed 2661 4 3454 zeroExpReturnProgram80
    (by change 2661 + 4 ≤ Artifact.instructions.length; rw [Artifact.instructionCount]; decide)
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

set_option linter.unusedSimpArgs false in
theorem run_zeroExp_return (s : State) (input : ByteArray)
    (hrun : s.halt = .Running) (hsmall : modulusSize input ≤ 32) (hwords : s.activeWords.toNat ≤ 1) :
    runInstructionsX zeroExpReturnProgram80 (zeroExpStoreState s input) =
      some (zeroExpFinalState s input) := by
  have haw : s.activeWordsAfterUInt256 0 32 = UInt256.ofNat 1 := by
    simp [State.activeWordsAfterUInt256, MachineState.activeWordsAfter, Nat.max_eq_right hwords]
  have hawn : MachineState.activeWordsAfter s.activeWords.toNat 0 32 = 1 := by
    simp [MachineState.activeWordsAfter, Nat.max_eq_right hwords]
  have hsub := Challenge.EvmProof.Word.ofNat_sub_ofNat hsmall (by norm_num : 32 < 2 ^ 256)
  have hsubn : (UInt256.ofNat (32 - modulusSize input)).toNat = 32 - modulusSize input :=
    toNat_ofNat_self (by omega)
  have hm : (UInt256.ofNat (modulusSize input)).toNat = modulusSize input :=
    toNat_ofNat_self (modulusSize_lt input)
  simp (config := { maxSteps := 400000 })
    [zeroExpReturnProgram80, runInstructionsX, runInstrX, Challenge.EvmProof.Stepper.runInstr,
     zeroExpStoreState, zeroExpFinalState, haw, hawn, hrun, hsub, hsubn, hm, List.exchange,
     State.activeWordsAfterUInt256,
     Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.ofNat_add_mod,
     Challenge.EvmProof.Word.succ_ofNat_mod,
     Challenge.EvmProof.Word.word_toNat_ofNat]
theorem zeroExp_readPadded (mem : ByteArray) (r width : Nat)
    (hpos : 0 < width) (hwidth : width ≤ 32) (_hr : r < 256 ^ width) :
    MachineState.readPadded
        (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded r 32) 0)
        (32 - width) width =
      Precompile.natToBytes r width := by
  apply ByteArray.ext_getElem
  · rw [Challenge.EvmProof.Memory.readPadded_size]
    rw [Precompile.natToBytes,
      YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  · intro k hleft hright
    have hk : k < width := by
      simpa [Precompile.natToBytes,
        YulEvmCompiler.BytesLemmas.natToBytesPadded_size] using hright
    rw [← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hleft,
      ← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hright,
      Challenge.EvmProof.Memory.readPadded_getElem?_getD,
      if_pos hk]
    rw [MachineState.writeBytes_getElem?_getD, if_pos (by
      constructor
      · omega
      · simp [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
        omega)]
    rw [show 32 - width + k - 0 = 32 - width + k by omega,
      YulEvmCompiler.BytesLemmas.natToBytesPadded_getElem?_getD _ 32 (32 - width + k)
        (by omega),
      Precompile.natToBytes,
      YulEvmCompiler.BytesLemmas.natToBytesPadded_getElem?_getD _ width k hk]
    rw [show 32 - 1 - (32 - width + k) = width - 1 - k by omega]
theorem zeroExpModulus_lt (input : ByteArray) (hsmall : modulusSize input ≤ 32) :
    zeroExpModulus input < 2 ^ 256 := by
  have h := Challenge.EvmProof.Bytes.bytesToNatPadded_lt_pow input
    (96 + baseSize input) (modulusSize input)
  calc
    zeroExpModulus input < 256 ^ modulusSize input := h
    _ ≤ 256 ^ 32 := pow_le_pow_right₀ (by norm_num) hsmall
    _ = 2 ^ 256 := by norm_num
theorem zeroExpWord_toNat (input : ByteArray) (hsmall : modulusSize input ≤ 32) :
    (zeroExpWord input).toNat = if 1 < zeroExpModulus input then 1 else 0 := by
  unfold zeroExpWord
  by_cases h : 1 < zeroExpModulus input
  · rw [lt_ofNat_of_lt (by norm_num) (zeroExpModulus_lt input hsmall) h, if_pos h]
    rfl
  · rw [lt_ofNat_of_le (by norm_num) (zeroExpModulus_lt input hsmall) (by omega), if_neg h]
    rfl
@[simp] theorem zeroExpFinalState_isDone (s : State) (input : ByteArray)
    (hcall : s.callStack = []) :
    (zeroExpFinalState s input).isDone = true := by
  simp [zeroExpFinalState, zeroExpStoreState, State.isDone, State.isHalted, State.isRunning, hcall]
theorem modPow_zero_exponent (b m : Nat) :
    Precompile.modPow b 0 m = if 1 < m then 1 else 0 := by
  unfold Precompile.modPow
  by_cases h0 : m = 0
  · simp [h0]
  · by_cases h1 : m = 1
    · simp [h1]
    · rw [if_neg h0, if_neg h1, if_pos (by omega)]
      rw [Precompile.modPowAux]
      simp
theorem zeroExpFinalState_result (s : State) (input : ByteArray)
    (hzero : exponentSize input = 0) (hpos : 0 < modulusSize input)
    (hsmall : modulusSize input ≤ 32) :
    (zeroExpFinalState s input).toResult = .returned (spec input) := by
  have hr : (zeroExpWord input).toNat < 256 ^ modulusSize input := by
    rw [zeroExpWord_toNat input hsmall]
    have h256 : 256 ≤ 256 ^ modulusSize input := by
      calc
        (256 : Nat) = 256 ^ 1 := by norm_num
        _ ≤ 256 ^ modulusSize input := pow_le_pow_right₀ (by norm_num) hpos
    split <;> omega
  show ExecutionResult.returned (MachineState.readPadded (zeroExpMemory s input)
      (32 - modulusSize input) (modulusSize input)) = _
  rw [zeroExpMemory, zeroExp_readPadded _ _ _ hpos hsmall hr, zeroExpWord_toNat input hsmall]
  have hm0 : modulusSize input ≠ 0 := by omega
  simp only [spec, if_neg hm0, hzero, Nat.add_zero,
    Challenge.EvmProof.Bytes.bytesToNatPadded_zero_width, modPow_zero_exponent,
    zeroExpModulus]
  rfl
def sizeCheckState (s : State) (input : ByteArray) : State :=
  { s with pc := UInt256.ofNat 579, stack := [UInt256.ofNat (modulusSize input)] }
theorem entryCond_zero (m : Nat) (hm : m < 2 ^ 256)
    (hlo : 32 < m) (hhi : m ≤ 256) :
    UInt256.lt (UInt256.ofNat 223) (UInt256.ofNat m - UInt256.ofNat 33) =
      UInt256.ofNat 0 := by
  rw [UInt256.lt, Challenge.EvmProof.Word.word_toNat_sub_cond,
    toNat_ofNat_self hm, toNat_ofNat_self (by norm_num : (33 : Nat) < 2 ^ 256),
    toNat_ofNat_self (by norm_num : (223 : Nat) < 2 ^ 256),
    if_neg (by omega : ¬ m < 33), if_neg (by omega : ¬ 223 < m - 33)]
theorem entryCond_one (m : Nat) (hm : m < 2 ^ 256)
    (hout : m ≤ 32 ∨ 256 < m) :
    UInt256.lt (UInt256.ofNat 223) (UInt256.ofNat m - UInt256.ofNat 33) =
      UInt256.ofNat 1 := by
  rw [UInt256.lt, Challenge.EvmProof.Word.word_toNat_sub_cond,
    toNat_ofNat_self hm, toNat_ofNat_self (by norm_num : (33 : Nat) < 2 ^ 256),
    toNat_ofNat_self (by norm_num : (223 : Nat) < 2 ^ 256)]
  rcases hout with hlo | hhi
  · rw [if_pos (by omega : m < 33)]
    have hlarge : 256 < 2 ^ 256 := by norm_num
    rw [if_pos (by omega : 223 < 2 ^ 256 + m - 33)]
  · rw [if_neg (by omega : ¬ m < 33), if_pos (by omega : 223 < m - 33)]
set_option linter.unusedSimpArgs false in
theorem run_entry_pass (s : State) (input : ByteArray)
    (hdata : s.executionEnv.calldata = input) (hrun : s.halt = .Running)
    (h : 32 < modulusSize input) (hupper : modulusSize input ≤ 256) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk977 (entryState s) =
      some (sizeCheckState s input) := by
  have hgt := entryCond_zero (modulusSize input) (modulusSize_lt input) h hupper
  simp (config := { maxSteps := 400000 })
    [blk977, opAt, pushAt, wfOp,
     Challenge.EvmProof.Stepper.runLocatedBlock,
     Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
     entryState, sizeCheckState, hdata, hrun, read_modulus, hgt, List.exchange,
     Challenge.EvmProof.Word.literal_eq_ofNat,
     Challenge.EvmProof.Word.succ_ofNat_mod,
     Challenge.EvmProof.Word.ofNat_add_mod,
     Challenge.EvmProof.Word.word_toNat_ofNat]
set_option linter.unusedSimpArgs false in
theorem run_entry_bail (s : State) (input : ByteArray)
    (hdata : s.executionEnv.calldata = input)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode) (hrun : s.halt = .Running)
    (h : modulusSize input ≤ 32 ∨ 256 < modulusSize input) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk977 (entryState s) =
      some (bail1State s input) := by
  have hgt := entryCond_one (modulusSize input) (modulusSize_lt input) h
  simp (config := { maxSteps := 400000 })
    [blk977, opAt, pushAt, wfOp,
     Challenge.EvmProof.Stepper.runLocatedBlock,
     Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
     entryState, bail1State, hdata, hcode, hrun, read_modulus, hgt, List.exchange,
     jumpDest1812,
     Challenge.EvmProof.Word.literal_eq_ofNat,
     Challenge.EvmProof.Word.succ_ofNat_mod,
     Challenge.EvmProof.Word.ofNat_add_mod,
     Challenge.EvmProof.Word.word_toNat_ofNat]
theorem ltWord_1024 (a : Nat) (ha : a < 2 ^ 256) :
    UInt256.lt (UInt256.ofNat 1024) (UInt256.ofNat a) =
      UInt256.ofNat (if 1024 < a then 1 else 0) := by
  by_cases hc : 1024 < a
  · rw [if_pos hc, lt_ofNat_of_lt (by norm_num) ha hc]
  · rw [if_neg hc, lt_ofNat_of_le (by norm_num) ha (Nat.not_lt.mp hc)]
theorem sizeCond_zero (input : ByteArray) (hb : baseSize input ≤ 1024)
    (he : exponentSize input ≤ 1024) (hm : modulusSize input ≤ 1024) :
    UInt256.lor (UInt256.lt (UInt256.ofNat 1024) (UInt256.ofNat (baseSize input)))
        (UInt256.lor (UInt256.lt (UInt256.ofNat 1024) (UInt256.ofNat (exponentSize input)))
          (UInt256.lt (UInt256.ofNat 1024) (UInt256.ofNat (modulusSize input)))) =
      UInt256.ofNat 0 := by
  rw [lt_ofNat_of_le (by norm_num) (baseSize_lt input) hb,
    lt_ofNat_of_le (by norm_num) (exponentSize_lt input) he,
    lt_ofNat_of_le (by norm_num) (modulusSize_lt input) hm, lor_zero_zero,
    lor_zero_zero]
theorem sizeCond_one (input : ByteArray)
    (h : 1024 < baseSize input ∨ 1024 < exponentSize input ∨
      1024 < modulusSize input) :
    UInt256.lor (UInt256.lt (UInt256.ofNat 1024) (UInt256.ofNat (baseSize input)))
        (UInt256.lor (UInt256.lt (UInt256.ofNat 1024) (UInt256.ofNat (exponentSize input)))
          (UInt256.lt (UInt256.ofNat 1024) (UInt256.ofNat (modulusSize input)))) =
      UInt256.ofNat 1 := by
  rw [ltWord_1024 _ (baseSize_lt input), ltWord_1024 _ (exponentSize_lt input),
    ltWord_1024 _ (modulusSize_lt input)]
  split_ifs <;> simp_all
def sizesOkStack (input : ByteArray) : List UInt256 :=
  [UInt256.ofNat (baseSize input), UInt256.ofNat (exponentSize input),
   UInt256.ofNat (modulusSize input)]
def topCheckState (s : State) (input : ByteArray) : State :=
  { s with pc := UInt256.ofNat 584, stack := sizesOkStack input }
set_option linter.unusedSimpArgs false in
theorem run_sizeCheck_pass (s : State) (input : ByteArray)
    (hdata : s.executionEnv.calldata = input) (hrun : s.halt = .Running)
    (hb : baseSize input ≤ 1024) (he : exponentSize input ≤ 1024)
    (hm : modulusSize input ≤ 1024) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk986 (sizeCheckState s input) =
      some (topCheckState s input) := by
  have hcond := sizeCond_zero input hb he hm
  simp (config := { maxSteps := 400000 })
    [blk986, opAt, pushAt, wfOp,
     Challenge.EvmProof.Stepper.runLocatedBlock,
     Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
     sizeCheckState, topCheckState, sizesOkStack, hdata, hrun, push0_word,
     read_base, read_exponent, hcond,
     Challenge.EvmProof.Word.literal_eq_ofNat,
     Challenge.EvmProof.Word.succ_ofNat_mod,
     Challenge.EvmProof.Word.ofNat_add_mod,
     Challenge.EvmProof.Word.word_toNat_ofNat]
theorem mod_word_self {a : Nat} (h : a < 2 ^ 256) :
    a % 115792089237316195423570985008687907853269984665640564039457584007913129639936
      = a :=
  Nat.mod_eq_of_lt h
theorem limbs_lt (input : ByteArray) (hm : modulusSize input ≤ 1024) :
    limbs input < 2 ^ 256 := by
  have h := limbs_le_32 input hm
  omega
theorem s32_lt (input : ByteArray) (hm : modulusSize input ≤ 1024) :
    s32 input < 2 ^ 256 := by
  have h := s32_le_1024 input hm
  omega
theorem modOffset_lt (input : ByteArray) (hb : baseSize input ≤ 1024)
    (he : exponentSize input ≤ 1024) : modOffset input < 2 ^ 256 := by
  unfold modOffset
  omega
theorem shr5_limbs (input : ByteArray) (hm : modulusSize input ≤ 1024) :
    UInt256.shiftRight (UInt256.ofNat (31 + modulusSize input)) (UInt256.ofNat 5) =
      UInt256.ofNat (limbs input) := by
  have h31 : 31 + modulusSize input < 2 ^ 256 := by omega
  rw [Challenge.EvmProof.Word.shiftRight_ofNat h31 (by norm_num)]
  congr 1
  rw [Nat.shiftRight_eq_div_pow]
  unfold limbs Limbs.limbCount
  norm_num
  omega
theorem shl5_s32 (input : ByteArray) (hm : modulusSize input ≤ 1024) :
    UInt256.shiftLeft (UInt256.ofNat (limbs input)) (UInt256.ofNat 5) =
      UInt256.ofNat (s32 input) := by
  have hn := limbs_le_32 input hm
  rw [Challenge.EvmProof.Word.shiftLeft_ofNat (limbs_lt input hm) (by norm_num)
    (by norm_num; omega)]
  congr 1
  unfold s32
  norm_num
  omega
theorem sub_s32_msize (input : ByteArray) (hm : modulusSize input ≤ 1024) :
    UInt256.ofNat (s32 input) - UInt256.ofNat (modulusSize input) =
      UInt256.ofNat (s32 input - modulusSize input) :=
  Challenge.EvmProof.Word.ofNat_sub_ofNat (modulusSize_le_s32 input) (s32_lt input hm)
theorem shl3_shift (input : ByteArray) (hm : modulusSize input ≤ 1024) :
    UInt256.shiftLeft (UInt256.ofNat (s32 input - modulusSize input))
        (UInt256.ofNat 3) =
      UInt256.ofNat ((s32 input - modulusSize input) * 8) := by
  have hs := s32_le_1024 input hm
  rw [Challenge.EvmProof.Word.shiftLeft_ofNat (by omega) (by norm_num)
    (by norm_num; omega)]
  norm_num
theorem topLimb_lt (input : ByteArray) : topLimb input < 2 ^ 256 := by
  have h := Challenge.EvmProof.Bytes.bytesToNatPadded_lt_pow input (modOffset input)
    (topWidth input)
  have hle : 256 ^ topWidth input ≤ 256 ^ 32 :=
    Nat.pow_le_pow_right (by norm_num) (topWidth_le input)
  rw [pow_256_32] at hle
  exact h.trans_le hle
theorem shiftRight_topLimb (input : ByteArray) (h : 32 < modulusSize input) :
    UInt256.shiftRight (MachineState.readWord input (modOffset input))
        (UInt256.ofNat ((s32 input - modulusSize input) * 8)) =
      UInt256.ofNat (topLimb input) := by
  have hshift : (s32 input - modulusSize input) * 8 = (32 - topWidth input) * 8 := by
    unfold s32 topWidth limbs Limbs.limbCount
    omega
  rw [hshift]
  exact Challenge.EvmProof.Bytes.shiftRight_readWord input (modOffset input)
    (topWidth input) (topWidth_pos input h) (topWidth_le input)
theorem shiftRight_topBit (input : ByteArray) :
    UInt256.shiftRight (MachineState.readWord input (modOffset input))
        (UInt256.ofNat 255) =
      UInt256.ofNat ((MachineState.readWord input (modOffset input)).toNat >>> 255) := by
  have hlt : (MachineState.readWord input (modOffset input)).toNat >>> 255 < 2 ^ 256 :=
    Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _)
      (MachineState.readWord input (modOffset input)).val.isLt
  apply Challenge.EvmProof.Word.word_ext
  rw [Challenge.EvmProof.Word.shiftRight_toNat _ (by norm_num),
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hlt]
theorem topLimb_ne_zero_of_topBit (input : ByteArray)
    (h32 : 32 < modulusSize input) (hmask : modulusSize input % 128 = 0)
    (htop : (MachineState.readWord input (modOffset input)).toNat >>> 255 ≠ 0) :
    topLimb input ≠ 0 := by
  have hw : topLimb input = (MachineState.readWord input (modOffset input)).toNat := by
    unfold topLimb
    rw [topWidth_eq_32_of_mask input h32 hmask, Challenge.EvmProof.Bytes.readWord_toNat]
  rw [hw]
  intro hz
  exact htop (by simp [hz])
def outerStack (input : ByteArray) : List UInt256 :=
  [UInt256.ofNat (s32 input), UInt256.ofNat (limbs input),
   UInt256.ofNat (baseSize input), UInt256.ofNat (exponentSize input),
   UInt256.ofNat (modulusSize input)]
def oddCheckState (s : State) (input : ByteArray) : State :=
  { s with pc := UInt256.ofNat 608
           stack := UInt256.ofNat (modOffset input) :: outerStack input }
def bail6State (s : State) (input : ByteArray) : State :=
  { s with pc := UInt256.ofNat 207
           stack := UInt256.ofNat (modOffset input) :: outerStack input }
def bigBailState (s : State) (input : ByteArray) : State :=
  { s with pc := UInt256.ofNat 207
           stack := UInt256.ofNat (modOffset input) :: outerStack input }
theorem jumpDestBig : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 207 = true :=
  CycleSubmission.Global.Binding.jumpDest 134 (by rfl)
theorem land_one_lastWord (input : ByteArray) (h : 32 < modulusSize input) :
    UInt256.land (UInt256.ofNat 1)
        (MachineState.readWord input (modOffset input + modulusSize input - 32)) =
      UInt256.ofNat (modulus input % 2) := by
  have h1 : (UInt256.ofNat 1).toNat = 1 := by decide
  have h2 : (UInt256.ofNat (modulus input % 2)).toNat = modulus input % 2 :=
    toNat_ofNat_self (by omega)
  have hsplit := Challenge.EvmProof.Bytes.bytesToNatPadded_add input (modOffset input)
    (modulusSize input - 32) 32
  rw [show modulusSize input - 32 + 32 = modulusSize input from by omega] at hsplit
  have haddr : modOffset input + modulusSize input - 32 =
      modOffset input + (modulusSize input - 32) := by omega
  apply Challenge.EvmProof.Word.word_ext
  rw [Challenge.EvmProof.Word.word_toNat_land, h1, h2,
    Challenge.EvmProof.Bytes.readWord_toNat, Nat.one_and_eq_mod_two, haddr]
  unfold modulus
  rw [hsplit, Nat.add_mod, Nat.mul_mod, show (256:Nat) ^ 32 % 2 = 0 from by norm_num]
  simp
def setupEntryState (s : State) (input : ByteArray) : State :=
  { s with pc := UInt256.ofNat 630
           stack := UInt256.ofNat (modOffset input) :: outerStack input }
set_option linter.unusedSimpArgs false in
theorem run_check_pass (s : State) (input : ByteArray)
    (hdata : s.executionEnv.calldata = input) (hrun : s.halt = .Running)
    (hb : baseSize input ≤ 1024) (he : exponentSize input ≤ 1024)
    (hm : modulusSize input ≤ 1024) (h32 : 32 < modulusSize input)
    (htop : (MachineState.readWord input (modOffset input)).toNat >>> 255 ≠ 0)
    (hodd : modulus input % 2 = 1)
    (hwidth : modulusSize input % 128 = 0)
    (hnprime : MachineState.readWord input (modOffset input + modulusSize input - 32) ≠
      UInt256.ofNat (Limbs.radix - 1)) :
    SignedTopBit.runLocatedBlockS blk1003 (topCheckState s input) =
      some (setupEntryState s input) := by
  have hmoff : 96 + (baseSize input + exponentSize input) = modOffset input := by
    unfold modOffset; omega
  have hmoff' : exponentSize input + (baseSize input + 96) = modOffset input := by
    unfold modOffset; omega
  have hshr :
      UInt256.shiftRight (UInt256.ofNat (modulusSize input + 31)) (UInt256.ofNat 5) =
        UInt256.ofNat (limbs input) := by
    simpa only [Nat.add_comm] using shr5_limbs input hm
  have hmodmod := mod_word_self (modOffset_lt input hb he)
  have hmoffval : modOffset input = 96 + baseSize input + exponentSize input := rfl
  have hsub : UInt256.ofNat (modOffset input + modulusSize input) - UInt256.ofNat 32 =
      UInt256.ofNat (modOffset input + modulusSize input - 32) :=
    Challenge.EvmProof.Word.ofNat_sub_ofNat (by omega) (by omega)
  have hmodmod' := mod_word_self
    (show modOffset input + modulusSize input - 32 < 2 ^ 256 by omega)
  have hlt : (MachineState.readWord input (modOffset input)).toNat >>> 255 < 2 ^ 256 :=
    Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _)
      (MachineState.readWord input (modOffset input)).val.isLt
  have hzero := isZero_ofNat_of_ne hlt htop
  simp (config := { maxSteps := 1600000 })
      [LowBitFlag.flag, LowBitFlag.flagRaw,
       PredicateIdentity.complement_parity, PredicateIdentity.not_isZero,
       lnot_ofNat_zero,
       blk1003, opAt, pushAt, wfOp,
       SignedTopBit.runLocatedBlockS,
       SignedTopBit.runLocatedS, SignedTopBit.runInstrS, SignedTopBit.sgt_zero_eq_shr, signedTopRaw, Challenge.EvmProof.Stepper.runInstr,
       topCheckState, sizesOkStack, outerStack, hdata, hrun,
       shr5_limbs input hm, hshr, hmoff', shl5_s32 input hm,
       hmoff, hmodmod, shiftRight_topBit input, hsub, hmodmod',
       land_one_lastWord input h32, lnot_zero_raw, List.exchange,
       setupEntryState, hzero, hodd, isZero_ofNat_one, isZero_ofNat_zero, lor_zero_zero,
       eq_maxWord_of_ne _ hnprime,
       land_mask_of_mod (modulusSize input) (modulusSize_lt input) hwidth,
       Challenge.EvmProof.Word.literal_eq_ofNat,
       Challenge.EvmProof.Word.succ_ofNat_mod,
       Challenge.EvmProof.Word.ofNat_add_mod,
       Challenge.EvmProof.Word.word_toNat_ofNat]
theorem lor_eq_zero_nat {x y : Nat} (h : x ||| y = 0) : x = 0 ∧ y = 0 := by
  have hb : ∀ i, x.testBit i = false ∧ y.testBit i = false := by
    intro i
    have hi : (x ||| y).testBit i = (0 : Nat).testBit i := by rw [h]
    rw [Nat.testBit_or, Nat.zero_testBit] at hi
    exact Bool.or_eq_false_iff.mp hi
  exact ⟨Nat.eq_of_testBit_eq fun i => by rw [(hb i).1, Nat.zero_testBit],
    Nat.eq_of_testBit_eq fun i => by rw [(hb i).2, Nat.zero_testBit]⟩
theorem isTrue_lor_iff (a b : UInt256) :
    UInt256.isTrue (UInt256.lor a b) ↔ (UInt256.isTrue a ∨ UInt256.isTrue b) := by
  unfold UInt256.isTrue
  rw [Challenge.EvmProof.Word.word_toNat_lor]
  constructor
  · intro h
    by_cases ha : a.toNat = 0
    · right
      intro hb
      exact h (by simp [ha, hb])
    · exact Or.inl ha
  · intro h h0
    rcases h with ha | hb
    · exact ha (lor_eq_zero_nat h0).1
    · exact hb (lor_eq_zero_nat h0).2
theorem land_mask_isTrue_of_not_mod (n : Nat) (hn : n < 2 ^ 256) (h : n % 128 ≠ 0) :
    UInt256.isTrue (UInt256.land (UInt256.ofNat 127) (UInt256.ofNat n)) := by
  unfold UInt256.isTrue
  rw [Challenge.EvmProof.Word.word_toNat_land, toNat_ofNat_self (by norm_num),
    toNat_ofNat_self hn]
  have : (127 : Nat) = 2 ^ 7 - 1 := by norm_num
  rw [this, Nat.and_comm, Nat.and_two_pow_sub_one_eq_mod]
  simpa using h
theorem eq_maxWord_of_eq (w : UInt256) (h : w = UInt256.ofNat (Limbs.radix - 1)) :
    UInt256.eq (UInt256.ofNat (Limbs.radix - 1)) w = UInt256.ofNat 1 := by
  rw [h, UInt256.eq, if_pos rfl]
theorem isTrue_ofNat_one : UInt256.isTrue (UInt256.ofNat 1) := by decide
set_option linter.unusedSimpArgs false in
theorem run_check_bail (s : State) (input : ByteArray)
    (hdata : s.executionEnv.calldata = input)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode) (hrun : s.halt = .Running)
    (hb : baseSize input ≤ 1024) (he : exponentSize input ≤ 1024)
    (hm : modulusSize input ≤ 1024) (h32 : 32 < modulusSize input)
    
    (hfail : (MachineState.readWord input (modOffset input)).toNat >>> 255 = 0 ∨
      modulus input % 2 = 0 ∨ modulusSize input % 128 ≠ 0 ∨
      MachineState.readWord input (modOffset input + modulusSize input - 32) =
        UInt256.ofNat (Limbs.radix - 1)) :
    SignedTopBit.runLocatedBlockS blk1003 (topCheckState s input) =
      some (bail6State s input) := by
  have hmoff : 96 + (baseSize input + exponentSize input) = modOffset input := by
    unfold modOffset; omega
  have hmoff' : exponentSize input + (baseSize input + 96) = modOffset input := by
    unfold modOffset; omega
  have hshr :
      UInt256.shiftRight (UInt256.ofNat (modulusSize input + 31)) (UInt256.ofNat 5) =
        UInt256.ofNat (limbs input) := by
    simpa only [Nat.add_comm] using shr5_limbs input hm
  have hmodmod := mod_word_self (modOffset_lt input hb he)
  have hmoffval : modOffset input = 96 + baseSize input + exponentSize input := rfl
  have hsub : UInt256.ofNat (modOffset input + modulusSize input) - UInt256.ofNat 32 =
      UInt256.ofNat (modOffset input + modulusSize input - 32) :=
    Challenge.EvmProof.Word.ofNat_sub_ofNat (by omega) (by omega)
  have hmodmod' := mod_word_self
    (show modOffset input + modulusSize input - 32 < 2 ^ 256 by omega)
  
  
  rcases hfail with htop | hodd | hwidth | hnprime
  · 
    simp (config := { maxSteps := 1600000 })
      [LowBitFlag.flag, LowBitFlag.flagRaw,
       PredicateIdentity.complement_parity, PredicateIdentity.not_isZero,
         lnot_ofNat_zero,
         blk1003, opAt, pushAt, wfOp,
         SignedTopBit.runLocatedBlockS,
         SignedTopBit.runLocatedS, SignedTopBit.runInstrS, SignedTopBit.sgt_zero_eq_shr, signedTopRaw, Challenge.EvmProof.Stepper.runInstr,
         topCheckState, sizesOkStack, outerStack, hdata, hrun,
         shr5_limbs input hm, hshr, hmoff', shl5_s32 input hm,
         hmoff, hmodmod, shiftRight_topBit input, hsub, hmodmod',
         land_one_lastWord input h32, lnot_zero_raw, List.exchange,
         bail6State, hcode, jumpDestBig, isTrue_lor_iff, isTrue_ofNat_one,
         htop, isZero_ofNat_zero,
         Challenge.EvmProof.Word.literal_eq_ofNat,
         Challenge.EvmProof.Word.succ_ofNat_mod,
         Challenge.EvmProof.Word.ofNat_add_mod,
         Challenge.EvmProof.Word.word_toNat_ofNat]
  · 
    simp (config := { maxSteps := 1600000 })
      [LowBitFlag.flag, LowBitFlag.flagRaw,
       PredicateIdentity.complement_parity, PredicateIdentity.not_isZero,
         lnot_ofNat_zero,
         blk1003, opAt, pushAt, wfOp,
         SignedTopBit.runLocatedBlockS,
         SignedTopBit.runLocatedS, SignedTopBit.runInstrS, SignedTopBit.sgt_zero_eq_shr, signedTopRaw, Challenge.EvmProof.Stepper.runInstr,
         topCheckState, sizesOkStack, outerStack, hdata, hrun,
         shr5_limbs input hm, hshr, hmoff', shl5_s32 input hm,
         hmoff, hmodmod, shiftRight_topBit input, hsub, hmodmod',
         land_one_lastWord input h32, lnot_zero_raw, List.exchange,
         bail6State, hcode, jumpDestBig, isTrue_lor_iff, isTrue_ofNat_one,
         hodd, isZero_ofNat_zero,
         Challenge.EvmProof.Word.literal_eq_ofNat,
         Challenge.EvmProof.Word.succ_ofNat_mod,
         Challenge.EvmProof.Word.ofNat_add_mod,
         Challenge.EvmProof.Word.word_toNat_ofNat]
  · 
    simp (config := { maxSteps := 1600000 })
      [LowBitFlag.flag, LowBitFlag.flagRaw,
       PredicateIdentity.complement_parity, PredicateIdentity.not_isZero,
         lnot_ofNat_zero,
         blk1003, opAt, pushAt, wfOp,
         SignedTopBit.runLocatedBlockS,
         SignedTopBit.runLocatedS, SignedTopBit.runInstrS, SignedTopBit.sgt_zero_eq_shr, signedTopRaw, Challenge.EvmProof.Stepper.runInstr,
         topCheckState, sizesOkStack, outerStack, hdata, hrun,
         shr5_limbs input hm, hshr, hmoff', shl5_s32 input hm,
         hmoff, hmodmod, shiftRight_topBit input, hsub, hmodmod',
         land_one_lastWord input h32, lnot_zero_raw, List.exchange,
         bail6State, hcode, jumpDestBig, isTrue_lor_iff, isTrue_ofNat_one,
         land_mask_isTrue_of_not_mod (modulusSize input) (modulusSize_lt input) hwidth,
         Challenge.EvmProof.Word.literal_eq_ofNat,
         Challenge.EvmProof.Word.succ_ofNat_mod,
         Challenge.EvmProof.Word.ofNat_add_mod,
         Challenge.EvmProof.Word.word_toNat_ofNat]
  · 
    simp (config := { maxSteps := 1600000 })
      [LowBitFlag.flag, LowBitFlag.flagRaw,
       PredicateIdentity.complement_parity, PredicateIdentity.not_isZero,
         lnot_ofNat_zero,
         blk1003, opAt, pushAt, wfOp,
         SignedTopBit.runLocatedBlockS,
         SignedTopBit.runLocatedS, SignedTopBit.runInstrS, SignedTopBit.sgt_zero_eq_shr, signedTopRaw, Challenge.EvmProof.Stepper.runInstr,
         topCheckState, sizesOkStack, outerStack, hdata, hrun,
         shr5_limbs input hm, hshr, hmoff', shl5_s32 input hm,
         hmoff, hmodmod, shiftRight_topBit input, hsub, hmodmod',
         land_one_lastWord input h32, lnot_zero_raw, List.exchange,
         bail6State, hcode, jumpDestBig, isTrue_lor_iff, isTrue_ofNat_one,
         eq_maxWord_of_eq _ hnprime,
         Challenge.EvmProof.Word.literal_eq_ofNat,
         Challenge.EvmProof.Word.succ_ofNat_mod,
         Challenge.EvmProof.Word.ofNat_add_mod,
         Challenge.EvmProof.Word.word_toNat_ofNat]
set_option linter.unusedSimpArgs false in
theorem run_bail1_probe (s : State) (input : ByteArray)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode) (hrun : s.halt = .Running)
    (hne : modulusSize input ≠ 0) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk1341 (bail1State s input) =
      some (ZeroMod12.entry s input) := by
  have hm : (UInt256.ofNat (modulusSize input)).toNat = modulusSize input :=
    toNat_ofNat_self (modulusSize_lt input)
  have htrue : UInt256.isTrue (UInt256.ofNat (modulusSize input)) = true := by
    simp [UInt256.isTrue, hm, hne]
  simp (config := { maxSteps := 400000 })
    [blk1341, opAt, pushAt, wfOp,
     Challenge.EvmProof.Stepper.runLocatedBlock,
     Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
     bail1State, ZeroMod12.entry, hrun, hcode, htrue, jumpDestZero12,
     Challenge.EvmProof.Word.literal_eq_ofNat,
     Challenge.EvmProof.Word.succ_ofNat_mod,
     Challenge.EvmProof.Word.ofNat_add_mod,
     Challenge.EvmProof.Word.word_toNat_ofNat]
theorem modulus_lt (input : ByteArray) :
    modulus input < Limbs.radix ^ limbs input :=
  Limbs.byteValue_fits_limbs input (modOffset input) (modulusSize input)
theorem modulus_split (input : ByteArray) (h : 32 < modulusSize input) :
    modulus input = topLimb input * Limbs.radix ^ (limbs input - 1) +
      Precompile.bytesToNatPadded input (modOffset input + topWidth input)
        (32 * (limbs input - 1)) := by
  unfold modulus topLimb
  rw [← topWidth_add input h, Challenge.EvmProof.Bytes.bytesToNatPadded_add,
    Limbs.pow_radix]
theorem modulus_tail_lt (input : ByteArray) :
    Precompile.bytesToNatPadded input (modOffset input + topWidth input)
        (32 * (limbs input - 1)) < Limbs.radix ^ (limbs input - 1) := by
  rw [Limbs.pow_radix]
  exact Challenge.EvmProof.Bytes.bytesToNatPadded_lt_pow _ _ _
theorem topLimb_ne_zero_iff (input : ByteArray) (h : 32 < modulusSize input) :
    topLimb input ≠ 0 ↔ Limbs.radix ^ (limbs input - 1) ≤ modulus input := by
  have hsplit := modulus_split input h
  have htail := modulus_tail_lt input
  constructor
  · intro hne
    have hone : 1 ≤ topLimb input := Nat.one_le_iff_ne_zero.mpr hne
    rw [hsplit]
    calc Limbs.radix ^ (limbs input - 1)
        = 1 * Limbs.radix ^ (limbs input - 1) := (Nat.one_mul _).symm
      _ ≤ topLimb input * Limbs.radix ^ (limbs input - 1) :=
          Nat.mul_le_mul_right _ hone
      _ ≤ _ := Nat.le_add_right _ _
  · intro hle hzero
    rw [hsplit, hzero, Nat.zero_mul, Nat.zero_add] at hle
    omega
def gasSteps_entry_pass (s : State) (input : ByteArray)
    (hdata : s.executionEnv.calldata = input)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (h : 32 < modulusSize input) (hupper : modulusSize input ≤ 256) :
    Challenge.EvmProof.GasSteps (entryState s) (sizeCheckState s input) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    CycleSubmission.Artifact.artifact .Osaka blk977 hcode hfork
      (run_entry_pass s input hdata hrun h hupper) hrun hnp
def gasSteps_entry_bail (s : State) (input : ByteArray)
    (hdata : s.executionEnv.calldata = input)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (h : modulusSize input ≤ 32 ∨ 256 < modulusSize input) :
    Challenge.EvmProof.GasSteps (entryState s) (bail1State s input) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    CycleSubmission.Artifact.artifact .Osaka blk977 hcode hfork
      (run_entry_bail s input hdata hcode hrun h) hrun hnp
def gasSteps_sizeCheck_pass (s : State) (input : ByteArray)
    (hdata : s.executionEnv.calldata = input)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hb : baseSize input ≤ 1024) (he : exponentSize input ≤ 1024)
    (hm : modulusSize input ≤ 1024) :
    Challenge.EvmProof.GasSteps (sizeCheckState s input) (topCheckState s input) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    CycleSubmission.Artifact.artifact .Osaka blk986 hcode hfork
      (run_sizeCheck_pass s input hdata hrun hb he hm) hrun hnp
def gasSteps_check_pass (s : State) (input : ByteArray)
    (hdata : s.executionEnv.calldata = input)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hb : baseSize input ≤ 1024) (he : exponentSize input ≤ 1024)
    (hm : modulusSize input ≤ 1024) (h32 : 32 < modulusSize input)
    (htop : (MachineState.readWord input (modOffset input)).toNat >>> 255 ≠ 0)
    (hodd : modulus input % 2 = 1)
    (hwidth : modulusSize input % 128 = 0)
    (hnprime : MachineState.readWord input (modOffset input + modulusSize input - 32) ≠
      UInt256.ofNat (Limbs.radix - 1)) :
    Challenge.EvmProof.GasSteps (topCheckState s input) (setupEntryState s input) :=
  SignedTopBit.runLocatedBlockS_sound
    CycleSubmission.Artifact.artifact .Osaka blk1003 hcode hfork
      (run_check_pass s input hdata hrun hb he hm h32 htop hodd hwidth hnprime) hrun hnp
def gasSteps_check_bail (s : State) (input : ByteArray)
    (hdata : s.executionEnv.calldata = input)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hb : baseSize input ≤ 1024) (he : exponentSize input ≤ 1024)
    (hm : modulusSize input ≤ 1024) (h32 : 32 < modulusSize input)
    (hfail : (MachineState.readWord input (modOffset input)).toNat >>> 255 = 0 ∨
      modulus input % 2 = 0 ∨ modulusSize input % 128 ≠ 0 ∨
      MachineState.readWord input (modOffset input + modulusSize input - 32) =
        UInt256.ofNat (Limbs.radix - 1)) :
    Challenge.EvmProof.GasSteps (topCheckState s input) (bail6State s input) :=
  SignedTopBit.runLocatedBlockS_sound
    CycleSubmission.Artifact.artifact .Osaka blk1003 hcode hfork
      (run_check_bail s input hdata hcode hrun hb he hm h32 hfail) hrun hnp
def gasSteps_bail1_probe (s : State) (input : ByteArray)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hne : modulusSize input ≠ 0) :
    Challenge.EvmProof.GasSteps (bail1State s input) (ZeroMod12.entry s input) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    CycleSubmission.Artifact.artifact .Osaka blk1341 hcode hfork
      (run_bail1_probe s input hcode hrun hne) hrun hnp
def gasSteps_bail1 (s : State) (input : ByteArray)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hne : modulusSize input ≠ 0) (hm : modulusSize input ≤ 1024)
    (h12 : modulusSize input ≠ 12) :
    Challenge.EvmProof.GasSteps (bail1State s input) (zeroExpEntryState s) :=
 (gasSteps_bail1_probe s input hcode hfork hrun hnp hne).trans
  (Challenge.EvmProof.Stepper.runLocatedBlock_sound
    CycleSubmission.Artifact.artifact .Osaka blkZero12WidthMiss hcode hfork
    (ZeroMod12.run_width_miss s input hrun hcode hm h12) hrun hnp)
def gasSteps_bail1_zero (s : State) (input : ByteArray)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hzero : modulusSize input = 0) :
    Challenge.EvmProof.GasSteps (bail1State s input) (emptyModulusState s) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    CycleSubmission.Artifact.artifact .Osaka blkEmptyModulus hcode hfork
      (run_bail1_zero s input hrun hzero) hrun hnp
def gasSteps_bail6 (s : State) (input : ByteArray)
    (_hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (_hfork : s.fork = .Osaka) (_hrun : s.halt = .Running)
    (_hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (bail6State s input) (bigBailState s input) :=
  Challenge.EvmProof.GasSteps.refl _
def gasSteps_zeroExp_miss (s : State) (input : ByteArray)
    (hdata : s.executionEnv.calldata = input)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hne : exponentSize input ≠ 0) :
    Challenge.EvmProof.GasSteps (zeroExpEntryState s) (memoEntryState s) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    CycleSubmission.Artifact.artifact .Osaka blkZeroExpMiss hcode hfork
      (run_zeroExp_miss s input hdata hcode hrun hne) hrun hnp
def gasSteps_zeroExp_wide (s : State) (input : ByteArray)
    (hdata : s.executionEnv.calldata = input)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hzero : exponentSize input = 0) (hwide : 32 < modulusSize input) :
    Challenge.EvmProof.GasSteps (zeroExpEntryState s) (memoEntryState s) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    CycleSubmission.Artifact.artifact .Osaka blkZeroExpWide hcode hfork
      (run_zeroExp_wide s input hdata hcode hrun hzero hwide) hrun hnp
def gasSteps_zeroExp_hitA (s : State) (input : ByteArray)
    (hdata : s.executionEnv.calldata = input)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hb : baseSize input ≤ 1024)
    (hzero : exponentSize input = 0) (hpos : 0 < modulusSize input)
    (hsmall : modulusSize input ≤ 32) :
    Challenge.EvmProof.GasSteps (zeroExpEntryState s) (zeroExpStoreState s input) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    CycleSubmission.Artifact.artifact .Osaka blkZeroExpHit hcode hfork
      (run_zeroExp_hit s input hdata hcode hrun hb hzero hpos hsmall) hrun hnp
def gasSteps_zeroExp_returnB (s : State) (input : ByteArray)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hsmall : modulusSize input ≤ 32) (hwords : s.activeWords.toNat ≤ 1) :
    Challenge.EvmProof.GasSteps (zeroExpStoreState s input) (zeroExpFinalState s input) :=
  WindowTwentyOneMsize.Block.stepsX zeroExpReturnBlock80
    (s := zeroExpStoreState s input)
    ⟨by change Artifact.bytecode.size < 2^256; rw [Artifact.bytecodeSize]; decide,
      hcode, hfork, hrun, hnp⟩ rfl
    (run_zeroExp_return s input hrun hsmall hwords)
def gasSteps_zeroExp_hit (s : State) (input : ByteArray)
    (hdata : s.executionEnv.calldata = input)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hb : baseSize input ≤ 1024)
    (hzero : exponentSize input = 0) (hpos : 0 < modulusSize input)
    (hsmall : modulusSize input ≤ 32) (hwords : s.activeWords.toNat ≤ 1) :
    Challenge.EvmProof.GasSteps (zeroExpEntryState s) (zeroExpFinalState s input) :=
  Challenge.EvmProof.GasSteps.trans
    (gasSteps_zeroExp_hitA s input hdata hcode hfork hrun hnp hb hzero hpos hsmall)
    (gasSteps_zeroExp_returnB s input hcode hfork hrun hnp hsmall hwords)
inductive Declined (s : State) (input : ByteArray) : Type
  | header (hsize : modulusSize input ≤ 32 ∨ 256 < modulusSize input)
      (steps : Challenge.EvmProof.GasSteps (entryState s) (memoEntryState s))
  | big (h32 : 32 < modulusSize input) (hupper : modulusSize input ≤ 256)
      (steps : Challenge.EvmProof.GasSteps (entryState s) (bigBailState s input))
  | empty (hzero : modulusSize input = 0)
      (steps : Challenge.EvmProof.GasSteps (entryState s) (emptyModulusState s))
  | zeroExp (hzero : exponentSize input = 0) (hpos : 0 < modulusSize input)
      (hsmall : modulusSize input ≤ 32)
      (steps : Challenge.EvmProof.GasSteps (entryState s) (zeroExpFinalState s input))
  | zeroMod12 (hsize : modulusSize input = 12) (hz : (ZeroMod12.rawWord input).toNat = 0)
      (steps : Challenge.EvmProof.GasSteps (entryState s) (ZeroMod12.finalState s))
def gasSteps_fallback_of (s : State) (input : ByteArray)
    (hdata : s.executionEnv.calldata = input)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hb : baseSize input ≤ 1024) (he : exponentSize input ≤ 1024)
    (hm : modulusSize input ≤ 1024)
    (hfail : ¬ FastPath input) (hwords : s.activeWords.toNat ≤ 1) :
    Declined s input :=
  if hupper : modulusSize input ≤ 256 then
    if h1 : 32 < modulusSize input then
      if htop : (MachineState.readWord input (modOffset input)).toNat >>> 255 = 0 then
        .big h1 hupper <|
          (gasSteps_entry_pass s input hdata hcode hfork hrun hnp h1 hupper).trans
            ((gasSteps_sizeCheck_pass s input hdata hcode hfork hrun hnp hb he hm).trans
              ((gasSteps_check_bail s input hdata hcode hfork hrun hnp
                  hb he hm h1 (Or.inl htop)).trans
                (gasSteps_bail6 s input hcode hfork hrun hnp)))
      else
        if hodd : modulus input % 2 = 0 then
          .big h1 hupper <|
            (gasSteps_entry_pass s input hdata hcode hfork hrun hnp h1 hupper).trans
              ((gasSteps_sizeCheck_pass s input hdata hcode hfork hrun hnp hb he hm).trans
                ((gasSteps_check_bail s input hdata hcode hfork hrun hnp
                    hb he hm h1 (Or.inr (Or.inl hodd))).trans
                  (gasSteps_bail6 s input hcode hfork hrun hnp)))
        else if hwidth : modulusSize input % 128 ≠ 0 then
          
          
          .big h1 hupper <|
            (gasSteps_entry_pass s input hdata hcode hfork hrun hnp h1 hupper).trans
              ((gasSteps_sizeCheck_pass s input hdata hcode hfork hrun hnp hb he hm).trans
                ((gasSteps_check_bail s input hdata hcode hfork hrun hnp
                    hb he hm h1 (Or.inr (Or.inr (Or.inl hwidth)))).trans
                  (gasSteps_bail6 s input hcode hfork hrun hnp)))
        else if hnprime : MachineState.readWord input
            (modOffset input + modulusSize input - 32) = UInt256.ofNat (Limbs.radix - 1) then
          
          .big h1 hupper <|
            (gasSteps_entry_pass s input hdata hcode hfork hrun hnp h1 hupper).trans
              ((gasSteps_sizeCheck_pass s input hdata hcode hfork hrun hnp hb he hm).trans
                ((gasSteps_check_bail s input hdata hcode hfork hrun hnp
                    hb he hm h1 (Or.inr (Or.inr (Or.inr hnprime)))).trans
                  (gasSteps_bail6 s input hcode hfork hrun hnp)))
        else
          absurd (show FastPath input from
            ⟨h1, ⟨hb, he, hupper⟩,
             (topLimb_ne_zero_iff input h1).mp
               (topLimb_ne_zero_of_topBit input h1 (by omega) htop),
             by omega, by omega, hnprime, htop⟩)
            hfail
    else if hzero : modulusSize input = 0 then
      .empty hzero <|
        (gasSteps_entry_bail s input hdata hcode hfork hrun hnp (Or.inl (by omega))).trans
          (gasSteps_bail1_zero s input hcode hfork hrun hnp hzero)
    else if h12 : modulusSize input = 12 then
      if hz : (ZeroMod12.rawWord input).toNat = 0 then
        .zeroMod12 h12 hz <|
          (gasSteps_entry_bail s input hdata hcode hfork hrun hnp (Or.inl (by omega))).trans
          ((gasSteps_bail1_probe s input hcode hfork hrun hnp hzero).trans
           (Challenge.EvmProof.Stepper.runLocatedBlock_sound
            CycleSubmission.Artifact.artifact .Osaka blkZero12Zero hcode hfork
            (ZeroMod12.run_zero s input hrun hcode hdata hb he h12 hz hwords) hrun hnp))
      else
        .header (Or.inl (by omega)) <|
          (gasSteps_entry_bail s input hdata hcode hfork hrun hnp (Or.inl (by omega))).trans
          ((gasSteps_bail1_probe s input hcode hfork hrun hnp hzero).trans
           (Challenge.EvmProof.Stepper.runLocatedBlock_sound
            CycleSubmission.Artifact.artifact .Osaka blkZero12Nonzero hcode hfork
            (ZeroMod12.run_nonzero s input hrun hcode hdata hb he h12 hz) hrun hnp))
    else if hez : exponentSize input = 0 then
      .zeroExp hez (by omega) (by omega) <|
        (gasSteps_entry_bail s input hdata hcode hfork hrun hnp (Or.inl (by omega))).trans
          ((gasSteps_bail1 s input hcode hfork hrun hnp hzero hm h12).trans
            (gasSteps_zeroExp_hit s input hdata hcode hfork hrun hnp hb hez
              (by omega) (by omega) hwords))
    else
      .header (Or.inl (by omega)) <|
        (gasSteps_entry_bail s input hdata hcode hfork hrun hnp (Or.inl (by omega))).trans
          ((gasSteps_bail1 s input hcode hfork hrun hnp hzero hm h12).trans
            (gasSteps_zeroExp_miss s input hdata hcode hfork hrun hnp hez))
  else if hez : exponentSize input = 0 then
    .header (Or.inr (by omega)) <|
      (gasSteps_entry_bail s input hdata hcode hfork hrun hnp
        (Or.inr (by omega))).trans ((gasSteps_bail1 s input hcode hfork hrun hnp (by omega) hm (by omega)).trans
          (gasSteps_zeroExp_wide s input hdata hcode hfork hrun hnp hez (by omega)))
  else
    .header (Or.inr (by omega)) <|
      (gasSteps_entry_bail s input hdata hcode hfork hrun hnp
        (Or.inr (by omega))).trans ((gasSteps_bail1 s input hcode hfork hrun hnp (by omega) hm (by omega)).trans
          (gasSteps_zeroExp_miss s input hdata hcode hfork hrun hnp hez))
theorem entryState_initial (input : ByteArray) :
    entryState (initialState CycleSubmission.Artifact.bytecode input 0) =
      Main.trampolineState input 564 := rfl
theorem fallbackState_initial (input : ByteArray) :
    fallbackState (initialState CycleSubmission.Artifact.bytecode input 0) =
      Main.trampolineState input 519 := rfl
theorem memoEntryState_initial (input : ByteArray) :
    memoEntryState (initialState CycleSubmission.Artifact.bytecode input 0) =
      Main.trampolineState input 674 := rfl
inductive Fallback (input : ByteArray) : Type
  | header (hsize : modulusSize input ≤ 32 ∨ 256 < modulusSize input)
      (steps : Challenge.EvmProof.GasSteps (Main.trampolineState input 564)
        (Main.trampolineState input 674))
  | big (h32 : 32 < modulusSize input) (hupper : modulusSize input ≤ 256)
      (steps : Challenge.EvmProof.GasSteps (Main.trampolineState input 564)
        (bigBailState (initialState CycleSubmission.Artifact.bytecode input 0) input))
  | empty (hzero : modulusSize input = 0)
      (steps : Challenge.EvmProof.GasSteps (Main.trampolineState input 564)
        (emptyModulusState (initialState CycleSubmission.Artifact.bytecode input 0)))
  | zeroExp (hzero : exponentSize input = 0) (hpos : 0 < modulusSize input)
      (hsmall : modulusSize input ≤ 32)
      (steps : Challenge.EvmProof.GasSteps (Main.trampolineState input 564)
        (zeroExpFinalState (initialState CycleSubmission.Artifact.bytecode input 0) input))
  | zeroMod12 (hsize : modulusSize input = 12) (hz : (ZeroMod12.rawWord input).toNat = 0)
      (steps : Challenge.EvmProof.GasSteps (Main.trampolineState input 564)
        (ZeroMod12.finalState (initialState CycleSubmission.Artifact.bytecode input 0)))
def gasSteps_fallback (input : ByteArray) (hvalid : ValidInput input)
    (hfail : ¬ FastPath input) : Fallback input :=
  match gasSteps_fallback_of (initialState CycleSubmission.Artifact.bytecode input 0) input rfl rfl rfl rfl
      deployAddress_not_precompile hvalid.2.1 hvalid.2.2.1 hvalid.2.2.2 hfail (by change 0 ≤ 1; decide) with
  | .header hsize steps =>
    .header hsize (Challenge.EvmProof.GasSteps.cast steps
      (entryState_initial input) (memoEntryState_initial input))
  | .big h32 hupper steps =>
    .big h32 hupper (Challenge.EvmProof.GasSteps.cast steps (entryState_initial input) rfl)
  | .empty hzero steps =>
    .empty hzero (Challenge.EvmProof.GasSteps.cast steps (entryState_initial input) rfl)
  | .zeroExp hzero hpos hsmall steps =>
    .zeroExp hzero hpos hsmall
      (Challenge.EvmProof.GasSteps.cast steps (entryState_initial input) rfl)
  | .zeroMod12 hsize hz steps =>
    .zeroMod12 hsize hz (Challenge.EvmProof.GasSteps.cast steps (entryState_initial input) rfl)
theorem word_toNat_mul (a b : UInt256) :
    (a * b).toNat = a.toNat * b.toNat % 2 ^ 256 := by
  change (a.val * b.val).val = _
  rw [Fin.val_mul]
  rfl
theorem ofNat_congr_mod {a b : Nat} (h : a % 2 ^ 256 = b % 2 ^ 256) :
    UInt256.ofNat a = UInt256.ofNat b := by
  apply Challenge.EvmProof.Word.word_ext
  simpa using h
theorem ofNat_mul_mod (a b : Nat) :
    UInt256.ofNat a * UInt256.ofNat b = UInt256.ofNat (a * b) := by
  apply Challenge.EvmProof.Word.word_ext
  simp only [word_toNat_mul, Challenge.EvmProof.Word.word_toNat_ofNat, ← Nat.mul_mod]
theorem ofNat_sub_word (a b : Nat) :
    UInt256.ofNat a - UInt256.ofNat b =
      UInt256.ofNat (2 ^ 256 + a % 2 ^ 256 - b % 2 ^ 256) := by
  apply Challenge.EvmProof.Word.word_ext
  simp only [Challenge.EvmProof.Word.word_toNat_sub,
    Challenge.EvmProof.Word.word_toNat_ofNat]
theorem newton_word_step (m0 x : Nat) :
    (UInt256.ofNat 2 - UInt256.ofNat m0 * UInt256.ofNat x) * UInt256.ofNat x =
      UInt256.ofNat (Model.newtonStep m0 x) := by
  have h2 : (2 : Nat) % 2 ^ 256 = 2 := by norm_num
  have hr : Limbs.radix = 2 ^ 256 := rfl
  have hcong : x * ((2 + 2 ^ 256 - m0 * x % 2 ^ 256) % 2 ^ 256) % 2 ^ 256
      = x * (2 + 2 ^ 256 - m0 * x % 2 ^ 256) % 2 ^ 256 :=
    (Nat.mod_modEq (2 + 2 ^ 256 - m0 * x % 2 ^ 256) (2 ^ 256)).mul_left x
  rw [ofNat_mul_mod, ofNat_sub_word, ofNat_mul_mod]
  apply ofNat_congr_mod
  rw [h2]
  unfold Model.newtonStep
  rw [hr, Nat.mod_mod_of_dvd _ (dvd_refl (2 ^ 256)), hcong, Nat.mul_comm x,
    Nat.add_comm 2 (2 ^ 256)]
def negWord (v : Nat) : Nat := (Limbs.radix - v % Limbs.radix) % Limbs.radix
theorem negWord_lt (v : Nat) : negWord v < 2 ^ 256 :=
  Nat.mod_lt _ Limbs.radix_pos
theorem neg_word (v : Nat) :
    UInt256.ofNat 0 - UInt256.ofNat v = UInt256.ofNat (negWord v) := by
  rw [ofNat_sub_word]
  apply ofNat_congr_mod
  unfold negWord Limbs.radix
  rw [Nat.mod_mod_of_dvd _ (dvd_refl (2 ^ 256))]
  congr 1
def newton4 (m0 : Nat) : Nat :=
  NewtonSeed.iter m0 3
def newton8 (m0 : Nat) : Nat :=
  Model.newtonStep m0 (Model.newtonStep m0 (Model.newtonStep m0 (newton4 m0)))
theorem newton8_eq (m0 : Nat) (hodd : m0 % 2 = 1) :
    newton8 m0 = Model.newtonIter m0 8 := NewtonSeed.six_eq_old hodd
theorem writeBytes_overwrite (mem a b : ByteArray) (start : Nat) (hsz : a.size = b.size) :
    MachineState.writeBytes (MachineState.writeBytes mem a start) b start =
      MachineState.writeBytes mem b start := by
  apply ByteArray.ext_getElem
  · simp only [MachineState.writeBytes_size, hsz]
    split_ifs <;> omega
  · intro i h1 h2
    rw [← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ h1,
      ← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ h2,
      MachineState.writeBytes_getElem?_getD, MachineState.writeBytes_getElem?_getD,
      MachineState.writeBytes_getElem?_getD, hsz]
    split <;> rfl
def mstoreAt (mem : ByteArray) (addr value : Nat) : ByteArray :=
  MachineState.writeBytes mem (Data.Bytes.natToBytesPadded value 32) addr
def varsMem (mem : ByteArray) (input : ByteArray) : ByteArray :=
  mstoreAt (mstoreAt (mstoreAt (mstoreAt mem 2656 (96 + baseSize input))
    2688 (s32 input)) 2752 (s32 input - 32))
    2784 (2080 + s32 input)
def modulusMem (mem : ByteArray) (input : ByteArray) : ByteArray :=
  MachineState.writeBytes
    (MachineState.writeBytes (varsMem mem input)
      (MachineState.readPadded input input.size (s32 input)) 0)
    (MachineState.readPadded input (modOffset input) (modulusSize input))
    (s32 input - modulusSize input)
def setupMem (mem : ByteArray) (input : ByteArray) (_m0 : Nat) : ByteArray :=
  modulusMem mem input
def awNext (w off sz : Nat) : Nat :=
  MachineState.activeWordsAfter (w % 2 ^ 256) off sz
theorem activeWordsAfter_max (X off n : Nat) (hn : n ≠ 0) :
    MachineState.activeWordsAfter X off n = max X ((off + n - 1) / 32 + 1) := by
  unfold MachineState.activeWordsAfter
  rw [if_neg hn]
theorem activeWords_refill (X n : Nat) (hX : X < 2 ^ 256) (hn : n < 2 ^ 256) :
    MachineState.activeWordsAfter
        (MachineState.activeWordsAfter X 0 n % 2 ^ 256) 0 n % 2 ^ 256 =
      MachineState.activeWordsAfter X 0 n % 2 ^ 256 := by
  by_cases hz : n = 0
  · simp [MachineState.activeWordsAfter, hz]
  · have hd : (0 + n - 1) / 32 ≤ 0 + n - 1 := Nat.div_le_self _ _
    have hk : (0 + n - 1) / 32 + 1 < 2 ^ 256 := by omega
    have hmax : max X ((0 + n - 1) / 32 + 1) < 2 ^ 256 := Nat.max_lt.mpr ⟨hX, hk⟩
    rw [activeWordsAfter_max X 0 n hz, Nat.mod_eq_of_lt hmax,
      activeWordsAfter_max _ 0 n hz, Nat.max_assoc, Nat.max_self,
      Nat.mod_eq_of_lt hmax]
theorem activeWords_refill_raw (X n : Nat) (hX : X < 2 ^ 256) (hn : n < 2 ^ 256) :
    MachineState.activeWordsAfter (MachineState.activeWordsAfter X 0 n % 2 ^ 256) 0 n =
      MachineState.activeWordsAfter X 0 n := by
  by_cases hz : n = 0
  · simp [MachineState.activeWordsAfter, hz]
    exact lt_of_lt_of_eq hX (by norm_num)
  · have hd : (0 + n - 1) / 32 ≤ 0 + n - 1 := Nat.div_le_self _ _
    have hk : (0 + n - 1) / 32 + 1 < 2 ^ 256 := by omega
    have hmax : max X ((0 + n - 1) / 32 + 1) < 2 ^ 256 := Nat.max_lt.mpr ⟨hX, hk⟩
    rw [activeWordsAfter_max X 0 n hz, Nat.mod_eq_of_lt hmax,
      activeWordsAfter_max _ 0 n hz, Nat.max_assoc, Nat.max_self]
def setupWords (w : UInt256) (input : ByteArray) : UInt256 :=
  UInt256.ofNat (awNext (awNext (awNext (awNext (awNext
    (MachineState.activeWordsAfter w.toNat 2656 32) 2688 32) 2752 32)
    2784 32) 0 (s32 input)) (s32 input - modulusSize input) (modulusSize input))
def setupPathA :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 443 (.Dup ⟨3,by decide⟩),
   pushAt 444 1 96,
   opAt 445 .ADD,
   pushAt 446 2 2656,
   opAt 447 .MSTORE,
   opAt 448 (.Dup ⟨1,by decide⟩),
   opAt 449 .MSIZE,
   opAt 450 .MSTORE,
   pushAt 451 1 32,
   opAt 452 (.Dup ⟨2,by decide⟩),
   opAt 453 .SUB,
   pushAt 454 2 2752,
   opAt 455 .MSTORE,
   opAt 456 (.Dup ⟨1,by decide⟩),
   pushAt 457 2 2080,
   opAt 458 .ADD,
   opAt 459 .MSIZE,
   opAt 460 .MSTORE,
   opAt 461 (.Dup ⟨5,by decide⟩),
   opAt 462 (.Dup ⟨1,by decide⟩),
   pushAt 463 0 0,
   opAt 464 .CALLDATACOPY,
   opAt 465 .POP,
   pushAt 466 2 2349,
   opAt 467 .JUMP]
def setupExitState (s : State) (input : ByteArray) (m0 : Nat) : State :=
  { s with pc := UInt256.ofNat 2349
           stack := outerStack input
           memory := setupMem s.memory input m0
           activeWords := setupWords s.activeWords input }
private theorem jumpDest3296 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2349 = true :=
  CycleSubmission.Global.Binding.jumpDest 1853 (by rfl)
namespace MsizeSetup
open Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleKernel
set_option linter.unusedSimpArgs false
def prefixWords (w : UInt256) : UInt256 :=
  UInt256.ofNat (awNext (awNext (MachineState.activeWordsAfter w.toNat 2656 32) 2688 32) 2752 32)

theorem prefixWords_eq (w : UInt256) (hw : w.toNat ≤ 84) :
    prefixWords w = UInt256.ofNat 87 := by
  have hb : 87 < (2 : Nat)^256 := by decide
  simp only [prefixWords, awNext, activeWordsAfter_max _ _ 32 (by decide)]
  congr 1
  omega

theorem prefixMsize_eq (w : UInt256) (hw : w.toNat ≤ 84) :
    UInt256.ofNat (32 * (prefixWords w).toNat) = UInt256.ofNat 2784 := by
  rw [prefixWords_eq w hw]
  decide
def headWords (w : UInt256) : UInt256 :=
  UInt256.ofNat (MachineState.activeWordsAfter w.toNat 2656 32)

theorem headWords_eq (w : UInt256) (hw : w.toNat ≤ 84) :
    headWords w = UInt256.ofNat 84 := by
  have hb : 84 < (2 : Nat)^256 := by decide
  simp only [headWords, activeWordsAfter_max _ _ 32 (by decide)]
  congr 1
  omega

def program80 : List Instr :=
  [.op (.Dup dA3),
   .push 1 96,
   .op .ADD,
   .push 2 2656,
   .op .MSTORE,
   .op (.Dup dA1),
   .op .MSIZE,
   .op .MSTORE,
   .push 1 32,
   .op (.Dup dA2),
   .op .SUB,
   .push 2 2752,
   .op .MSTORE,
   .op (.Dup dA1),
   .push 2 2080,
   .op .ADD,
   .op .MSIZE,
   .op .MSTORE,
   .op (.Dup dA5),
   .op (.Dup dA1),
   .push 0 0,
   .op .CALLDATACOPY,
   .op .POP,
   .push 2 2349,
   .op .JUMP]

def headProgram : List Instr := program80.take 6

def midProgram : List Instr := (program80.drop 7).take 9

def prefixMemory (mem : ByteArray) (input : ByteArray) : ByteArray :=
  mstoreAt (mstoreAt (mstoreAt mem 2656 (96 + baseSize input))
    2688 (s32 input)) 2752 (s32 input - 32)

def headState (s : State) (input : ByteArray) : State :=
  { s with pc := UInt256.ofNat 639
           memory := mstoreAt s.memory 2656 (96 + baseSize input)
           activeWords := headWords s.activeWords
           stack := UInt256.ofNat (s32 input) :: UInt256.ofNat (modOffset input) :: outerStack input }

def sized1State (s : State) (input : ByteArray) : State :=
  { (headState s input) with
    pc := UInt256.ofNat 640
    stack := UInt256.ofNat 2688 :: (headState s input).stack }

def prefixState (s : State) (input : ByteArray) : State :=
  { s with pc := UInt256.ofNat 654
           memory := prefixMemory s.memory input
           activeWords := prefixWords s.activeWords
           stack := UInt256.ofNat (2080 + s32 input) :: UInt256.ofNat (modOffset input) :: outerStack input }

theorem run_head (s : State) (input : ByteArray)
    (hb : baseSize input ≤ 1024) (he : exponentSize input ≤ 1024)
    (hm : modulusSize input ≤ 1024) (h32 : 32 < modulusSize input) :
    runInstructions headProgram (setupEntryState s input) = some (headState s input) := by
  have hn2 := limbs_ge_two input h32
  have hS := s32_le_1024 input hm
  have hmodS := mod_word_self (s32_lt input hm)
  have hmodn := mod_word_self (limbs_lt input hm)
  have hmodb := mod_word_self (show 96 + baseSize input < 2 ^ 256 by omega)
  have hmodmoff := mod_word_self (modOffset_lt input hb he)
  simp [headProgram, program80, headState, setupEntryState, outerStack,
    runInstructions, Challenge.EvmProof.Stepper.runInstr,
    mstoreAt, headWords, State.activeWordsAfterUInt256,
    hmodS, hmodn, hmodb, hmodmoff, hn2,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod, Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.add_assoc, List.exchange]

theorem run_msize1 (s : State) (input : ByteArray) (hw : s.activeWords.toNat ≤ 84) :
    runInstructionsX [.op .MSIZE] (headState s input) = some (sized1State s input) := by
  simp [runInstructionsX, runInstrX, headState, sized1State, outerStack,
    headWords_eq s.activeWords hw, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod]

theorem run_mid (s : State) (input : ByteArray)
    (hb : baseSize input ≤ 1024) (he : exponentSize input ≤ 1024)
    (hm : modulusSize input ≤ 1024) (h32 : 32 < modulusSize input) :
    runInstructions midProgram (sized1State s input) = some (prefixState s input) := by
  have hn2 := limbs_ge_two input h32
  have hS := s32_le_1024 input hm
  have hSge : 32 ≤ s32 input := by unfold s32; omega
  have hsub32 : UInt256.ofNat (s32 input) - UInt256.ofNat 32 =
      UInt256.ofNat (s32 input - 32) :=
    Challenge.EvmProof.Word.ofNat_sub_ofNat hSge (by omega)
  have hmodS := mod_word_self (s32_lt input hm)
  have hmodn := mod_word_self (limbs_lt input hm)
  have hmodb := mod_word_self (show 96 + baseSize input < 2 ^ 256 by omega)
  have hmodml := mod_word_self (show s32 input - 32 < 2 ^ 256 by omega)
  have hmodtl := mod_word_self (show 2080 + s32 input < 2 ^ 256 by omega)
  have hmodmoff := mod_word_self (modOffset_lt input hb he)
  simp [midProgram, program80, sized1State, headState, prefixState, prefixMemory,
    runInstructions, Challenge.EvmProof.Stepper.runInstr, outerStack,
    mstoreAt, headWords, prefixWords, awNext, State.activeWordsAfterUInt256, hsub32,
    hmodS, hmodn, hmodb, hmodml, hmodtl, hmodmoff,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod, Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.add_assoc, List.exchange]


def sizedState (s : State) (input : ByteArray) : State :=
  { (prefixState s input) with
    pc := UInt256.ofNat 655
    stack := UInt256.ofNat 2784 :: (prefixState s input).stack }

theorem run_msize (s : State) (input : ByteArray) (hw : s.activeWords.toNat ≤ 84) :
    runInstructionsX [.op .MSIZE] (prefixState s input) = some (sizedState s input) := by
  simp [runInstructionsX, runInstrX, prefixState, sizedState, outerStack,
    prefixWords_eq s.activeWords hw, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod]

theorem setupWords_bounded (w : UInt256) (input : ByteArray) (hw : w.toNat ≤ 84)
    (hm : modulusSize input ≤ 1024) (h32 : 32 < modulusSize input) :
    setupWords w input = UInt256.ofNat 88 := by
  have hn2 := limbs_ge_two input h32
  have hS := s32_le_1024 input hm
  have hSge : 32 ≤ s32 input := by unfold s32; omega
  have hms := modulusSize_le_s32 input
  have hSne : s32 input ≠ 0 := by omega
  have hmsne : modulusSize input ≠ 0 := by omega
  simp only [setupWords, awNext,
    activeWordsAfter_max _ _ 32 (by norm_num),
    activeWordsAfter_max _ _ (s32 input) hSne,
    activeWordsAfter_max _ _ (modulusSize input) hmsne,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  congr 1
  omega

theorem copyWords88 (n : Nat) (hn : n ≤ 1024) :
    MachineState.activeWordsAfter 88 0 n = 88 := by
  by_cases hz : n = 0
  · simp [MachineState.activeWordsAfter, hz]
  · simp only [MachineState.activeWordsAfter, if_neg hz, Nat.zero_add]
    exact Nat.max_eq_left (by omega)



def restProgram : List Instr := program80.drop 17
private theorem jumpDest2390 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2349 = true :=
  CycleSubmission.Global.Binding.jumpDest 1853 (by rfl)

theorem run_rest (s : State) (input : ByteArray) (m0 : Nat)
    (hdata : s.executionEnv.calldata = input)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hb : baseSize input ≤ 1024) (he : exponentSize input ≤ 1024)
    (hm : modulusSize input ≤ 1024) (h32 : 32 < modulusSize input)
    (hwidth : modulusSize input % 128 = 0) (hw : s.activeWords.toNat ≤ 84) :
    runInstructions restProgram (sizedState s input) = some (setupExitState s input m0) := by
  have hs32 : s32 input = modulusSize input := s32_eq_of_mask input hwidth
  have hpad : s32 input - modulusSize input = 0 := by omega
  have hmem : ∀ mem : ByteArray,
      MachineState.writeBytes (MachineState.writeBytes mem
            (MachineState.readPadded input input.size (s32 input)) 0)
          (MachineState.readPadded input (modOffset input) (modulusSize input))
          (s32 input - modulusSize input) =
        MachineState.writeBytes mem
          (MachineState.readPadded input (modOffset input) (modulusSize input)) 0 := by
    intro mem
    rw [hpad]
    exact writeBytes_overwrite mem _ _ 0 (by simp [hs32])
  have hmodtl := mod_word_self (show 2080 + s32 input < 2^256 by
    have hS := s32_le_1024 input hm; omega)
  have hmodms := mod_word_self (show modulusSize input < 2^256 by omega)
  have hmodmoff := mod_word_self (modOffset_lt input hb he)
  have hStore : MachineState.activeWordsAfter 87 2784 32 = 88 := by decide
  simp [restProgram, program80, sizedState, prefixState, prefixMemory,
    runInstructions, Challenge.EvmProof.Stepper.runInstr, setupExitState, outerStack,
    setupMem, modulusMem, varsMem, mstoreAt, prefixWords_eq s.activeWords hw,
    setupWords_bounded s.activeWords input hw hm h32, hmem, hdata, hcode,
    State.activeWordsAfterUInt256, hStore, copyWords88 (modulusSize input) hm,
    push0_word, hmodtl, hmodms, hmodmoff, jumpDest2390,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod, Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.add_assoc, List.exchange]

theorem run_setup80 (s : State) (input : ByteArray) (m0 : Nat)
    (hdata : s.executionEnv.calldata = input)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hb : baseSize input ≤ 1024) (he : exponentSize input ≤ 1024)
    (hm : modulusSize input ≤ 1024) (h32 : 32 < modulusSize input)
    (hwidth : modulusSize input % 128 = 0) (hw : s.activeWords.toNat ≤ 84) :
    runInstructionsX program80 (setupEntryState s input) = some (setupExitState s input m0) := by
  have hh : runInstructionsX headProgram (setupEntryState s input) = some (headState s input) := by
    rw [runInstructionsX_eq headProgram (by decide)]
    exact run_head s input hb he hm h32
  have hz1 := run_msize1 s input hw
  have hmid : runInstructionsX midProgram (sized1State s input) = some (prefixState s input) := by
    rw [runInstructionsX_eq midProgram (by decide)]
    exact run_mid s input hb he hm h32
  have hz := run_msize s input hw
  have hr : runInstructionsX restProgram (sizedState s input) = some (setupExitState s input m0) := by
    rw [runInstructionsX_eq restProgram (by decide)]
    exact run_rest s input m0 hdata hcode hb he hm h32 hwidth hw
  change runInstructionsX ((((headProgram ++ [.op .MSIZE]) ++ midProgram) ++ [.op .MSIZE]) ++
    restProgram) _ = _
  exact runInstructionsX_append_some _ _ _ _ _
    (runInstructionsX_append_some _ _ _ _ _
      (runInstructionsX_append_some _ _ _ _ _
        (runInstructionsX_append_some _ _ _ _ _ hh hz1) hmid) hz) hr

end MsizeSetup

def setupBlock80 : WindowTwentyOneBinding.Block Artifact.artifact .Osaka 630 MsizeSetup.program80 :=
  WindowTwentyOneSlice.block Artifact.wellFormed 443 25 630 MsizeSetup.program80
    (by change 443 + 25 ≤ Artifact.instructions.length; rw [Artifact.instructionCount]; decide)
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

theorem run_setupA (s : State) (input : ByteArray) (m0 : Nat)
    (hdata : s.executionEnv.calldata = input)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (_hrun : s.halt = .Running) (_hsize : input.size < 2^256)
    (hb : baseSize input ≤ 1024) (he : exponentSize input ≤ 1024)
    (hm : modulusSize input ≤ 1024) (h32 : 32 < modulusSize input)
    (hwidth : modulusSize input % 128 = 0) (hupper : s.activeWords.toNat ≤ 84) :
    runInstructionsX MsizeSetup.program80 (setupEntryState s input) = some (setupExitState s input m0) :=
  MsizeSetup.run_setup80 s input m0 hdata hcode hb he hm h32 hwidth hupper

theorem byteFrom_eq (bs : ByteArray) (i : Nat) :
    YulSemantics.EVM.byteFrom bs.toList i = bs[i]?.getD 0 := by
  unfold YulSemantics.EVM.byteFrom
  rw [YulEvmCompiler.ByteArray.toList_eq_data, List.getD_eq_getElem?_getD,
    Array.getElem?_toList]
  rfl
set_option linter.unusedSimpArgs false in
theorem bytesToNatPadded_eq_zero (bs : ByteArray) (off : Nat) : ∀ n : Nat,
    (∀ i, i < n → bs[off + i]?.getD 0 = 0) →
    Precompile.bytesToNatPadded bs off n = 0
  | 0, _ => Challenge.EvmProof.Bytes.bytesToNatPadded_zero_width bs off
  | n + 1, h => by
      have hb : YulSemantics.EVM.byteFrom bs.toList (off + n) = 0 := by
        rw [byteFrom_eq]
        exact h n (by omega)
      have hih := bytesToNatPadded_eq_zero bs off n (fun i hi => h i (by omega))
      simp [Challenge.EvmProof.Bytes.bytesToNatPadded_succ, hih, hb]
theorem readWord_empty (target : Nat) :
    MachineState.readWord ByteArray.empty target = UInt256.ofNat 0 := by
  unfold MachineState.readWord
  congr 1
  exact bytesToNatPadded_eq_zero ByteArray.empty target 32
    (fun i _ => Challenge.EvmProof.Memory.getElem?_getD_eq_zero_of_size_le _ _ (by simp))
theorem readPadded_beyond_getElem (bs : ByteArray) (start n i : Nat)
    (hstart : bs.size ≤ start) :
    (MachineState.readPadded bs start n)[i]?.getD 0 = 0 := by
  rw [Challenge.EvmProof.Memory.readPadded_getElem?_getD]
  split
  · exact Challenge.EvmProof.Memory.getElem?_getD_eq_zero_of_size_le bs (start + i)
      (by omega)
  · rfl
theorem readWord_mstoreAt_ne (mem : ByteArray) (addr value target : Nat)
    (h : target + 32 ≤ addr ∨ addr + 32 ≤ target) :
    MachineState.readWord (mstoreAt mem addr value) target =
      MachineState.readWord mem target := by
  unfold mstoreAt
  apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
  rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  exact h
theorem readWord_mstoreAt_self (mem : ByteArray) (addr value : Nat)
    (hv : value < 2 ^ 256) :
    MachineState.readWord (mstoreAt mem addr value) addr = UInt256.ofNat value := by
  unfold mstoreAt
  exact Challenge.EvmProof.Memory.readWord_writeBytes_of_lt mem addr value
    (by rw [pow_256_32]; exact hv)
theorem readWord_writeBytes_ne (mem src : ByteArray) (start target : Nat)
    (h : target + 32 ≤ start ∨ start + src.size ≤ target) :
    MachineState.readWord (MachineState.writeBytes mem src start) target =
      MachineState.readWord mem target :=
  Challenge.EvmProof.Memory.readWord_writeBytes_disjoint mem src target start h
theorem readWord_setupMem_var (mem : ByteArray) (input : ByteArray) (m0 target : Nat)
    (hm : modulusSize input ≤ 1024) (hlo : 2688 ≤ target) :
    MachineState.readWord (setupMem mem input m0) target =
      MachineState.readWord (varsMem mem input) target := by
  have hS := s32_le_1024 input hm
  have hms := modulusSize_le_s32 input
  unfold setupMem modulusMem
  rw [readWord_writeBytes_ne _ _ _ _ (Or.inr (by rw [Challenge.EvmProof.Memory.readPadded_size]; omega)),
    readWord_writeBytes_ne _ _ _ _ (Or.inr (by rw [Challenge.EvmProof.Memory.readPadded_size]; omega))]
theorem readWord_V_S32 (mem : ByteArray) (input : ByteArray) (m0 : Nat)
    (hm : modulusSize input ≤ 1024) :
    MachineState.readWord (setupMem mem input m0) 2688 =
      UInt256.ofNat (s32 input) := by
  rw [readWord_setupMem_var mem input m0 2688 hm (by omega)]
  unfold varsMem
  rw [readWord_mstoreAt_ne _ _ _ _ (Or.inl (by omega)),
    readWord_mstoreAt_ne _ _ _ _ (Or.inl (by omega)),
    readWord_mstoreAt_self _ _ _ (s32_lt input hm)]
theorem readWord_V_EOFF (mem : ByteArray) (input : ByteArray) (m0 : Nat)
    (hm : modulusSize input ≤ 1024) (hb : baseSize input ≤ 1024) :
    MachineState.readWord (setupMem mem input m0) 2656 =
      UInt256.ofNat (96 + baseSize input) := by
  have hS := s32_le_1024 input hm
  have hms := modulusSize_le_s32 input
  unfold setupMem modulusMem varsMem
  rw [readWord_writeBytes_ne _ _ _ _
      (Or.inr (by rw [Challenge.EvmProof.Memory.readPadded_size]; omega)),
    readWord_writeBytes_ne _ _ _ _
      (Or.inr (by rw [Challenge.EvmProof.Memory.readPadded_size]; omega)),
    readWord_mstoreAt_ne _ _ _ _ (Or.inl (by omega)),
    readWord_mstoreAt_ne _ _ _ _ (Or.inl (by omega)),
    readWord_mstoreAt_ne _ _ _ _ (Or.inl (by omega)),
    readWord_mstoreAt_self _ _ _ (by omega)]
theorem readWord_V_ML (mem : ByteArray) (input : ByteArray) (m0 : Nat)
    (hm : modulusSize input ≤ 1024) :
    MachineState.readWord (setupMem mem input m0) 2752 =
      UInt256.ofNat (s32 input - 32) := by
  have hS := s32_le_1024 input hm
  rw [readWord_setupMem_var mem input m0 2752 hm (by omega)]
  unfold varsMem
  rw [readWord_mstoreAt_ne _ _ _ _ (Or.inl (by omega)),
    readWord_mstoreAt_self _ _ _ (by omega)]
theorem readWord_V_TL (mem : ByteArray) (input : ByteArray) (m0 : Nat)
    (hm : modulusSize input ≤ 1024) :
    MachineState.readWord (setupMem mem input m0) 2784 =
      UInt256.ofNat (2080 + s32 input) := by
  have hS := s32_le_1024 input hm
  rw [readWord_setupMem_var mem input m0 2784 hm (by omega)]
  unfold varsMem
  rw [readWord_mstoreAt_self _ _ _ (by omega)]
theorem fastRepresents_bytes (bs : ByteArray) (ptr count : Nat) :
    Model.FastRepresents bs ptr count
      (Precompile.bytesToNatPadded bs ptr (32 * count)) := by
  apply Model.fastRepresents_of_limbs
  · rw [Limbs.pow_radix]
    exact Challenge.EvmProof.Bytes.bytesToNatPadded_lt_pow _ _ _
  · intro k hk
    rw [Challenge.EvmProof.Bytes.readWord_toNat]
    have hrk : Limbs.radix ^ k = 256 ^ (32 * k) := Limbs.pow_radix k
    have hpos : 0 < Limbs.radix ^ k := Nat.pow_pos Limbs.radix_pos
    have hBlt : Precompile.bytesToNatPadded bs (ptr + 32 * (count - 1 - k)) 32
        < Limbs.radix := by
      rw [Limbs.radix_eq]
      exact Challenge.EvmProof.Bytes.bytesToNatPadded_lt_pow _ _ _
    have hClt : Precompile.bytesToNatPadded bs
        (ptr + 32 * (count - 1 - k) + 32) (32 * k) < Limbs.radix ^ k := by
      rw [hrk]
      exact Challenge.EvmProof.Bytes.bytesToNatPadded_lt_pow _ _ _
    have hA := Challenge.EvmProof.Bytes.bytesToNatPadded_add bs ptr
      (32 * (count - 1 - k)) (32 + 32 * k)
    rw [show 32 * (count - 1 - k) + (32 + 32 * k) = 32 * count from by omega] at hA
    have hB := Challenge.EvmProof.Bytes.bytesToNatPadded_add bs
      (ptr + 32 * (count - 1 - k)) 32 (32 * k)
    have hpow : (256 : Nat) ^ (32 + 32 * k) = Limbs.radix ^ k * Limbs.radix := by
      rw [hrk, Limbs.radix_eq, ← pow_add]
      congr 1
      omega
    have hring : ∀ a b c : Nat,
        a * (Limbs.radix ^ k * Limbs.radix) + (b * Limbs.radix ^ k + c)
          = Limbs.radix ^ k * (a * Limbs.radix + b) + c := by
      intro a b c
      ring
    rw [hA, hB, hpow, ← hrk, hring, Nat.mul_add_div hpos,
      Nat.div_eq_of_lt hClt, Nat.add_zero, Nat.mul_add_mod',
      Nat.mod_eq_of_lt hBlt]
theorem modulusMem_zero_region (mem : ByteArray) (input : ByteArray) (i : Nat)
    (hi : i < s32 input - modulusSize input) :
    (modulusMem mem input)[0 + i]?.getD 0 = 0 := by
  have hms := modulusSize_le_s32 input
  unfold modulusMem
  rw [MachineState.writeBytes_getElem?_getD,
    if_neg (by simp only [Challenge.EvmProof.Memory.readPadded_size]; omega),
    MachineState.writeBytes_getElem?_getD,
    if_pos (by simp only [Challenge.EvmProof.Memory.readPadded_size]; omega)]
  exact readPadded_beyond_getElem input input.size (s32 input) _ le_rfl
theorem modulusMem_value (mem : ByteArray) (input : ByteArray) :
    Precompile.bytesToNatPadded (modulusMem mem input) 0 (s32 input) =
      modulus input := by
  have hms := modulusSize_le_s32 input
  have hsplit := Challenge.EvmProof.Bytes.bytesToNatPadded_add (modulusMem mem input) 0
    (s32 input - modulusSize input) (modulusSize input)
  rw [show s32 input - modulusSize input + modulusSize input = s32 input from by omega]
    at hsplit
  have hhigh : Precompile.bytesToNatPadded (modulusMem mem input) 0
      (s32 input - modulusSize input) = 0 :=
    bytesToNatPadded_eq_zero _ _ _ (fun i hi => modulusMem_zero_region mem input i hi)
  have hsize : (MachineState.readPadded input (modOffset input)
      (modulusSize input)).size = modulusSize input :=
    Challenge.EvmProof.Memory.readPadded_size _ _ _
  have hsame := Challenge.EvmProof.Memory.readPadded_writeBytes_same
    (MachineState.writeBytes (varsMem mem input)
      (MachineState.readPadded input input.size (s32 input)) 0)
    (MachineState.readPadded input (modOffset input) (modulusSize input))
    (s32 input - modulusSize input)
  rw [hsize] at hsame
  have hlow : Precompile.bytesToNatPadded (modulusMem mem input)
      (0 + (s32 input - modulusSize input)) (modulusSize input) = modulus input := by
    rw [Nat.zero_add]
    unfold modulusMem modulus Precompile.bytesToNatPadded
    rw [hsame]
  rw [hsplit, hhigh, hlow, Nat.zero_mul, Nat.zero_add]
theorem modulusMem_represents (mem : ByteArray) (input : ByteArray) :
    Model.FastRepresents (modulusMem mem input) 0 (limbs input) (modulus input) := by
  have h := fastRepresents_bytes (modulusMem mem input) 0 (limbs input)
  rw [show 32 * limbs input = s32 input from rfl, modulusMem_value mem input] at h
  exact h
theorem setupMem_represents (mem : ByteArray) (input : ByteArray) (m0 : Nat)
    (hm : modulusSize input ≤ 1024) :
    Model.FastRepresents (setupMem mem input m0) 0 (limbs input) (modulus input) := by
  have hS := s32_le_1024 input hm
  have h32n : 32 * limbs input = s32 input := rfl
  unfold setupMem
  exact modulusMem_represents mem input
theorem lowLimb_eq (mem : ByteArray) (input : ByteArray) (h32 : 32 < modulusSize input) :
    (MachineState.readWord (modulusMem mem input) (s32 input - 32)).toNat =
      modulus input % Limbs.radix := by
  have hn2 := limbs_ge_two input h32
  have h := Model.readWord_of_fastRepresents (modulusMem_represents mem input)
    (j := limbs input - 1) (by omega)
  rw [show (0 : Nat) + 32 * (limbs input - 1) = s32 input - 32 from by
    unfold s32; omega] at h
  rw [h, show limbs input - 1 - (limbs input - 1) = 0 from by omega, pow_zero,
    Nat.div_one]
theorem readWord_setupMem_high (input : ByteArray) (m0 target : Nat)
    (hm : modulusSize input ≤ 1024) (hlo : 2048 ≤ target) (hhi : target + 32 ≤ 2656) :
    MachineState.readWord (setupMem ByteArray.empty input m0) target =
      UInt256.ofNat 0 := by
  have hS := s32_le_1024 input hm
  have hms := modulusSize_le_s32 input
  unfold setupMem modulusMem varsMem
  rw [readWord_writeBytes_ne _ _ _ _
      (Or.inr (by rw [Challenge.EvmProof.Memory.readPadded_size]; omega)),
    readWord_writeBytes_ne _ _ _ _
      (Or.inr (by rw [Challenge.EvmProof.Memory.readPadded_size]; omega)),
    readWord_mstoreAt_ne _ _ _ _ (Or.inl (by omega)),
    readWord_mstoreAt_ne _ _ _ _ (Or.inl (by omega)),
    readWord_mstoreAt_ne _ _ _ _ (Or.inl (by omega)),
    readWord_mstoreAt_ne _ _ _ _ (Or.inl (by omega)),
    readWord_empty]


theorem setupMem_R1_zero (input : ByteArray) (m0 : Nat)
    (hm : modulusSize input ≤ 256) (_h32 : 32 < modulusSize input) :
    Model.FastRepresents (setupMem ByteArray.empty input m0) 2048 (limbs input) 0 := by
  have hn32 := limbs_le_8 input hm
  rw [Model.fastRepresents_zero_iff]
  intro j hj
  rw [readWord_setupMem_high input m0 (2048 + 32 * j) (by omega) (by omega) (by omega),
    toNat_ofNat_self (show (0 : Nat) < 2 ^ 256 by norm_num)]
theorem minv_correct (input : ByteArray) (m0 : Nat)
    (hodd : modulus input % 2 = 1) (hm0 : m0 = modulus input % Limbs.radix) :
    (m0 * negWord (newton8 m0) + 1) % Limbs.radix = 0 := by
  have hodd0 : m0 % 2 = 1 := by rw [hm0]; exact Model.low_limb_odd hodd
  have height : m0 * Model.newtonIter m0 8 % Limbs.radix = 1 :=
    Model.newtonIter_eight hodd0
  have hlt : Model.newtonIter m0 8 < Limbs.radix := by
    rw [show (8 : Nat) = 7 + 1 from rfl, Model.newtonIter_succ]
    exact Model.newtonStep_lt _ _
  have hpos : 0 < Model.newtonIter m0 8 := by
    rcases Nat.eq_zero_or_pos (Model.newtonIter m0 8) with hz | hp
    · rw [hz, Nat.mul_zero, Nat.zero_mod] at height
      omega
    · exact hp
  have hm0lt : m0 < Limbs.radix := by
    rw [hm0]
    exact Nat.mod_lt _ Limbs.radix_pos
  have hneg : negWord (newton8 m0) = Limbs.radix - Model.newtonIter m0 8 := by
    unfold negWord
    rw [newton8_eq m0 hodd0, Nat.mod_eq_of_lt hlt]
    exact Nat.mod_eq_of_lt (by omega)
  rw [hneg]
  refine Model.minv_spec ?_ (le_of_lt hlt)
  rw [Nat.mod_eq_of_lt hm0lt]
  exact height
def gasSteps_setup (s : State) (input : ByteArray) (m0 : Nat)
    (hdata : s.executionEnv.calldata = input)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hsize : input.size < 2 ^ 256)
    (hb : baseSize input ≤ 1024) (he : exponentSize input ≤ 1024)
    (hm : modulusSize input ≤ 1024) (h32 : 32 < modulusSize input)
    (hwidth : modulusSize input % 128 = 0) (hupper : s.activeWords.toNat ≤ 84) :
    Challenge.EvmProof.GasSteps (setupEntryState s input) (setupExitState s input m0) :=
  WindowTwentyOneMsize.Block.stepsX setupBlock80
    (s := setupEntryState s input)
    ⟨by change Artifact.bytecode.size < 2^256; rw [Artifact.bytecodeSize]; decide,
      hcode, hfork, hrun, hnp⟩ rfl
    (run_setupA s input m0 hdata hcode hrun hsize hb he hm h32 hwidth hupper)
def gasSteps_fastPath_of (s : State) (input : ByteArray) (m0 : Nat)
    (hdata : s.executionEnv.calldata = input)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hsize : input.size < 2 ^ 256)
    (hpath : FastPath input) (hupper : s.activeWords.toNat ≤ 84) :
    Challenge.EvmProof.GasSteps (entryState s) (setupExitState s input m0) :=
  (gasSteps_entry_pass s input hdata hcode hfork hrun hnp hpath.1 hpath.2.1.2.2).trans
    ((gasSteps_sizeCheck_pass s input hdata hcode hfork hrun hnp
        hpath.2.1.1 hpath.2.1.2.1 (fastPath_modulus_le_1024 input hpath)).trans
      ((gasSteps_check_pass s input hdata hcode hfork hrun hnp
          hpath.2.1.1 hpath.2.1.2.1 (fastPath_modulus_le_1024 input hpath) hpath.1
          (fastPath_topBit input hpath) (fastPath_odd input hpath) (fastPath_width input hpath)
          (fastPath_nprime input hpath)).trans
          (gasSteps_setup s input m0 hdata hcode hfork hrun hnp hsize
            hpath.2.1.1 hpath.2.1.2.1 (fastPath_modulus_le_1024 input hpath) hpath.1
            (fastPath_width input hpath) hupper)))
def lowLimb (input : ByteArray) : Nat :=
  (MachineState.readWord (modulusMem ByteArray.empty input) (s32 input - 32)).toNat
def minvValue (input : ByteArray) : Nat := negWord (newton8 (lowLimb input))
def fastSetupState (input : ByteArray) : State :=
  setupExitState (initialState CycleSubmission.Artifact.bytecode input 0) input (lowLimb input)
def fastSetupMemory (input : ByteArray) : ByteArray :=
  setupMem ByteArray.empty input (lowLimb input)
theorem fastSetupState_memory (input : ByteArray) :
    (fastSetupState input).memory = fastSetupMemory input := rfl
theorem fastSetupState_pc (input : ByteArray) :
    (fastSetupState input).pc = UInt256.ofNat 2349 := rfl
theorem fastSetupState_stack (input : ByteArray) :
    (fastSetupState input).stack = outerStack input := rfl
def gasSteps_fastSetup (input : ByteArray) (hsize : input.size < 2 ^ 256)
    (hpath : FastPath input) :
    Challenge.EvmProof.GasSteps (Main.trampolineState input 564)
      (fastSetupState input) :=
  Challenge.EvmProof.GasSteps.cast
    (gasSteps_fastPath_of (initialState CycleSubmission.Artifact.bytecode input 0) input
      (lowLimb input) rfl rfl rfl rfl deployAddress_not_precompile hsize hpath (by change 0 ≤ 84; decide))
    (entryState_initial input) rfl
theorem fastSetup_modulus (input : ByteArray) (hpath : FastPath input) :
    Model.FastRepresents (fastSetupMemory input) 0 (limbs input) (modulus input) :=
  setupMem_represents ByteArray.empty input (lowLimb input) (fastPath_modulus_le_1024 input hpath)
theorem fastSetup_R1_zero (input : ByteArray) (hpath : FastPath input) :
    Model.FastRepresents (fastSetupMemory input) 2048 (limbs input) 0 :=
  setupMem_R1_zero input (lowLimb input) hpath.2.1.2.2 hpath.1
theorem fastSetup_V_S32 (input : ByteArray) (hpath : FastPath input) :
    MachineState.readWord (fastSetupMemory input) 2688 = UInt256.ofNat (s32 input) :=
  readWord_V_S32 ByteArray.empty input (lowLimb input) (fastPath_modulus_le_1024 input hpath)
theorem fastSetup_V_ML (input : ByteArray) (hpath : FastPath input) :
    MachineState.readWord (fastSetupMemory input) 2752 =
      UInt256.ofNat (s32 input - 32) :=
  readWord_V_ML ByteArray.empty input (lowLimb input) (fastPath_modulus_le_1024 input hpath)
theorem fastSetup_V_TL (input : ByteArray) (hpath : FastPath input) :
    MachineState.readWord (fastSetupMemory input) 2784 =
      UInt256.ofNat (2080 + s32 input) :=
  readWord_V_TL ByteArray.empty input (lowLimb input) (fastPath_modulus_le_1024 input hpath)
theorem fastSetup_V_EOFF (input : ByteArray) (hpath : FastPath input) :
    MachineState.readWord (fastSetupMemory input) 2656 =
      UInt256.ofNat (96 + baseSize input) :=
  readWord_V_EOFF ByteArray.empty input (lowLimb input) (fastPath_modulus_le_1024 input hpath) hpath.2.1.1
theorem fastSetup_lowLimb (input : ByteArray) (hpath : FastPath input) :
    lowLimb input = modulus input % Limbs.radix :=
  lowLimb_eq ByteArray.empty input hpath.1
theorem fastSetup_minv (input : ByteArray) (hpath : FastPath input) :
    (lowLimb input * minvValue input + 1) % Limbs.radix = 0 :=
  minv_correct input (lowLimb input) (fastPath_odd input hpath) (fastSetup_lowLimb input hpath)
theorem fastSetup_limbs_ge_two (input : ByteArray) (hpath : FastPath input) :
    2 ≤ limbs input := limbs_ge_two input hpath.1
theorem fastSetup_limbs_le_8 (input : ByteArray) (hpath : FastPath input) :
    limbs input ≤ 8 := limbs_le_8 input hpath.2.1.2.2
theorem fastSetup_s32_le_256 (input : ByteArray) (hpath : FastPath input) :
    s32 input ≤ 256 := s32_le_256 input hpath.2.1.2.2
theorem fastSetup_limbs_le_32 (input : ByteArray) (hpath : FastPath input) :
    limbs input ≤ 32 := limbs_le_32 input (fastPath_modulus_le_1024 input hpath)
theorem fastSetup_s32_eq (input : ByteArray) : s32 input = 32 * limbs input := rfl
theorem fastSetup_modulus_odd (input : ByteArray) (hpath : FastPath input) :
    modulus input % 2 = 1 := (fastPath_odd input hpath)
theorem fastSetup_modulus_bounds (input : ByteArray) (hpath : FastPath input) :
    Limbs.radix ^ (limbs input - 1) ≤ modulus input ∧
      modulus input < Limbs.radix ^ limbs input :=
  ⟨hpath.2.2.1, modulus_lt input⟩
theorem fastSetup_modulus_eq (input : ByteArray) :
    modulus input =
      Precompile.bytesToNatPadded input (96 + baseSize input + exponentSize input)
        (modulusSize input) := rfl
theorem activeWordsAfter_eq (curr off sz : Nat) (hsz : sz ≠ 0) :
    MachineState.activeWordsAfter curr off sz = max curr ((off + sz - 1) / 32 + 1) := by
  unfold MachineState.activeWordsAfter
  rw [if_neg hsz]
theorem setupWords_initial (input : ByteArray) (hm : modulusSize input ≤ 1024)
    (h32 : 32 < modulusSize input) :
    setupWords (UInt256.ofNat 0) input = UInt256.ofNat 88 := by
  have hn2 := limbs_ge_two input h32
  have hS := s32_le_1024 input hm
  have hSge : 32 ≤ s32 input := by unfold s32; omega
  have hms := modulusSize_le_s32 input
  have hSne : s32 input ≠ 0 := by omega
  have hmsne : modulusSize input ≠ 0 := by omega
  simp only [setupWords, awNext,
    activeWordsAfter_eq _ _ 32 (by norm_num),
    activeWordsAfter_eq _ _ (s32 input) hSne,
    activeWordsAfter_eq _ _ (modulusSize input) hmsne,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  congr 1
  omega
theorem fastSetup_activeWords (input : ByteArray) (hpath : FastPath input) :
    (fastSetupState input).activeWords = UInt256.ofNat 88 :=
  setupWords_initial input (fastPath_modulus_le_1024 input hpath) hpath.1
theorem fastSetup_activeWords_ge (input : ByteArray) (hpath : FastPath input) :
    88 ≤ (fastSetupState input).activeWords.toNat := by
  rw [fastSetup_activeWords input hpath,
    toNat_ofNat_self (show (88 : Nat) < 2 ^ 256 by norm_num)]
theorem fastPath_em (input : ByteArray) : FastPath input ∨ ¬ FastPath input :=
  Classical.em _
end CycleSubmission.Global.Fast.Setup

