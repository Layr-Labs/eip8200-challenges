import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedStep
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RawExpressionAC
import Challenge.Ripemd160.Submission.Proofs.Bytecode.GuardInstructionWindow
import Challenge.Ripemd160.Submission.Proofs.Bytecode.TinyGuardLogic
import Challenge.Ripemd160.Submission.Proofs.Bytecode.AbcRecognition
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Execution
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Msize
import Challenge.EvmProof.Memory

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.AbcArm
open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open TinyGuardLogic
abbrev Located := DataStepper.Located Artifact.submissionArtifact .Osaka

@[simp] theorem pc_176 : Artifact.submissionArtifact.instructionPC 3528 = 4905 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_4095 : Artifact.submissionArtifact.instructionPC 3395 = 4629 := by
  exact GuardInstructionWindow.pc 0
@[simp] theorem pc_4096 : Artifact.submissionArtifact.instructionPC 3396 = 4662 := by
  exact GuardInstructionWindow.pc 1
@[simp] theorem pc_4097 : Artifact.submissionArtifact.instructionPC 3397 = 4663 := by
  exact GuardInstructionWindow.pc 2
@[simp] theorem pc_4098 : Artifact.submissionArtifact.instructionPC 3398 = 4664 := by
  exact GuardInstructionWindow.pc 3
@[simp] theorem pc_4099 : Artifact.submissionArtifact.instructionPC 3399 = 4665 := by
  exact GuardInstructionWindow.pc 4
@[simp] theorem pc_4100 : Artifact.submissionArtifact.instructionPC 3400 = 4666 := by
  exact GuardInstructionWindow.pc 5
@[simp] theorem pc_4101 : Artifact.submissionArtifact.instructionPC 3401 = 4667 := by
  exact GuardInstructionWindow.pc 6
@[simp] theorem pc_4102 : Artifact.submissionArtifact.instructionPC 3402 = 4668 := by
  exact GuardInstructionWindow.pc 7
@[simp] theorem pc_4103 : Artifact.submissionArtifact.instructionPC 3403 = 4669 := by
  exact GuardInstructionWindow.pc 8
@[simp] theorem pc_4104 : Artifact.submissionArtifact.instructionPC 3404 = 4672 := by
  exact GuardInstructionWindow.pc 9
@[simp] theorem pc_4105 : Artifact.submissionArtifact.instructionPC 3405 = 4673 := by
  exact GuardInstructionWindow.pc 10
@[simp] theorem pc_4106 : Artifact.submissionArtifact.instructionPC 3406 = 4694 := by
  exact GuardInstructionWindow.pc 11
@[simp] theorem pc_4107 : Artifact.submissionArtifact.instructionPC 3407 = 4695 := by
  exact GuardInstructionWindow.pc 12
@[simp] theorem pc_4108 : Artifact.submissionArtifact.instructionPC 3408 = 4696 := by
  exact GuardInstructionWindow.pc 13
@[simp] theorem pc_4109 : Artifact.submissionArtifact.instructionPC 3409 = 4717 := by
  exact GuardInstructionWindow.pc 14
@[simp] theorem pc_241 : Artifact.submissionArtifact.instructionPC 3410 = 4718 := by
  exact GuardInstructionWindow.pc 15
@[simp] theorem pc_inlineStore : Artifact.submissionArtifact.instructionPC 3411 = 4719 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_inlineMsize : Artifact.submissionArtifact.instructionPC 3412 = 4720 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_inlineZero : Artifact.submissionArtifact.instructionPC 3413 = 4721 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_inlineReturn : Artifact.submissionArtifact.instructionPC 3414 = 4722 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl

def wordMaskNat : Nat :=
  109629802895867119430885776324251105184819939959857484870201727791975914012671

def wordMask : UInt256 := UInt256.ofNat wordMaskNat

def entryDest : Located :=
  ⟨3528, .op .JUMPDEST, by rfl, ⟨by decide, trivial, rfl⟩⟩

def wordPath : List Located :=
  [⟨3395, .push ⟨32, by decide⟩ wordMask, by exact GuardInstructionWindow.get 0, by decide⟩,
   ⟨3396, .op (.Dup ⟨0, by decide⟩), by exact GuardInstructionWindow.get 1, ⟨by decide, trivial, rfl⟩⟩,
   ⟨3397, .push ⟨0, by decide⟩ (UInt256.ofNat 0), by exact GuardInstructionWindow.get 2, by decide⟩,
   ⟨3398, .op .CALLDATALOAD, by exact GuardInstructionWindow.get 3, ⟨by decide, trivial, rfl⟩⟩,
   ⟨3399, .op .XOR, by exact GuardInstructionWindow.get 4, ⟨by decide, trivial, rfl⟩⟩,
   ⟨3400, .op .CALLDATASIZE, by exact GuardInstructionWindow.get 5, ⟨by decide, trivial, rfl⟩⟩,
   ⟨3401, .op .SAR, by exact GuardInstructionWindow.get 6, ⟨by decide, trivial, rfl⟩⟩,
   ⟨3402, .op .XOR, by exact GuardInstructionWindow.get 7, ⟨by decide, trivial, rfl⟩⟩,
   ⟨3403, .push ⟨2, by decide⟩ (UInt256.ofNat 4905), by exact GuardInstructionWindow.get 8, by decide⟩,
   ⟨3404, .op .JUMPI, by exact GuardInstructionWindow.get 9, ⟨by decide, trivial, rfl⟩⟩]

def wordMissPath : List Located := wordPath ++ [entryDest]

def storePath : List Located :=
  [⟨3405, .push ⟨20, by decide⟩ (UInt256.ofNat 95383801997447390147238369573240532004699299169), by exact GuardInstructionWindow.get 10, by decide⟩,
   ⟨3406, .op .CALLDATASIZE, by exact GuardInstructionWindow.get 11, ⟨by decide, trivial, rfl⟩⟩,
   ⟨3407, .op .SHR, by exact GuardInstructionWindow.get 12, ⟨by decide, trivial, rfl⟩⟩,
   ⟨3408, .push ⟨20, by decide⟩ (UInt256.ofNat 802931186561056611446976448233794645126013734992), by exact GuardInstructionWindow.get 13, by decide⟩,
   ⟨3409, .op .XOR, by exact GuardInstructionWindow.get 14, ⟨by decide, trivial, rfl⟩⟩,
   ⟨3410, .push ⟨0, by decide⟩ (UInt256.ofNat 0), by rfl, by decide⟩,
   ⟨3411, .op .MSTORE, by rfl, ⟨by decide, trivial, rfl⟩⟩]

def finishPath : List Located :=
  [⟨3413, .push ⟨0, by decide⟩ (UInt256.ofNat 0), by rfl, by decide⟩,
   ⟨3414, .op .RETURN, by rfl, ⟨by decide, trivial, rfl⟩⟩]

def maskedWord (input : ByteArray) : UInt256 :=
  UInt256.xor (MachineState.readWord input 0) wordMask

def shiftedWord (input : ByteArray) : UInt256 :=
  UInt256.sar (maskedWord input) (UInt256.ofNat input.size)

def wordCond (input : ByteArray) : UInt256 :=
  UInt256.xor (shiftedWord input) wordMask

def armEntry (input : ByteArray) : State := Execution.atPC input 4629
def fallbackState (input : ByteArray) : State := Execution.atPC input 4906
def answerWord (input : ByteArray) : UInt256 :=
  UInt256.xor (UInt256.ofNat 802931186561056611446976448233794645126013734992)
    (UInt256.shiftRight (UInt256.ofNat 95383801997447390147238369573240532004699299169)
      (UInt256.ofNat input.size))
def answerBytes (input : ByteArray) : ByteArray :=
  Data.Bytes.natToBytesPadded (answerWord input).toNat 32
def answerMemory (input : ByteArray) : ByteArray :=
  MachineState.writeBytes ByteArray.empty (answerBytes input) 0
def stored (input : ByteArray) : State :=
  {initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 4720
    memory := answerMemory input
    activeWords := UInt256.ofNat 1}
def sized (input : ByteArray) : State :=
  {stored input with pc := UInt256.ofNat 4721, stack := [UInt256.ofNat 32]}
def returned (input : ByteArray) : State :=
  {stored input with
    pc := UInt256.ofNat 4722
    halt := .Returned
    hReturn := MachineState.readPadded (answerMemory input) 0 32}

@[simp] private theorem add_nat (a b : Nat) :
    UInt256.add (UInt256.ofNat a) (UInt256.ofNat b) = UInt256.ofNat (a + b) :=
  Word.ofNat_add_mod a b
@[simp] private theorem zero_toNat : ({val := 0} : UInt256).toNat = 0 := rfl
@[simp] private theorem literal_zero_toNat : (0 : UInt256).toNat = 0 := rfl

private theorem true_of_ne_zero (w : UInt256) (h : w ≠ 0) : UInt256.isTrue w = true := by
  have ht : UInt256.isTrue w := by
    intro hn
    apply h
    apply Word.word_ext
    exact hn
  simpa using ht

private theorem valid_generic : Decode.isValidJumpDest submissionBytecode 4905 = true := by
  have h := Artifact.submissionArtifact.isValidJumpDest_index 3528 (by rfl)
  rw [pc_176] at h
  exact h

/-! ### Sign-extending shift and mask arithmetic -/

private theorem xor_toNat (a b : UInt256) : (UInt256.xor a b).toNat = a.toNat ^^^ b.toNat := by
  have ha := a.val.isLt
  have hb := b.val.isLt
  change ((a.toNat ^^^ b.toNat) % UInt256.size) = a.toNat ^^^ b.toNat
  apply Nat.mod_eq_of_lt
  exact Nat.xor_lt_two_pow ha hb

private theorem wordMask_toNat : wordMask.toNat = wordMaskNat := by
  unfold wordMask wordMaskNat
  rw [Word.word_toNat_ofNat]
  decide

private theorem shiftedWord_eq_of_wordCond (input : ByteArray) (hz : wordCond input = 0) :
    (shiftedWord input).toNat = wordMaskNat := by
  have h := congrArg UInt256.toNat ((KnownInputLogic.wordXor_eq_zero_iff _ _).mp hz)
  rw [wordMask_toNat] at h
  exact h

private theorem sar_ge_of_size_ge_four (v s : UInt256)
    (hs4 : 4 ≤ s.toNat) (hs256 : s.toNat < 256) (hv : 2 ^ 255 ≤ v.toNat) :
    2 ^ 256 - 2 ^ 251 ≤ (UInt256.sar v s).toNat := by
  unfold UInt256.sar UInt256.toSignedNat UInt256.ofSignedInt
  have hsize : UInt256.size = 2 ^ 256 := rfl
  have hvlt : v.toNat < 2 ^ 256 := v.val.isLt
  rw [if_neg (by omega)]
  simp only [hsize]
  rw [if_neg (by rw [show (2:Nat) ^ 256 / 2 = 2 ^ 255 by norm_num]; omega)]
  rw [Word.word_toNat_ofNat]
  have hd_ge : 16 ≤ 2 ^ s.toNat := by
    simpa using Nat.pow_le_pow_right (by decide : 0 < 2) hs4
  have hd_lt : 2 ^ s.toNat < 2 ^ 256 :=
    Nat.pow_lt_pow_right (by decide : 1 < 2) hs256
  generalize hx : v.toNat = x at hv hvlt
  generalize hd : (2 : Nat) ^ s.toNat = d at hd_ge hd_lt ⊢
  have hcast : ((2 : Int) ^ s.toNat) = (d : Int) := by
    rw [← hd]
    push_cast
    rfl
  rw [hcast]
  set a : Int := (x : Int) - ((2 ^ 256 : Nat) : Int)
  set q : Int := a / (d : Int)
  set r : Int := a % (d : Int)
  have hdiv : (d : Int) * q + r = a := Int.mul_ediv_add_emod a (d : Int)
  have hr0 : 0 ≤ r := Int.emod_nonneg a (by omega)
  have hrd : r < (d : Int) := Int.emod_lt_of_pos a (by omega)
  have hq_ge : -(2 ^ 251 : Int) ≤ q := by
    by_contra hlt
    have hq_le : q + (2 ^ 251 : Int) + 1 ≤ 0 := by omega
    have hmul : (d : Int) * (q + (2 ^ 251 : Int) + 1) ≤ 0 :=
      Int.mul_nonpos_of_nonneg_of_nonpos (by omega) hq_le
    rw [Int.mul_add, Int.mul_add, Int.mul_one] at hmul
    omega
  have hq_lt : q < 0 := by
    by_contra hge
    have hq0 : 0 ≤ q := by omega
    have hmul : 0 ≤ (d : Int) * q := Int.mul_nonneg (by omega) hq0
    omega
  have hmod_lt : (q % ((2 ^ 256 : Nat) : Int)).toNat < 2 ^ 256 := by omega
  have hmod_ge : 2 ^ 256 - 2 ^ 251 ≤ (q % ((2 ^ 256 : Nat) : Int)).toNat := by omega
  rw [Nat.mod_eq_of_lt hmod_lt]
  exact hmod_ge

private theorem sar_lt_of_small (v s : UInt256)
    (hs256 : s.toNat < 256) (hv : v.toNat < 2 ^ 255) :
    (UInt256.sar v s).toNat < 2 ^ 255 := by
  unfold UInt256.sar UInt256.toSignedNat UInt256.ofSignedInt
  have hsize : UInt256.size = 2 ^ 256 := rfl
  rw [if_neg (by omega)]
  simp only [hsize]
  rw [if_pos (by rw [show (2:Nat) ^ 256 / 2 = 2 ^ 255 by norm_num]; exact hv)]
  rw [Word.word_toNat_ofNat]
  have hd_pos : 1 ≤ 2 ^ s.toNat := Nat.one_le_pow s.toNat 2 (by decide)
  generalize hx : v.toNat = x at hv
  generalize hd : (2 : Nat) ^ s.toNat = d at hd_pos ⊢
  have hcast : ((2 : Int) ^ s.toNat) = (d : Int) := by
    rw [← hd]
    push_cast
    rfl
  rw [hcast]
  set q : Int := (x : Int) / (d : Int)
  set r : Int := (x : Int) % (d : Int)
  have hdiv : (d : Int) * q + r = (x : Int) := Int.mul_ediv_add_emod (x : Int) (d : Int)
  have hr0 : 0 ≤ r := Int.emod_nonneg (x : Int) (by omega)
  have hrd : r < (d : Int) := Int.emod_lt_of_pos (x : Int) (by omega)
  have hq0 : 0 ≤ q := Int.ediv_nonneg (by omega) (by omega)
  have hq_le : q ≤ (x : Int) := by
    by_contra hgt
    have hq1 : (x : Int) + 1 ≤ q := by omega
    have hmul : 1 * ((x : Int) + 1) ≤ (d : Int) * q :=
      Int.mul_le_mul (by omega) hq1 (by omega) (by omega)
    omega
  have hmod_lt : (q % ((2 ^ 256 : Nat) : Int)).toNat < 2 ^ 256 := by omega
  rw [Nat.mod_eq_of_lt hmod_lt]
  omega

/-- The sign-extended arm test can only match inputs shorter than four bytes. -/
theorem size_lt_four_of_wordCond (input : ByteArray) (hfit : CalldataFits input)
    (hz : wordCond input = 0) : input.size < 4 := by
  have heq := shiftedWord_eq_of_wordCond input hz
  unfold shiftedWord at heq
  have hs_toNat : (UInt256.ofNat input.size).toNat = input.size := by
    rw [Word.word_toNat_ofNat]
    exact Nat.mod_eq_of_lt (Nat.lt_trans hfit (by norm_num))
  by_contra hge4
  have h4 : 4 ≤ (UInt256.ofNat input.size).toNat := by omega
  by_cases hs256 : (UInt256.ofNat input.size).toNat < 256
  · by_cases hv : (maskedWord input).toNat < 2 ^ 255
    · have hlt := sar_lt_of_small (maskedWord input) (UInt256.ofNat input.size) hs256 hv
      unfold wordMaskNat at heq
      omega
    · have hge := sar_ge_of_size_ge_four (maskedWord input) (UInt256.ofNat input.size)
        h4 hs256 (by omega)
      unfold wordMaskNat at heq
      omega
  · unfold UInt256.sar at heq
    rw [if_pos (by omega)] at heq
    split_ifs at heq <;> {
      unfold wordMaskNat at heq
      revert heq
      decide
    }

private theorem maskedWord_div_eq (input : ByteArray) :
    (maskedWord input).toNat / 2 ^ 232 = (leadWord input).toNat ^^^ 0xf26044 := by
  have hxor : (maskedWord input).toNat = (MachineState.readWord input 0).toNat ^^^ wordMaskNat := by
    unfold maskedWord
    rw [xor_toNat, wordMask_toNat]
  have hlead : (leadWord input).toNat = (MachineState.readWord input 0).toNat >>> 232 := by
    unfold leadWord
    rw [Word.shiftRight_toNat _ (by decide)]
  have hmask : wordMaskNat >>> 232 = 0xf26044 := by decide
  rw [← Nat.shiftRight_eq_div_pow, hxor, Nat.shiftRight_xor_distrib, hlead, hmask]

private theorem xor_cancel_right (a b : Nat) : (a ^^^ b) ^^^ b = a := by
  rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

private theorem sar_const_big (v : UInt256) (k : Nat) (hk : k = 1 ∨ k = 2 ∨ k = 3)
    (h : (UInt256.sar v (UInt256.ofNat k)).toNat = wordMaskNat) :
    ((v.toNat : Int) - ((2 ^ 256 : Nat) : Int)) / ((2 : Int) ^ k) + ((2 ^ 256 : Nat) : Int) =
      (wordMaskNat : Int) := by
  have hk256 : (UInt256.ofNat k).toNat < 256 := by
    rcases hk with rfl | rfl | rfl <;> decide
  have hv_ge : 2 ^ 255 ≤ v.toNat := by
    by_contra hlt
    have hs := sar_lt_of_small v (UInt256.ofNat k) hk256 (by omega)
    unfold wordMaskNat at h
    omega
  have hvlt : v.toNat < 2 ^ 256 := v.val.isLt
  unfold UInt256.sar UInt256.toSignedNat UInt256.ofSignedInt at h
  have hsize : UInt256.size = 2 ^ 256 := rfl
  rw [if_neg (by omega)] at h
  simp only [hsize] at h
  rw [if_neg (by rw [show (2:Nat) ^ 256 / 2 = 2 ^ 255 by norm_num]; omega)] at h
  rw [Word.word_toNat_ofNat] at h
  rcases hk with rfl | rfl | rfl
  · change ((((v.toNat : Int) - ((2 ^ 256 : Nat) : Int)) / 2 % ((2 ^ 256 : Nat) : Int)).toNat) % 2 ^ 256 = wordMaskNat at h
    unfold wordMaskNat at h ⊢
    omega
  · change ((((v.toNat : Int) - ((2 ^ 256 : Nat) : Int)) / 4 % ((2 ^ 256 : Nat) : Int)).toNat) % 2 ^ 256 = wordMaskNat at h
    unfold wordMaskNat at h ⊢
    omega
  · change ((((v.toNat : Int) - ((2 ^ 256 : Nat) : Int)) / 8 % ((2 ^ 256 : Nat) : Int)).toNat) % 2 ^ 256 = wordMaskNat at h
    unfold wordMaskNat at h ⊢
    omega

theorem wordCond_zero_size_pos (input : ByteArray) (_hfit : CalldataFits input)
    (hpos : 0 < input.size) (hsmall : input.size < 4) (hz : wordCond input = 0) :
    input = AbcInputData.abcInput := by
  have heq := shiftedWord_eq_of_wordCond input hz
  unfold shiftedWord at heq
  have hdiv := maskedWord_div_eq input
  have hvlt : (maskedWord input).toNat < 2 ^ 256 := (maskedWord input).val.isLt
  have b0 := (byte input 0).toNat_lt
  have b1 := (byte input 1).toNat_lt
  have b2 := (byte input 2).toNat_lt
  have hs : input.size = 1 ∨ input.size = 2 ∨ input.size = 3 := by omega
  rcases hs with hs | hs | hs
  · rw [hs] at heq
    have hsar := sar_const_big (maskedWord input) 1 (Or.inl rfl) heq
    have htop : (maskedWord input).toNat / 2 ^ 232 = 0xe4c089 := by
      unfold wordMaskNat at hsar
      omega
    rw [hdiv] at htop
    have hlead : (leadWord input).toNat = 0x16a0cd := by
      have hx := congrArg (· ^^^ 0xf26044) htop
      rw [xor_cancel_right] at hx
      exact hx
    rw [prefix_toNat] at hlead
    have hz2 : byte input 2 = 0 := by
      rw [byte_getD]
      exact Memory.getElem?_getD_eq_zero_of_size_le input 2 (by omega)
    rw [hz2] at hlead
    change (byte input 0).toNat * 65536 + (byte input 1).toNat * 256 + 0 = 0x16a0cd at hlead
    omega
  · rw [hs] at heq
    have hsar := sar_const_big (maskedWord input) 2 (Or.inr (Or.inl rfl)) heq
    have htop : (maskedWord input).toNat / 2 ^ 232 = 0xc98113 := by
      unfold wordMaskNat at hsar
      omega
    rw [hdiv] at htop
    have hlead : (leadWord input).toNat = 0x3be157 := by
      have hx := congrArg (· ^^^ 0xf26044) htop
      rw [xor_cancel_right] at hx
      exact hx
    rw [prefix_toNat] at hlead
    have hz2 : byte input 2 = 0 := by
      rw [byte_getD]
      exact Memory.getElem?_getD_eq_zero_of_size_le input 2 (by omega)
    rw [hz2] at hlead
    change (byte input 0).toNat * 65536 + (byte input 1).toNat * 256 + 0 = 0x3be157 at hlead
    omega
  · rw [hs] at heq
    have hsar := sar_const_big (maskedWord input) 3 (Or.inr (Or.inr rfl)) heq
    have htop : (maskedWord input).toNat / 2 ^ 232 = 0x930227 := by
      unfold wordMaskNat at hsar
      omega
    rw [hdiv] at htop
    have hlead : (leadWord input).toNat = 0x616263 := by
      have hx := congrArg (· ^^^ 0xf26044) htop
      rw [xor_cancel_right] at hx
      exact hx
    rw [prefix_toNat] at hlead
    have h0 : (byte input 0).toNat = 97 := by omega
    have h1 : (byte input 1).toNat = 98 := by omega
    have h2 : (byte input 2).toNat = 99 := by omega
    apply ByteArray.ext_getElem hs
    intro i hi hir
    have hi3 : i < 3 := by omega
    rw [← TailProjection.byteFrom_getElem input i hi]
    change byte input i = _
    interval_cases i <;> apply UInt8.ext
    · exact h0
    · exact h1
    · exact h2

private def sarStep {s : State} {shift value : UInt256} {rest : List UInt256}
    (hop : s.decodedOp = some .SAR)
    (hstack : s.stack = shift :: value :: rest)
    (hcap : s.stack.length + Operation.pushArity .SAR ≤ 1024 + Operation.popArity .SAR)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    GasSteps s { s with stack := UInt256.sar value shift :: rest, pc := s.pc.succ } := by
  let cost := Gas.baseCost s.fork .SAR
  apply GasStep.of_running cost hrun hnp
  intro gas hgas
  simpa [withGas, cost] using
    StepRunning.sar (withGas s gas) shift value rest hop hgas hstack hcap

/-! ### The word test, with the sign-extending shift stepped directly -/

def wordHead : List Located := wordPath.take 6
def wordCalc : List Located := (wordPath.drop 7).take 2
def wordBranch : Located :=
  ⟨3404, .op .JUMPI, by exact GuardInstructionWindow.get 9, ⟨by decide, trivial, rfl⟩⟩
def wordLoaded (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 4667
    stack := [UInt256.ofNat input.size, maskedWord input, wordMask] }
def wordShifted (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 4668
    stack := [shiftedWord input, wordMask] }
def wordTested (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 4672
    stack := [UInt256.ofNat 4905, wordCond input] }

private theorem run_word_head (input : ByteArray) :
    DataStepper.runLocatedBlock wordHead (armEntry input) = some (wordLoaded input) := by
  simp [wordHead, wordPath, Artifact.op, DataStepper.runLocatedBlock, DataStepper.runLocated, DataStepper.runInstr,
    armEntry, wordLoaded, maskedWord, wordMask, Execution.atPC, initialState, UInt256.succ,
    Word.ofNat_add_mod, Word.word_toNat_ofNat, List.getElem?_cons_zero]
private theorem run_word_calc (input : ByteArray) :
    DataStepper.runLocatedBlock wordCalc (wordShifted input) = some (wordTested input) := by
  simp [wordCalc, wordPath, DataStepper.runLocatedBlock, DataStepper.runLocated, DataStepper.runInstr,
    wordShifted, wordTested, wordCond, Execution.atPC, initialState, UInt256.succ,
    Word.ofNat_add_mod, Word.word_toNat_ofNat]

private def gasSteps_sar (input : ByteArray) : GasSteps (wordLoaded input) (wordShifted input) := by
  have hd := Artifact.submissionArtifact.decodeAt_op_index 3401 .SAR
    (by exact GuardInstructionWindow.get 6) (by decide) trivial
  have hp : (wordLoaded input).pc.toNat = Artifact.submissionArtifact.instructionPC 3401 := by
    rw [pc_4101]; rfl
  have hop : (wordLoaded input).decodedOp = some .SAR :=
    Artifact.submissionArtifact.state_decodedOp_of (wordLoaded input) 3401 rfl hp .SAR none hd rfl
  have g := sarStep (s := wordLoaded input) (shift := UInt256.ofNat input.size)
    (value := maskedWord input) (rest := [wordMask]) hop rfl
    (by show 3 + Operation.pushArity .SAR ≤ 1024 + Operation.popArity .SAR; decide) rfl
    deployAddress_not_precompile
  have ht : { wordLoaded input with
      stack := UInt256.sar (maskedWord input) (UInt256.ofNat input.size) :: [wordMask],
      pc := (wordLoaded input).pc.succ } = wordShifted input := by
    simp [wordLoaded, wordShifted, shiftedWord, initialState, Word.succ_ofNat_mod,
      Word.word_toNat_ofNat]
  exact GasSteps.cast g rfl ht

private def soundW (path : List Located) {s t : State}
    (h : DataStepper.runLocatedBlock path s = some t)
    (hc : s.executionEnv.code = Artifact.submissionArtifact.code := by rfl)
    (hf : s.fork = .Osaka := by rfl) (hr : s.halt = .Running := by rfl)
    (hn : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false := by exact deployAddress_not_precompile) :
    GasSteps s t :=
  DataStepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka path hc hf h hr hn

private def gasSteps_word_prefix (input : ByteArray) :
    GasSteps (armEntry input) (wordTested input) :=
  (soundW wordHead (run_word_head input)).trans
    ((gasSteps_sar input).trans (soundW wordCalc (run_word_calc input)))

theorem run_word_miss (input : ByteArray) (hm : wordCond input ≠ 0) :
    DataStepper.runLocatedBlock [wordBranch, entryDest] (wordTested input) =
      some (fallbackState input) := by
  have hbranch : DataStepper.runLocatedBlock [wordBranch] (wordTested input) =
      some (PatternedScan.stS input 4905 []) :=
    PatternedScan.blockOfS wordBranch
      (PatternedScan.pcFactS input 3404 4672 [UInt256.ofNat 4905, wordCond input] (by norm_num) pc_4104)
      (PatternedScan.stepS_jumpi_taken input 4672 4905 (UInt256.ofNat 4905) (wordCond input) []
        (by simp) (by norm_num) rfl (by simpa using true_of_ne_zero (wordCond input) hm) valid_generic)
  have hd : DataStepper.runLocatedBlock [entryDest] (PatternedScan.stS input 4905 []) =
      some (fallbackState input) := by
    exact PatternedScan.blockOfS entryDest
      (PatternedScan.pcFactS input 3528 4905 [] (by norm_num) pc_176)
      (PatternedScan.stepS_jumpdest input 4905 [] (by simp) (by norm_num))
  exact DataStepper.runLocatedBlock_append [wordBranch] [entryDest]
    _ _ _ hbranch rfl hd

theorem run_word_hit (input : ByteArray) (hm : wordCond input = 0) :
    DataStepper.runLocatedBlock [wordBranch] (wordTested input) = some (Execution.atPC input 4673) := by
  have ht : ¬ UInt256.isTrue (wordCond input) := by rw [hm]; decide
  exact PatternedScan.blockOfS wordBranch
    (PatternedScan.pcFactS input 3404 4672 [UInt256.ofNat 4905, wordCond input] (by norm_num) pc_4104)
    (PatternedScan.stepS_jumpi_fall input 4672 (UInt256.ofNat 4905) (wordCond input) []
      (by simp) (by norm_num) ht)

def storeHead : List Located := storePath.take 5
def storeTail : List Located := storePath.drop 5

theorem run_store_head (input : ByteArray) :
    DataStepper.runLocatedBlock storeHead (Execution.atPC input 4673) =
      some (PatternedScan.stS input 4718 [answerWord input]) := by
  simp (config := { maxSteps := 1000000 })
    [storeHead, storePath, DataStepper.runLocatedBlock, DataStepper.runLocated,
     DataStepper.runInstr, PatternedScan.stS, Execution.atPC, initialState,
     Word.literal_eq_ofNat, Word.succ_ofNat_mod, Word.ofNat_add_mod, answerWord,
     UInt256.succ, List.exchange, List.getElem?_cons_zero]

theorem run_store_tail (input : ByteArray) :
    DataStepper.runLocatedBlock storeTail (PatternedScan.stS input 4718 [answerWord input]) =
      some (stored input) := by
  simp (config := { maxSteps := 1000000 })
    [storeTail, storePath, DataStepper.runLocatedBlock, DataStepper.runLocated,
     DataStepper.runInstr, PatternedScan.stS, stored, answerMemory, answerBytes,
     MachineState.mstore, State.activeWordsAfterUInt256, MachineState.activeWordsAfter,
     initialState, Word.literal_eq_ofNat, Word.succ_ofNat_mod, Word.ofNat_add_mod,
     Word.word_toNat_ofNat, UInt256.succ, List.exchange, List.getElem?_cons_zero]

theorem run_store (input : ByteArray) :
    DataStepper.runLocatedBlock storePath (Execution.atPC input 4673) = some (stored input) := by
  rw [← List.take_append_drop 5 storePath]
  exact DataStepper.runLocatedBlock_append _ _ _ _ _ (run_store_head input) rfl (run_store_tail input)

theorem run_finish (input : ByteArray) :
    DataStepper.runLocatedBlock finishPath (sized input) = some (returned input) := by
  simp (config := { maxSteps := 1000000 })
    [finishPath, DataStepper.runLocatedBlock, DataStepper.runLocated,
     DataStepper.runInstr, sized, stored, returned, initialState,
     Word.literal_eq_ofNat, Word.succ_ofNat_mod, Word.ofNat_add_mod,
     State.activeWordsAfterUInt256, MachineState.activeWordsAfter,
     Word.word_toNat_ofNat, UInt256.succ, List.exchange, List.getElem?_cons_zero]

private def sound (path : List Located) {s t : State}
    (h : DataStepper.runLocatedBlock path s = some t)
    (hc : s.executionEnv.code = Artifact.submissionArtifact.code := by rfl)
    (hf : s.fork = .Osaka := by rfl) (hr : s.halt = .Running := by rfl)
    (hn : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false := by exact deployAddress_not_precompile) :
    GasSteps s t :=
  DataStepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka path hc hf h hr hn

def gasSteps_miss (input : ByteArray) (hw : wordCond input ≠ 0) :
    GasSteps (armEntry input) (fallbackState input) :=
  (gasSteps_word_prefix input).trans (sound [wordBranch, entryDest] (run_word_miss input hw))

def gasSteps_hit (input : ByteArray) (hw : wordCond input = 0) :
    GasSteps (armEntry input) (returned input) := by
  have gw := (gasSteps_word_prefix input).trans (sound [wordBranch] (run_word_hit input hw))
  have gs := sound storePath (run_store input)
  have hd := Artifact.submissionArtifact.decodeAt_op_index 3412 .MSIZE
    (by rfl) (by decide) trivial
  have hp : (stored input).pc.toNat = Artifact.submissionArtifact.instructionPC 3412 := by
    rw [pc_inlineMsize]; rfl
  have hop : (stored input).decodedOp = some .MSIZE :=
    Artifact.submissionArtifact.state_decodedOp_of (stored input) 3412 rfl hp .MSIZE none hd rfl
  have gmraw := Msize.step hop (by change (0 : Nat) < 1024; decide)
    rfl deployAddress_not_precompile
  have gm : GasSteps (stored input) (sized input) := by
    simpa [stored, sized, initialState, Word.succ_ofNat_mod, Word.word_toNat_ofNat] using gmraw
  have gf := sound finishPath (run_finish input)
  exact gw.trans (gs.trans (gm.trans gf))

theorem answer_empty : answerBytes ByteArray.empty = EmptySpec.emptyOutput := by
  rw [answerBytes, Memory.natToBytesPadded_eq_natToBE]
  decide
theorem answer_abc : answerBytes AbcInputData.abcInput = AbcInputData.abcPaddedDigest := by
  rw [answerBytes, Memory.natToBytesPadded_eq_natToBE]
  decide

private theorem readWord_empty : MachineState.readWord ByteArray.empty 0 = 0 := by
  unfold MachineState.readWord
  rw [← Bytes.bytesNat_toList, Bytes.readPadded_toList,
    YulEvmCompiler.ByteArray.toList_eq_data]
  decide

private theorem readWord_abc :
    MachineState.readWord AbcInputData.abcInput 0 = UInt256.ofNat (0x616263 * 2 ^ 232) := by
  unfold MachineState.readWord
  rw [← Bytes.bytesNat_toList, Bytes.readPadded_toList,
    YulEvmCompiler.ByteArray.toList_eq_data]
  decide

theorem wordCond_empty : wordCond ByteArray.empty = 0 := by
  unfold wordCond shiftedWord maskedWord
  rw [readWord_empty]
  decide

theorem wordCond_abc : wordCond AbcInputData.abcInput = 0 := by
  unfold wordCond shiftedWord maskedWord
  rw [readWord_abc]
  decide

private theorem correct_known (input : ByteArray)
    (hw : wordCond input = 0) (hspec : spec input = answerBytes input)
    (entryPrefix : GasSteps (initialState submissionBytecode input 0) (armEntry input)) :
    ∃ g₀ : Nat, ∀ gas : Nat, g₀ ≤ gas →
      Eval (initialState submissionBytecode input gas) (.returned (spec input)) := by
  let trace := entryPrefix.trans (gasSteps_hit input hw)
  have hsize : (answerBytes input).size = 32 :=
    YulEvmCompiler.BytesLemmas.natToBytesPadded_size _ _
  have hread : MachineState.readPadded (answerMemory input) 0 32 = answerBytes input := by
    rw [← hsize]
    exact Memory.readPadded_writeBytes_same ByteArray.empty (answerBytes input) 0
  refine ⟨trace.cost, fun gas hgas => ?_⟩
  have heval := eval_of_steps (trace.trace gas hgas) (by
    simp [withGas, returned, stored, State.isDone, State.isHalted, State.isRunning]
    rfl)
  rw [State.toResult_returned _ (by rfl)] at heval
  change Eval (withGas (initialState submissionBytecode input 0) gas)
    (.returned (MachineState.readPadded (answerMemory input) 0 32)) at heval
  rw [hread, ← hspec] at heval
  exact heval

theorem correct_abc (input : ByteArray) (_hfit : CalldataFits input)
    (heq : input = AbcInputData.abcInput)
    (entryPrefix : GasSteps (initialState submissionBytecode input 0) (armEntry input)) :
    ∃ g₀ : Nat, ∀ gas : Nat, g₀ ≤ gas →
      Eval (initialState submissionBytecode input gas) (.returned (spec input)) := by
  subst input
  exact correct_known _ wordCond_abc (by rw [AbcDigest.spec_abc, answer_abc]) entryPrefix

theorem correct_empty (input : ByteArray) (_hfit : CalldataFits input)
    (heq : input = ByteArray.empty)
    (entryPrefix : GasSteps (initialState submissionBytecode input 0) (armEntry input)) :
    ∃ g₀ : Nat, ∀ gas : Nat, g₀ ≤ gas →
      Eval (initialState submissionBytecode input gas) (.returned (spec input)) := by
  subst input
  exact correct_known _ wordCond_empty (by rw [EmptySpec.spec_empty, answer_empty]) entryPrefix

#print axioms correct_abc
#print axioms correct_empty
#print axioms gasSteps_miss
end Challenge.Ripemd160.Submission.Proofs.Bytecode.AbcArm
