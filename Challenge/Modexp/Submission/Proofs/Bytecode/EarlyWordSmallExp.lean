import Challenge.Modexp.Submission.Proofs.Bytecode.EarlyWordProgram


set_option warningAsError true

/-!
# Zero-exponent early return

When the declared exponent and modulus sizes each fit in one word and the
exponent word is zero, the result is decided without entering the Montgomery
path: `b^0 mod m` is `1` for `m > 1` and `0` otherwise.  The appended block at
pc 5312 checks the two width guards, loads the exponent word, and either
returns directly or falls back to the legacy miss entry at pc 5304.  A zero
declared exponent size yields a zero word, so the `e = 0` case also covers
`esize = 0`.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.EarlyWordSmallExp

open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open WindowTwentyOneEntry WindowNibbleKernel EarlyWordProgram

/-- Right-shift amount that keeps the low `w` bytes of a loaded word. -/
def smallExpShift (w : UInt256) : UInt256 :=
  UInt256.shiftLeft (UInt256.ofNat 32 - w) (UInt256.ofNat 3)

/-- The `w`-byte big-endian value at `offset`, as a word. -/
def smallExpValue (raw w : UInt256) : UInt256 :=
  UInt256.shiftRight raw (smallExpShift w)

/-- The two width guards: bail to the legacy miss entry when the modulus or
exponent size exceeds one word. -/
def zeroExpGuardProgram : List Instr :=
  [.op .JUMPDEST,
   .push 1 32, .op (.Dup ⟨1, by decide⟩), .op .GT, .push 2 5304, .op .JUMPI,
   .push 1 32, .op (.Dup ⟨2, by decide⟩), .op .GT, .push 2 5304, .op .JUMPI]

/-- Load and right-align the exponent word; bail when it is nonzero. -/
def zeroExpLoadEProgram : List Instr :=
  [.push 1 96, .op (.Dup ⟨3, by decide⟩), .op .ADD, .op .CALLDATALOAD,
   .push 1 32, .op (.Dup ⟨3, by decide⟩), .op .SUB, .push 1 3, .op .SHL,
   .op .SHR,
   .push 2 5304, .op .JUMPI]

/-- `e = 0`: load the modulus word and return `1` when `m > 1`, else `0`. -/
def zeroExpFinishProgram : List Instr :=
  [.push 1 96, .op (.Dup ⟨3, by decide⟩), .op .ADD,
   .op (.Dup ⟨2, by decide⟩), .op .ADD, .op .CALLDATALOAD,
   .push 1 32, .op (.Dup ⟨3, by decide⟩), .op .SUB, .push 1 3, .op .SHL,
   .op .SHR,
   .push 1 1, .op .LT, .push 0 0, .op .MSTORE,
   .op (.Dup ⟨0, by decide⟩), .push 1 32, .op .SUB, .op .RETURN]

/-- The halted state produced by the zero-exponent return: `word` is stored
at memory offset 0 and the low `msize` bytes are returned. -/
def smallExpReturned (template : State) (pc word mWord : UInt256)
    (active : Nat) (rest : List UInt256) : State :=
  { template with
    pc := pc
    stack := rest
    memory := WindowTableMemory.storeWord template.memory 0 word
    activeWords := UInt256.ofNat (max active 1)
    halt := .Returned
    hReturn := MachineState.readPadded
      (WindowTableMemory.storeWord template.memory 0 word)
      (UInt256.ofNat 32 - mWord).toNat mWord.toNat }

/-- The low `m` bytes of a stored word are its `m`-byte big-endian encoding. -/
theorem readPadded_storeWord_tail (memory : ByteArray) (word : UInt256)
    (m : Nat) (hm : m ≤ 32) :
    MachineState.readPadded (WindowTableMemory.storeWord memory 0 word)
        (32 - m) m =
      Data.Bytes.natToBytesPadded word.toNat m := by
  apply ByteArray.ext_getElem
  · rw [Challenge.EvmProof.Memory.readPadded_size,
      YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  · intro i hi₁ hi₂
    rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size] at hi₂
    rw [← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hi₁,
      ← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hi₂,
      Challenge.EvmProof.Memory.readPadded_getElem?_getD, if_pos hi₂,
      WindowTableMemory.storeWord,
      MachineState.writeBytes_getElem?_getD]
    rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
    rw [if_pos (by omega)]
    rw [show 32 - m + i - 0 = 32 - m + i by omega]
    rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_getElem?_getD _ _ _ (by omega),
      YulEvmCompiler.BytesLemmas.natToBytesPadded_getElem?_getD _ _ _ hi₂]
    congr 2
    omega

/-- The returned payload is the `msize`-byte encoding of the stored word. -/
theorem smallExpReturned_result (template : State) (pc word mWord : UInt256)
    (active : Nat) (rest : List UInt256) (m : Nat)
    (hm : mWord = UInt256.ofNat m) (hm32 : m ≤ 32) :
    (smallExpReturned template pc word mWord active rest).toResult =
      .returned (Precompile.natToBytes word.toNat m) := by
  change ExecutionResult.returned
      (MachineState.readPadded
        (WindowTableMemory.storeWord template.memory 0 word)
        (UInt256.ofNat 32 - mWord).toNat mWord.toNat) = _
  rw [hm, Challenge.EvmProof.Word.ofNat_sub_ofNat (by omega) (by norm_num),
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : 32 - m < 2 ^ 256),
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hm32 (by norm_num)),
    readPadded_storeWord_tail template.memory word m hm32]
  rfl

theorem run_zeroExpGuard (template : State) (b e m : UInt256)
    (hjump : Decode.isValidJumpDest template.executionEnv.code 5304 = true) :
    runInstructions zeroExpGuardProgram
      (framed template (UInt256.ofNat 5312) [m, e, b]) =
      some (framed template
        (if 32 < m.toNat then UInt256.ofNat 5304
         else if 32 < e.toNat then UInt256.ofNat 5304
         else UInt256.ofNat 5329) [m, e, b]) := by
  by_cases hm : 32 < m.toNat <;>
  by_cases he : 32 < e.toNat <;>
    simp [zeroExpGuardProgram, runInstructions, framed,
      Stepper.runInstr, UInt256.isTrue, UInt256.gt, hm, he, hjump,
      Word.literal_eq_ofNat, Word.word_toNat_ofNat,
      Word.succ_ofNat_mod, Word.ofNat_add_mod]

theorem run_zeroExpLoadE (template : State) (b e m : UInt256)
    (hjump : Decode.isValidJumpDest template.executionEnv.code 5304 = true) :
    runInstructions zeroExpLoadEProgram
      (framed template (UInt256.ofNat 5329) [m, e, b]) =
      some (framed template
        (if (smallExpValue
            (MachineState.readWord template.executionEnv.calldata
              (UInt256.ofNat 96 + b).toNat) e).toNat = 0
          then UInt256.ofNat 5346 else UInt256.ofNat 5304)
        [m, e, b]) := by
  by_cases hv : (smallExpValue
      (MachineState.readWord template.executionEnv.calldata
        (UInt256.ofNat 96 + b).toNat) e).toNat = 0 <;>
    simp [zeroExpLoadEProgram, smallExpValue, smallExpShift, runInstructions,
      framed, Stepper.runInstr, UInt256.isTrue, hv, hjump,
      Word.literal_eq_ofNat, Word.word_toNat_ofNat,
      Word.succ_ofNat_mod, Word.ofNat_add_mod]

theorem run_zeroExpFinish (template : State) (b e m : UInt256)
    (active : Nat) (hsmall : active < 2 ^ 256)
    (hactive : template.activeWords = UInt256.ofNat active) :
    runInstructions zeroExpFinishProgram
      (framed template (UInt256.ofNat 5346) [m, e, b]) =
      some (smallExpReturned template (UInt256.ofNat 5371)
        (UInt256.lt (UInt256.ofNat 1)
          (smallExpValue
            (MachineState.readWord template.executionEnv.calldata
              (UInt256.ofNat 96 + b + e).toNat) m))
        m active [e, b]) := by
  have hcap0 : ([e, b] : List UInt256).length < 1024 := by decide
  have hcap1 : ([e, b] : List UInt256).length + 1 < 1024 := by decide
  have hcap2 : ([e, b] : List UInt256).length + 2 < 1024 := by decide
  have hcap3 : ([e, b] : List UInt256).length + 3 < 1024 := by decide
  have hcap4 : ([e, b] : List UInt256).length + 4 < 1024 := by decide
  have hcap5 : ([e, b] : List UInt256).length + 5 < 1024 := by decide
  have hcap6 : ([e, b] : List UInt256).length + 6 < 1024 := by decide
  have hzero : ({ val := 0 } : UInt256).toNat = 0 := rfl
  have ha : (UInt256.ofNat active).toNat = active := by
    rw [Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hm : (UInt256.ofNat (max active 1)).toNat = max active 1 := by
    rw [Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  simp [zeroExpFinishProgram, smallExpReturned, runInstructions, framed,
    Stepper.runInstr, hcap0, hcap1, hcap2, hcap3, hcap4, hcap5, hcap6,
    hzero, hactive, ha, hm, WindowTableMemory.storeWord,
    State.activeWordsAfterUInt256, MachineState.activeWordsAfter,
    Word.literal_eq_ofNat, Word.word_toNat_ofNat,
    Word.succ_ofNat_mod, Word.ofNat_add_mod, word_add_assoc]

/-- The loaded exponent word equals the declared-width big-endian value. -/
theorem smallExpValue_toNat (input : ByteArray) (offset w : Nat)
    (hw : w ≤ 32) :
    (smallExpValue (MachineState.readWord input offset)
        (UInt256.ofNat w)).toNat =
      Precompile.bytesToNatPadded input offset w := by
  unfold smallExpValue smallExpShift
  by_cases h0 : w = 0
  · subst h0
    have hsh : UInt256.shiftLeft (UInt256.ofNat 32 - UInt256.ofNat 0)
        (UInt256.ofNat 3) = UInt256.ofNat 256 := by
      rw [Word.ofNat_sub_ofNat (by omega) (by norm_num),
        Word.shiftLeft_ofNat (by norm_num) (by norm_num) (by norm_num)]
      norm_num
    rw [hsh]
    have hz : UInt256.shiftRight (MachineState.readWord input offset)
        (UInt256.ofNat 256) = UInt256.ofNat 0 := by
      unfold UInt256.shiftRight
      rw [if_pos (by simp [Word.word_toNat_ofNat])]
      rfl
    rw [hz, Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt (by norm_num : 0 < 2 ^ 256),
      Challenge.EvmProof.Bytes.bytesToNatPadded_zero_width]
  · have hwpos : 0 < w := Nat.pos_of_ne_zero h0
    have hsh : UInt256.shiftLeft (UInt256.ofNat 32 - UInt256.ofNat w)
        (UInt256.ofNat 3) = UInt256.ofNat ((32 - w) * 8) := by
      rw [Word.ofNat_sub_ofNat (by omega) (by norm_num),
        Word.shiftLeft_ofNat (by omega) (by norm_num) (by
          have : (32 - w) * 2 ^ 3 = (32 - w) * 8 := by norm_num
          rw [this]; have : (32 - w) * 8 ≤ 32 * 8 := by
            apply Nat.mul_le_mul_right; omega
          omega)]
      congr 1
      omega
    rw [hsh, Challenge.EvmProof.Bytes.shiftRight_readWord input offset w
      hwpos hw, Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le
        (Challenge.EvmProof.Bytes.bytesToNatPadded_lt_pow input offset w)
        (by calc (256:Nat) ^ w ≤ 256 ^ 32 :=
              Nat.pow_le_pow_right (by norm_num) hw
          _ = 2 ^ 256 := by norm_num)))]

/-- The exponent word the block computes from calldata. -/
def zeroExpEvWord (input : ByteArray) : UInt256 :=
  smallExpValue
    (MachineState.readWord input
      (UInt256.ofNat 96 + UInt256.ofNat (baseSize input)).toNat)
    (UInt256.ofNat (exponentSize input))

/-- The modulus word the block computes from calldata. -/
def zeroExpMvWord (input : ByteArray) : UInt256 :=
  smallExpValue
    (MachineState.readWord input
      (UInt256.ofNat 96 + UInt256.ofNat (baseSize input) +
        UInt256.ofNat (exponentSize input)).toNat)
    (UInt256.ofNat (modulusSize input))

/-- The appended block decides the result exactly when the exponent and
modulus sizes fit in one word and the exponent word is zero. -/
def ZeroExpGuard (input : ByteArray) : Prop :=
  exponentSize input ≤ 32 ∧ modulusSize input ≤ 32 ∧
    Precompile.bytesToNatPadded input (96 + baseSize input)
      (exponentSize input) = 0

/-- The halted state the appended block reaches on a zero-exponent hit. -/
def zeroExpFinal (template : State) (input : ByteArray) (active : Nat)
    (rest : List UInt256) : State :=
  smallExpReturned template (UInt256.ofNat 5371)
    (UInt256.lt (UInt256.ofNat 1) (zeroExpMvWord input))
    (UInt256.ofNat (modulusSize input)) active rest

theorem zeroExpEvWord_toNat (input : ByteArray)
    (he : exponentSize input ≤ 32) :
    (zeroExpEvWord input).toNat =
      Precompile.bytesToNatPadded input (96 + baseSize input)
        (exponentSize input) := by
  have hoff : (UInt256.ofNat 96 + UInt256.ofNat (baseSize input)).toNat =
      96 + baseSize input := by
    rw [Word.ofNat_add_mod, Word.word_toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by
      have := Challenge.EvmProof.Bytes.bytesToNatPadded_lt_pow input 0 32
      have h256 : (256:Nat) ^ 32 = 2 ^ 256 := by norm_num
      omega)]
  rw [hoff]
  exact smallExpValue_toNat input (96 + baseSize input)
    (exponentSize input) he

/-- The computed modulus word is the declared-width value. -/
theorem zeroExpMvWord_toNat (input : ByteArray)
    (hb : baseSize input ≤ 1024) (he : exponentSize input ≤ 1024)
    (hm : modulusSize input ≤ 32) :
    (zeroExpMvWord input).toNat =
      Precompile.bytesToNatPadded input
        (96 + baseSize input + exponentSize input) (modulusSize input) := by
  unfold zeroExpMvWord
  have hoff : (UInt256.ofNat 96 + UInt256.ofNat (baseSize input) +
      UInt256.ofNat (exponentSize input)).toNat =
      96 + baseSize input + exponentSize input := by
    rw [Word.ofNat_add_mod, Word.ofNat_add_mod, Word.word_toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by
      have h1' := Challenge.EvmProof.Bytes.bytesToNatPadded_lt_pow input 0 32
      have h2' := Challenge.EvmProof.Bytes.bytesToNatPadded_lt_pow input 32 32
      have h256 : (256:Nat) ^ 32 = 2 ^ 256 := by norm_num
      omega)]
    omega
  rw [hoff]
  exact smallExpValue_toNat input
    (96 + baseSize input + exponentSize input) (modulusSize input) hm

theorem natToBytes_zero (n : Nat) :
    Precompile.natToBytes n 0 = ByteArray.empty := by
  apply ByteArray.ext
  simp [Precompile.natToBytes, Data.Bytes.natToBytesPadded]

theorem zeroExpFinal_isDone (template : State) (input : ByteArray)
    (active : Nat) (rest : List UInt256)
    (hcall : template.callStack = []) :
    (zeroExpFinal template input active rest).isDone = true := by
  unfold zeroExpFinal
  simp [smallExpReturned, State.isDone, State.isHalted, State.isRunning,
    hcall]

/-- On a zero-exponent hit the specification reduces to the decided word:
one when the modulus exceeds one, zero otherwise. -/
theorem modPow_zero (b m : Nat) :
    Precompile.modPow b 0 m = if 1 < m then 1 else 0 := by
  unfold Precompile.modPow
  by_cases h0 : m = 0
  · simp [h0]
  · by_cases h1 : m = 1
    · simp [h1]
    · have hm : 1 < m := by omega
      simp [h0, h1, hm, Precompile.modPowAux]

theorem spec_zeroExp (input : ByteArray) (hzero : ZeroExpGuard input) :
    spec input = Precompile.natToBytes (if 1 < Precompile.bytesToNatPadded
        input (96 + baseSize input + exponentSize input) (modulusSize input)
      then 1 else 0) (modulusSize input) := by
  obtain ⟨he32, hm32, hev⟩ := hzero
  unfold spec
  dsimp only
  by_cases hm0 : modulusSize input = 0
  · rw [if_pos hm0, hm0, natToBytes_zero]
  · rw [if_neg hm0]
    dsimp only
    rw [hev, modPow_zero]

theorem zeroExpFinal_result (template : State) (input : ByteArray)
    (active : Nat) (rest : List UInt256)
    (hb : baseSize input ≤ 1024) (he : exponentSize input ≤ 1024)
    (hzero : ZeroExpGuard input) :
    (zeroExpFinal template input active rest).toResult =
      .returned (spec input) := by
  obtain ⟨he32, hm32, hev⟩ := hzero
  rw [spec_zeroExp input hzero]
  unfold zeroExpFinal
  rw [smallExpReturned_result template _ _ _ _ _ (modulusSize input) rfl
    hm32]
  rw [Word.word_toNat_lt, zeroExpMvWord_toNat input hb he hm32,
    Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt (by norm_num : (1:Nat) < 2 ^ 256)]


/-- Certified locations and jump facts for the appended zero-exponent
block. -/
structure ZeroExpPaths (artifact : ProgramArtifact) (fork : Fork) where
  guard : WindowTwentyOneBinding.Block artifact fork 5312 zeroExpGuardProgram
  loadE : WindowTwentyOneBinding.Block artifact fork 5329 zeroExpLoadEProgram
  finish : WindowTwentyOneBinding.Block artifact fork 5346 zeroExpFinishProgram
  missJump : Decode.isValidJumpDest artifact.code 5304 = true

end Challenge.Modexp.Submission.Proofs.Bytecode.EarlyWordSmallExp
