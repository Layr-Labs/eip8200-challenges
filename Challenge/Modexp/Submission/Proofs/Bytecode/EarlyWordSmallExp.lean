import Challenge.Modexp.Submission.Proofs.Bytecode.EarlyWordProgram

set_option warningAsError true

/-!
# Small-exponent early return

When every declared size is at most 32 bytes and the single-word exponent is
zero or one, the result is decided without entering the Montgomery path:
`b^0 mod m` is `1` for `m > 1` and `0` otherwise, and `b^1 mod m` is `b`
whenever `b < m` (the only case handled here).  The appended block at pc 5312
loads the three operand words, checks the guards, and either returns directly
or falls back to the legacy miss entry at pc 5304.
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

/-- The three width guards: bail to the legacy miss entry when any declared
size exceeds one word. -/
def smallExpGuardProgram : List Instr :=
  [.op .JUMPDEST,
   .op (.Dup ⟨0, by decide⟩), .push 1 32, .op .LT, .push 2 5304, .op .JUMPI,
   .op (.Dup ⟨1, by decide⟩), .push 1 32, .op .LT, .push 2 5304, .op .JUMPI,
   .op (.Dup ⟨2, by decide⟩), .push 1 32, .op .LT, .push 2 5304, .op .JUMPI]

/-- Load and right-align the exponent word; bail when it exceeds one. -/
def smallExpLoadEProgram : List Instr :=
  [.push 1 96, .op (.Dup ⟨3, by decide⟩), .op .ADD, .op .CALLDATALOAD,
   .op (.Dup ⟨2, by decide⟩), .push 1 32, .op .SUB, .push 1 3, .op .SHL,
   .op .SHR,
   .op (.Dup ⟨0, by decide⟩), .push 1 1, .op .LT, .push 2 5427, .op .JUMPI]

/-- Load and right-align the base and modulus words; dispatch on `ev = 0`. -/
def smallExpLoadMProgram : List Instr :=
  [.push 1 96, .op .CALLDATALOAD,
   .op (.Dup ⟨4, by decide⟩), .push 1 32, .op .SUB, .push 1 3, .op .SHL,
   .op .SHR,
   .push 1 96, .op (.Dup ⟨4, by decide⟩), .op .ADD, .op (.Dup ⟨5, by decide⟩),
   .op .ADD, .op .CALLDATALOAD,
   .op (.Dup ⟨3, by decide⟩), .push 1 32, .op .SUB, .push 1 3, .op .SHL,
   .op .SHR,
   .op (.Dup ⟨2, by decide⟩), .push 2 5404, .op .JUMPI]

/-- `e = 0`: return `1` when `m > 1`, else `0`. -/
def smallExpZeroProgram : List Instr :=
  [.op (.Dup ⟨0, by decide⟩), .push 1 1, .op .LT, .push 0 0, .op .MSTORE,
   .op .POP, .op .POP, .op .POP,
   .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨0, by decide⟩), .push 1 32,
   .op .SUB, .op .RETURN]

/-- `e = 1`: return `b` when `b < m`, else bail. -/
def smallExpOneProgram : List Instr :=
  [.op .JUMPDEST,
   .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .GT,
   .op .ISZERO, .push 2 5424, .op .JUMPI,
   .op (.Swap ⟨0, by decide⟩), .push 0 0, .op .MSTORE,
   .op .POP, .op .POP,
   .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨0, by decide⟩), .push 1 32,
   .op .SUB, .op .RETURN]

/-- `b ≥ m` under `e = 1`: drop the loaded words and rejoin the bail tail. -/
def smallExpBail5Program : List Instr :=
  [.op .JUMPDEST, .op .POP, .op .POP]

/-- `e > 1` (or the `b ≥ m` fall-through): drop `ev` and jump to the legacy
miss entry. -/
def smallExpBail4Program : List Instr :=
  [.op .JUMPDEST, .op .POP, .push 2 5304, .op .JUMP]

/-- The halted state produced by the small-exponent returns: `word` is stored
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

theorem run_smallExpGuard1 (template : State) (b e m : UInt256)
    (hjump : Decode.isValidJumpDest template.executionEnv.code 5304 = true) :
    runInstructions smallExpGuardProgram
      (framed template (UInt256.ofNat 5312) [m, e, b]) =
      some (framed template
        (if 32 < m.toNat then UInt256.ofNat 5304
         else if 32 < e.toNat then UInt256.ofNat 5304
         else if 32 < b.toNat then UInt256.ofNat 5304
         else UInt256.ofNat 5337) [m, e, b]) := by
  by_cases hm : 32 < m.toNat <;>
  by_cases he : 32 < e.toNat <;>
  by_cases hb : 32 < b.toNat <;>
    simp [smallExpGuardProgram, runInstructions, framed,
      Stepper.runInstr, UInt256.isTrue, UInt256.lt, hm, he, hb, hjump,
      Word.literal_eq_ofNat, Word.word_toNat_ofNat,
      Word.succ_ofNat_mod, Word.ofNat_add_mod]

theorem run_smallExpLoadE (template : State) (b e m : UInt256)
    (hjump : Decode.isValidJumpDest template.executionEnv.code 5427 = true) :
    runInstructions smallExpLoadEProgram
      (framed template (UInt256.ofNat 5337) [m, e, b]) =
      some (framed template
        (if 1 < (smallExpValue
            (MachineState.readWord template.executionEnv.calldata
              (UInt256.ofNat 96 + b).toNat) e).toNat
          then UInt256.ofNat 5427 else UInt256.ofNat 5358)
        (smallExpValue
          (MachineState.readWord template.executionEnv.calldata
            (UInt256.ofNat 96 + b).toNat) e :: [m, e, b])) := by
  by_cases hv : 1 < (smallExpValue
      (MachineState.readWord template.executionEnv.calldata
        (UInt256.ofNat 96 + b).toNat) e).toNat <;>
    simp [smallExpLoadEProgram, smallExpValue, smallExpShift, runInstructions,
      framed, Stepper.runInstr, UInt256.isTrue, UInt256.lt, hv, hjump,
      Word.literal_eq_ofNat, Word.word_toNat_ofNat,
      Word.succ_ofNat_mod, Word.ofNat_add_mod]

theorem run_smallExpLoadM (template : State) (b e m ev : UInt256)
    (hjump : Decode.isValidJumpDest template.executionEnv.code 5404 = true) :
    runInstructions smallExpLoadMProgram
      (framed template (UInt256.ofNat 5358) (ev :: [m, e, b])) =
      some (framed template
        (if ev.toNat = 0 then UInt256.ofNat 5389 else UInt256.ofNat 5404)
        (smallExpValue
          (MachineState.readWord template.executionEnv.calldata
            (UInt256.ofNat 96 + e + b).toNat) m ::
         smallExpValue
          (MachineState.readWord template.executionEnv.calldata
            (UInt256.ofNat 96).toNat) b :: ev :: [m, e, b])) := by
  by_cases hv : ev.toNat = 0 <;>
    simp [smallExpLoadMProgram, smallExpValue, smallExpShift, runInstructions,
      framed, Stepper.runInstr, UInt256.isTrue, hv, hjump,
      Word.literal_eq_ofNat, Word.word_toNat_ofNat,
      Word.succ_ofNat_mod, Word.ofNat_add_mod, word_add_assoc]

theorem run_smallExpZero (template : State) (b e m ev bv mv : UInt256)
    (active : Nat) (hsmall : active < 2 ^ 256)
    (hactive : template.activeWords = UInt256.ofNat active) :
    runInstructions smallExpZeroProgram
      (framed template (UInt256.ofNat 5389) [mv, bv, ev, m, e, b]) =
      some (smallExpReturned template (UInt256.ofNat 5404)
        (UInt256.lt (UInt256.ofNat 1) mv) m active [m, e, b]) := by
  have hcap0 : ([m, e, b] : List UInt256).length < 1024 := by decide
  have hcap1 : ([m, e, b] : List UInt256).length + 1 < 1024 := by decide
  have hcap2 : ([m, e, b] : List UInt256).length + 2 < 1024 := by decide
  have hcap3 : ([m, e, b] : List UInt256).length + 3 < 1024 := by decide
  have hcap4 : ([m, e, b] : List UInt256).length + 4 < 1024 := by decide
  have hcap5 : ([m, e, b] : List UInt256).length + 5 < 1024 := by decide
  have hcap6 : ([m, e, b] : List UInt256).length + 6 < 1024 := by decide
  have hzero : ({ val := 0 } : UInt256).toNat = 0 := rfl
  have ha : (UInt256.ofNat active).toNat = active := by
    rw [Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hm : (UInt256.ofNat (max active 1)).toNat = max active 1 := by
    rw [Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  simp [smallExpZeroProgram, smallExpReturned, runInstructions, framed,
    Stepper.runInstr, hcap0, hcap1, hcap2, hcap3, hcap4, hcap5, hcap6,
    hzero, hactive, ha, hm, WindowTableMemory.storeWord,
    State.activeWordsAfterUInt256, MachineState.activeWordsAfter,
    Word.literal_eq_ofNat, Word.word_toNat_ofNat,
    Word.succ_ofNat_mod, Word.ofNat_add_mod, word_add_assoc]

theorem run_smallExpOne (template : State) (b e m ev bv mv : UInt256)
    (active : Nat) (hsmall : active < 2 ^ 256)
    (hactive : template.activeWords = UInt256.ofNat active)
    (hjump : Decode.isValidJumpDest template.executionEnv.code 5424 = true) :
    runInstructions smallExpOneProgram
      (framed template (UInt256.ofNat 5404) [mv, bv, ev, m, e, b]) =
      some (if mv.toNat ≤ bv.toNat
        then framed template (UInt256.ofNat 5424) [mv, bv, ev, m, e, b]
        else smallExpReturned template (UInt256.ofNat 5424) bv m active
          [m, e, b]) := by
  have hcap0 : ([m, e, b] : List UInt256).length < 1024 := by decide
  have hcap1 : ([m, e, b] : List UInt256).length + 1 < 1024 := by decide
  have hcap2 : ([m, e, b] : List UInt256).length + 2 < 1024 := by decide
  have hcap3 : ([m, e, b] : List UInt256).length + 3 < 1024 := by decide
  have hcap4 : ([m, e, b] : List UInt256).length + 4 < 1024 := by decide
  have hcap5 : ([m, e, b] : List UInt256).length + 5 < 1024 := by decide
  have hcap6 : ([m, e, b] : List UInt256).length + 6 < 1024 := by decide
  have hzero : ({ val := 0 } : UInt256).toNat = 0 := rfl
  have ha : (UInt256.ofNat active).toNat = active := by
    rw [Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hm : (UInt256.ofNat (max active 1)).toNat = max active 1 := by
    rw [Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  by_cases hv : mv.toNat ≤ bv.toNat <;>
    simp [smallExpOneProgram, smallExpReturned, runInstructions, framed,
      Stepper.runInstr, UInt256.isTrue, UInt256.gt, UInt256.isZero,
      List.exchange, hv, hjump, hcap0, hcap1, hcap2, hcap3, hcap4, hcap5,
      hcap6, hzero, hactive, ha, hm, WindowTableMemory.storeWord,
      State.activeWordsAfterUInt256, MachineState.activeWordsAfter,
      Word.literal_eq_ofNat, Word.word_toNat_ofNat,
      Word.succ_ofNat_mod, Word.ofNat_add_mod, word_add_assoc]

theorem run_smallExpBail5 (template : State) (b e m ev bv mv : UInt256) :
    runInstructions smallExpBail5Program
      (framed template (UInt256.ofNat 5424) [mv, bv, ev, m, e, b]) =
      some (framed template (UInt256.ofNat 5427) [ev, m, e, b]) := by
  simp [smallExpBail5Program, runInstructions, framed, Stepper.runInstr,
    Word.literal_eq_ofNat, Word.succ_ofNat_mod]

theorem run_smallExpBail4 (template : State) (b e m ev : UInt256)
    (hjump : Decode.isValidJumpDest template.executionEnv.code 5304 = true) :
    runInstructions smallExpBail4Program
      (framed template (UInt256.ofNat 5427) [ev, m, e, b]) =
      some (framed template (UInt256.ofNat 5304) [m, e, b]) := by
  simp [smallExpBail4Program, runInstructions, framed, Stepper.runInstr,
    hjump, Word.literal_eq_ofNat, Word.word_toNat_ofNat,
    Word.succ_ofNat_mod, Word.ofNat_add_mod]

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
def smallExpEvWord (input : ByteArray) : UInt256 :=
  smallExpValue
    (MachineState.readWord input
      (UInt256.ofNat 96 + UInt256.ofNat (baseSize input)).toNat)
    (UInt256.ofNat (exponentSize input))

/-- The base word the block computes from calldata. -/
def smallExpBvWord (input : ByteArray) : UInt256 :=
  smallExpValue (MachineState.readWord input 96)
    (UInt256.ofNat (baseSize input))

/-- The modulus word the block computes from calldata. -/
def smallExpMvWord (input : ByteArray) : UInt256 :=
  smallExpValue
    (MachineState.readWord input
      (UInt256.ofNat 96 + UInt256.ofNat (exponentSize input) +
        UInt256.ofNat (baseSize input)).toNat)
    (UInt256.ofNat (modulusSize input))

/-- The appended block decides the result exactly when every operand fits in
one word, the exponent word is at most one, and (for `e = 1`) the base word is
already below the modulus word. -/
def SmallExpGuard (input : ByteArray) : Prop :=
  baseSize input ≤ 32 ∧ exponentSize input ≤ 32 ∧ modulusSize input ≤ 32 ∧
    (Precompile.bytesToNatPadded input (96 + baseSize input)
        (exponentSize input) = 0 ∨
      (Precompile.bytesToNatPadded input (96 + baseSize input)
          (exponentSize input) = 1 ∧
        Precompile.bytesToNatPadded input 96 (baseSize input) <
          Precompile.bytesToNatPadded input (96 + baseSize input +
            exponentSize input) (modulusSize input)))

/-- The halted state the appended block reaches on a small-exponent hit. -/
def smallExpFinal (template : State) (input : ByteArray) (active : Nat)
    (rest : List UInt256) : State :=
  if Precompile.bytesToNatPadded input (96 + baseSize input)
      (exponentSize input) = 0 then
    smallExpReturned template (UInt256.ofNat 5404)
      (UInt256.lt (UInt256.ofNat 1) (smallExpMvWord input))
      (UInt256.ofNat (modulusSize input)) active rest
  else
    smallExpReturned template (UInt256.ofNat 5424) (smallExpBvWord input)
      (UInt256.ofNat (modulusSize input)) active rest

theorem smallExpEvWord_toNat (input : ByteArray)
    (hb : baseSize input ≤ 32) (he : exponentSize input ≤ 32) :
    (smallExpEvWord input).toNat =
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

/-- The computed base word is the declared-width value. -/
theorem smallExpBvWord_toNat (input : ByteArray)
    (hb : baseSize input ≤ 32) :
    (smallExpBvWord input).toNat =
      Precompile.bytesToNatPadded input 96 (baseSize input) := by
  unfold smallExpBvWord
  exact smallExpValue_toNat input 96 (baseSize input) hb

/-- The computed modulus word is the declared-width value. -/
theorem smallExpMvWord_toNat (input : ByteArray)
    (hb : baseSize input ≤ 32) (he : exponentSize input ≤ 32)
    (hm : modulusSize input ≤ 32) :
    (smallExpMvWord input).toNat =
      Precompile.bytesToNatPadded input
        (96 + baseSize input + exponentSize input) (modulusSize input) := by
  unfold smallExpMvWord
  have hoff : (UInt256.ofNat 96 + UInt256.ofNat (exponentSize input) +
      UInt256.ofNat (baseSize input)).toNat =
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

theorem smallExpFinal_isDone (template : State) (input : ByteArray)
    (active : Nat) (rest : List UInt256)
    (hcall : template.callStack = []) :
    (smallExpFinal template input active rest).isDone = true := by
  unfold smallExpFinal
  split <;>
    simp [smallExpReturned, State.isDone, State.isHalted, State.isRunning,
      hcall]

/-- On a small-exponent hit the specification reduces to the decided word:
one when the exponent is zero and the modulus exceeds one, the base word when
the exponent is one. -/
theorem spec_smallExp (input : ByteArray) (hsmall : SmallExpGuard input) :
    spec input = if Precompile.bytesToNatPadded input (96 + baseSize input)
        (exponentSize input) = 0 then
      Precompile.natToBytes (if 1 < Precompile.bytesToNatPadded input
          (96 + baseSize input + exponentSize input) (modulusSize input)
        then 1 else 0) (modulusSize input)
    else Precompile.natToBytes (Precompile.bytesToNatPadded input 96
        (baseSize input)) (modulusSize input) := by
  obtain ⟨hb32, he32, hm32, hev⟩ := hsmall
  unfold spec
  dsimp only
  by_cases hm0 : modulusSize input = 0
  · rw [if_pos hm0]
    rcases hev with hev0 | ⟨hev1, hbm⟩
    · rw [if_pos hev0, hm0, natToBytes_zero]
    · rw [if_neg (by omega : ¬ Precompile.bytesToNatPadded input
          (96 + baseSize input) (exponentSize input) = 0), hm0,
        natToBytes_zero]
  · rw [if_neg hm0]
    dsimp only
    rcases hev with hev0 | ⟨hev1, hbm⟩
    · rw [if_pos hev0, hev0, modPow_zero]
    · rw [if_neg (by omega : ¬ Precompile.bytesToNatPadded input
          (96 + baseSize input) (exponentSize input) = 0), hev1,
        modPow_one _ _ hbm]

theorem smallExpFinal_result (template : State) (input : ByteArray)
    (active : Nat) (rest : List UInt256) (hsmall : SmallExpGuard input) :
    (smallExpFinal template input active rest).toResult =
      .returned (spec input) := by
  obtain ⟨hb32, he32, hm32, hev⟩ := hsmall
  rw [spec_smallExp input hsmall]
  unfold smallExpFinal
  rcases hev with hev0 | ⟨hev1, hbm⟩
  · rw [if_pos hev0]
    rw [smallExpReturned_result template _ _ _ _ _ (modulusSize input) rfl
      hm32]
    rw [Word.word_toNat_lt, smallExpMvWord_toNat input hb32 he32 hm32,
      Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt (by norm_num : (1:Nat) < 2 ^ 256)]
  · rw [if_neg (by omega : ¬ Precompile.bytesToNatPadded input
        (96 + baseSize input) (exponentSize input) = 0)]
    rw [smallExpReturned_result template _ _ _ _ _ (modulusSize input) rfl
      hm32]
    rw [smallExpBvWord_toNat input hb32]


theorem modPow_zero (b m : Nat) :
    Precompile.modPow b 0 m = if 1 < m then 1 else 0 := by
  unfold Precompile.modPow
  by_cases h0 : m = 0
  · simp [h0]
  · by_cases h1 : m = 1
    · simp [h1]
    · have hm : 1 < m := by omega
      simp [h0, h1, hm, Precompile.modPowAux]

theorem modPow_one (b m : Nat) (h : b < m) :
    Precompile.modPow b 1 m = b := by
  have hm : 1 < m := by omega
  unfold Precompile.modPow
  rw [if_neg (by omega : m ≠ 0), if_neg (by omega : m ≠ 1)]
  show Precompile.modPowAux b 1 m 1 = b
  unfold Precompile.modPowAux
  rw [dif_neg (by norm_num : ¬ (1:Nat) = 0)]
  rw [show (1:Nat) % 2 = 1 by norm_num, if_pos rfl]
  rw [show (1:Nat) / 2 = 0 by norm_num]
  unfold Precompile.modPowAux
  rw [dif_pos rfl]
  rw [Nat.one_mul]
  exact Nat.mod_eq_of_lt h

/-- Certified locations and jump facts for the appended small-exponent
block. -/
structure SmallExpPaths (artifact : ProgramArtifact) (fork : Fork) where
  guard : WindowTwentyOneBinding.Block artifact fork 5312 smallExpGuardProgram
  loadE : WindowTwentyOneBinding.Block artifact fork 5337 smallExpLoadEProgram
  loadM : WindowTwentyOneBinding.Block artifact fork 5358 smallExpLoadMProgram
  zero : WindowTwentyOneBinding.Block artifact fork 5389 smallExpZeroProgram
  one : WindowTwentyOneBinding.Block artifact fork 5404 smallExpOneProgram
  bail5 : WindowTwentyOneBinding.Block artifact fork 5424 smallExpBail5Program
  bail4 : WindowTwentyOneBinding.Block artifact fork 5427 smallExpBail4Program
  missJump : Decode.isValidJumpDest artifact.code 5304 = true
  oneJump : Decode.isValidJumpDest artifact.code 5404 = true
  bail5Jump : Decode.isValidJumpDest artifact.code 5424 = true
  bail4Jump : Decode.isValidJumpDest artifact.code 5427 = true

end Challenge.Modexp.Submission.Proofs.Bytecode.EarlyWordSmallExp
