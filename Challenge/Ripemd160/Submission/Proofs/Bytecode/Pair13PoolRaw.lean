import Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80SiteCommon
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerRawCommon
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Stagger144Active
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RawExpressionAC
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairStoreMerge
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Pair13PoolRaw
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace PairedScheduleMemory

/-- `2 ^ 144 + 1`: the dual-lane broadcast constant.  S51 no longer pushes it (the
scratch duplicates the lanes instead), but the table image is still described by it. -/
def coefficient : UInt256 := UInt256.ofNat 22300745198530623141535718272648361505980417

/-- The two four-byte lanes the schedule loads keep: bytes `10..14` and `28..32`. -/
def poolMask : UInt256 := UInt256.ofNat 95780971281817308448866066055358605703522837925462015

/-- The sixteen load addresses, in schedule-word order. -/
def poolAddr : Nat → Nat
  | 0 => 0    | 1 => 4    | 2 => 8    | 3 => 12
  | 4 => 34   | 5 => 38   | 6 => 42   | 7 => 46
  | 8 => 68   | 9 => 72   | 10 => 76  | 11 => 80
  | 12 => 102 | 13 => 106 | 14 => 110 | _ => 114

def rawLoad (memory : ByteArray) (i : Nat) : UInt256 :=
  MachineState.readWord memory (poolAddr i)

/-- Word 3's upper lane falls inside the zero prefix `[0,28)`, so it is rebuilt with
`DUP1; SHL 144; OR` instead of being read twice. -/
def cleanPoolWord (memory : ByteArray) (i : Nat) : UInt256 :=
  if i = 0 ∨ i = 1 ∨ i = 2 then rawLoad memory i
  else if i = 3 then
    UInt256.lor (UInt256.shiftLeft (UInt256.land poolMask (rawLoad memory 3)) (UInt256.ofNat 144))
      (UInt256.land poolMask (rawLoad memory 3))
  else UInt256.land poolMask (rawLoad memory i)

/-- Keep word 11 masked: the terminal paired round receives an unmasked D.
Word 9's mask is dropped at the bytecode level (S51 pops the mask instead of
applying it); like the eight other unmasked sources it is normalized by the
ordinary round-sum mask, and `PoolCertificates.slack_sources` re-witnesses the
three table slots whose zero byte word 9 now occupies. -/
def poolWord (memory : ByteArray) (i : Nat) : UInt256 :=
  if i = 3 then
    UInt256.lor (UInt256.shiftLeft (rawLoad memory 3) (UInt256.ofNat 144)) (rawLoad memory 3)
  else if i ∈ [0, 1, 2, 8, 9, 10, 12, 13, 14, 15] then rawLoad memory i
  else UInt256.land poolMask (rawLoad memory i)

/-- The two sixteen-byte copies that duplicate the upper scratch word's lanes. -/
def copiedOnce (memory : ByteArray) : ByteArray :=
  MachineState.writeBytes memory (MachineState.readPadded memory 96 16) 78

def copied (memory : ByteArray) : ByteArray :=
  MachineState.writeBytes (copiedOnce memory)
    (MachineState.readPadded (copiedOnce memory) 112 16) 130

def poolStack (words : Nat → UInt256) (rho : List UInt256) : List UInt256 :=
  [ words 9, words 0, words 3, words 8, words 11, words 5, words 15, words 1,
    words 4, words 2, words 13, words 10, words 7, words 6, words 12, words 14 ] ++ rho

theorem copy_active_preserved (current : UInt256) (o1 o2 : Nat)
    (hc : 34 ≤ current.toNat) (h1 : o1 ≤ 1000) (h2 : o2 ≤ 1000) :
    UInt256.ofNat (MachineState.activeWordsAfter
      (MachineState.activeWordsAfter current.toNat o1 16) o2 16) = current := by
  have h : MachineState.activeWordsAfter current.toNat o1 16 = current.toNat := by
    simp only [MachineState.activeWordsAfter, if_neg (by decide : (16 : Nat) ≠ 0)]
    exact Nat.max_eq_left (by omega)
  rw [h]
  have h2' : MachineState.activeWordsAfter current.toNat o2 16 = current.toNat := by
    simp only [MachineState.activeWordsAfter, if_neg (by decide : (16 : Nat) ≠ 0)]
    exact Nat.max_eq_left (by omega)
  rw [h2']
  exact (Word.word_eq_ofNat_toNat _).symm

def template : List Instr :=
  [ .push ⟨1, by decide⟩ (UInt256.ofNat 16),
    .op (.Dup ⟨0, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 96),
    .push ⟨1, by decide⟩ (UInt256.ofNat 78),
    .op .MCOPY,
    .push ⟨1, by decide⟩ (UInt256.ofNat 112),
    .push ⟨1, by decide⟩ (UInt256.ofNat 130),
    .op .MCOPY,
    .push ⟨22, by decide⟩ (UInt256.ofNat 95780971281817308448866066055358605703522837925462015),
    .push ⟨1, by decide⟩ (UInt256.ofNat 102),
    .op .MLOAD,
    .op (.Dup ⟨1, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 42),
    .op .MLOAD,
    .op .AND,
    .push ⟨1, by decide⟩ (UInt256.ofNat 46),
    .op .MLOAD,
    .op (.Dup ⟨3, by decide⟩),
    .op .AND,
    .push ⟨1, by decide⟩ (UInt256.ofNat 76),
    .op .MLOAD,
    .push ⟨1, by decide⟩ (UInt256.ofNat 106),
    .op .MLOAD,
    .push ⟨1, by decide⟩ (UInt256.ofNat 8),
    .op .MLOAD,
    .push ⟨1, by decide⟩ (UInt256.ofNat 34),
    .op .MLOAD,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND,
    .push ⟨1, by decide⟩ (UInt256.ofNat 4),
    .op .MLOAD,
    .push ⟨1, by decide⟩ (UInt256.ofNat 114),
    .op .MLOAD,
    .op (.Dup ⟨9, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 38),
    .op .MLOAD,
    .op .AND,
    .push ⟨1, by decide⟩ (UInt256.ofNat 110),
    .op .MLOAD,
    .op (.Swap ⟨10, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 80),
    .op .MLOAD,
    .op .AND,
    .push ⟨1, by decide⟩ (UInt256.ofNat 68),
    .op .MLOAD,
    .push ⟨3, by decide⟩ (UInt256.ofNat 12),
    .op .MLOAD,
    .op (.Dup ⟨0, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 144),
    .op .SHL,
    .op .OR,
    .push ⟨0, by decide⟩ (UInt256.ofNat 0),
    .op .MLOAD,
    .push ⟨1, by decide⟩ (UInt256.ofNat 72),
    .op .MLOAD ]

theorem run_actual_of_small (s : State) (pc : UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 34 ≤ s.activeWords.toNat) :
    runInstrSeq template {s with pc := pc, stack := rho} =
      some {s with
        pc := pcAfter pc template
        stack := poolStack (poolWord (copied s.memory)) rho
        memory := copied s.memory} := by
  have hbase : rho.length < 1024 := by omega
  have hzero : ({val := 0} : UInt256).toNat = 0 := rfl
  have hcap (n : Nat) (hn : n ≤ 40) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 1056) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) = s.activeWords :=
    Stagger144Active.word_active_preserved_of_small s.activeWords address hactive haddress
  have hactiveCopy (o1 o2 : Nat) (h1 : o1 ≤ 1000) (h2 : o2 ≤ 1000) :
      UInt256.ofNat (MachineState.activeWordsAfter
        (MachineState.activeWordsAfter s.activeWords.toNat o1 16) o2 16) = s.activeWords :=
    copy_active_preserved s.activeWords o1 o2 hactive h1 h2
  simp (config := { maxSteps := 900000 }) (discharger := omega)
    [template, poolStack, poolWord, poolMask, rawLoad, poolAddr, copied, copiedOnce, runInstrSeq,
     DataStepper.runInstr, pcAfter, UInt256.succ, Instr.size, List.exchange,
     List.getElem?_cons_zero, Nat.add_assoc, hrun, hbase, hzero, hcap,
     State.activeWordsAfterUInt256, State.activeWordsAfterUInt256_2, hactiveAt, hactiveCopy,
     Word.word_toNat_ofNat, Word.literal_eq_ofNat, RawExpressionAC.land_comm]
  all_goals repeat first | apply And.intro | rfl

theorem run_actual (s : State) (pc : UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 35 ≤ s.activeWords.toNat) :
    runInstrSeq template {s with pc := pc, stack := rho} =
      some {s with
        pc := pcAfter pc template
        stack := poolStack (poolWord (copied s.memory)) rho
        memory := copied s.memory} := by
  exact run_actual_of_small s pc rho hstack hrun (by omega)

/-! ### The dual-lane mask

`poolMask` keeps bytes `10..14` and `28..32` of the loaded word.  Where the scratch has
duplicated a four-byte field eighteen bytes apart, those two lanes agree and the masked load
IS the `2 ^ 144 + 1` broadcast the table wants, with no multiply. -/

theorem coefficient_toNat : coefficient.toNat = 2 ^ 144 + 1 := by
  rw [coefficient, Word.word_toNat_ofNat]
  norm_num

theorem mul_coefficient_toNat (w : UInt256) (hw : w.toNat < 2 ^ 32) :
    (UInt256.mul coefficient w).toNat = 2 ^ 144 * w.toNat + w.toNat := by
  rw [PairStoreMerge.mul_toNat, coefficient_toNat]
  have hb : (2 ^ 144 + 1) * w.toNat < 2 ^ 256 := by
    rw [Nat.mul_comm]
    exact (PairStoreMerge.pack_nat_bound _ hw).trans (by norm_num)
  rw [Nat.mod_eq_of_lt hb, Nat.add_mul, Nat.one_mul]

private theorem mask_split : (95780971281817308448866066055358605703522837925462015 : Nat)
    = 2 ^ 144 * (2 ^ 32 - 1) + (2 ^ 32 - 1) := by norm_num

theorem land_poolMask_nat (x wlo whi : Nat) (hlo' : wlo < 2 ^ 32) (hhi' : whi < 2 ^ 32)
    (hlo : x % 2 ^ 32 = wlo) (hhi : x / 2 ^ 144 % 2 ^ 32 = whi) :
    x &&& 95780971281817308448866066055358605703522837925462015 = 2 ^ 144 * whi + wlo := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [mask_split, Nat.testBit_and,
    Nat.testBit_two_pow_mul_add (2 ^ 32 - 1) (by norm_num : (2:Nat) ^ 32 - 1 < 2 ^ 144) i,
    Nat.testBit_two_pow_mul_add whi (by omega : wlo < 2 ^ 144) i]
  simp only [Nat.testBit_two_pow_sub_one]
  by_cases h144 : i < 144
  · rw [if_pos h144, if_pos h144]
    by_cases h32 : i < 32
    · rw [decide_eq_true h32, Bool.and_true, ← hlo, Nat.testBit_mod_two_pow,
        decide_eq_true h32, Bool.true_and]
    · rw [decide_eq_false h32, Bool.and_false]
      exact (Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hlo'
        (Nat.pow_le_pow_right (by decide) (by omega)))).symm
  · rw [if_neg h144, if_neg h144]
    by_cases h176 : i - 144 < 32
    · rw [decide_eq_true h176, Bool.and_true, ← hhi, Nat.testBit_mod_two_pow,
        decide_eq_true h176, Bool.true_and, Nat.testBit_div_two_pow,
        show i - 144 + 144 = i by omega]
    · rw [decide_eq_false h176, Bool.and_false]
      exact (Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hhi'
        (Nat.pow_le_pow_right (by decide) (by omega)))).symm

theorem lor_mul_eq (a b : Nat) (hb : b < 2 ^ 144) : a * 2 ^ 144 ||| b = 2 ^ 144 * a + b := by
  apply Nat.eq_of_testBit_eq
  intro i
  have ha : a * 2 ^ 144 = 2 ^ 144 * a + 0 := by rw [Nat.mul_comm, Nat.add_zero]
  rw [Nat.testBit_or, ha,
    Nat.testBit_two_pow_mul_add a (by norm_num : (0:Nat) < 2 ^ 144) i,
    Nat.testBit_two_pow_mul_add a (by omega : b < 2 ^ 144) i]
  by_cases h144 : i < 144
  · rw [if_pos h144, if_pos h144, Nat.zero_testBit, Bool.false_or]
  · rw [if_neg h144, if_neg h144]
    have : b.testBit i = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hb (Nat.pow_le_pow_right (by decide) (by omega)))
    rw [this, Bool.or_false]

theorem window_congr (memory : ByteArray) (a b width : Nat)
    (h : ∀ i, i < width → memory[a + i]?.getD 0 = memory[b + i]?.getD 0) :
    Precompile.bytesToNatPadded memory a width = Precompile.bytesToNatPadded memory b width := by
  unfold Precompile.bytesToNatPadded
  congr 1
  apply ByteArray.ext_getElem
  · simp
  · intro i hiA hiB
    rw [← Memory.getD0_eq_getElem _ _ hiA, ← Memory.getD0_eq_getElem _ _ hiB,
      Memory.readPadded_getElem?_getD, Memory.readPadded_getElem?_getD]
    have hi : i < width := by simpa using hiA
    rw [if_pos hi, if_pos hi]
    exact h i hi

theorem lane_lo (memory : ByteArray) (A : Nat) :
    (MachineState.readWord memory A).toNat % 2 ^ 32
      = Precompile.bytesToNatPadded memory (A + 28) 4 := by
  have h := Bytes.bytesToNatPadded_add memory A 28 4
  rw [show (28 : Nat) + 4 = 32 from rfl] at h
  rw [Bytes.readWord_toNat, h, show (2:Nat) ^ 32 = 256 ^ 4 by norm_num,
    Nat.mul_comm, Nat.mul_add_mod]
  exact Nat.mod_eq_of_lt (Bytes.bytesToNatPadded_lt_pow _ _ _)

theorem lane_hi (memory : ByteArray) (A : Nat) :
    (MachineState.readWord memory A).toNat / 2 ^ 144 % 2 ^ 32
      = Precompile.bytesToNatPadded memory (A + 10) 4 := by
  have h14 := Bytes.readWord_shift_toNat memory A 14 (by omega)
  rw [show (32 - 14) * 8 = 144 from rfl, Nat.shiftRight_eq_div_pow] at h14
  have h := Bytes.bytesToNatPadded_add memory A 10 4
  rw [show (10 : Nat) + 4 = 14 from rfl] at h
  rw [h14, h, show (2:Nat) ^ 32 = 256 ^ 4 by norm_num, Nat.mul_comm, Nat.mul_add_mod]
  exact Nat.mod_eq_of_lt (Bytes.bytesToNatPadded_lt_pow _ _ _)

/-- A masked load whose two lanes hold the same four bytes is the broadcast of that field. -/
theorem poolWord_dual (memory : ByteArray) (i : Nat) (hi : 4 ≤ i) (w : UInt256)
    (hw : w.toNat < 2 ^ 32)
    (hlo : Precompile.bytesToNatPadded memory (poolAddr i + 28) 4 = w.toNat)
    (hhi : Precompile.bytesToNatPadded memory (poolAddr i + 10) 4 = w.toNat) :
    cleanPoolWord memory i = UInt256.mul coefficient w := by
  have h0 : ¬ (i = 0 ∨ i = 1 ∨ i = 2) := by omega
  have h3 : ¬ (i = 3) := by omega
  rw [cleanPoolWord, if_neg h0, if_neg h3, rawLoad]
  apply Word.word_ext
  rw [Word.word_toNat_land, poolMask, Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt (by norm_num :
      95780971281817308448866066055358605703522837925462015 < 2 ^ 256),
    Nat.and_comm,
    land_poolMask_nat _ w.toNat w.toNat hw hw (by rw [lane_lo]; exact hlo)
      (by rw [lane_hi]; exact hhi),
    mul_coefficient_toNat w hw]

/-- Word 3's upper lane lies in the zero prefix, so the `DUP1; SHL 144; OR` rebuild
produces the same broadcast. -/
theorem poolWord_three (memory : ByteArray) (w : UInt256) (hw : w.toNat < 2 ^ 32)
    (hlo : Precompile.bytesToNatPadded memory 40 4 = w.toNat)
    (hhi : Precompile.bytesToNatPadded memory 22 4 = 0) :
    cleanPoolWord memory 3 = UInt256.mul coefficient w := by
  have h0 : ¬ ((3:Nat) = 0 ∨ (3:Nat) = 1 ∨ (3:Nat) = 2) := by decide
  have hmask : UInt256.land poolMask (rawLoad memory 3) = w := by
    apply Word.word_ext
    rw [rawLoad, Word.word_toNat_land, poolMask, Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt (by norm_num :
        95780971281817308448866066055358605703522837925462015 < 2 ^ 256),
      Nat.and_comm,
      land_poolMask_nat _ w.toNat 0 hw (by norm_num)
        (by rw [lane_lo]; exact hlo) (by rw [lane_hi]; exact hhi),
      Nat.mul_zero, Nat.zero_add]
  rw [cleanPoolWord, if_neg h0, if_pos rfl, hmask]
  apply Word.word_ext
  have h1 : w.toNat * 2 ^ 144 < 2 ^ 32 * 2 ^ 144 :=
    (Nat.mul_lt_mul_right (by norm_num : 0 < 2 ^ 144)).mpr hw
  have hb : w.toNat * 2 ^ 144 < 2 ^ 256 :=
    Nat.lt_of_lt_of_le h1 (by norm_num)
  have hsl : (UInt256.shiftLeft w (UInt256.ofNat 144)).toNat = w.toNat * 2 ^ 144 := by
    conv_lhs => rw [Word.word_eq_ofNat_toNat w]
    rw [Word.shiftLeft_ofNat (by exact w.val.isLt) (by norm_num) hb, Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt hb]
  rw [Word.word_toNat_lor, mul_coefficient_toNat w hw, hsl,
    lor_mul_eq w.toNat w.toNat (by omega)]

#print axioms run_actual
#print axioms poolWord_dual
#print axioms poolWord_three
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Pair13PoolRaw
