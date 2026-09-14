import Challenge.EvmProof.Stepper
import Challenge.EvmProof.Word

attribute [simp]
  Challenge.EvmProof.Word.word_toNat_add
  Challenge.EvmProof.Word.word_toNat_sub
  Challenge.EvmProof.Word.word_toNat_lt
  Challenge.EvmProof.Word.word_toNat_isZero
  Challenge.EvmProof.Word.word_toNat_lor
  Challenge.EvmProof.Word.word_toNat_land
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
/-! Pure fallback state and word utilities; no artifact or located path dependency. -/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.BigC

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- A fallback state: everything but pc, stack, memory and active words is
inherited from the entry state `s`. -/
def st (s : State) (pc : Nat) (stack : List UInt256) (mem : ByteArray)
    (aw : UInt256) : State :=
  { s with pc := UInt256.ofNat pc, stack := stack, memory := mem, activeWords := aw }

/-- A halted fallback state after `RETURN`. -/
def rt (s : State) (pc : Nat) (stack : List UInt256) (mem : ByteArray)
    (aw : UInt256) (out : ByteArray) : State :=
  { s with pc := UInt256.ofNat pc, stack := stack, memory := mem, activeWords := aw,
           halt := .Returned, hReturn := out }

/-- Active words once the fallback has zero-filled its 9248-byte arena. -/
abbrev AW : UInt256 := UInt256.ofNat 289

/-- `2 ^ 256` as the literal that `simp` normalizes to. -/
abbrev LIM : Nat :=
  115792089237316195423570985008687907853269984665640564039457584007913129639936

/-- The bit selected by `MLOAD a; SHL j; PUSH1 255; SHR`. -/
def bitWord (mem : ByteArray) (a j : Nat) : UInt256 :=
  UInt256.shiftRight
    (UInt256.shiftLeft (MachineState.readWord mem a) (UInt256.ofNat j))
    (UInt256.ofNat 255)

/-- Byte `k` of memory as a word (`MLOAD k; PUSH0; BYTE`). -/
def byteW (mem : ByteArray) (k : Nat) : UInt256 :=
  UInt256.byteAt (UInt256.ofNat 0) (MachineState.readWord mem k)

theorem aw_keep (off sz : Nat) (h : off + sz ≤ 9248) :
    MachineState.activeWordsAfter 289 off sz = 289 := by
  unfold MachineState.activeWordsAfter
  split
  · rfl
  · dsimp only
    rw [show Nat.max 289 ((off + sz - 1) / 32 + 1) =
      max 289 ((off + sz - 1) / 32 + 1) from rfl]
    omega

theorem dec_ofNat (i : Nat) (hi : 1 ≤ i) (hi' : i < 2 ^ 256) :
    UInt256.lnot (UInt256.ofNat 0) + UInt256.ofNat i = UInt256.ofNat (i - 1) := by
  apply Challenge.EvmProof.Word.word_ext
  rw [Challenge.EvmProof.Word.word_toNat_add]
  simp only [UInt256.lnot, Challenge.EvmProof.Word.word_toNat_ofNat, UInt256.size]
  have h1 : (2 ^ 256 - 1 - 0 % 2 ^ 256) % 2 ^ 256 = 2 ^ 256 - 1 := by norm_num
  rw [h1, Nat.mod_eq_of_lt hi', Nat.mod_eq_of_lt (by omega : i - 1 < 2 ^ 256)]
  omega

theorem shl3_ofNat (n : Nat) (h : n < 2 ^ 240) :
    UInt256.shiftLeft (UInt256.ofNat n) (UInt256.ofNat 3) = UInt256.ofNat (n * 8) := by
  have := Challenge.EvmProof.Word.shiftLeft_ofNat (value := n) (shift := 3)
    (by omega) (by omega) (by omega)
  simpa using this

theorem shr3_ofNat (n : Nat) (h : n < 2 ^ 256) :
    UInt256.shiftRight (UInt256.ofNat n) (UInt256.ofNat 3) = UInt256.ofNat (n / 8) := by
  have := Challenge.EvmProof.Word.shiftRight_ofNat (value := n) (shift := 3) h (by omega)
  rw [this, Nat.shiftRight_eq_div_pow]

theorem and7_ofNat (n : Nat) (h : n < 2 ^ 256) :
    UInt256.land (UInt256.ofNat 7) (UInt256.ofNat n) = UInt256.ofNat (n % 8) := by
  apply Challenge.EvmProof.Word.word_ext
  rw [Challenge.EvmProof.Word.word_toNat_land]
  simp only [Challenge.EvmProof.Word.word_toNat_ofNat]
  rw [Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt (by norm_num : 7 < 2 ^ 256),
    Nat.mod_eq_of_lt (by omega : n % 8 < 2 ^ 256)]
  rw [show (7 : Nat) = 2 ^ 3 - 1 by norm_num, Nat.and_comm,
    Nat.and_two_pow_sub_one_eq_mod]

theorem eq_ofNat_toNat (a b : Nat) (ha : a < 2 ^ 256) (hb : b < 2 ^ 256) :
    (UInt256.eq (UInt256.ofNat a) (UInt256.ofNat b)).toNat = if a = b then 1 else 0 := by
  unfold UInt256.eq
  simp only [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt ha,
    Nat.mod_eq_of_lt hb]
  split <;> simp

theorem caps (n : Nat) (h : n < 1000) :
    n + 1 < 1024 ∧
    n + 1 + 1 < 1024 ∧
    n + 1 + 1 + 1 < 1024 ∧
    n + 1 + 1 + 1 + 1 < 1024 ∧
    n + 1 + 1 + 1 + 1 + 1 < 1024 ∧
    n + 1 + 1 + 1 + 1 + 1 + 1 < 1024 ∧
    n + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 ∧
    n + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 ∧
    n + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 ∧
    n + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 ∧
    n + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 ∧
    n + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩

theorem zero_lit : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide


end Challenge.Modexp.Submission.Proofs.Bytecode.BigC
