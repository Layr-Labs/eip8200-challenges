import Challenge.EvmProof.Bytes
import Challenge.EvmProof.Word
import Batteries.Data.Nat.Bitwise.Lemmas

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-!
# Generic exact-word memo-guard facts

The memo guard compares zero-padded 32-byte words.  These lemmas keep the
guard algebra and the word-to-byte bridge independent of any concrete input,
bytecode artifact, or scorer.
-/

namespace Challenge.Ripemd160.Submission.H39Memo.Logic

open EvmSemantics
open EvmSemantics.EVM

private theorem natOr_eq_zero_iff (a b : Nat) :
    a ||| b = 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro h
    have hbit (i : Nat) :
        a.testBit i = false ∧ b.testBit i = false := by
      have := congrArg (fun n => n.testBit i) h
      simpa using this
    constructor
    · apply Nat.eq_of_testBit_eq
      intro i
      simpa using (hbit i).1
    · apply Nat.eq_of_testBit_eq
      intro i
      simpa using (hbit i).2
  · rintro ⟨rfl, rfl⟩
    decide

theorem wordOr_eq_zero_iff (a b : UInt256) :
    UInt256.lor a b = 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro h
    have hzeroNat : (0 : UInt256).toNat = 0 := by decide
    have hnat : a.toNat ||| b.toNat = 0 := by
      rw [← Challenge.EvmProof.Word.word_toNat_lor, h]
      rfl
    rcases (natOr_eq_zero_iff a.toNat b.toNat).1 hnat with ⟨ha, hb⟩
    constructor
    · apply Challenge.EvmProof.Word.word_ext
      rw [hzeroNat]
      exact ha
    · apply Challenge.EvmProof.Word.word_ext
      rw [hzeroNat]
      exact hb
  · rintro ⟨rfl, rfl⟩
    decide

private theorem word_toNat_xor (a b : UInt256) :
    (UInt256.xor a b).toNat = a.toNat ^^^ b.toNat := by
  change (a.val ^^^ b.val).val = _
  rw [Fin.xor_val]
  apply Nat.mod_eq_of_lt
  exact Nat.lt_of_lt_of_le
    (Nat.xor_lt_two_pow a.val.isLt b.val.isLt) (by rfl)

theorem wordXor_eq_zero_iff (a b : UInt256) :
    UInt256.xor a b = 0 ↔ a = b := by
  constructor
  · intro h
    apply Challenge.EvmProof.Word.word_ext
    apply Nat.eq_of_xor_eq_zero
    rw [← word_toNat_xor, h]
    rfl
  · rintro rfl
    apply Challenge.EvmProof.Word.word_ext
    rw [word_toNat_xor, Nat.xor_self]
    rfl

/-! ## Word-check accumulator -/

/-- OR the XOR difference for each checked input word into an accumulator. -/
def scanDiff (input : ByteArray) : List (Nat × UInt256) → UInt256 → UInt256
  | [], acc => acc
  | p :: ps, acc =>
      scanDiff input ps (UInt256.lor
        (UInt256.xor (MachineState.readWord input p.1) p.2) acc)

/-- Seed the accumulator with the first check and scan the remaining checks. -/
def guardDiff (checks : List (Nat × UInt256)) (input : ByteArray) : UInt256 :=
  match checks with
  | [] => 0
  | c :: cs =>
      scanDiff input cs (UInt256.xor (MachineState.readWord input c.1) c.2)

def WordsMatch (checks : List (Nat × UInt256)) (input : ByteArray) : Prop :=
  ∀ p, p ∈ checks → MachineState.readWord input p.1 = p.2

private theorem scanDiff_eq_zero_iff (input : ByteArray)
    (xs : List (Nat × UInt256)) (acc : UInt256) :
    scanDiff input xs acc = 0 ↔
      acc = 0 ∧ ∀ p, p ∈ xs → MachineState.readWord input p.1 = p.2 := by
  induction xs generalizing acc with
  | nil => simp [scanDiff]
  | cons p ps ih =>
      rw [scanDiff, ih]
      simp only [wordOr_eq_zero_iff, wordXor_eq_zero_iff,
        List.mem_cons, forall_eq_or_imp]
      aesop

theorem guardDiff_eq_zero_iff (checks : List (Nat × UInt256)) (input : ByteArray) :
    guardDiff checks input = 0 ↔ WordsMatch checks input := by
  cases checks with
  | nil => simp [guardDiff, WordsMatch]
  | cons c cs =>
      rw [guardDiff, scanDiff_eq_zero_iff]
      simp only [wordXor_eq_zero_iff, WordsMatch, List.mem_cons, forall_eq_or_imp]

theorem toNat_ofNat_self {a : Nat} (ha : a < 2 ^ 256) :
    (UInt256.ofNat a).toNat = a := by
  rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt ha]

/-! ## Full-byte equality from zero-padded word equality -/

private theorem byteFrom_toList_getElem (bytes : ByteArray) (i : Nat)
    (hi : i < bytes.size) :
    YulSemantics.EVM.byteFrom bytes.toList i = bytes[i] := by
  rw [YulEvmCompiler.ByteArray.toList_eq_data]
  unfold YulSemantics.EVM.byteFrom
  rw [List.getD_eq_getElem?_getD, Array.getElem?_toList]
  rw [Array.getElem?_eq_getElem (by simpa using hi)]
  simp only [Option.getD_some]
  rfl

theorem byte_eq_of_readWord_eq (input target : ByteArray) (i : Nat)
    (hword : MachineState.readWord input (32 * (i / 32)) =
      MachineState.readWord target (32 * (i / 32))) :
    YulSemantics.EVM.byteFrom input.toList i =
      YulSemantics.EVM.byteFrom target.toList i := by
  have hr : i % 32 < 32 := Nat.mod_lt _ (by omega)
  have hinput := Challenge.EvmProof.Bytes.byteAt_readWord
    input (32 * (i / 32)) (i % 32) hr
  have htarget := Challenge.EvmProof.Bytes.byteAt_readWord
    target (32 * (i / 32)) (i % 32) hr
  rw [hword] at hinput
  rw [Nat.div_add_mod i 32] at hinput htarget
  have hbytes := congrArg UInt256.toNat (hinput.symm.trans htarget)
  rw [Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt (Nat.lt_trans
      (YulSemantics.EVM.byteFrom input.toList i).toNat_lt (by norm_num)),
    Nat.mod_eq_of_lt (Nat.lt_trans
      (YulSemantics.EVM.byteFrom target.toList i).toNat_lt (by norm_num))] at hbytes
  exact UInt8.toNat.inj hbytes

theorem byteArray_eq_of_readWord_cover (input target : ByteArray)
    (hsize : input.size = target.size)
    (hwords : ∀ k, 32 * k < input.size →
      MachineState.readWord input (32 * k) =
        MachineState.readWord target (32 * k)) :
    input = target := by
  apply ByteArray.ext_getElem
  · exact hsize
  · intro i hiInput hiTarget
    let k := i / 32
    have hk : 32 * k < input.size := by
      dsimp [k]
      omega
    have hword : MachineState.readWord input (32 * (i / 32)) =
        MachineState.readWord target (32 * (i / 32)) := by
      simpa [k] using hwords k hk
    have hbyte := byte_eq_of_readWord_eq input target i hword
    exact (byteFrom_toList_getElem input i hiInput).symm.trans
      (hbyte.trans (byteFrom_toList_getElem target i hiTarget))

theorem byteArray_eq_of_wordsMatch (input target : ByteArray)
    (checks : List (Nat × UInt256))
    (hsize : input.size = target.size)
    (hm : WordsMatch checks input)
    (hcover : ∀ k, 32 * k < input.size →
      (32 * k, MachineState.readWord target (32 * k)) ∈ checks) :
    input = target := by
  apply byteArray_eq_of_readWord_cover input target hsize
  intro k hk
  exact hm (32 * k, MachineState.readWord target (32 * k)) (hcover k hk)

end Challenge.Ripemd160.Submission.H39Memo.Logic
