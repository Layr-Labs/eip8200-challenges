import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScanMask
import Challenge.Ripemd160.Submission.Proofs.Bytecode.AbcDigest
import Challenge.Ripemd160.Submission.Proofs.Bytecode.EmptySpec
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.TinyGuardLogic
open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM

def leadWord (input : ByteArray) : UInt256 :=
  UInt256.shiftRight (MachineState.readWord input 0) (UInt256.ofNat 232)
def condition (input : ByteArray) : UInt256 :=
  UInt256.lor (UInt256.xor (leadWord input)
    (UInt256.mul (UInt256.ofNat input.size) (UInt256.ofNat 0x207621)))
    (UInt256.shiftRight (UInt256.ofNat input.size) (UInt256.ofNat 2))
def byte (input : ByteArray) (i : Nat) : UInt8 :=
  YulSemantics.EVM.byteFrom input.toList i

theorem byte_getD (input : ByteArray) (i : Nat) :
    byte input i = input[i]?.getD 0 := by
  rw [byte, YulEvmCompiler.ByteArray.toList_eq_data]
  simp [YulSemantics.EVM.byteFrom, List.getD_eq_getElem?_getD]
  rfl

theorem prefix_toNat (input : ByteArray) :
    (leadWord input).toNat = (byte input 0).toNat * 65536 +
      (byte input 1).toNat * 256 + (byte input 2).toNat := by
  have h := Bytes.shiftRight_readWord input 0 3 (by decide) (by decide)
  change leadWord input = UInt256.ofNat (Precompile.bytesToNatPadded input 0 3) at h
  rw [h, Word.word_toNat_ofNat]
  have hb := Bytes.bytesToNatPadded_lt_pow input 0 3
  rw [Nat.mod_eq_of_lt (Nat.lt_trans hb (by norm_num))]
  norm_num [Bytes.bytesToNatPadded_succ, byte, Nat.mul_add, Nat.add_mul, Nat.mul_assoc]

theorem input_eq_empty (input : ByteArray) (h : input.size = 0) : input = ByteArray.empty := by
  apply ByteArray.ext_getElem
  · exact h
  · intro i hi _
    omega

theorem leadWord_empty : leadWord ByteArray.empty = 0 := by
  apply Word.word_ext
  rw [prefix_toNat]
  norm_num [byte, YulSemantics.EVM.byteFrom, YulEvmCompiler.ByteArray.toList_eq_data,
    AbcInputData.abcInput, Word.word_toNat_ofNat, UInt256.toNat]
  decide
theorem leadWord_abc : leadWord AbcInputData.abcInput = UInt256.ofNat 0x616263 := by
  apply Word.word_ext
  rw [prefix_toNat]
  norm_num [byte, YulSemantics.EVM.byteFrom, YulEvmCompiler.ByteArray.toList_eq_data,
    AbcInputData.abcInput, Word.word_toNat_ofNat, UInt256.toNat]
  decide
theorem condition_empty : condition ByteArray.empty = 0 := by
  unfold condition
  rw [leadWord_empty]
  decide
theorem condition_abc : condition AbcInputData.abcInput = 0 := by
  unfold condition
  rw [leadWord_abc]
  decide

theorem zero_cases (input : ByteArray) (hfit : CalldataFits input)
    (hz : condition input = 0) : input = ByteArray.empty ∨ input = AbcInputData.abcInput := by
  rcases (KnownInputLogic.wordOr_eq_zero_iff _ _).mp hz with ⟨hp, hn⟩
  have hp := (KnownInputLogic.wordXor_eq_zero_iff _ _).mp hp
  have hn := congrArg UInt256.toNat hn
  rw [Word.shiftRight_toNat _ (by decide), Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt (Nat.lt_trans hfit (by norm_num)), Nat.shiftRight_eq_div_pow] at hn
  change input.size / 4 = 0 at hn
  have hsmall : input.size < 4 := by omega
  have b0 := (byte input 0).toNat_lt
  have b1 := (byte input 1).toNat_lt
  have b2 := (byte input 2).toNat_lt
  have hs : input.size = 0 ∨ input.size = 1 ∨ input.size = 2 ∨ input.size = 3 := by omega
  rcases hs with hs | hs | hs | hs
  · exact Or.inl (input_eq_empty input hs)
  · rw [hs] at hp
    change leadWord input = UInt256.ofNat 2127393 at hp
    have hv := congrArg UInt256.toNat hp
    rw [prefix_toNat] at hv
    have hz2 : byte input 2 = 0 := by rw [byte_getD]; exact Memory.getElem?_getD_eq_zero_of_size_le input 2 (by omega)
    rw [hz2] at hv
    norm_num [Word.word_toNat_ofNat] at hv
    omega
  · rw [hs] at hp
    change leadWord input = UInt256.ofNat 4254786 at hp
    have hv := congrArg UInt256.toNat hp
    rw [prefix_toNat] at hv
    have hz2 : byte input 2 = 0 := by rw [byte_getD]; exact Memory.getElem?_getD_eq_zero_of_size_le input 2 (by omega)
    rw [hz2] at hv
    norm_num [Word.word_toNat_ofNat] at hv
    omega
  · right
    rw [hs] at hp
    change leadWord input = UInt256.ofNat 6382179 at hp
    have hv := congrArg UInt256.toNat hp
    rw [prefix_toNat] at hv
    norm_num [Word.word_toNat_ofNat] at hv
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

#print axioms zero_cases
end Challenge.Ripemd160.Submission.Proofs.Bytecode.TinyGuardLogic
