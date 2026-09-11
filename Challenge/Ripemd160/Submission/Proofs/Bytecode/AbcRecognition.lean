import Challenge.Ripemd160.Submission.Proofs.Bytecode.AbcInputData
import Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputLogic
import Challenge.EvmProof.Bytes
import Challenge.EvmProof.Word
import Challenge.EvmProof.Memory

/-!
# Guard soundness for the `abc` fast path

`Correct` is universal over all calldata, so the guard must **provably** imply
the input is exactly the three bytes `0x61 0x62 0x63`.

The guard performs two tests:

* `CALLDATASIZE == 3`   (instructions 4092-4096, pc `0x1470`-`0x1477`)
* `CALLDATALOAD 0 == abcWord`  (instructions 4097-4102, pc `0x1478`-`0x149f`)

Because `3 ≤ 32`, a single zero-padded word read covers the whole input, so the
two together pin the calldata down to one value.  `input_eq_abc` is exactly that
statement, and it does not depend on how control reached the arm.

Provenance: `byteFrom_toList_getElem`, `byte_eq_of_readWord_eq`,
`byteArray_eq_of_readWord_cover` and `input_eq_abc` are lifted from
`Challenge/Ripemd160/Submission/H39Memo/{Logic,Correct}.lean` at commit
`3dad8ba6`, submission `cf170158-635a-4916-a3ca-220a0d3a4099`, co-authored by
Amal-David.  They are artifact-independent (no program counter, instruction
index or bytecode constant occurs in them), which is why they transfer verbatim
from that 4,178-byte artifact to this 5,306-byte one.
-/

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.AbcRecognition

open EvmSemantics EvmSemantics.EVM
open AbcInputData

private theorem byteFrom_toList_getElem (bytes : ByteArray) (i : Nat)
    (hi : i < bytes.size) :
    YulSemantics.EVM.byteFrom bytes.toList i = bytes[i] := by
  rw [YulEvmCompiler.ByteArray.toList_eq_data]
  unfold YulSemantics.EVM.byteFrom
  rw [List.getD_eq_getElem?_getD, Array.getElem?_toList]
  rw [Array.getElem?_eq_getElem (by simpa using hi)]
  simp only [Option.getD_some]
  rfl

/-- Equal zero-padded words give equal bytes inside those words. -/
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

/-- Two byte arrays of equal size agreeing on every covering 32-byte word are
equal. -/
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

/-- The literal `"abc"` reads back as the guard's comparison word. -/
theorem readWord_abcInput : MachineState.readWord abcInput 0 = abcWord := by
  apply Challenge.EvmProof.Word.word_ext
  rw [Challenge.EvmProof.Bytes.readWord_toNat]
  change Data.Bytes.bytesToBigEndianNat (MachineState.readPadded abcInput 0 32) = _
  rw [← Challenge.EvmProof.Bytes.bytesNat_toList,
    Challenge.EvmProof.Bytes.readPadded_toList,
    YulEvmCompiler.ByteArray.toList_eq_data]
  decide

/-- **Guard soundness.**  Passing both tests forces the calldata to be exactly
the three bytes `0x61 0x62 0x63`. -/
theorem input_eq_abc (input : ByteArray) (hsize : input.size = 3)
    (hword : MachineState.readWord input 0 = abcWord) :
    input = abcInput := by
  apply byteArray_eq_of_readWord_cover input abcInput
  · exact hsize.trans abcInput_size.symm
  · intro k hk
    have hk0 : k = 0 := by omega
    subst k
    simpa using hword.trans readWord_abcInput.symm

#print axioms input_eq_abc

/-! ## The fused empty/`abc` condition

The arm's single test is
`condition input = (leadWord input ⊻ size · 0x207621) ∨ (size ≫ 2)`.
`size ≫ 2` vanishes exactly on inputs shorter than four bytes; on those,
`size · 0x207621` is `0` for the empty input and `0x616263` for `"abc"`, and no
other sub-four-byte input can equal it because the zero-padded tail bytes of
`leadWord` would have to be nonzero.  `zero_cases` is that case analysis.

Provenance: `leadWord`, `condition`, `prefix_toNat`, `input_eq_empty`,
`leadWord_empty`, `leadWord_abc`, `condition_empty`, `condition_abc` and
`zero_cases` are ported from `TinyGuardLogic.lean` at commit `7c9d3ca2`
(submission `819379e5`, co-authored by terrapinelf), retargeted from
`TinyABCSpec.inputBytes` to `AbcInputData.abcInput`. -/

/-- The top three bytes of the first calldata word. -/
def leadWord (input : ByteArray) : UInt256 :=
  UInt256.shiftRight (MachineState.readWord input 0) (UInt256.ofNat 232)

/-- The arm's single fused test: zero iff the input is empty or `"abc"`. -/
def condition (input : ByteArray) : UInt256 :=
  UInt256.lor (UInt256.xor (leadWord input)
    (UInt256.mul (UInt256.ofNat input.size) (UInt256.ofNat 0x207621)))
    (UInt256.shiftRight (UInt256.ofNat input.size) (UInt256.ofNat 2))

/-- The size gate: `size ≫ 2` is zero exactly below four bytes. -/
def sizeWord (input : ByteArray) : UInt256 :=
  UInt256.shiftRight (UInt256.ofNat input.size) (UInt256.ofNat 2)

/-- The content mix: `leadWord ⊻ size · 0x207621`. -/
def mixWord (input : ByteArray) : UInt256 :=
  UInt256.xor (leadWord input) (UInt256.mul (UInt256.ofNat input.size) (UInt256.ofNat 0x207621))

theorem condition_split (input : ByteArray) :
    condition input = UInt256.lor (mixWord input) (sizeWord input) := rfl

private def byte (input : ByteArray) (i : Nat) : UInt8 :=
  YulSemantics.EVM.byteFrom input.toList i

private theorem byte_getD (input : ByteArray) (i : Nat) :
    byte input i = input[i]?.getD 0 := by
  rw [byte, YulEvmCompiler.ByteArray.toList_eq_data]
  simp [YulSemantics.EVM.byteFrom, List.getD_eq_getElem?_getD]
  rfl

private theorem prefix_toNat (input : ByteArray) :
    (leadWord input).toNat = (byte input 0).toNat * 65536 +
      (byte input 1).toNat * 256 + (byte input 2).toNat := by
  have h := Challenge.EvmProof.Bytes.shiftRight_readWord input 0 3 (by decide) (by decide)
  change leadWord input = UInt256.ofNat (EvmSemantics.EVM.Precompile.bytesToNatPadded input 0 3) at h
  rw [h, Challenge.EvmProof.Word.word_toNat_ofNat]
  have hb := Challenge.EvmProof.Bytes.bytesToNatPadded_lt_pow input 0 3
  rw [Nat.mod_eq_of_lt (Nat.lt_trans hb (by norm_num))]
  norm_num [Challenge.EvmProof.Bytes.bytesToNatPadded_succ, byte,
    Nat.mul_add, Nat.add_mul, Nat.mul_assoc]

theorem input_eq_empty (input : ByteArray) (h : input.size = 0) :
    input = ByteArray.empty := by
  apply ByteArray.ext_getElem
  · exact h
  · intro i hi _
    omega

private theorem leadWord_empty : leadWord ByteArray.empty = 0 := by
  apply Challenge.EvmProof.Word.word_ext
  rw [prefix_toNat]
  norm_num [byte, YulSemantics.EVM.byteFrom, YulEvmCompiler.ByteArray.toList_eq_data,
    Challenge.EvmProof.Word.word_toNat_ofNat, UInt256.toNat]
  decide

private theorem leadWord_abc : leadWord abcInput = UInt256.ofNat 0x616263 := by
  apply Challenge.EvmProof.Word.word_ext
  rw [prefix_toNat]
  have h0 : byte abcInput 0 = 0x61 := byteFrom_toList_getElem abcInput 0 (by decide)
  have h1 : byte abcInput 1 = 0x62 := byteFrom_toList_getElem abcInput 1 (by decide)
  have h2 : byte abcInput 2 = 0x63 := byteFrom_toList_getElem abcInput 2 (by decide)
  rw [h0, h1, h2]
  decide

theorem condition_empty : condition ByteArray.empty = 0 := by
  unfold condition
  rw [leadWord_empty]
  decide

theorem condition_abc : condition abcInput = 0 := by
  unfold condition
  rw [leadWord_abc]
  decide

/-- **Fused guard soundness.**  `condition input = 0` iff the calldata is the
empty input or exactly `"abc"`. -/
theorem zero_cases (input : ByteArray) (hfit : CalldataFits input)
    (hz : condition input = 0) : input = ByteArray.empty ∨ input = abcInput := by
  rcases (KnownInputLogic.wordOr_eq_zero_iff _ _).mp hz with ⟨hp, hn⟩
  have hp := (KnownInputLogic.wordXor_eq_zero_iff _ _).mp hp
  have hn := congrArg UInt256.toNat hn
  rw [Challenge.EvmProof.Word.shiftRight_toNat _ (by decide),
    Challenge.EvmProof.Word.word_toNat_ofNat,
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
    have hz2 : byte input 2 = 0 := by
      rw [byte_getD]
      exact Challenge.EvmProof.Memory.getElem?_getD_eq_zero_of_size_le input 2 (by omega)
    rw [hz2] at hv
    norm_num [Challenge.EvmProof.Word.word_toNat_ofNat] at hv
    omega
  · rw [hs] at hp
    change leadWord input = UInt256.ofNat 4254786 at hp
    have hv := congrArg UInt256.toNat hp
    rw [prefix_toNat] at hv
    have hz2 : byte input 2 = 0 := by
      rw [byte_getD]
      exact Challenge.EvmProof.Memory.getElem?_getD_eq_zero_of_size_le input 2 (by omega)
    rw [hz2] at hv
    norm_num [Challenge.EvmProof.Word.word_toNat_ofNat] at hv
    omega
  · right
    rw [hs] at hp
    change leadWord input = UInt256.ofNat 6382179 at hp
    have hv := congrArg UInt256.toNat hp
    rw [prefix_toNat] at hv
    norm_num [Challenge.EvmProof.Word.word_toNat_ofNat] at hv
    have h0 : (byte input 0).toNat = 97 := by omega
    have h1 : (byte input 1).toNat = 98 := by omega
    have h2 : (byte input 2).toNat = 99 := by omega
    apply ByteArray.ext_getElem hs
    intro i hi hir
    have hi3 : i < 3 := by omega
    rw [← byteFrom_toList_getElem input i hi]
    change byte input i = _
    interval_cases i <;> apply UInt8.ext
    · exact h0
    · exact h1
    · exact h2

#print axioms zero_cases

end Challenge.Ripemd160.Submission.Proofs.Bytecode.AbcRecognition
