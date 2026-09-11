import Challenge.Ripemd160.Submission.Proofs.Bytecode.AbcInputData
import Challenge.EvmProof.Bytes
import Challenge.EvmProof.Word
import Challenge.EvmProof.Memory

/-!
# Guard soundness for the `abc` fast path

`Correct` is universal over all calldata, so the guard must **provably** imply
the input is exactly the three bytes `0x61 0x62 0x63`.

The guard performs two tests:

* `CALLDATASIZE == 3`   (instructions 4091-4095, pc `0x1470`-`0x1477`)
* `CALLDATALOAD 0 == abcWord`  (instructions 4096-4101, pc `0x1478`-`0x149f`)

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

end Challenge.Ripemd160.Submission.Proofs.Bytecode.AbcRecognition
