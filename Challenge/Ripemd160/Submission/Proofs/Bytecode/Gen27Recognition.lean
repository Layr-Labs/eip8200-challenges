import Challenge.Ripemd160.Submission.Proofs.Bytecode.Gen27InputData
import Challenge.EvmProof.Bytes
import Challenge.EvmProof.Word
import Challenge.EvmProof.Memory

/-!
# Guard soundness for the generated-vector #27 fast path

`Correct` is universal over all calldata, so the guard must **provably** imply
the input is exactly the 128 bytes of `gen27Input`.

The guard performs five tests:

* `CALLDATASIZE == 128`   (instructions 4115-4120, pc `0x1453`-`0x145c`)
* `CALLDATALOAD (32*k) == gen27Word k` for `k = 0,1,2,3`
  (instructions 4121-4143, pc `0x145d`-`0x14e4`)

Because `128 = 4 * 32`, the four word reads cover the whole input, so the five
tests together pin the calldata down to one value.  `input_eq_gen27` is exactly
that statement, and it does not depend on how control reached the arm.
-/

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Gen27Recognition

open EvmSemantics EvmSemantics.EVM
open Gen27InputData

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

/-- The literal `gen27Input` reads back as the guard's comparison words. -/
theorem readWord_gen27Input0 : MachineState.readWord gen27Input 0 = gen27Word0 := by
  apply Challenge.EvmProof.Word.word_ext
  rw [Challenge.EvmProof.Bytes.readWord_toNat]
  change Data.Bytes.bytesToBigEndianNat (MachineState.readPadded gen27Input 0 32) = _
  rw [← Challenge.EvmProof.Bytes.bytesNat_toList,
    Challenge.EvmProof.Bytes.readPadded_toList,
    YulEvmCompiler.ByteArray.toList_eq_data]
  decide

theorem readWord_gen27Input1 : MachineState.readWord gen27Input 32 = gen27Word1 := by
  apply Challenge.EvmProof.Word.word_ext
  rw [Challenge.EvmProof.Bytes.readWord_toNat]
  change Data.Bytes.bytesToBigEndianNat (MachineState.readPadded gen27Input 32 32) = _
  rw [← Challenge.EvmProof.Bytes.bytesNat_toList,
    Challenge.EvmProof.Bytes.readPadded_toList,
    YulEvmCompiler.ByteArray.toList_eq_data]
  decide

theorem readWord_gen27Input2 : MachineState.readWord gen27Input 64 = gen27Word2 := by
  apply Challenge.EvmProof.Word.word_ext
  rw [Challenge.EvmProof.Bytes.readWord_toNat]
  change Data.Bytes.bytesToBigEndianNat (MachineState.readPadded gen27Input 64 32) = _
  rw [← Challenge.EvmProof.Bytes.bytesNat_toList,
    Challenge.EvmProof.Bytes.readPadded_toList,
    YulEvmCompiler.ByteArray.toList_eq_data]
  decide

theorem readWord_gen27Input3 : MachineState.readWord gen27Input 96 = gen27Word3 := by
  apply Challenge.EvmProof.Word.word_ext
  rw [Challenge.EvmProof.Bytes.readWord_toNat]
  change Data.Bytes.bytesToBigEndianNat (MachineState.readPadded gen27Input 96 32) = _
  rw [← Challenge.EvmProof.Bytes.bytesNat_toList,
    Challenge.EvmProof.Bytes.readPadded_toList,
    YulEvmCompiler.ByteArray.toList_eq_data]
  decide

/-- **Guard soundness.**  Passing the size test and all four word tests forces
the calldata to be exactly `gen27Input`. -/
theorem input_eq_gen27 (input : ByteArray) (hsize : input.size = 128)
    (hword0 : MachineState.readWord input 0 = gen27Word0)
    (hword1 : MachineState.readWord input 32 = gen27Word1)
    (hword2 : MachineState.readWord input 64 = gen27Word2)
    (hword3 : MachineState.readWord input 96 = gen27Word3) :
    input = gen27Input := by
  apply byteArray_eq_of_readWord_cover input gen27Input
  · exact hsize.trans gen27Input_size.symm
  · intro k hk
    have hk' : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases hk' with rfl | rfl | rfl | rfl
    · simpa using hword0.trans readWord_gen27Input0.symm
    · simpa using hword1.trans readWord_gen27Input1.symm
    · simpa using hword2.trans readWord_gen27Input2.symm
    · simpa using hword3.trans readWord_gen27Input3.symm

#print axioms input_eq_gen27

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Gen27Recognition
