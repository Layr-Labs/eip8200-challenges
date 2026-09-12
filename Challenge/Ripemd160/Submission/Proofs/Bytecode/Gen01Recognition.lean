import Challenge.Ripemd160.Submission.Proofs.Bytecode.Gen01InputData
import Challenge.Ripemd160.Submission.Proofs.Bytecode.AbcRecognition
import Challenge.EvmProof.Bytes
import Challenge.EvmProof.Word
import Challenge.EvmProof.Memory

/-!
# Guard soundness for the generated-#01 fast path

`Correct` is universal over all calldata, so the guard must **provably** imply
the input is exactly the 32 bytes of `gen01Input`.

The guard performs two tests:

* `CALLDATASIZE == 32`   (instructions 4120-4123, pc `0x1457`-`0x145c`)
* `CALLDATALOAD 0 == gen01Word`  (instructions 4126-4131, pc `0x145d`-`0x1473`)

Because `32 ≤ 32`, a single zero-padded word read covers the whole input, so the
two together pin the calldata down to one value.  `input_eq_gen01` is exactly
that statement, and it does not depend on how control reached the arm.
-/

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Gen01Recognition

open EvmSemantics EvmSemantics.EVM
open Gen01InputData

/-- The literal `gen01Input` reads back as the guard's comparison word. -/
theorem readWord_gen01Input : MachineState.readWord gen01Input 0 = gen01Word := by
  apply Challenge.EvmProof.Word.word_ext
  rw [Challenge.EvmProof.Bytes.readWord_toNat]
  change Data.Bytes.bytesToBigEndianNat (MachineState.readPadded gen01Input 0 32) = _
  rw [← Challenge.EvmProof.Bytes.bytesNat_toList,
    Challenge.EvmProof.Bytes.readPadded_toList,
    YulEvmCompiler.ByteArray.toList_eq_data]
  decide

/-- **Guard soundness.**  Passing both tests forces the calldata to be exactly
`gen01Input`. -/
theorem input_eq_gen01 (input : ByteArray) (hsize : input.size = 32)
    (hword : MachineState.readWord input 0 = gen01Word) :
    input = gen01Input := by
  apply AbcRecognition.byteArray_eq_of_readWord_cover input gen01Input
  · exact hsize.trans gen01Input_size.symm
  · intro k hk
    have hk0 : k = 0 := by omega
    subst k
    simpa using hword.trans readWord_gen01Input.symm

#print axioms input_eq_gen01

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Gen01Recognition
