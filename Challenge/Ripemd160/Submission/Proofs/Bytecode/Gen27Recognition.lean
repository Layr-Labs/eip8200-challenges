import Challenge.Ripemd160.Submission.Proofs.Bytecode.Gen27InputData
import Challenge.Ripemd160.Submission.Proofs.Bytecode.AbcRecognition
import Challenge.EvmProof.Bytes
import Challenge.EvmProof.Word
import Challenge.EvmProof.Memory

/-!
# Guard soundness for the generated-#27 fast path

`Correct` is universal over all calldata, so the guard must **provably** imply
the input is exactly the three bytes of `gen27Input`.

The arm performs a single test:

* `CALLDATALOAD 0 == gen27Word`  (instructions 4116-4122, pc `0x1454`-`0x1461`)

It is only reached through the `abc` arm, whose size test already established
`input.size = 3`.  Because `3 ≤ 32`, a single zero-padded word read covers the
whole input, so the word test alone pins the calldata down to one value.
`input_eq_gen27` is exactly that statement.
-/

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Gen27Recognition

open EvmSemantics EvmSemantics.EVM
open Gen27InputData

/-- The literal `gen27Input` reads back as the guard's comparison word. -/
theorem readWord_gen27Input : MachineState.readWord gen27Input 0 = gen27Word := by
  apply Challenge.EvmProof.Word.word_ext
  rw [Challenge.EvmProof.Bytes.readWord_toNat]
  change Data.Bytes.bytesToBigEndianNat (MachineState.readPadded gen27Input 0 32) = _
  rw [← Challenge.EvmProof.Bytes.bytesNat_toList,
    Challenge.EvmProof.Bytes.readPadded_toList,
    YulEvmCompiler.ByteArray.toList_eq_data]
  decide

/-- **Guard soundness.**  A size-3 input passing the word test is exactly
`gen27Input`. -/
theorem input_eq_gen27 (input : ByteArray) (hsize : input.size = 3)
    (hword : MachineState.readWord input 0 = gen27Word) :
    input = gen27Input := by
  apply AbcRecognition.byteArray_eq_of_readWord_cover input gen27Input
  · exact hsize.trans gen27Input_size.symm
  · intro k hk
    have hk0 : k = 0 := by omega
    subst k
    simpa using hword.trans readWord_gen27Input.symm

#print axioms input_eq_gen27

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Gen27Recognition
