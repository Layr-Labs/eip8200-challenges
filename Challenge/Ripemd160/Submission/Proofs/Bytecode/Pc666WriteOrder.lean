import Challenge.Ripemd160.Submission.Proofs.Bytecode.Pair13WriterRaw

set_option warningAsError true

/-!
# A certified local memory-order step for the PC666 experiment

This lemma is independent of the submitted artifact. It proves only the store
commutations needed by the measured experimental rewrite, for arbitrary word
values and arbitrary initial memory. It does not prove executable correctness
of pc666-experiment.hex and must not be used as a substitute for that endpoint.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Pc666WriteOrder

open EvmSemantics EvmSemantics.EVM
open Pair13WriterRaw

/-- The moved 666 store crosses six disjoint windows. Overlapping schedule
neighbors 684 and 648 are deliberately not included in the crossed list. -/
theorem move_666 (memory : ByteArray) (words : Nat → UInt256) :
    writeChain memory
      [(540, words 1), (756, words 9), (522, words 0),
       (90, words 12), (72, words 4), (54, words 0), (666, words 14)] =
    writeChain memory
      [(666, words 14), (540, words 1), (756, words 9), (522, words 0),
       (90, words 12), (72, words 4), (54, words 0)] := by
  simp only [writeChain_cons]
  rw [writeWord_comm _ 54 666 _ _ (by decide),
    writeWord_comm _ 72 666 _ _ (by decide),
    writeWord_comm _ 90 666 _ _ (by decide),
    writeWord_comm _ 522 666 _ _ (by decide),
    writeWord_comm _ 756 666 _ _ (by decide),
    writeWord_comm _ 540 666 _ _ (by decide)]

#print axioms move_666

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Pc666WriteOrder
