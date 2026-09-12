import Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80LateMask77
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80WideFinalWord
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80ConsumedTerminalTail
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80TailNormalize
set_option warningAsError true
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80WideFinalMemory
open EvmSemantics Paired80WordRound Paired80Algorithm Paired80CryptoBridge

private theorem storedMemory_eq_old (memory : ByteArray) (message : Nat → UInt256)
    (words : Nat → UInt32) (l q : CryptoLane) (hm : MessageReady message words 80) :
    Table80ConsumedTerminalTail.storedMemory memory
      (Table80LateMask77.finish message (fold message 77 (packCrypto l q))) =
    Table80Tail.resultMemory memory
      (Paired80FinalWord.finish message (fold message 78 (packCrypto l q))) := by
  rw [Table80ConsumedTerminalTail.storedMemory_eq]
  apply Table80TailNormalize.resultMemory_eq_of_normalize_eq_arbitrary
  exact Table80LateMask77.finish_fold_eq_old message words l q hm

theorem resultMemory_eq_old (memory : ByteArray) (message : Nat → UInt256)
    (words : Nat → UInt32) (l q : CryptoLane) (hm : MessageReady message words 80) :
    Table80ConsumedTerminalTail.resultMemory memory
      (Table80LateMask77.finish message (fold message 77 (packCrypto l q))) =
    Table80Tail.cleanedResultMemory memory
      (Paired80FinalWord.finish message (fold message 78 (packCrypto l q))) := by
  exact congrArg Table80Cleanup.memory (storedMemory_eq_old memory message words l q hm)

#print axioms resultMemory_eq_old
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80WideFinalMemory
