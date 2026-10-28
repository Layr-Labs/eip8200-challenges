import Challenge.Ripemd160.Submission.Local20261028.CoreModel
set_option warningAsError true
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.CoreMessage
open EvmSemantics EvmSemantics.EVM
structure Ready (memory : ByteArray) (words : Nat → UInt32) : Prop where
  paired : StaggerAlgorithm.MessageReady (CoreModel.message memory) words 77
  scalar : ∀ j, j < 61 → Paired80Compression.low32 (CoreModel.load memory (18*j)) =
    words StaggerTableLayout.slots[j]!
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.CoreMessage
