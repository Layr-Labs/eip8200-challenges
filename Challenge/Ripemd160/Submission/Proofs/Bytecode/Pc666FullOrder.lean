import Challenge.Ripemd160.Submission.Proofs.Bytecode.PoolRawWriter
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000
/- Memory-order certificate only: no binding to experimental executable bytes. -/
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Pc666FullOrder
open EvmSemantics EvmSemantics.EVM Pair13WriterRaw

def reorderedWrites (words : Nat → UInt256) : List (Nat × UInt256) :=
[ (126, words 11),
    (900, words 9),
    (216, words 10),
    (882, words 3),
    (864, words 11),
    (846, words 3),
    (828, words 9),
    (558, words 8),
    (684, words 6),
    (936, words 8),
    (108, words 5),
    (792, words 1),
    (666, words 14),
    (540, words 1),
    (756, words 9),
    (522, words 0),
    (90, words 12),
    (72, words 4),
    (54, words 0),
    (504, words 1),
    (1080, words 5),
    (1062, words 13),
    (486, words 5),
    (972, words 3),
    (648, words 15),
    (1008, words 15),
    (630, words 10),
    (612, words 15),
    (738, words 8),
    (288, words 7),
    (594, words 11),
    (1044, words 6),
    (414, words 6),
    (720, words 5),
    (270, words 15),
    (396, words 4),
    (468, words 1),
    (18, words 4),
    (360, words 2),
    (198, words 13),
    (324, words 10),
    (252, words 7),
    (0, words 6),
    (450, words 12),
    (162, words 14) ]

theorem writerMemory_preserved (m : ByteArray) (words : Nat → UInt256) :
    writeChain m (reorderedWrites words) = PoolRawWriter.writerMemory m words := by
  simp only [reorderedWrites, PoolRawWriter.writerMemory, PoolRawWriter.rawWrites,
    writeChain_cons]
  rw [writeWord_comm _ 666 540 _ _ (by decide),
    writeWord_comm _ 666 756 _ _ (by decide),
    writeWord_comm _ 666 522 _ _ (by decide),
    writeWord_comm _ 666 90 _ _ (by decide),
    writeWord_comm _ 666 72 _ _ (by decide),
    writeWord_comm _ 666 54 _ _ (by decide)]

#print axioms writerMemory_preserved
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Pc666FullOrder
