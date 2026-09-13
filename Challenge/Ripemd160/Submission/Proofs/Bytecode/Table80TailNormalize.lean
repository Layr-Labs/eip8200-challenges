import Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80FinalBridgeMemory

set_option warningAsError true
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80TailNormalize
open EvmSemantics Paired80WordRound Table80FinalBridge

theorem resultMemory_normalize (memory : ByteArray) (q : WordLane)
    (h : Compression.HashState)
    (hh : StackMemory.hashAt memory = Compression.embedHash h) :
    Table80Tail.resultMemory memory (Paired80FinalWord.normalizeLane q) =
      Table80Tail.resultMemory memory q := by
  rw [resultMemory_eq_storeHash _ _ h hh, resultMemory_eq_storeHash _ _ h hh,
    Paired80FinalWord.combine_normalize]

theorem resultMemory_eq_of_normalize_eq (memory : ByteArray) (a b : WordLane)
    (h : Compression.HashState)
    (hh : StackMemory.hashAt memory = Compression.embedHash h)
    (heq : Paired80FinalWord.normalizeLane a = Paired80FinalWord.normalizeLane b) :
    Table80Tail.resultMemory memory a = Table80Tail.resultMemory memory b := by
  rw [← resultMemory_normalize memory a h hh, ← resultMemory_normalize memory b h hh, heq]

theorem combineWord_normalize (memory : ByteArray) (address : Nat) (left right : UInt256) :
    Table80Tail.combineWord memory address
      (UInt256.land left Paired80WordBoolean.pairWord)
      (UInt256.land right Paired80WordBoolean.pairWord) =
    Table80Tail.combineWord memory address left right := by
  rw [Table80Tail.tail_combine_normalized, Table80Tail.tail_combine_normalized]
  have hl := Paired80FinalWord.low32_mask left
  have hr := Paired80FinalWord.high32_mask right
  change Challenge.EvmProof.Word.toUInt32 (UInt256.land left Paired80WordBoolean.pairWord) =
    Challenge.EvmProof.Word.toUInt32 left at hl
  change Challenge.EvmProof.Word.toUInt32
    (UInt256.shiftRight (UInt256.land right Paired80WordBoolean.pairWord) (UInt256.ofNat 80)) =
    Challenge.EvmProof.Word.toUInt32 (UInt256.shiftRight right (UInt256.ofNat 80)) at hr
  rw [hl, hr]

theorem resultMemory_normalize_arbitrary (memory : ByteArray) (q : WordLane) :
    Table80Tail.resultMemory memory (Paired80FinalWord.normalizeLane q) =
      Table80Tail.resultMemory memory q := by
  simp only [Table80Tail.resultMemory, Table80Tail.result0, Table80Tail.result1,
    Table80Tail.result2, Table80Tail.result3, Table80Tail.result4,
    Paired80FinalWord.normalizeLane, combineWord_normalize]

theorem resultMemory_eq_of_normalize_eq_arbitrary (memory : ByteArray) (a b : WordLane)
    (heq : Paired80FinalWord.normalizeLane a = Paired80FinalWord.normalizeLane b) :
    Table80Tail.resultMemory memory a = Table80Tail.resultMemory memory b := by
  rw [← resultMemory_normalize_arbitrary memory a,
    ← resultMemory_normalize_arbitrary memory b, heq]

#print axioms resultMemory_normalize_arbitrary
#print axioms resultMemory_eq_of_normalize_eq_arbitrary
#print axioms resultMemory_normalize
#print axioms resultMemory_eq_of_normalize_eq
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80TailNormalize
