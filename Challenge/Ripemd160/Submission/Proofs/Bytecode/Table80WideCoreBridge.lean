import Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80TerminalTranspose
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired80WordRotate
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired80WordRound
set_option warningAsError true
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80WideCoreBridge
open EvmSemantics PairedLaneUInt256Bridge Paired80WordRotate Paired80WordBoolean

def wideFactorWord : UInt256 := word Table80TerminalTranspose.wideFactor

def wideWordShift (x : UInt256) (n : Nat) : UInt256 :=
  UInt256.shiftRight (UInt256.mul x wideFactorWord) (UInt256.ofNat n)

theorem bits_wideWordShift (x : UInt256) (n : Nat) (hn : n < 256) :
    bits (wideWordShift x n) = (bits x * Table80TerminalTranspose.wideFactor) >>> n := by
  unfold wideWordShift
  rw [bits_productShift x wideFactorWord n hn]
  simp only [wideFactorWord, bits_word]

theorem shift_eq112 (x : UInt256) (n : Nat) (hn : n ≤ 43) :
    Paired80Message.Eq112 (bits (wideWordShift x n)) (bits (wordShift x n)) := by
  rw [bits_wideWordShift _ _ (by omega), bits_wordShift _ _ (by omega)]
  exact Table80TerminalTranspose.eq112_wide_shift _ _ hn

theorem masked_shift (x : UInt256) (n : Nat) (hn : n ≤ 43) :
    UInt256.land (wideWordShift x n) pairWord = UInt256.land (wordShift x n) pairWord := by
  apply bits_injective
  simp only [bits_land, pairWord, bits_word, ← Paired80Core.normalize_eq_and]
  exact Paired80Message.normalize_congr _ _ (shift_eq112 x n hn)

theorem masked_shift_add (x e : UInt256) (n : Nat) (hn : n ≤ 43) :
    UInt256.land (UInt256.add (wideWordShift x n) e) pairWord =
      UInt256.land (UInt256.add (wordShift x n) e) pairWord := by
  apply bits_injective
  simp only [bits_land, bits_add, pairWord, bits_word, ← Paired80Core.normalize_eq_and]
  exact Paired80Message.normalize_congr _ _ (Paired80Message.add_right _ _ _ (shift_eq112 x n hn))

private theorem mul_comm (x y : UInt256) : UInt256.mul x y = UInt256.mul y x := by
  apply bits_injective
  simp only [bits_mul]
  exact BitVec.mul_comm _ _
private theorem add_comm (x y : UInt256) : UInt256.add x y = UInt256.add y x := by
  apply bits_injective
  simp only [bits_add]
  exact BitVec.add_comm _ _
private theorem land_comm (x y : UInt256) : UInt256.land x y = UInt256.land y x := by
  apply bits_injective
  simp only [bits_land]
  exact BitVec.and_comm _ _

theorem masked_shift_raw (x : UInt256) (n : Nat) (hn : n ≤ 43) :
    UInt256.land pairWord (UInt256.shiftRight (UInt256.mul wideFactorWord x) (UInt256.ofNat n)) =
      UInt256.land pairWord (UInt256.shiftRight (UInt256.mul factorWord x) (UInt256.ofNat n)) := by
  simpa only [wideWordShift, wordShift, mul_comm, land_comm] using masked_shift x n hn

theorem masked_shift_add_raw (x e : UInt256) (n : Nat) (hn : n ≤ 43) :
    UInt256.land pairWord (UInt256.add e
      (UInt256.shiftRight (UInt256.mul wideFactorWord x) (UInt256.ofNat n))) =
    UInt256.land pairWord (UInt256.add e
      (UInt256.shiftRight (UInt256.mul factorWord x) (UInt256.ofNat n))) := by
  simpa only [wideWordShift, wordShift, mul_comm, add_comm, land_comm] using masked_shift_add x e n hn

#print axioms masked_shift_raw
#print axioms masked_shift_add_raw

#print axioms shift_eq112
#print axioms masked_shift
#print axioms masked_shift_add
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80WideCoreBridge
