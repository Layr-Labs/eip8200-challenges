import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairTable144Sparse
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadShiftDiet
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PairTable144Pad
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open PairTable144Memory PairTable144Layout PairTable144Sparse

def lowLength (n : UInt256) : UInt256 :=
  UInt256.land (UInt256.ofNat 0xffffffff) (UInt256.shiftLeft n (UInt256.ofNat 3))
def highLength (n : UInt256) : UInt256 :=
  UInt256.land (UInt256.ofNat 0xffffffff) (UInt256.shiftRight n (UInt256.ofNat 29))
def padWords (n : UInt256) (i : Nat) : UInt256 :=
  if i = 0 then UInt256.ofNat 128 else
  if i = 14 then lowLength n else
  if i = 15 then highLength n else UInt256.ofNat 0

def keepPad (j : Nat) : Bool :=
  decide (slots[j]! = 0 ∨ slots[j]! = 14 ∨ slots[j]! = 15)

def resultMemory (memory : ByteArray) (n : UInt256) : ByteArray :=
  storeSelected (zeroMemory memory) (tableWords (padWords n)) keepPad 0 78

private theorem masked_bound (value : UInt256) :
    (UInt256.land (UInt256.ofNat 0xffffffff) value).toNat < 2 ^ 32 := by
  rw [Word.word_toNat_land]
  have hm : (UInt256.ofNat 0xffffffff).toNat = 0xffffffff := by decide
  rw [hm]
  exact Nat.lt_of_le_of_lt Nat.and_le_left (by decide)

theorem padWords_bound (n : UInt256) (i : Nat) :
    (padWords n i).toNat < 2 ^ 32 := by
  unfold padWords
  split
  · decide
  · split
    · exact masked_bound _
    · split
      · exact masked_bound _
      · decide

theorem resultMemory_eq_table (memory : ByteArray) (n : UInt256) :
    resultMemory memory n = PairTable144Layout.resultMemory memory (padWords n) := by
  unfold resultMemory
  refine (selected_eq_full memory (tableWords (padWords n)) keepPad 0 78
    (by decide) ?_ ?_).trans (erase_zeroMemory _ _)
  · intro j hj hj'
    exact padWords_bound n slots[j]!
  · intro j hj hj' hk
    have h : ¬ (slots[j]! = 0 ∨ slots[j]! = 14 ∨ slots[j]! = 15) :=
      of_decide_eq_false hk
    simp only [tableWords, padWords,
      if_neg (show slots[j]! ≠ 0 by omega), if_neg (show slots[j]! ≠ 14 by omega),
      if_neg (show slots[j]! ≠ 15 by omega)]

theorem readPadded_end (input : ByteArray) :
    MachineState.readPadded input input.size 1418 = PairTable144Sparse.zeroBytes := by
  simp [MachineState.readPadded, PairTable144Sparse.zeroBytes]

#print axioms padWords_bound
#print axioms resultMemory_eq_table
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PairTable144Pad
