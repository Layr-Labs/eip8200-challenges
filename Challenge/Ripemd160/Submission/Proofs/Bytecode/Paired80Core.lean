import Init.Data.BitVec.Lemmas

set_option warningAsError true

/-!
Two arbitrary 32-bit lanes occupy bits [0,32) and [80,112).  The
48-bit spacers absorb the carries of the four input summands.  This
module has no bytecode, memory, scored-input, or artifact dependency.
All proofs below are ordinary extract/bitwise/arithmetic proofs; no
native decision procedure or externally trusted certificate is used.
-/
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired80Core

def pack (lo hi : BitVec 32) : BitVec 256 :=
  hi.setWidth 176 ++ lo.setWidth 80

def low (x : BitVec 256) : BitVec 32 := x.extractLsb' 0 32
def high (x : BitVec 256) : BitVec 32 := x.extractLsb' 80 32

def normalize (x : BitVec 256) : BitVec 256 := pack (low x) (high x)
def pairMask : BitVec 256 := pack (BitVec.allOnes 32) (BitVec.allOnes 32)

@[simp] theorem low_pack (lo hi : BitVec 32) : low (pack lo hi) = lo := by
  unfold low pack
  rw [BitVec.extractLsb'_append_eq_of_add_le (by decide),
    BitVec.extractLsb'_setWidth_of_le (by decide)]
  exact BitVec.extractLsb'_eq_self

@[simp] theorem high_pack (lo hi : BitVec 32) : high (pack lo hi) = hi := by
  unfold high pack
  rw [BitVec.extractLsb'_append_eq_of_le (by decide)]
  simp only [Nat.sub_self]
  rw [BitVec.extractLsb'_setWidth_of_le (by decide)]
  exact BitVec.extractLsb'_eq_self

theorem pack_injective {a b c d : BitVec 32} (h : pack a b = pack c d) :
    a = c ∧ b = d := by
  constructor
  · simpa only [low_pack] using congrArg low h
  · simpa only [high_pack] using congrArg high h

@[simp] theorem normalize_pack (lo hi : BitVec 32) :
    normalize (pack lo hi) = pack lo hi := by
  simp only [normalize, low_pack, high_pack]

@[simp] theorem normalize_idem (x : BitVec 256) :
    normalize (normalize x) = normalize x := by
  exact normalize_pack (low x) (high x)

theorem normalize_eq_and (x : BitVec 256) :
    normalize x = x &&& pairMask := by
  unfold normalize low high pairMask pack
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_and,
    BitVec.getLsbD_append
      (x := (x.extractLsb' 80 32).setWidth 176)
      (y := (x.extractLsb' 0 32).setWidth 80),
    BitVec.getLsbD_append
      (x := (BitVec.allOnes 32).setWidth 176)
      (y := (BitVec.allOnes 32).setWidth 80)]
  by_cases h : i < 80
  · simp only [h, if_pos, BitVec.getLsbD_setWidth,
      BitVec.getLsbD_extractLsb', BitVec.getLsbD_allOnes,
      decide_true, Bool.true_and, Nat.zero_add, Bool.and_comm]
  · have hi' : i - 80 < 176 := by omega
    have hindex : 80 + (i - 80) = i := by omega
    simp only [h, ite_false, BitVec.getLsbD_setWidth,
      BitVec.getLsbD_extractLsb', BitVec.getLsbD_allOnes,
      hi', hindex, decide_true, Bool.true_and]
    exact Bool.and_comm _ _

theorem pairMask_value :
    pairMask = BitVec.ofNat 256 0xffffffff000000000000ffffffff := by
  decide

#print axioms low_pack
#print axioms high_pack
#print axioms pack_injective
#print axioms normalize_pack
#print axioms normalize_idem
#print axioms normalize_eq_and
#print axioms pairMask_value

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired80Core
