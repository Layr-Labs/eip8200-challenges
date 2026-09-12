import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedLaneUInt256Bridge
import Init.Data.Nat.Bitwise.Lemmas

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionSwar

private def repeatByte (n : Nat) : Nat :=
  n * 0x0101010101010101010101010101010101010101010101010101010101010101

def lowMask : BitVec 256 := BitVec.ofNat 256 (repeatByte 127)
def highMask : BitVec 256 := BitVec.ofNat 256 (repeatByte 128)
def increment32 : BitVec 256 := BitVec.ofNat 256 (repeatByte 32)
def increment43 : BitVec 256 := BitVec.ofNat 256 (repeatByte 43)

def advance32 (x : BitVec 256) : BitVec 256 :=
  ((x &&& lowMask) + increment32) ^^^ ((~~~x) &&& highMask)

def advance43 (x : BitVec 256) : BitVec 256 :=
  ((x &&& lowMask) + increment43) ^^^ ((~~~x) &&& highMask)

/-- All byte-boundary carry tests, including the final 256-bit boundary. -/
private theorem constants32 : ∀ j : Fin 33,
    lowMask.toNat % 2 ^ (8 * j.val) + increment32.toNat % 2 ^ (8 * j.val) <
      2 ^ (8 * j.val) := by decide

private theorem constants43 : ∀ j : Fin 33,
    lowMask.toNat % 2 ^ (8 * j.val) + increment43.toNat % 2 ^ (8 * j.val) <
      2 ^ (8 * j.val) := by decide

theorem no_carry32 (x : BitVec 256) (j : Fin 33) :
    (x &&& lowMask).toNat % 2 ^ (8 * j.val) + increment32.toNat % 2 ^ (8 * j.val) <
      2 ^ (8 * j.val) := by
  rw [BitVec.toNat_and, Nat.and_mod_two_pow]
  have hb : (x.toNat % 2 ^ (8 * j.val)) &&& (lowMask.toNat % 2 ^ (8 * j.val)) ≤
      lowMask.toNat % 2 ^ (8 * j.val) := Nat.and_le_right
  have hc := constants32 j
  omega

theorem no_carry43 (x : BitVec 256) (j : Fin 33) :
    (x &&& lowMask).toNat % 2 ^ (8 * j.val) + increment43.toNat % 2 ^ (8 * j.val) <
      2 ^ (8 * j.val) := by
  rw [BitVec.toNat_and, Nat.and_mod_two_pow]
  have hb : (x.toNat % 2 ^ (8 * j.val)) &&& (lowMask.toNat % 2 ^ (8 * j.val)) ≤
      lowMask.toNat % 2 ^ (8 * j.val) := Nat.and_le_right
  have hc := constants43 j
  omega

private theorem all_byte32 : ∀ x : BitVec 8,
    ((x &&& 127#8) + 32#8) ^^^ ((~~~x) &&& 128#8) = x + 160#8 := by decide
private theorem all_byte43 : ∀ x : BitVec 8,
    ((x &&& 127#8) + 43#8) ^^^ ((~~~x) &&& 128#8) = x + 171#8 := by decide

theorem byte32 (x : BitVec 8) :
    ((x &&& 127#8) + 32#8) ^^^ ((~~~x) &&& 128#8) = x + 160#8 := all_byte32 x

theorem byte43 (x : BitVec 8) :
    ((x &&& 127#8) + 43#8) ^^^ ((~~~x) &&& 128#8) = x + 171#8 := all_byte43 x

#print axioms no_carry32
#print axioms no_carry43
#print axioms byte32
#print axioms byte43

end Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionSwar
