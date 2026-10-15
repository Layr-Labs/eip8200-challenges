import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedLaneUInt256Bridge
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DenseScheduleTemplate
import Init.Data.BitVec.Bitblast

set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 10000000

/-!
# Shift-free multiplication byte swap of the digest word

The epilogue swaps the bytes of each 32-bit lane of the packed 160-bit digest word `v`.
Instead of the former XOR/shift/multiply stages it uses, for a mask `m` selecting the low
half of every lane pair,

  `v + (v & m) * (2^k - 1) = (swap_k v) * 2^k`

where `swap_k` swaps the two `k`-bit halves of every `2k`-bit lane.  The right-hand side is
kept scaled by `2^k`, so no right shift is executed; the stage order (16 then 8) makes the
second mask periodic under the first scaling.  The `2^24` scaling is absorbed by a store at
byte offset three.  All identities are exact in `BitVec 256`.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.FinishMath

open EvmSemantics Challenge.EvmProof PairedLaneUInt256Bridge DenseScheduleTemplate

def M8 : BitVec 256 :=
  BitVec.ofNat 256 0x00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff

def M16 : BitVec 256 :=
  BitVec.ofNat 256 0x0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff

def P8 (x : BitVec 256) : BitVec 256 := ((x &&& M8) <<< 8) ||| ((x >>> 8) &&& M8)
def P16 (x : BitVec 256) : BitVec 256 := ((x &&& M16) <<< 16) ||| ((x >>> 16) &&& M16)

private theorem masked_disjoint (x mask : BitVec w) (shift : Nat)
    (h : (~~~mask) &&& (mask <<< shift) = 0#w) :
    (x &&& ~~~mask) &&& ((x &&& mask) <<< shift) = 0#w := by
  rw [BitVec.shiftLeft_and_distrib]
  calc
    (x &&& ~~~mask) &&& ((x <<< shift) &&& (mask <<< shift)) =
        (x &&& (x <<< shift)) &&& ((~~~mask) &&& (mask <<< shift)) := by
      ac_rfl
    _ = 0#w := by rw [h]; simp

private theorem split_add (x m : BitVec 256) : x = (x &&& m) + (x &&& ~~~m) := by
  have hd : (x &&& m) &&& (x &&& ~~~m) = 0#256 := by
    calc (x &&& m) &&& (x &&& ~~~m) = x &&& (x &&& (m &&& ~~~m)) := by ac_rfl
      _ = 0#256 := by simp
  rw [BitVec.add_eq_or_of_and_eq_zero _ _ hd]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, decide_true,
    Bool.true_and]
  cases x.getLsbD i <;> cases m.getLsbD i <;> rfl

set_option linter.unusedSimpArgs false in
theorem fast16 (x : BitVec 256) :
    x + (x &&& M16) * BitVec.ofNat 256 4294967295 = (P16 x) <<< 16 := by
  have hnot : (~~~M16) &&& (M16 <<< 32) = 0#256 := by decide
  have hd := masked_disjoint x M16 32 hnot
  have harith : ∀ t u : BitVec 256,
      (t + u) + t * BitVec.ofNat 256 4294967295 = u + t * BitVec.ofNat 256 4294967296 := by
    intro t u; bv_omega
  have h1 := harith (x &&& M16) (x &&& ~~~M16)
  rw [← split_add x M16] at h1
  have hshl : ∀ t : BitVec 256, t * BitVec.ofNat 256 4294967296 = t <<< 32 := by
    intro t
    rw [BitVec.shiftLeft_eq_mul_twoPow]
    congr 1
  rw [h1, hshl, add_comm, BitVec.add_eq_or_of_and_eq_zero _ _ (by rw [BitVec.and_comm]; exact hd)]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  interval_cases i <;>
    simp [P16, M16, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
      BitVec.getLsbD_ofNat, Nat.testBit, BitVec.getLsbD_not]

set_option linter.unusedSimpArgs false in
theorem fast8 (x : BitVec 256) :
    x + (x &&& M8) * BitVec.ofNat 256 65535 = (P8 x) <<< 8 := by
  have hnot : (~~~M8) &&& (M8 <<< 16) = 0#256 := by decide
  have hd := masked_disjoint x M8 16 hnot
  have harith : ∀ t u : BitVec 256,
      (t + u) + t * BitVec.ofNat 256 65535 = u + t * BitVec.ofNat 256 65536 := by
    intro t u; bv_omega
  have h1 := harith (x &&& M8) (x &&& ~~~M8)
  rw [← split_add x M8] at h1
  have hshl : ∀ t : BitVec 256, t * BitVec.ofNat 256 65536 = t <<< 16 := by
    intro t
    rw [BitVec.shiftLeft_eq_mul_twoPow]
    congr 1
  rw [h1, hshl, add_comm, BitVec.add_eq_or_of_and_eq_zero _ _ (by rw [BitVec.and_comm]; exact hd)]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  interval_cases i <;>
    simp [P8, M8, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
      BitVec.getLsbD_ofNat, Nat.testBit, BitVec.getLsbD_not]

set_option linter.unusedSimpArgs false in
theorem P8_shl16 (z : BitVec 256) : P8 (z <<< 16) = (P8 z) <<< 16 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  interval_cases i <;>
    simp [P8, M8, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
      BitVec.getLsbD_ofNat, Nat.testBit]

set_option linter.unusedSimpArgs false in
theorem P16_P8_comm (v : BitVec 256) : P16 (P8 v) = P8 (P16 v) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  interval_cases i <;>
    simp [P8, P16, M8, M16, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
      BitVec.getLsbD_ofNat, Nat.testBit]

/-- Both executed stages together: the digest word byte-swapped and scaled by `2^24`. -/
theorem fast_all (v : BitVec 256) :
    (v + (v &&& M16) * BitVec.ofNat 256 4294967295) +
      ((v + (v &&& M16) * BitVec.ofNat 256 4294967295) &&&  M8) * BitVec.ofNat 256 65535 =
      (P16 (P8 v)) <<< 24 := by
  rw [fast16 v]
  rw [fast8 ((P16 v) <<< 16)]
  rw [P8_shl16, P16_P8_comm, ← BitVec.shiftLeft_add]

#print axioms fast16
#print axioms fast8
#print axioms P8_shl16
#print axioms P16_P8_comm

end Challenge.Ripemd160.Submission.Proofs.Bytecode.FinishMath
