import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedLaneRoundSemantic
import EvmSemantics.Crypto.Ripemd160
import Init.Data.UInt.Bitwise

set_option warningAsError true

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedLaneCryptoBridge

open PairedLaneCore PairedLaneBoolean PairedLaneRoundSemantic
open EvmSemantics

theorem select_xor (x y z : BitVec w) :
    ((y ^^^ z) &&& x) ^^^ z = (x &&& y) ||| ((~~~x) &&& z) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_or,
    BitVec.getLsbD_not, hi, decide_true, Bool.true_and]
  cases x.getLsbD i <;> cases y.getLsbD i <;> cases z.getLsbD i <;> rfl

theorem crypto_f_toBitVec (j : Nat) (b c d : UInt32) :
    (Crypto.Ripemd160.f j b c d).toBitVec =
      PairedLaneBoolean.f j (BitVec.allOnes 32) b.toBitVec c.toBitVec d.toBitVec := by
  cases j with
  | zero => rfl
  | succ j => cases j with
    | zero =>
      change (b.toBitVec &&& c.toBitVec) |||
          ((b.toBitVec ^^^ BitVec.allOnes 32) &&& d.toBitVec) = _
      rw [BitVec.xor_allOnes]
      exact (select_xor b.toBitVec c.toBitVec d.toBitVec).symm
    | succ j => cases j with
      | zero =>
        change (b.toBitVec ||| (c.toBitVec ^^^ BitVec.allOnes 32)) ^^^ d.toBitVec =
          ((c.toBitVec ^^^ BitVec.allOnes 32) ||| b.toBitVec) ^^^ d.toBitVec
        exact congrArg (fun n => n ^^^ d.toBitVec) (BitVec.or_comm _ _)
      | succ j => cases j with
        | zero =>
          change (b.toBitVec &&& d.toBitVec) |||
              (c.toBitVec &&& (d.toBitVec ^^^ BitVec.allOnes 32)) = _
          rw [BitVec.xor_allOnes, BitVec.and_comm b.toBitVec d.toBitVec,
            BitVec.and_comm c.toBitVec (~~~d.toBitVec)]
          exact (select_xor d.toBitVec b.toBitVec c.toBitVec).symm
        | succ j =>
          change b.toBitVec ^^^ (c.toBitVec ||| (d.toBitVec ^^^ BitVec.allOnes 32)) =
            ((d.toBitVec ^^^ BitVec.allOnes 32) ||| c.toBitVec) ^^^ b.toBitVec
          rw [BitVec.or_comm c.toBitVec (d.toBitVec ^^^ BitVec.allOnes 32),
            BitVec.xor_comm b.toBitVec]

theorem crypto_rotl_toBitVec (x : UInt32) (r : Nat)
    (hr0 : 0 < r) (hr : r < 32) :
    (Crypto.Ripemd160.rotl32 x r).toBitVec = x.toBitVec.rotateLeft r := by
  apply BitVec.eq_of_toNat_eq
  have hwide : r < UInt32.size := Nat.lt_trans hr (by decide)
  have hback : 32 - r < 32 := by omega
  have hbackWide : 32 - r < UInt32.size := Nat.lt_trans hback (by decide)
  change (Crypto.Ripemd160.rotl32 x r).toNat = _
  simp only [Crypto.Ripemd160.rotl32, UInt32.toNat_or, UInt32.toNat_shiftLeft,
    UInt32.toNat_shiftRight, UInt32.toNat_ofNat_of_lt' hwide,
    UInt32.toNat_ofNat_of_lt' hbackWide, Nat.mod_eq_of_lt hr,
    Nat.mod_eq_of_lt hback, BitVec.rotateLeft_def, BitVec.toNat_or,
    BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight]
  rfl

structure CryptoLane where
  a : UInt32
  b : UInt32
  c : UInt32
  d : UInt32
  e : UInt32

def bits (q : CryptoLane) : Lane 32 :=
  ⟨q.a.toBitVec, q.b.toBitVec, q.c.toBitVec, q.d.toBitVec, q.e.toBitVec⟩

/-- The exact scalar update from the pinned Crypto.compressBlock loops. -/
def cryptoStep (j r : Nat) (word k : UInt32) (q : CryptoLane) : CryptoLane :=
  ⟨q.e, Crypto.Ripemd160.rotl32 (q.a + Crypto.Ripemd160.f j q.b q.c q.d + word + k) r + q.e,
    q.b, Crypto.Ripemd160.rotl32 q.c 10, q.d⟩

theorem cryptoStep_bits (j r : Nat) (hr0 : 0 < r) (hr : r < 32)
    (word k : UInt32) (q : CryptoLane) :
    bits (cryptoStep j r word k q) =
      scalarStep j r word.toBitVec k.toBitVec (bits q) := by
  cases q
  unfold bits cryptoStep scalarStep scalarT scalarSum
  simp only [UInt32.toBitVec_add, crypto_rotl_toBitVec _ r hr0 hr,
    crypto_rotl_toBitVec _ 10 (by decide) (by decide), crypto_f_toBitVec]

theorem pairedStep_of_crypto (j r s : Nat)
    (hr0 : 0 < r) (hr : r < 32) (hs0 : 0 < s) (hs : s < 32)
    (wl wr kl kr : UInt32) (l q : CryptoLane) :
    pairedStep j r s (pack wl.toBitVec wr.toBitVec) (pack kl.toBitVec kr.toBitVec)
        (packLane (bits l) (bits q)) =
      packLane (bits (cryptoStep j r wl kl l)) (bits (cryptoStep (4 - j) s wr kr q)) := by
  rw [pairedStep_pack j r s hr0 hr hs0 hs,
    cryptoStep_bits j r hr0 hr, cryptoStep_bits (4 - j) s hs0 hs]

#print axioms select_xor
#print axioms crypto_f_toBitVec
#print axioms crypto_rotl_toBitVec
#print axioms cryptoStep_bits
#print axioms pairedStep_of_crypto

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedLaneCryptoBridge
